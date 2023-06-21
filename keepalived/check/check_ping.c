/*
 * Soft:        Keepalived is a failover program for the LVS project
 *              <www.linuxvirtualserver.org>. It monitor & manipulate
 *              a loadbalanced server pool using multi-layer checks.
 *
 * Part:        PING checker.
 *
 * Author:      Jie Liu, <liujie165@huawei.com>
 *
 *              This program is distributed in the hope that it will be useful,
 *              but WITHOUT ANY WARRANTY; without even the implied warranty of
 *              MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *              See the GNU General Public License for more details.
 *
 *              This program is free software; you can redistribute it and/or
 *              modify it under the terms of the GNU General Public License
 *              as published by the Free Software Foundation; either version
 *              2 of the License, or (at your option) any later version.
 *
 * Copyright (C) 2019-2019 Alexandre Cassen, <acassen@gmail.com>
 */
#include "config.h"

/* system includes */
#include <netinet/in.h>
#include <netinet/ip_icmp.h>
#include <netinet/icmp6.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <fcntl.h>

#include "check_ping.h"
#include "check_api.h"
#include "logger.h"
#include "layer4.h"
#include "parser.h"
#include "smtp.h"
#include "ipwrapper.h"

#define ICMP_BUFSIZE 128
#define SOCK_RECV_BUFF 128*1024

// 内核参数net.ipv4.ping_group_range指定了哪些用户组可以创建ICMP Echo sockets
// 默认为1 0表示不允许任何用户组创建（即只有内核本身可以创建）
// 若假设进程组id为10000，则可以将其ping_group_range设置为10000 10000，表示只允许
// 这一个进程组创建ICMP Echo sockets
// keepalived需要修改此range确保keepalived可以创建ICMP Echo sockets
static const char * const ping_group_range = "/proc/sys/net/ipv4/ping_group_range";

static gid_t save_gid_min;
static bool checked_ping_group_range;

static uint16_t seq_no;

static void icmp_connect_thread(thread_ref_t);

// 设置内核参数net.ipv4.ping_group_range，确保keepalived可以创建ICMP Echo sockets
// 因为keepalived总是以root用户运行，用户组为0，因此实际上只需将range_begin改为0即可
bool
set_ping_group_range(bool set)
{
	// buf存放ping_group_range值，格式：range_begin\trange_end\t\n，因此最大23字节
	char buf[10 + 1 + 10 + 1 + 1];	/* 2000000000<TAB>4294967295<NL> */
	int fd;
	ssize_t len, ret;
	unsigned long val[2];
	char *endptr;

	if (set == checked_ping_group_range)
		return true;

	// 打开/proc/sys/net/ipv4/ping_group_range
	fd = open(ping_group_range, O_RDWR);
	if (fd == -1)
		return false;
	len = read(fd, buf, sizeof(buf));

	if (len == -1 || len == sizeof(buf)) {
		close(fd);
		return false;
	}

	buf[len] = '\0';

	// range begin
	val[0] = strtoul(buf, &endptr, 10);
#if ULONG_MAX >= 1UL << 32
	// 检查range begin小于32位无符号整数的最大值
	if (val[0] >= 1UL << 32 || (*endptr != '\t' && *endptr != ' ')) {
		close(fd);
		return false;
	}
#endif

	// range end
	val[1] = strtol(endptr + 1, &endptr, 10);
#if ULONG_MAX >= 1UL << 32
	// 检查range end小于32位无符号整数的最大值
	if (val[1] >= 1UL << 32 || *endptr != '\n') {
		close(fd);
		return false;
	}
#endif

	checked_ping_group_range = set;

	// 如果是要打开权限且range begin已经是0，则直接返回true，因为keepalive是以root权限运行，用户组为0
    // 如果是要恢复OS原初始值且range begin已经是之前keepalived暂存的OS初始值，则直接返回true
	if ((set && val[0] == 0) ||
	    (!set && val[0] == save_gid_min)) {
		close(fd);
		return true;
	}

	// 如果是要打开权限且range begin大于1，说明ping_group_range是其他用户设置过的，不是OS默认值1 0
    // 此时需要发出一条告警，表示keepalived即将要修改ping_group_range中的range begin
	if (set && val[0] > 1 && val[1] > 1)
		log_message(LOG_INFO, "Warning: %s being expanded from %lu %lu to 0 %lu",
				ping_group_range, val[0], val[1], val[1]);

	// 如果是打开权限，range_begin设置为0，如果是关闭权限，则range_begin恢复初始值,range_end保持不变
    // 不用关心range_end，因为keepalived是以root权限运行，即使0 0也可以确保root用户能创建ICMP Echo sockets
	len = sprintf(buf, "%u\t%lu\t\n", set ? 0 : save_gid_min, val[1]);

	// 文件游标移到文件开始处，前面read时已经后移了
	lseek(fd, 0, SEEK_SET);
	// 写入内核参数ping_group_range
	ret = write(fd, buf, len);
	if (ret == -1)
		log_message(LOG_INFO, "Write %s failed - errno %d", ping_group_range, errno);
	else if (ret != len)
		log_message(LOG_INFO, "Write %s wrote %zd bytes instead of %zd", ping_group_range, ret, len);
	close(fd);

	// 保存原range_begin，keepalived退出时需要恢复ping_group_range原始值
	if (set)
		save_gid_min = val[0];

	return true;
}

/* Configuration stream handling */
static void
free_ping_check(checker_t *checker)
{
	FREE(checker->co);
	FREE_PTR(checker->data);
	FREE(checker);
}

static void
dump_ping_check(FILE *fp, __attribute__((unused)) const checker_t *checker)
{
	conf_write(fp, "   Keepalive method = PING_CHECK");
}

static bool
compare_ping_check(const checker_t *a, checker_t *b)
{
	return compare_conn_opts(a->co, b->co);
}

static const checker_funcs_t ping_checker_funcs = { CHECKER_PING, free_ping_check, dump_ping_check, compare_ping_check, NULL };

static void
ping_check_handler(__attribute__((unused)) const vector_t *strvec)
{
	ping_check_t *ping_check = sizeof(ping_check_t) ? MALLOC(sizeof (ping_check_t)) : NULL;

	/* queue new checker */
	queue_checker(&ping_checker_funcs, icmp_connect_thread, ping_check, CHECKER_NEW_CO(), true);

	// 设置内核参数net.ipv4.ping_group_range，确保keepalived可以创建ICMP Echo sockets
	if (!checked_ping_group_range)
		set_ping_group_range(true);
}

static void
ping_check_end_handler(void)
{
	if (!check_conn_opts(CHECKER_GET_CO()))
		dequeue_new_checker();
}

void
install_ping_check_keyword(void)
{
	/* We don't want some common keywords */
	install_keyword("PING_CHECK", &ping_check_handler);
	install_sublevel();
	install_checker_common_keywords(true);
	install_sublevel_end_handler(ping_check_end_handler);
	install_sublevel_end();
}

static enum connect_result
ping_it(int fd, conn_opts_t* co)
{
	struct icmphdr *icmp_hdr;
	// send_buf即完整的icmp报文，包含icmp头和载荷
	char send_buf[sizeof(*icmp_hdr) + ICMP_BUFSIZE] __attribute__((aligned(__alignof__(struct icmphdr))));

	// 填充icmp载荷，这里我们填充的载荷是字符串"keepalived check - "的循环，最长为128字节
	// 注意，icmp request报文是可以携带载荷的，而且对应的reply中必须携带相同载荷
	set_buf(send_buf + sizeof(*icmp_hdr), ICMP_BUFSIZE);

	// 将send_buf强制转换为struct icmphdr指针
	icmp_hdr = PTR_CAST(struct icmphdr, send_buf);

	// 设置icmp头，type为echo request
	memset(icmp_hdr, 0, sizeof(*icmp_hdr));
	icmp_hdr->type = ICMP_ECHO;
	// 序号为全局变量seq_no，初始为0，注意赋值完之后会将seq_no加1
	icmp_hdr->un.echo.sequence = seq_no++;

	// 向rs发送request
	if (sendto(fd, send_buf, sizeof(send_buf), 0, PTR_CAST(struct sockaddr, &co->dst), sizeof(struct sockaddr)) < 0) {
		log_message(LOG_INFO, "send ICMP packet fail");
		// 如果发送失败返回connect_error
		return connect_error;
	}
	// 发送成功返回connect_success，接下来就是等rs reply
	return connect_success;
}

static enum connect_result
recv_it(int fd)
{
	ssize_t len;
	const struct icmphdr *icmp_hdr;
	// recv_buf存放完整icmp reply报文，含icmp头和载荷
	char recv_buf[sizeof(*icmp_hdr) + ICMP_BUFSIZE] __attribute__((aligned(__alignof__(struct icmphdr))));

	// 从socket接收reply报文
	len = recv(fd, recv_buf, sizeof(recv_buf), 0);

	// 接收失败直接返回connect_error
	if (len < 0) {
		log_message(LOG_INFO, "recv ICMP packet error");
		return connect_error;
	}

	// 检查报文长度至少要大于icmp头的长度
	if ((size_t)len < sizeof(*icmp_hdr)) {
		log_message(LOG_INFO, "Error, got short ICMP packet, %zd bytes", len);
		return connect_error;
	}

	// recv_buf强制转换为struct icmphdr指针
	icmp_hdr = PTR_CAST_CONST(struct icmphdr, recv_buf);
	// 检查icmp报文type为echo reply
	if (icmp_hdr->type != ICMP_ECHOREPLY) {
		log_message(LOG_INFO, "Got ICMP packet with type 0x%x", icmp_hdr->type);
		return connect_error;
	}

	// 也就是说虽然我们在request报文中设置了载荷，但是我们并不检查reply报文载荷是否匹配
	// rcz_TODO，这是闲的慌？是否可以不在request报文中设置载荷？
	return connect_success;
}

// 实现类似ping_it
static enum connect_result
ping6_it(int fd, conn_opts_t* co)
{
	struct icmp6_hdr* icmp6_hdr;
	char send_buf[sizeof(*icmp6_hdr) + ICMP_BUFSIZE] __attribute__((aligned(__alignof__(struct icmp6_hdr))));

	set_buf(send_buf + sizeof(*icmp6_hdr), ICMP_BUFSIZE);

	icmp6_hdr = PTR_CAST(struct icmp6_hdr, &send_buf);

	memset(icmp6_hdr, 0, sizeof(*icmp6_hdr));
	icmp6_hdr->icmp6_type = ICMP6_ECHO_REQUEST;
	icmp6_hdr->icmp6_seq = seq_no++;

	if (sendto(fd, send_buf, sizeof(send_buf), 0, PTR_CAST(struct sockaddr, &co->dst), sizeof(struct sockaddr_in6)) < 0) {
		log_message(LOG_INFO, "send ICMPv6 packet fail - errno %d", errno);
		return connect_error;
	}

	return connect_success;
}

// 实现类似recv_it
static enum connect_result
recv6_it(int fd)
{
	ssize_t len;
	const struct icmp6_hdr* icmp6_hdr;
	char recv_buf[sizeof (*icmp6_hdr) + ICMP_BUFSIZE] __attribute__((aligned(__alignof__(struct icmp6_hdr))));

	len = recv(fd, recv_buf, sizeof(recv_buf), 0);

	if (len < 0) {
		log_message(LOG_INFO, "recv ICMPv6 packet error");
		return connect_error;
	}

	if ((size_t)len < sizeof(*icmp6_hdr)) {
		log_message(LOG_INFO, "Error, got short ICMPv6 packet, %zd bytes", len);
		return connect_error;
	}

	icmp6_hdr = PTR_CAST_CONST(struct icmp6_hdr, recv_buf);
	if (icmp6_hdr->icmp6_type != ICMP6_ECHO_REPLY) {
		log_message(LOG_INFO, "Got ICMPv6 packet with type 0x%x", icmp6_hdr->icmp6_type);
		return connect_error;
	}

	return connect_success;
}

static void
icmp_epilog(thread_ref_t thread, bool is_success)
{
	checker_t *checker;
	unsigned long delay;
	bool checker_was_up;
	bool rs_was_alive;

	checker = THREAD_ARG(thread);

	// 默认下一次健康检查时间为delay_loop之后
	delay = checker->delay_loop;
	// 如果1)本次检查成功，或者
	// 2)已经连续失败的次数达到了用户设置的retry次数且checker当前为up或第一次运行
	if (is_success || ((checker->is_up || !checker->has_run) && checker->retry_it >= checker->retry)) {
		// 连续失败次数置0
		checker->retry_it = 0;

		// 若本次检查成功且之前checker为down或第一次运行，此时需要更新rs为up
		if (is_success && (!checker->is_up || !checker->has_run)) {
			log_message(LOG_INFO, "ICMP connection to %s success."
					, FMT_CHK(checker));
			// 暂存rs和checker先前状态，
			// 如果是keepalived启动时，则alpha模式下checker和rs初始状态必是down,非alpha
			// 模式checker和rs必为up
			// 如果checker不是第一次运行，则checker和rs先前必为down，否则进不到这个if块中
			checker_was_up = checker->is_up;
			rs_was_alive = checker->rs->alive;
			// 更新checker状态为up，如果rs没有其他failed checker的话，还会更新rs alive为true并向ipvs
			// 添加rs或恢复rs原始权重，取决于rs是否设置inhibit参数
			update_svr_checker_state(UP, checker);
			// 如果rs状态变化，根据配置参数决定是否邮件通知
			if (checker->rs->smtp_alert && !checker_was_up &&
			    (rs_was_alive != checker->rs->alive || !global_data->no_checker_emails))
				smtp_alert(SMTP_MSG_RS, checker, NULL,
					   "=> ICMP CHECK succeed on service <=");
		// 如果本次检查失败，且之前checker检查成功或者这是checker第一次运行
		} else if (!is_success &&
			   (checker->is_up || !checker->has_run)) {
			// checker第一次运行且retry参数非0打印的日志，此时已经连续失败了retry次
			if (checker->retry && checker->has_run)
				log_message(LOG_INFO
				    , "ICMP CHECK on service %s of %s failed after %u retries."
				    , FMT_CHK(checker), FMT_VS(checker->vs)
				    , checker->retry);
			// checker非第一次运行或retry参数为0打印的日志
			else
				log_message(LOG_INFO
				    , "ICMP CHECK on service %s failed."
				    , FMT_CHK(checker));
			// 暂存rs和checker先前状态
			checker_was_up = checker->is_up;
			rs_was_alive = checker->rs->alive;
			// 更新checker状态为down，如果rs先前没有其他failed checker的话，还会更新rs alive为false并从dpvs
			// 删除rs或设置rs权重为0，取决于rs是否设置inhibit参数
			update_svr_checker_state(DOWN, checker);
			// 如果rs状态变化，根据配置参数决定是否邮件通知
			if (checker->rs->smtp_alert && checker_was_up &&
			    (rs_was_alive != checker->rs->alive || !global_data->no_checker_emails))
				smtp_alert(SMTP_MSG_RS, checker, NULL,
					   "=> ICMP CHECK failed on service <=");
		}
	// 本次检查失败时且checker先前为up时，retry_it计数加1
	// 如果先前checker就是down，则没有必要增加retry_it计数
	} else if (checker->is_up) {
		// 此时下一次健康检查的时间为delay_before_retry后
		delay = checker->delay_before_retry;
		++checker->retry_it;
	}

	// 无论如何，checker->has_run置为true
	checker->has_run = true;

	// 注册下一次健康检查timer
	thread_add_timer(thread->master, icmp_connect_thread, checker, delay);
}

static void
icmp_check_thread(thread_ref_t thread)
{
	checker_t *checker = THREAD_ARG(thread);
	int status;

	// thread->type由keepalived scheduler设置，epoll超时则设置thread->type为THREAD_READ_TIMEOUT
	// 如果等待reply超时，则status置为error，并根据配置决定是否打印log
	if (thread->type == THREAD_READ_TIMEOUT) {
		if (checker->is_up &&
		    (global_data->checker_log_all_failures || checker->log_all_failures))
			log_message(LOG_INFO, "ICMP connection to address %s timeout.", FMT_CHK(checker));
		status = connect_error;
	} else
		// 如果没有超时，说明收到了rs reply，调用recv_it/recv6_it函数接收reply报文
		// recv_it/recv6_it函数不检查reply载荷，只要icmp type为echo reply即可
		status = checker->co->dst.ss_family == AF_INET ?
				recv_it(thread->u.f.fd) : recv6_it(thread->u.f.fd);

	/*
	 * If status = connect_success, then we start udp check with the record of icmp failed times.
	 * Otherwise we will do the icmp connect again until it reaches the unhealthy threshold.
	 * we handle fd uniform.
	 */
	thread_close_fd(thread);

	// 接收reply成功或失败，调用icmp_epilog更新checker和rs状态
	if (status == connect_success)
		icmp_epilog(thread, 1);
	else if (status == connect_error) {
		if (checker->is_up &&
		    thread->type != THREAD_READ_TIMEOUT &&
		    (global_data->checker_log_all_failures || checker->log_all_failures))
			log_message(LOG_INFO, "ICMP connection to %s of %s failed."
				,FMT_CHK(checker), FMT_VS(checker->vs));
		icmp_epilog(thread, 0);
	}

	return;
}

static void
icmp_connect_thread(thread_ref_t thread)
{
	checker_t *checker = THREAD_ARG(thread);
	conn_opts_t *co = checker->co;
	int fd;
	int status;
	int size = SOCK_RECV_BUFF;

	if (!checker->enabled) {
		thread_add_timer(thread->master, icmp_connect_thread, checker,
				checker->delay_loop);
		return;
	}

	// 根据这段注释，当一个rs ip会配置在多个vs中时，我们应取消icmp_ratelimit限制
	// 关于内核参数icmp_ratelimit，可参考https://www.man7.org/linux/man-pages/man7/icmp.7.html
	 /*
	  * If we config a real server in several virtual server, the icmp_ratelimit should be cancelled.
	  * echo 0 > /proc/sys/net/ipv4/icmp_ratelimit
	  */
	// icmp socket type为SOCK_DGRAM，同时设置了非阻塞和close_on_exec标志
	// socket协议是ICMP或ICMPv6，取决于rs IP类型
	if ((fd = socket(co->dst.ss_family, SOCK_DGRAM | SOCK_CLOEXEC | SOCK_NONBLOCK,
			 co->dst.ss_family == AF_INET ? IPPROTO_ICMP : IPPROTO_ICMPV6)) == -1) {
		log_message(LOG_INFO, "ICMP%s connect fail to create socket. Rescheduling.",
				co->dst.ss_family == AF_INET ? "" : "v6");
		// 如果socket fd创建失败，则等待delay_loop秒后再次尝试发起健康检查
		thread_add_timer(thread->master, icmp_connect_thread, checker,
				checker->delay_loop);
		return;
	}

	// 设置socket接收buffer大小，代码中写死为128KB
	// rcz_TODO 这个大小对于echo reply应该是够用了？
	if (setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &size, sizeof(size)))
		log_message(LOG_INFO, "setsockopt SO_RCVBUF for socket %d failed (%d) - %m", fd, errno);

	/*
	 * OK if setsockopt fails
	 * Prevent users from pinging broadcast or multicast addresses
	 */
	// 向RS发送echo request报文
	if (co->dst.ss_family == AF_INET)
		status = ping_it(fd, co);
	else
		status = ping6_it(fd, co);

	// 检查icmp request发送状态
	// 当status状态为connect_success时，udp_icmp_check_state会
	// 添加调用icmp_check_thread函数的线程，并返回false，其他status则直接返回true
	/* handle icmp send status & register check worker thread */
	if (udp_icmp_check_state(fd, status, thread, icmp_check_thread,
		co->connection_to)) {
		// status为非connect_success时，关闭fd并调用icmp_epilog更新checker和rs状态
		close(fd);
		icmp_epilog(thread, false);
	}
	return;
}

#ifdef THREAD_DUMP
void
register_check_ping_addresses(void)
{
	register_thread_address("icmp_check_thread", icmp_check_thread);
	register_thread_address("icmp_connect_thread", icmp_connect_thread);
}
#endif
