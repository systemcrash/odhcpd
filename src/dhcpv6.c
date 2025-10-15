/**
 * Copyright (C) 2012-2013 Steven Barth <steven@midlink.org>
 * Copyright (C) 2018 Hans Dedecker <dedeckeh@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 *
 */

#include <errno.h>
#include <unistd.h>
#include <stddef.h>
#include <resolv.h>
#include <sys/timerfd.h>
#include <arpa/inet.h>

#include <libubox/utils.h>

#include "odhcpd.h"
#include "dhcpv6.h"
#include "dhcpv6-pxe.h"
#ifdef DHCPV4_SUPPORT
#include "dhcpv4.h"
#endif

static void relay_client_request(struct sockaddr_in6 *source,
		const void *data, size_t len, struct interface *iface);
static void relay_server_response(uint8_t *data, size_t len);

static void handle_dhcpv6(void *addr, void *data, size_t len,
		struct interface *iface, void *dest);
static void handle_client_request(void *addr, void *data, size_t len,
		struct interface *iface, void *dest_addr);

/* Lightweight client binding structure compatible with odhcpd's dhcpv6-ia.c.
 * Mirrors the runtime lease/binding state derived from struct dhcp_assignment.
 */
struct lq_client_binding {
	/* DUID and its length if present */
	/* Client DUID (dhcp_assignment.clid_data / clid_len) */
	const uint8_t *duid;
	size_t duid_len;

	/* IAID for this binding (dhcp_assignment.iaid) */
	uint32_t iaid;

	// /* Lease lifetimes (preferred and valid) */
	// uint32_t preferred_lifetime;
	// uint32_t valid_lifetime;

	/* client last transaction time (seconds since epoch) if known */
	uint32_t clt_time;

	/* IAADDR(s) and lengths (one or more addresses may apply) */
	/* Addresses or delegated prefixes (dhcp_assignment.managed) */
	struct in6_addr *addrs6;
	size_t addrs6_cnt;

	/* Client options (not stored persistently; only if OPTION_CLIENT_DATA present) */
	const uint8_t *client_options;
	size_t client_options_len;

	/* Peer (client) address (dhcp_assignment.peer.sin6_addr) */
	struct in6_addr peer_address;

	/* If server kept a relay message and peer-address, provide them */
	/* Relay message, if we cached the original Relay-Forward */
	const struct dhcpv6_option_relay_data *relay_msg; /* raw DHCPv6 relay message bytes */
	size_t relay_msg_len;

	/* Links where this client has bindings or can be found (used for OPTION_LQ_CLIENT_LINK) */
	struct in6_addr *link_addresses;
	size_t link_addresses_cnt;

	/* Link (interface) on which this binding is valid */
	const char *ifname;
};

/* -------------------------------------------------------------------------- */
/* Look-up helpers reflecting odhcpd's binding database (iface->ia_assignments)
 * These traverse struct interface->ia_assignments (list of dhcp_assignment).
 * Return dynamically allocated copies of binding data (caller must free).
 */
static struct lq_client_binding *find_binding_by_iaaddr(const struct in6_addr *addr6,
								const struct in6_addr *link_addr6)
{
	struct interface *iface;
	struct dhcp_assignment *a;
	struct odhcpd_ipaddr *addrs;
	struct odhcpd_ipaddr *if_addr6s;
	size_t n;
	bool link_specific = !IN6_IS_ADDR_UNSPECIFIED(link_addr6);
	bool found_link = (link_specific == true) ? false : true;

/*	RFC5007 4.4.1
	If the OPTION_LQ_QUERY specified a non-zero link-address, the server
	MUST use the link-address to find the appropriate link for the
	client.  For a QUERY_BY_ADDRESS, if the 0::0 link-address was
	specified, the server uses the address from the OPTION_IAADDR option
	to find the appropriate link for the client. */

	avl_for_each_element(&interfaces, iface, avl) {
		if_addr6s = iface->addr6;
		if (link_specific) {
			for (n = 0; n < iface->addr6_len / sizeof(*if_addr6s); n++) {
				if (IN6_ARE_ADDR_EQUAL(&if_addr6s[n].addr.in6, link_addr6))
					found_link = true;
			}
		}

		list_for_each_entry(a, &iface->ia_assignments, head) {
			addrs = a->managed;
			size_t addrs_cnt = a->managed_size / sizeof(*addrs);
			size_t valid_addrs_cnt = addrs_cnt;

			for (n = 0; n < addrs_cnt / sizeof(*addrs); n++) {
				if (addrs[n].valid_lt == 0)
					valid_addrs_cnt -= 1;
			}

			if (valid_addrs_cnt == 0)
				return NULL;

			for (n = 0; n < addrs_cnt / sizeof(*addrs); n++) {
				if (IN6_ARE_ADDR_EQUAL(&addrs[n].addr.in6, addr6) && found_link) {
					struct lq_client_binding *b = calloc(1, sizeof(*b));
					if (!b)
						return NULL;

					b->duid = a->clid_data;
					b->duid_len = a->clid_len;
					b->iaid = a->iaid;
					b->clt_time = a->clt_time;
					/* Addresses from assignment */
					b->addrs6 = calloc(valid_addrs_cnt, sizeof(struct in6_addr));
					if (!b->addrs6) {
						free(b);
						return NULL;
					}
					for (size_t i = 0; i < addrs_cnt; i++)
						if (addrs[i].valid_lt != 0)
							b->addrs6[i] = addrs[i].addr.in6;
					b->addrs6_cnt = addrs_cnt;
					b->peer_address = a->peer.sin6_addr;
					b->relay_msg = a->relay_msg;
					b->relay_msg_len = a->relay_msg_len;
					/* --- Properly handle iface->addr6 array --- */
					size_t link_cnt = iface->addr6_len / sizeof(struct odhcpd_ipaddr);
					b->link_addresses_cnt = link_cnt;

					if (link_cnt > 0 && iface->addr6) {
						b->link_addresses = calloc(link_cnt, sizeof(struct in6_addr));
						if (!b->link_addresses) {
							free(b->addrs6);
							free(b);
							return NULL;
						}

						for (size_t j = 0; j < link_cnt; j++)
							b->link_addresses[j] = iface->addr6[j].addr.in6;
					}
					b->ifname = iface->ifname;
					return b;
				}
			}
		}
	}
	return NULL;
}

static struct lq_client_binding *find_binding_by_duid(const uint8_t *duid, size_t duid_len,
								const struct in6_addr *link_addr6)
{
	struct interface *iface;
	struct dhcp_assignment *a;
	struct odhcpd_ipaddr *addrs;
	// struct odhcpd_ipaddr *if_addr6s;
	size_t n;
	// bool link_specific = !IN6_IS_ADDR_UNSPECIFIED(link_addr6);
	// bool found_link = (link_specific == true) ? false : true;

/*	RFC5007 4.4.1
	For a QUERY_BY_CLIENTID, if a 0::0 link-address was specified, the
	server MUST search all of its links for the client.  If the client is
	only found on a single link, the server SHOULD return that client's
	data in an OPTION_CLIENT_DATA option.  If the client is found on more
	than a single link, the server MUST return the list of links in the
	OPTION_LQ_CLIENT_LINK option; the server MUST NOT return any client
	data. */

	avl_for_each_element(&interfaces, iface, avl) {
		// if_addr6s = iface->addr6;
		// if (link_specific) {
		// 	for (n = 0; n < iface->addr6_len / sizeof(*if_addr6s); n++) {
		// 		if (IN6_ARE_ADDR_EQUAL(&if_addr6s[n].addr.in6, link_addr6))
		// 			found_link = true;
		// 	}
		// }

		list_for_each_entry(a, &iface->ia_assignments, head) {
			addrs = a->managed;
			size_t addrs_cnt = a->managed_size / sizeof(*addrs);
			size_t valid_addrs_cnt = addrs_cnt;

			for (n = 0; n < addrs_cnt / sizeof(*addrs); n++) {
				if (addrs[n].valid_lt == 0)
					valid_addrs_cnt -= 1;
			}

			if (valid_addrs_cnt == 0)
				return NULL;

			if (a->clid_len == duid_len &&
				!memcmp(a->clid_data, duid, duid_len)) {
				struct lq_client_binding *b = calloc(1, sizeof(*b));
				if (!b)
					return NULL;

				b->duid = a->clid_data;
				b->duid_len = a->clid_len;
				b->iaid = a->iaid;
				b->clt_time = a->clt_time;
				/* Addresses from assignment */
				b->addrs6 = calloc(valid_addrs_cnt, sizeof(struct in6_addr));
				if (!b->addrs6) {
					free(b);
					return NULL;
				}
				for (size_t i = 0; i < addrs_cnt; i++)
					if (addrs[i].valid_lt != 0)
						b->addrs6[i] = addrs[i].addr.in6;
				b->addrs6_cnt = addrs_cnt;
				b->peer_address = a->peer.sin6_addr;
				b->relay_msg = a->relay_msg;
				b->relay_msg_len = a->relay_msg_len;
				/* --- Properly handle iface->addr6 array --- */
				size_t link_cnt = iface->addr6_len / sizeof(struct odhcpd_ipaddr);
				b->link_addresses_cnt = link_cnt;

				if (link_cnt > 0 && iface->addr6) {
					b->link_addresses = calloc(link_cnt, sizeof(struct in6_addr));
					if (!b->link_addresses) {
						free(b->addrs6);
						free(b);
						return NULL;
					}

					for (size_t j = 0; j < link_cnt; j++)
						b->link_addresses[j] = iface->addr6[j].addr.in6;
				}
				b->ifname = iface->ifname;
				return b;
			}
		}
	}
	return NULL;
}

/* Safely free a dynamically allocated lq_client_binding.
 * Only frees what was explicitly allocated by the caller or find_binding_*().
 */
static void free_lq_client_binding(struct lq_client_binding *b)
{
	if (!b)
		return;

	/* In our current design:
	 *  - b->addrs points into odhcpd's internal assignment, do NOT free.
	 *  - b->duid points into odhcpd memory, do NOT free.
	 *  - b->client_options or relay_msg MAY be allocated copies, so free safely.
	 */
	free((void *)b->client_options);
	free((void *)b->relay_msg);
    free(b->addrs6);

	free(b);
}

// /* Build OPTION_CLIENT_DATA (45): opaque client data (from OPTION_CLIENT_DATA) */
// static ssize_t append_client_data(uint8_t *buf, size_t buf_len,
// 								  const struct lq_client_binding *b)
// {
// 	// strategy: invoke:
// 	// - append_client_time (and its length is known)
// 	// - append_client_id (and its length is known)
// 	// - append_lq_relay_data (and its length is known)
// 	// - append_client_link (and its length is known)
// 	// sum the lengths, and form the header.
// 	// return


// 	if (!b || !b->client_options || b->client_options_len == 0)
// 		return 0;

// 	size_t payload_len = b->client_options_len;
// 	size_t total_len   = sizeof(struct dhcpv6_option_client_data) + payload_len;

// 	if (buf_len < total_len)
// 		return -1;

// 	struct dhcpv6_option_client_data *opt = (struct dhcpv6_option_client_data *)buf;

// 	opt->type = htons(DHCPV6_OPTION_CLIENT_DATA);
// 	opt->len  = htons(payload_len);

// 	memcpy(opt->data, b->client_options, payload_len);

// 	return total_len;
// }


/* https://www.rfc-editor.org/rfc/rfc5007#section-4.1.2.3 Client Last Transaction Time Option (46)
	The Client Last Transaction Time option is encapsulated in an
	OPTION_CLIENT_DATA and identifies how long ago the server last
	communicated with the client, in seconds.

	The format of the Client Last Transaction Time option is shown below:

		 0                   1                   2                   3
		 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|        OPTION_CLT_TIME        |         option-len            |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|                 client-last-transaction-time                  |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*/
/* Build OPTION_CLT_TIME (46): client's last transaction time */
static ssize_t append_client_time(uint8_t *buf, size_t buf_len,
								  const struct lq_client_binding *b)
{
	if (!b)
		return 0;

	size_t total_len = sizeof(struct dhcpv6_option_client_time);

	if (buf_len < total_len)
		return -1;

	struct dhcpv6_option_client_time *opt = (struct dhcpv6_option_client_time *)buf;

	opt->type		= htons(DHCPV6_OPTION_CLT_TIME);
	opt->len		= htons(sizeof(opt->clt_time));
	opt->clt_time	= htonl(b->clt_time);

	return total_len;
}


/* Append OPTION_CLIENTID (1)
 * into a contiguous DHCPv6 option block.
 *
 * Returns total bytes written, or -1 on error.
 */
static ssize_t append_client_id(uint8_t *buf, size_t buf_len,
									 const struct lq_client_binding *b)
{
	if (!b || b->duid_len == 0)
		return 0;

	size_t payload_len = b->duid_len;
	size_t total_len   = sizeof(struct dhcpv6_option_client_id) + payload_len;

	if (buf_len < total_len)
		return -1;

	struct dhcpv6_option_client_id *opt = (struct dhcpv6_option_client_id *)buf;

	opt->type = htons(DHCPV6_OPT_CLIENTID);
	opt->len  = htons(payload_len);

	memcpy(opt->data, b->duid, payload_len);

	return total_len;

}

/* https://www.rfc-editor.org/rfc/rfc5007#section-4.1.2.4 Relay Data (47)
   The Relay Data option is used only in a LEASEQUERY-REPLY message and
   provides the relay agent information used when the client last
   communicated with the server.

   The format of the Relay Data option is shown below:

		0                   1                   2                   3
		0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	   |     OPTION_LQ_RELAY_DATA      |         option-len            |
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	   |                                                               |
	   |                  peer-address (IPv6 address)                  |
	   |                                                               |
	   |                                                               |
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	   |                                                               |
	   |                       DHCP-relay-message                      |
	   .                                                               .
	   .                                                               .
	   .                                                               .
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*/
/* Build LQ_RELAY_DATA option (47). Format per RFC5007:
 * | option (2) | len (2) | peer-address (16) | DHCP-relay-message (variable) |

   If returned, the DHCP-relay-message MUST contain a valid (perhaps
   multi-hop) RELAY-FORW message as the most recently received by the
   server for the client.  However, the (innermost) OPTION_RELAY_MSG
   option containing the client's message MUST have been removed.
   This option SHOULD only be returned if requested by the OPTION_ORO of
   the OPTION_LQ_QUERY.
 */
static ssize_t append_lq_relay_data(uint8_t *buf, size_t buf_len,
									const struct lq_client_binding *b)
{
	if (!b || !b->relay_msg || b->relay_msg_len == 0)
		return 0;

	size_t payload_len = b->relay_msg_len;
	size_t total_len   = sizeof(struct dhcpv6_option_relay_data) + payload_len;

	if (buf_len < total_len)
		return -1;

	struct dhcpv6_option_relay_data *opt = (struct dhcpv6_option_relay_data *)buf;

	// TODO: remove the OPTION_RELAY_MSG option

	opt->type = htons(DHCPV6_OPTION_LQ_RELAY_DATA);
	opt->len  = htons(payload_len);

	memcpy(opt->data, b->relay_msg, payload_len);

	return total_len;
}

/* https://www.rfc-editor.org/rfc/rfc5007#section-4.1.2.5 Client Link Option (48)
	The Client Link option is used only in a LEASEQUERY-REPLY message and
	identifies the links on which the client has one or more bindings.
	It is used in reply to a query when no link-address was specified and
	the client is found to be on more than one link.

	The format of the Client Link option is shown below:

		 0                   1                   2                   3
		 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|     OPTION_LQ_CLIENT_LINK     |         option-len            |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|                                                               |
		|                  link-address (IPv6 address)                  |
		|                                                               |
		|                                                               |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|                                                               |
		|                  link-address (IPv6 address)                  |
		|                                                               |
		|                                                               |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		|                              ...                              |
		+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*/
/* Build OPTION_LQ_CLIENT_LINK (48): list of IPv6 addresses */
static ssize_t append_client_link(uint8_t *buf, size_t buf_len,
								  const struct lq_client_binding *b)
{
	if (!b || b->link_addresses_cnt == 0 || !b->link_addresses)
		return 0;

	// size_t opt_len = 4 + 16 * b->link_addresses_cnt;
	// if (opt_len > buf_len)
	// 	return -1;

	size_t payload_len = b->link_addresses_cnt * sizeof(struct in6_addr);
	size_t total_len   = sizeof(struct dhcpv6_option_client_link) + payload_len;

	if (buf_len < total_len)
		return -1;

	struct dhcpv6_option_client_link *opt = (struct dhcpv6_option_client_link *)buf;

	opt->type = htons(DHCPV6_OPTION_LQ_CLIENT_LINK);
	opt->len  = htons(payload_len);

	memcpy(opt->addrs, b->link_addresses, payload_len);

	return total_len;
}

/* https://www.rfc-editor.org/rfc/rfc5007#section-4.1.2.2 Client Data Option (45)
   The Client Data option is used to encapsulate the data for a single
   client on a single link in a LEASEQUERY-REPLY message.

   The format of the Client Data option is shown below:

		0                   1                   2                   3
		0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	   |       OPTION_CLIENT_DATA      |         option-len            |
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	   .                                                               .
	   .                        client-options                         .
	   .                                                               .
	   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
*/
/* Append
 * OPTION_CLIENTID (1)
 * OPTION_CLIENT_DATA (45)
 * OPTION_CLT_TIME (46)
 * OPTION_LQ_RELAY_DATA (47)
 * OPTION_LQ_CLIENT_LINK (48)
 * into a contiguous DHCPv6 option block.
 *
 * Returns total bytes written, or -1 on error.
 */
static ssize_t append_client_options(uint8_t *buf, size_t buf_len,
									 const struct lq_client_binding *b)
{
/*	An OPTION_CLIENT_DATA option in a LEASEQUERY-REPLY message MUST
	minimally contain the following options:
	1.  OPTION_CLIENTID
	2.  OPTION_IAADDR and/or OPTION_IAPREFIX
	3.  OPTION_CLT_TIME */

	uint8_t *p = buf;
	size_t remaining = buf_len;
	//size_t opts_len = 0;
	ssize_t len;

	/* OPTION_CLIENT_DATA - 45 */
	uint16_t opt_client_data = htons(DHCPV6_OPTION_CLIENT_DATA);
	memcpy(p, &opt_client_data, 2);
    p += 2;
    uint8_t *len_field = p; /* 2 bytes to fill later */
    p += 2;

	/* OPTION_CLIENTID - 1 */
	len = append_client_id(p, remaining, b);
	if (len < 0)
		return -1;
	p += len;
	// opts_len += len;
	remaining -= len;

	/* OPTION_CLT_TIME - 46 */
	len = append_client_time(p, remaining, b);
	if (len < 0)
		return -1;
	p += len;
	// opts_len += len;
	remaining -= len;

	/* OPTION_CLIENTID - 47 */
	len = append_lq_relay_data(p, remaining, b);
	if (len < 0)
		return -1;
	p += len;
	// opts_len += len;
	remaining -= len;

	/* OPTION_LQ_CLIENT_LINK - 48 */
	len = append_client_link(p, remaining, b);
	if (len < 0)
		return -1;
	p += len;
	// opts_len += len;
	remaining -= len;

	// store the OPTION_CLIENT_DATA length field
    uint16_t client_data_len = htons((uint16_t)(p - (len_field + 2)));
    memcpy(len_field, &client_data_len, 2);
	// len_field = htons(opts_len);

	return p - buf;
}


/* Create socket and register events */
int dhcpv6_init(void)
{
	return dhcpv6_ia_init();
}

int dhcpv6_setup_interface(struct interface *iface, bool enable)
{
	int ret = 0;

	enable = enable && (iface->dhcpv6 != MODE_DISABLED);

	if (iface->dhcpv6_event.uloop.fd >= 0) {
		uloop_fd_delete(&iface->dhcpv6_event.uloop);
		close(iface->dhcpv6_event.uloop.fd);
		iface->dhcpv6_event.uloop.fd = -1;
	}

	/* Configure multicast settings */
	if (enable) {
		struct sockaddr_in6 bind_addr = {AF_INET6, htons(DHCPV6_SERVER_PORT),
					0, IN6ADDR_ANY_INIT, 0};
		struct ipv6_mreq mreq;
		int val = 1;

		iface->dhcpv6_event.uloop.fd = socket(AF_INET6, SOCK_DGRAM | SOCK_CLOEXEC, IPPROTO_UDP);
		if (iface->dhcpv6_event.uloop.fd < 0) {
			error("socket(AF_INET6): %m");
			ret = -1;
			goto out;
		}

		/* Basic IPv6 configuration */
		if (setsockopt(iface->dhcpv6_event.uloop.fd, SOL_SOCKET, SO_BINDTODEVICE,
					iface->ifname, strlen(iface->ifname)) < 0) {
			error("setsockopt(SO_BINDTODEVICE): %m");
			ret = -1;
			goto out;
		}

		if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_V6ONLY,
					&val, sizeof(val)) < 0) {
			error("setsockopt(IPV6_V6ONLY): %m");
			ret = -1;
			goto out;
		}

		if (setsockopt(iface->dhcpv6_event.uloop.fd, SOL_SOCKET, SO_REUSEADDR,
					&val, sizeof(val)) < 0) {
			error("setsockopt(SO_REUSEADDR): %m");
			ret = -1;
			goto out;
		}

		if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_RECVPKTINFO,
					&val, sizeof(val)) < 0) {
			error("setsockopt(IPV6_RECVPKTINFO): %m");
			ret = -1;
			goto out;
		}

		val = DHCPV6_HOP_COUNT_LIMIT;
		if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_MULTICAST_HOPS,
					&val, sizeof(val)) < 0) {
			error("setsockopt(IPV6_MULTICAST_HOPS): %m");
			ret = -1;
			goto out;
		}

		val = 0;
		if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_MULTICAST_LOOP,
					&val, sizeof(val)) < 0) {
			error("setsockopt(IPV6_MULTICAST_LOOP): %m");
			ret = -1;
			goto out;
		}

		if (bind(iface->dhcpv6_event.uloop.fd, (struct sockaddr*)&bind_addr,
					sizeof(bind_addr)) < 0) {
			error("bind(): %m");
			ret = -1;
			goto out;
		}

		memset(&mreq, 0, sizeof(mreq));
		inet_pton(AF_INET6, ALL_DHCPV6_RELAYS, &mreq.ipv6mr_multiaddr);
		mreq.ipv6mr_interface = iface->ifindex;

		if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_ADD_MEMBERSHIP,
					&mreq, sizeof(mreq)) < 0) {
			error("setsockopt(IPV6_ADD_MEMBERSHIP): %m");
			ret = -1;
			goto out;
		}

		if (iface->dhcpv6 == MODE_SERVER) {
			memset(&mreq, 0, sizeof(mreq));
			inet_pton(AF_INET6, ALL_DHCPV6_SERVERS, &mreq.ipv6mr_multiaddr);
			mreq.ipv6mr_interface = iface->ifindex;

			if (setsockopt(iface->dhcpv6_event.uloop.fd, IPPROTO_IPV6, IPV6_ADD_MEMBERSHIP,
						&mreq, sizeof(mreq)) < 0) {
				error("setsockopt(IPV6_ADD_MEMBERSHIP): %m");
				ret = -1;
				goto out;
			}
		}

		iface->dhcpv6_event.handle_dgram = handle_dhcpv6;
		odhcpd_register(&iface->dhcpv6_event);
	}

	ret = dhcpv6_ia_setup_interface(iface, enable);

out:
	if (ret < 0 && iface->dhcpv6_event.uloop.fd >= 0) {
		close(iface->dhcpv6_event.uloop.fd);
		iface->dhcpv6_event.uloop.fd = -1;
	}

	return ret;
}

enum {
	IOV_NESTED = 0,
	IOV_DEST,
	IOV_CLIENTID,
	IOV_MAXRT,
#define IOV_STAT IOV_MAXRT
	IOV_RAPID_COMMIT,
	IOV_DNS,
	IOV_DNS_ADDR,
	IOV_SEARCH,
	IOV_SEARCH_DOMAIN,
	IOV_PDBUF,
#define	IOV_REFRESH IOV_PDBUF
	IOV_DHCPV6_RAW,
	IOV_NTP,
	IOV_NTP_ADDR,
	IOV_SNTP,
	IOV_SNTP_ADDR,
	IOV_RELAY_MSG,
	IOV_DHCPV4O6_SERVER,
	IOV_DNR,
	IOV_BOOTFILE_URL,
	IOV_POSIX_TZ,
	IOV_POSIX_TZ_STR,
	IOV_TZDB_TZ,
	IOV_TZDB_TZ_STR,
	IOV_OPT_STATUS,
	IOV_TOTAL
};

static void handle_nested_message(uint8_t *data, size_t len,
				  struct dhcpv6_client_header **c_hdr, uint8_t **opts,
				  uint8_t **end, struct iovec iov[IOV_TOTAL])
{
	struct dhcpv6_relay_header *r_hdr = (struct dhcpv6_relay_header *)data;
	uint16_t otype, olen;
	uint8_t *odata;

	if (iov[IOV_NESTED].iov_base == NULL) {
		iov[IOV_NESTED].iov_base = data;
		iov[IOV_NESTED].iov_len = len;
	}

	if (len < sizeof(struct dhcpv6_client_header))
		return;

	if (r_hdr->msg_type != DHCPV6_MSG_RELAY_FORW) {
		iov[IOV_NESTED].iov_len = data - (uint8_t *)iov[IOV_NESTED].iov_base;
		*c_hdr = (void *)data;
		*opts = (uint8_t *)&(*c_hdr)[1];
		*end = data + len;
		return;
	}

	dhcpv6_for_each_option(r_hdr->options, data + len, otype, olen, odata) {
		if (otype == DHCPV6_OPT_RELAY_MSG) {
			iov[IOV_RELAY_MSG].iov_base = odata + olen;
			iov[IOV_RELAY_MSG].iov_len = (((uint8_t *)iov[IOV_NESTED].iov_base) +
					iov[IOV_NESTED].iov_len) - (odata + olen);
			handle_nested_message(odata, olen, c_hdr, opts, end, iov);
			return;
		}
	}
}


static void update_nested_message(uint8_t *data, size_t len, ssize_t pdiff)
{
	struct dhcpv6_relay_header *hdr = (struct dhcpv6_relay_header*)data;
	if (hdr->msg_type != DHCPV6_MSG_RELAY_FORW)
		return;

	hdr->msg_type = DHCPV6_MSG_RELAY_REPL;

	uint16_t otype, olen;
	uint8_t *odata;
	dhcpv6_for_each_option(hdr->options, data + len, otype, olen, odata) {
		if (otype == DHCPV6_OPT_RELAY_MSG) {
			olen += pdiff;
			odata[-2] = (olen >> 8) & 0xff;
			odata[-1] = olen & 0xff;
			update_nested_message(odata, olen - pdiff, pdiff);
			return;
		}
	}
}

#ifdef DHCPV4_SUPPORT

struct dhcpv4_msg_data {
	uint8_t *msg;
	size_t maxsize;
	ssize_t len;
};

static ssize_t dhcpv6_4o6_send_reply(struct iovec *iov, size_t iov_len,
				     _unused struct sockaddr *dest,
				     _unused socklen_t dest_len,
				     void *opaque)
{
	struct dhcpv4_msg_data *reply = opaque;
	size_t len = 0;

	for (size_t i = 0; i < iov_len; i++)
		len += iov[i].iov_len;

	if (len > reply->maxsize) {
		error("4o6: reply too large, %zu > %zu", len, reply->maxsize);
		reply->len = -1;
		return -1;
	}

	for (size_t i = 0, off = 0; i < iov_len; i++) {
		memcpy(reply->msg + off, iov[i].iov_base, iov[i].iov_len);
		off += iov[i].iov_len;
	}
	reply->len = len;

	return len;
}

static ssize_t dhcpv6_4o6_query(uint8_t *buf, size_t buflen,
				struct interface *iface,
				const struct sockaddr_in6 *addr,
				const void *data, const uint8_t *end)
{
	const struct dhcpv6_client_header *hdr = data;
	uint16_t otype, olen, msgv4_len = 0;
	uint8_t *msgv4_data = NULL;
	uint8_t *start = (uint8_t *)&hdr[1], *odata;
	struct sockaddr_in addrv4;
	struct dhcpv4_msg_data reply = { .msg = buf, .maxsize = buflen, .len = -1 };

	dhcpv6_for_each_option(start, end, otype, olen, odata) {
		if (otype == DHCPV6_OPT_DHCPV4_MSG) {
			msgv4_data = odata;
			msgv4_len = olen;
		}
	}

	if (!msgv4_data || msgv4_len == 0) {
		error("4o6: missing DHCPv4 message option (%d)", DHCPV6_OPT_DHCPV4_MSG);
		return -1;
	}

	// Dummy IPv4 address
	memset(&addrv4, 0, sizeof(addrv4));
	addrv4.sin_family = AF_INET;
	addrv4.sin_addr.s_addr = INADDR_ANY;
	addrv4.sin_port = htons(DHCPV4_CLIENT_PORT);

	dhcpv4_handle_msg(&addrv4, msgv4_data, msgv4_len,
			  iface, NULL, dhcpv6_4o6_send_reply, &reply);

	return reply.len;
}
#endif	/* DHCPV4_SUPPORT */

/* Simple DHCPv6-server for information requests */
static void handle_client_request(void *addr, void *data, size_t len,
		struct interface *iface, void *dest_addr)
{
	struct dhcpv6_client_header *hdr = data;
	uint8_t *opts = (uint8_t *)&hdr[1], *opts_end = (uint8_t *)data + len;
	bool o_rapid_commit = false;

	if (len < sizeof(*hdr))
		return;

	switch (hdr->msg_type) {
	/* Valid message types for clients */
	case DHCPV6_MSG_SOLICIT:
	case DHCPV6_MSG_REQUEST:
	case DHCPV6_MSG_CONFIRM:
	case DHCPV6_MSG_RENEW:
	case DHCPV6_MSG_REBIND:
	case DHCPV6_MSG_RELEASE:
	case DHCPV6_MSG_DECLINE:
	case DHCPV6_MSG_INFORMATION_REQUEST:
	case DHCPV6_MSG_RELAY_FORW:
	case DHCPV6_MSG_LEASEQUERY:
#ifdef DHCPV4_SUPPORT
	/* if we include DHCPV4 support, handle this message type */
	case DHCPV6_MSG_DHCPV4_QUERY:
#endif
		break;
	/* Invalid message types for clients i.e. server messages */
	case DHCPV6_MSG_ADVERTISE:
	case DHCPV6_MSG_REPLY:
	case DHCPV6_MSG_RECONFIGURE:
	case DHCPV6_MSG_RELAY_REPL:
	case DHCPV6_MSG_LEASEQUERY_REPLY:
#ifndef DHCPV4_SUPPORT
	/* if we omit DHCPV4 support, ignore this client message type */
	case DHCPV6_MSG_DHCPV4_QUERY:
#endif
	case DHCPV6_MSG_DHCPV4_RESPONSE:
	default:
		return;
	}

	debug("Got a DHCPv6-request on %s", iface->name);

	/* Construct reply message */
	struct _packed {
		uint8_t msg_type;
		uint8_t tr_id[3];
		uint16_t serverid_type;
		uint16_t serverid_length;
		uint8_t serverid_buf[DUID_MAX_LEN];
	} dest = {
		.msg_type = DHCPV6_MSG_REPLY,
		.serverid_type = htons(DHCPV6_OPT_SERVERID),
		.serverid_length = 0,
		.serverid_buf = { 0 },
	};

	if (config.default_duid_len > 0) {
		memcpy(dest.serverid_buf, config.default_duid, config.default_duid_len);
		dest.serverid_length = htons(config.default_duid_len);
	} else {
		uint16_t duid_ll_hdr[] = { htons(DUID_TYPE_LL), htons(ARPHRD_ETHER) };
		memcpy(dest.serverid_buf, duid_ll_hdr, sizeof(duid_ll_hdr));
		odhcpd_get_mac(iface, &dest.serverid_buf[sizeof(duid_ll_hdr)]);
		dest.serverid_length = htons(sizeof(duid_ll_hdr) + ETH_ALEN);
	}

	struct _packed {
		uint16_t type;
		uint16_t len;
		uint8_t buf[DUID_MAX_LEN];
	} clientid = {
		.type = htons(DHCPV6_OPT_CLIENTID),
		.len = 0,
		.buf = { 0 },
	};

	struct __attribute__((packed)) {
		uint16_t type;
		uint16_t len;
		uint32_t value;
	} maxrt = {htons(DHCPV6_OPT_SOL_MAX_RT), htons(sizeof(maxrt) - 4),
			htonl(60)};

	struct __attribute__((packed)) {
		uint16_t type;
		uint16_t len;
	} rapid_commit = {htons(DHCPV6_OPT_RAPID_COMMIT), 0};

	struct __attribute__((packed)) {
		uint16_t type;
		uint16_t len;
		uint16_t value;
	} stat = {htons(DHCPV6_OPT_STATUS), htons(sizeof(stat) - 4),
			htons(DHCPV6_STATUS_USEMULTICAST)};

	struct __attribute__((packed)) {
		uint16_t type;
		uint16_t len;
		uint32_t value;
	} refresh = {htons(DHCPV6_OPT_INFO_REFRESH), htons(sizeof(uint32_t)),
			htonl(600)};

	struct in6_addr dns_addr, *dns_addr_ptr = iface->dns;
	size_t dns_cnt = iface->dns_cnt;

	if ((dns_cnt == 0) &&
		!odhcpd_get_interface_dns_addr(iface, &dns_addr)) {
		dns_addr_ptr = &dns_addr;
		dns_cnt = 1;
	}

	struct {
		uint16_t type;
		uint16_t len;
	} dns = {htons(DHCPV6_OPT_DNS_SERVERS), htons(dns_cnt * sizeof(*dns_addr_ptr))};

	/* SNTP */
	struct in6_addr *sntp_addr_ptr = iface->dhcpv6_sntp;
	size_t sntp_cnt = 0;
	struct {
		uint16_t type;
		uint16_t len;
	} dhcpv6_sntp;

	/* RFC 4833 - Timezones */
	bool posix_want = false;
	uint8_t *posix_ptr = sys_conf.posix_tz;
	uint16_t posix_len = sys_conf.posix_tz_len;
	/* RFC 4833 - OPTION_NEW_POSIX_TIMEZONE (41)
	 * e.g. EST5EDT4,M3.2.0/02:00,M11.1.0/02:00
	 * Variable-length opaque tz_string blob.
	 */
	struct {
		uint16_t type;
		uint16_t len;
	} posix_tz;

	bool tzdb_want = false;
	uint8_t *tzdb_ptr = sys_conf.tzdb_tz;
	uint16_t tzdb_len = sys_conf.tzdb_tz_len;
	/* RFC 4833 - OPTION_NEW_TZDB_TIMEZONE (42)
	 * e.g. Europe/Zurich
	 * Variable-length opaque tz_name blob.
	 */
	struct {
		uint16_t type;
		uint16_t len;
	} tzdb_tz;

	/* NTP */
	uint8_t *ntp_ptr = iface->dhcpv6_ntp;
	uint16_t ntp_len = iface->dhcpv6_ntp_len;
	size_t ntp_cnt = 0;
	struct {
		uint16_t type;
		uint16_t len;
	} ntp;

	/* DNR */
	struct dhcpv6_dnr {
		uint16_t type;
		uint16_t len;
		uint16_t priority;
		uint16_t adn_len;
		uint8_t body[];
	};
	struct dhcpv6_dnr *dnrs = NULL;
	size_t dnrs_len = 0;

	uint16_t otype, olen;
	uint8_t *odata;
	uint16_t *reqopts = NULL;
	size_t reqopts_cnt = 0;

	/* FIXME: this should be merged with the second loop further down */
	dhcpv6_for_each_option(opts, opts_end, otype, olen, odata) {
		/* Requested options, array of uint16_t, RFC 8415 §21.7 */
		if (otype == DHCPV6_OPT_ORO) {
			reqopts_cnt = olen / sizeof(uint16_t);
			reqopts = (uint16_t *)odata;
			break;
		}
	}

	/* Requested options */
	for (size_t i = 0; i < reqopts_cnt; i++) {
		uint16_t opt = ntohs(reqopts[i]);

		switch (opt) {
		case DHCPV6_OPT_SNTP_SERVERS:
			sntp_cnt = iface->dhcpv6_sntp_cnt;
			dhcpv6_sntp.type = htons(DHCPV6_OPT_SNTP_SERVERS);
			dhcpv6_sntp.len = htons(sntp_cnt * sizeof(*sntp_addr_ptr));
			break;

		case DHCPV6_OPT_NTP_SERVERS:
			ntp_cnt = iface->dhcpv6_ntp_cnt;
			ntp.type = htons(DHCPV6_OPT_NTP_SERVERS);
			ntp.len = htons(ntp_len);
			break;

		case DHCPV6_OPT_NEW_POSIX_TIMEZONE:
			posix_want = true;
			posix_tz.type = htons(DHCPV6_OPT_NEW_POSIX_TIMEZONE);
			posix_tz.len  = htons(posix_len);
			break;

		case DHCPV6_OPT_NEW_TZDB_TIMEZONE:
			tzdb_want = true;
			tzdb_tz.type = htons(DHCPV6_OPT_NEW_TZDB_TIMEZONE);
			tzdb_tz.len  = htons(tzdb_len);
			break;

		case DHCPV6_OPT_DNR:
			for (size_t i = 0; i < iface->dnr_cnt; i++) {
				struct dnr_options *dnr = &iface->dnr[i];

				if (dnr->addr6_cnt == 0 && dnr->addr4_cnt > 0)
					continue;

				dnrs_len += sizeof(struct dhcpv6_dnr);
				dnrs_len += dnr->adn_len;

				if (dnr->addr6_cnt > 0 || dnr->svc_len > 0) {
					dnrs_len += sizeof(uint16_t);
					dnrs_len += dnr->addr6_cnt * sizeof(*dnr->addr6);
					dnrs_len += dnr->svc_len;
				}
			}

			dnrs = alloca(dnrs_len);
			uint8_t *pos = (uint8_t *)dnrs;

			for (size_t i = 0; i < iface->dnr_cnt; i++) {
				struct dnr_options *dnr = &iface->dnr[i];
				struct dhcpv6_dnr *d6dnr = (struct dhcpv6_dnr *)pos;
				uint16_t d6dnr_type_be = htons(DHCPV6_OPT_DNR);
				uint16_t d6dnr_len = 2 * sizeof(uint16_t) + dnr->adn_len;
				uint16_t d6dnr_len_be;
				uint16_t d6dnr_priority_be = htons(dnr->priority);
				uint16_t d6dnr_adn_len_be = htons(dnr->adn_len);

				if (dnr->addr6_cnt == 0 && dnr->addr4_cnt > 0)
					continue;

				/* memcpy as the struct is unaligned */
				memcpy(&d6dnr->type, &d6dnr_type_be, sizeof(d6dnr_type_be));
				memcpy(&d6dnr->priority, &d6dnr_priority_be, sizeof(d6dnr_priority_be));
				memcpy(&d6dnr->adn_len, &d6dnr_adn_len_be, sizeof(d6dnr_adn_len_be));

				pos = d6dnr->body;
				memcpy(pos, dnr->adn, dnr->adn_len);
				pos += dnr->adn_len;

				if (dnr->addr6_cnt > 0 || dnr->svc_len > 0) {
					uint16_t addr6_len = dnr->addr6_cnt * sizeof(*dnr->addr6);
					uint16_t addr6_len_be = htons(addr6_len);

					memcpy(pos, &addr6_len_be, sizeof(addr6_len_be));
					pos += sizeof(addr6_len_be);
					memcpy(pos, dnr->addr6, addr6_len);
					pos += addr6_len;
					memcpy(pos, dnr->svc, dnr->svc_len);
					pos += dnr->svc_len;

					d6dnr_len += sizeof(addr6_len_be) + addr6_len + dnr->svc_len;
				}

				d6dnr_len_be = htons(d6dnr_len);
				memcpy(&d6dnr->len, &d6dnr_len_be, sizeof(d6dnr_len_be));
			}
			break;
		}
	}

	/* DNS Search options */
	uint8_t search_buf[256], *search_domain = iface->search;
	size_t search_len = iface->search_len;

	if (!search_domain && !res_init() && _res.dnsrch[0] && _res.dnsrch[0][0]) {
		int len = dn_comp(_res.dnsrch[0], search_buf,
				sizeof(search_buf), NULL, NULL);
		if (len > 0) {
			search_domain = search_buf;
			search_len = len;
		}
	}

	struct {
		uint16_t type;
		uint16_t len;
	} search = {htons(DHCPV6_OPT_DNS_DOMAIN), htons(search_len)};


	struct __attribute__((packed)) dhcpv4o6_server {
		uint16_t type;
		uint16_t len;
		struct in6_addr addr;
	} dhcpv4o6_server = {htons(DHCPV6_OPT_4O6_SERVER), htons(sizeof(struct in6_addr)),
			IN6ADDR_ANY_INIT};

	struct dhcpv6_opt_status {
		uint16_t code;   /* OPTION_STATUS_CODE = 13 */
		uint16_t len;    /* payload length */
		uint16_t status; /* status code (e.g. 6 = UnknownQueryType) */
		/* followed by optional UTF-8 message text */
	} __attribute__((packed));

	uint8_t pdbuf[512];
	struct iovec iov[IOV_TOTAL] = {
		[IOV_NESTED] = {NULL, 0},
		[IOV_DEST] = {&dest, offsetof(typeof(dest), serverid_buf) + ntohs(dest.serverid_length) },
		[IOV_CLIENTID] = {&clientid, 0},
		[IOV_MAXRT] = {&maxrt, sizeof(maxrt)},
		[IOV_RAPID_COMMIT] = {&rapid_commit, 0},
		[IOV_DNS] = {&dns, (dns_cnt) ? sizeof(dns) : 0},
		[IOV_DNS_ADDR] = {dns_addr_ptr, dns_cnt * sizeof(*dns_addr_ptr)},
		[IOV_SEARCH] = {&search, (search_len) ? sizeof(search) : 0},
		[IOV_SEARCH_DOMAIN] = {search_domain, search_len},
		[IOV_PDBUF] = {pdbuf, 0},
		[IOV_DHCPV6_RAW] = {iface->dhcpv6_raw, iface->dhcpv6_raw_len},
		[IOV_NTP] = {&ntp, (ntp_cnt) ? sizeof(ntp) : 0},
		[IOV_NTP_ADDR] = {ntp_ptr, (ntp_cnt) ? ntp_len : 0},
		[IOV_SNTP] = {&dhcpv6_sntp, (sntp_cnt) ? sizeof(dhcpv6_sntp) : 0},
		[IOV_SNTP_ADDR] = {sntp_addr_ptr, sntp_cnt * sizeof(*sntp_addr_ptr)},
		[IOV_POSIX_TZ] = {&posix_tz, (posix_want) ? sizeof(posix_tz) : 0},
		[IOV_POSIX_TZ_STR] = {posix_ptr, (posix_want) ? posix_len : 0 },
		[IOV_TZDB_TZ] = {&tzdb_tz, (tzdb_want) ? sizeof(tzdb_tz) : 0},
		[IOV_TZDB_TZ_STR] = {tzdb_ptr, (tzdb_want) ? tzdb_len : 0 },
		[IOV_DNR] = {dnrs, dnrs_len},
		[IOV_RELAY_MSG] = {NULL, 0},
		[IOV_DHCPV4O6_SERVER] = {&dhcpv4o6_server, 0},
		[IOV_BOOTFILE_URL] = {NULL, 0}
	};

	if (hdr->msg_type == DHCPV6_MSG_RELAY_FORW) {
		// TODO: store the RELAY-FORW for later (RFC5007) without the OPTION_RELAY_MSG

		// If returned, the DHCP-relay-message MUST contain a valid (perhaps
		// multi-hop) RELAY-FORW message as the most recently received by the
		// server for the client.  However, the (innermost) OPTION_RELAY_MSG
		// option containing the client's message MUST have been removed.

		handle_nested_message(data, len, &hdr, &opts, &opts_end, iov);
	}

	if (!IN6_IS_ADDR_MULTICAST((struct in6_addr *)dest_addr) && iov[IOV_NESTED].iov_len == 0 &&
	    (hdr->msg_type == DHCPV6_MSG_SOLICIT || hdr->msg_type == DHCPV6_MSG_CONFIRM ||
	     hdr->msg_type == DHCPV6_MSG_REBIND || hdr->msg_type == DHCPV6_MSG_INFORMATION_REQUEST))
		return;

	memcpy(dest.tr_id, hdr->transaction_id, sizeof(dest.tr_id));

	/* Go through options and find what we need */
	dhcpv6_for_each_option(opts, opts_end, otype, olen, odata) {
		if (otype == DHCPV6_OPT_CLIENTID && olen <= DUID_MAX_LEN) {
			clientid.len = htons(olen);
			memcpy(clientid.buf, odata, olen);
			iov[IOV_CLIENTID].iov_len = offsetof(typeof(clientid), buf) + olen;
		} else if (otype == DHCPV6_OPT_SERVERID) {
			if (olen != ntohs(dest.serverid_length) ||
			    memcmp(odata, &dest.serverid_buf, olen))
				return; /* Not for us */
		} else if (otype == DHCPV6_OPT_RAPID_COMMIT && hdr->msg_type == DHCPV6_MSG_SOLICIT) {
			iov[IOV_RAPID_COMMIT].iov_len = sizeof(rapid_commit);
			o_rapid_commit = true;
		} else if (otype == DHCPV6_OPT_ORO) {
			for (int i=0; i < olen/2; i++) {
				uint16_t option = ntohs(((uint16_t *)odata)[i]);

				switch (option) {
#ifdef DHCPV4_SUPPORT
				case DHCPV6_OPT_4O6_SERVER:
					if (iface->dhcpv4) {
						/* According to RFC 7341, 7.2. DHCP 4o6 Server Address Option Format:
						 * This option may also carry no IPv6 addresses, which instructs the
						 * client to use the All_DHCP_Relay_Agents_and_Servers multicast address
						 * as the destination address.
						 *
						 * The ISC dhclient logs a missing IPv6 address as an error but seems to
						 * work anyway:
						 * dhcp4-o-dhcp6-server: expecting at least 16 bytes; got 0
						 *
						 * Include the All_DHCP_Relay_Agents_and_Servers multicast address
						 * to make it explicit which address to use. */
						struct dhcpv4o6_server *server = iov[IOV_DHCPV4O6_SERVER].iov_base;

						inet_pton(AF_INET6, ALL_DHCPV6_RELAYS, &server->addr);

						iov[IOV_DHCPV4O6_SERVER].iov_len = sizeof(dhcpv4o6_server);
					}
					break;
#endif /* DHCPV4_SUPPORT */
				default:
					break;
				}
			}
		} else if (otype == DHCPV6_OPT_CLIENT_ARCH) {
			uint16_t arch_code = ntohs(((uint16_t*)odata)[0]);
			ipv6_pxe_serve_boot_url(arch_code, &iov[IOV_BOOTFILE_URL]);
		}
	}

	if (!IN6_IS_ADDR_MULTICAST((struct in6_addr *)dest_addr) && iov[IOV_NESTED].iov_len == 0 &&
	    (hdr->msg_type == DHCPV6_MSG_REQUEST || hdr->msg_type == DHCPV6_MSG_RENEW ||
	     hdr->msg_type == DHCPV6_MSG_RELEASE || hdr->msg_type == DHCPV6_MSG_DECLINE)) {
		iov[IOV_STAT].iov_base = &stat;
		iov[IOV_STAT].iov_len = sizeof(stat);

		for (ssize_t i = IOV_STAT + 1; i < IOV_TOTAL; ++i)
			iov[i].iov_len = 0;

		odhcpd_send(iface->dhcpv6_event.uloop.fd, addr, iov, ARRAY_SIZE(iov), iface);
		return;
	}

	if (hdr->msg_type == DHCPV6_MSG_SOLICIT && !o_rapid_commit) {
		dest.msg_type = DHCPV6_MSG_ADVERTISE;
	} else if (hdr->msg_type == DHCPV6_MSG_INFORMATION_REQUEST) {
		iov[IOV_REFRESH].iov_base = &refresh;
		iov[IOV_REFRESH].iov_len = sizeof(refresh);

		/* Return inf max rt option in reply to information request */
		maxrt.type = htons(DHCPV6_OPT_INF_MAX_RT);
	}

	if (hdr->msg_type == DHCPV6_MSG_LEASEQUERY) {
		dest.msg_type = DHCPV6_MSG_LEASEQUERY_REPLY;
		// https://www.rfc-editor.org/rfc/rfc5007#section-3.3 Query by IPv6 address
		// https://www.rfc-editor.org/rfc/rfc5007#section-3.3 Query by Client Identifier (DUID)

		/* https://www.rfc-editor.org/rfc/rfc5007#section-4.1.2.1 Query Option (44)
		   The Query option is used only in a LEASEQUERY message and identifies
		   the query being performed.  The option includes the query type, link-
		   address (or 0::0), and option(s) to provide data needed for the
		   query.

		   The format of the Query option is shown below:

				0                   1                   2                   3
				0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
			   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			   |        OPTION_LQ_QUERY        |         option-len            |
			   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			   |   query-type  |                                               |
			   +-+-+-+-+-+-+-+-+                                               |
			   |                                                               |
			   |                         link-address                          |
			   |                                                               |
			   |               +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			   |               |                                               .
			   +-+-+-+-+-+-+-+-+                                               .
			   .                         query-options                         .
			   .                                                               .
			   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

			QUERY_BY_ADDRESS (needs OPTION_IAADDR) or QUERY_BY_CLIENTID (needs OPTION_CLIENTID)
		*/
		/* Find the LQ Query option (44) in the incoming message */
		uint16_t qtype = 0;
		struct in6_addr link_address;
		bool have_query = false;
		uint8_t *query_opts = NULL;
		uint8_t *query_opts_end = NULL;

		dhcpv6_for_each_option(opts, opts_end, otype, olen, odata) {
			if (otype == DHCPV6_OPTION_LQ_QUERY && olen >= 1 + 16) {
				have_query = true;
				qtype = odata[0]; /* one octet query-type per RFC5007 */
				/* link-address starts at odata[1] (16 bytes) */
				memcpy(&link_address, &odata[1], 16);
				/* query-options start after that */
				query_opts = &odata[1 + 16];
				query_opts_end = query_opts + (olen - (1 + 16));
				break;
			}
		}

		if (!have_query) {
			/* No Query option -> per RFC we may ignore or send empty reply; we ignore */
			return;
		}

		/* Determine whether the nested query-options contain OPTION_IAADDR or OPTION_CLIENTID */
		uint8_t *qopt = query_opts;
		// uint16_t found_clientid = 0;
		struct in6_addr query_addr;
		bool have_iaaddr = false, have_clientid = false;
		uint8_t *found_clientid_ptr = NULL;
		uint16_t found_clientid_len = 0;

		uint16_t status_code = 0;
		char status_msg[64] = {0};

		while (qopt + 4 <= query_opts_end) {
			uint16_t q_otype = ntohs(*(uint16_t *)qopt);
			uint16_t q_olen  = ntohs(*(uint16_t *)(qopt + 2));
			uint8_t *q_odata = qopt + 4;
			if (qopt + 4 + q_olen > query_opts_end)
				break;

			if (qtype == DHCPV6_QUERY_BY_ADDRESS && q_otype == DHCPV6_OPT_IA_ADDR) {
				/* IA_ADDR carries an IPv6 address inside its payload; extract IPv6
				 * RFC8415 IAADDR body: addr(16) + preferred(4) + valid(4) + ... */
				if (q_olen >= 16) {
					memcpy(&query_addr, q_odata, 16);
					have_iaaddr = true;
				} else {
					status_code = DHCPV6_STATUS_MALFORMED_QUERY; /* 8 */
					snprintf(status_msg, sizeof(status_msg),
							"QUERY_BY_ADDRESS missing IPv6 link-address");
					break;
				}
			} else if (qtype == DHCPV6_QUERY_BY_CLIENTID && q_otype == DHCPV6_OPT_CLIENTID) {
				/* record the clientid pointer+len for later lookup */
				// found_clientid = q_otype;
				found_clientid_ptr = q_odata;
				found_clientid_len = q_olen;
				have_clientid = true;
			} else {
				/* Unsupported query type */
				status_code = DHCPV6_STATUS_UNKNOWN_QUERY_TYPE; /* 7 */
				snprintf(status_msg, sizeof(status_msg),
						"Unsupported query-type %u", q_otype);
				break;
			}
			qopt = q_odata + q_olen;
		}

		if (qtype == DHCPV6_QUERY_BY_ADDRESS && !have_iaaddr) {
			status_code = DHCPV6_STATUS_MALFORMED_QUERY; /* 8 */
			snprintf(status_msg, sizeof(status_msg),
					"QUERY_BY_ADDRESS but missing OPTION_IAADDR");
		}
		else if (qtype == DHCPV6_QUERY_BY_CLIENTID && !have_clientid) {
			status_code = DHCPV6_STATUS_MALFORMED_QUERY; /* 8 */
			snprintf(status_msg, sizeof(status_msg),
					"QUERY_BY_CLIENTID but missing OPTION_CLIENTID");
		}

		/*	RFC5007 4.4.1:
			A server may also restrict LEASEQUERY messages, or query-types, to
			certain requestors.  In this case, the server MAY discard the
			LEASEQUERY message or MAY add an OPTION_STATUS_CODE option with the
			NotAllowed status code and send the LEASEQUERY-REPLY to the
			requestor. */

		/* If an error was detected in the included client options,
			append a Status Code option to the reply */
		if (status_code) {
			struct {
				struct dhcpv6_opt_status hdr;
				char msg[64];
			} __attribute__((packed)) st_opt = {
				.hdr = {
					.code = htons(DHCPV6_OPT_STATUS), /* 13 */
					.len  = htons(sizeof(uint16_t) + strlen(status_msg)),
					.status = htons(status_code),
				},
			};

			memcpy(st_opt.msg, status_msg, strlen(status_msg));

			struct iovec iov_status = {
				.iov_base = &st_opt,
				.iov_len  = 4 + ntohs(st_opt.hdr.len),
			};

			/* Append to existing iovec array */
			iov[IOV_OPT_STATUS] = iov_status;

			/* Now send a minimal LQ-Reply containing this status */
			odhcpd_send(iface->dhcpv6_event.uloop.fd, addr, iov, ARRAY_SIZE(iov), iface);
			return;
		}

		struct lq_client_binding *binding = NULL;

		if (have_iaaddr) {
			binding = find_binding_by_iaaddr(&query_addr, &link_address);
		} else if (have_clientid) {
			binding = find_binding_by_duid(found_clientid_ptr, found_clientid_len, &link_address);
		} else {
			/* Query without IAADDR or CLIENTID: RFC5007 supports other behaviors
			 * (e.g. query the database for clients on link), but here we ignore. */
			return;
		}

		if (!binding) {
			/* No such client */
			// iov[IOV_PDBUF].iov_len = 0;

			status_code = DHCPV6_STATUS_NOT_CONFIGURED; /* 9 */
			snprintf(status_msg, sizeof(status_msg),
					"Server hasn't the target address or link in its configuration");

			struct {
				struct dhcpv6_opt_status hdr;
				char msg[64];
			} __attribute__((packed)) st_opt = {
				.hdr = {
					.code = htons(DHCPV6_OPT_STATUS), /* 13 */
					.len  = htons(sizeof(uint16_t) + strlen(status_msg)),
					.status = htons(status_code),
				},
			};

			memcpy(st_opt.msg, status_msg, strlen(status_msg));

			struct iovec iov_status = {
				.iov_base = &st_opt,
				.iov_len  = 4 + ntohs(st_opt.hdr.len),
			};

			/* Append to existing iovec array */
			iov[IOV_OPT_STATUS] = iov_status;

			odhcpd_send(iface->dhcpv6_event.uloop.fd, addr, iov, ARRAY_SIZE(iov), iface);
			return;
		}

		/* Build OPTION_CLIENT_DATA (+ nested client-options such as CLT_TIME) in pdbuf */
		memset(pdbuf, 0, sizeof(pdbuf));
		ssize_t built = append_client_options(pdbuf, sizeof(pdbuf), binding);
		if (built < 0) {
			syslog(LOG_ERR, "LEASEQUERY: client data too large");
			goto free_binding;
		}

		size_t total = built;

		/* Build OPTION_XXX in pdbuf 
		ssize_t xxx = append_xxx(pdbuf + total, sizeof(pdbuf) - total, binding);
		if (xxx < 0) {
			syslog(LOG_ERR, "LEASEQUERY: client data too large");
			goto free_binding;
		}

		total += (xxx > 0) ? xxx : 0;
		*/

		iov[IOV_PDBUF].iov_base = pdbuf;
		iov[IOV_PDBUF].iov_len  = total;

		/* dest.msg_type already set to LEASEQUERY_REPLY earlier */
		/* send reply */
		odhcpd_send(iface->dhcpv6_event.uloop.fd, addr, iov, ARRAY_SIZE(iov), iface);
		free_binding:
		free_lq_client_binding(binding);
		return;
	}

#ifdef DHCPV4_SUPPORT
	if (hdr->msg_type == DHCPV6_MSG_DHCPV4_QUERY) {
		struct _packed dhcpv4_msg_data {
			uint16_t type;
			uint16_t len;
			uint8_t msg[1];
		} *msg_opt = (struct dhcpv4_msg_data*)pdbuf;
		ssize_t msglen;

		memset(pdbuf, 0, sizeof(pdbuf));

		msglen = dhcpv6_4o6_query(msg_opt->msg, sizeof(pdbuf) - sizeof(*msg_opt) + 1,
						iface, addr, (const void *)hdr, opts_end);
		if (msglen <= 0) {
			error("4o6: query failed");
			return;
		}

		msg_opt->type = htons(DHCPV6_OPT_DHCPV4_MSG);
		msg_opt->len = htons(msglen);
		iov[IOV_PDBUF].iov_len = sizeof(*msg_opt) - 1 + msglen;
		dest.msg_type = DHCPV6_MSG_DHCPV4_RESPONSE;
	} else
#endif	/* DHCPV4_SUPPORT */

	if (hdr->msg_type != DHCPV6_MSG_INFORMATION_REQUEST) {
		ssize_t ialen = dhcpv6_ia_handle_IAs(pdbuf, sizeof(pdbuf), iface, addr, (const void *)hdr, opts_end);

		iov[IOV_PDBUF].iov_len = ialen;
		if (ialen < 0 ||
		    (ialen == 0 && (hdr->msg_type == DHCPV6_MSG_REBIND || hdr->msg_type == DHCPV6_MSG_CONFIRM)))
			return;
	}

	if (iov[IOV_NESTED].iov_len > 0) /* Update length */
		update_nested_message(data, len, iov[IOV_DEST].iov_len + iov[IOV_MAXRT].iov_len +
				      iov[IOV_RAPID_COMMIT].iov_len + iov[IOV_DNS].iov_len +
				      iov[IOV_DNS_ADDR].iov_len + iov[IOV_SEARCH].iov_len +
				      iov[IOV_SEARCH_DOMAIN].iov_len + iov[IOV_PDBUF].iov_len +
				      iov[IOV_DHCPV4O6_SERVER].iov_len +
				      iov[IOV_DHCPV6_RAW].iov_len +
				      iov[IOV_NTP].iov_len + iov[IOV_NTP_ADDR].iov_len +
				      iov[IOV_SNTP].iov_len + iov[IOV_SNTP_ADDR].iov_len +
				      iov[IOV_POSIX_TZ].iov_len + iov[IOV_POSIX_TZ_STR].iov_len + 
				      iov[IOV_TZDB_TZ].iov_len + iov[IOV_TZDB_TZ_STR].iov_len +
				      iov[IOV_DNR].iov_len + iov[IOV_BOOTFILE_URL].iov_len -
				      (4 + opts_end - opts));

	debug("Sending a DHCPv6-%s on %s", iov[IOV_NESTED].iov_len ? "relay-reply" : "reply", iface->name);

	odhcpd_send(iface->dhcpv6_event.uloop.fd, addr, iov, ARRAY_SIZE(iov), iface);
}


/* Central DHCPv6-relay handler */
static void handle_dhcpv6(void *addr, void *data, size_t len,
		struct interface *iface, void *dest_addr)
{
	if (iface->dhcpv6 == MODE_SERVER) {
		handle_client_request(addr, data, len, iface, dest_addr);
	} else if (iface->dhcpv6 == MODE_RELAY) {
		if (iface->master)
			relay_server_response(data, len);
		else
			relay_client_request(addr, data, len, iface);
	}
}


/* Relay server response (regular relay server handling) */
static void relay_server_response(uint8_t *data, size_t len)
{
	/* Information we need to gather */
	uint8_t *payload_data = NULL;
	size_t payload_len = 0;
	int32_t ifaceidx = 0;
	struct sockaddr_in6 target = {AF_INET6, htons(DHCPV6_CLIENT_PORT),
		0, IN6ADDR_ANY_INIT, 0};
	int otype, olen;
	uint8_t *odata, *end = data + len;
	/* Relay DHCPv6 reply from server to client */
	struct dhcpv6_relay_header *h = (void*)data;

	debug("Got a DHCPv6-relay-reply");

	if (len < sizeof(*h) || h->msg_type != DHCPV6_MSG_RELAY_REPL)
		return;

	memcpy(&target.sin6_addr, &h->peer_address, sizeof(struct in6_addr));

	/* Go through options and find what we need */
	dhcpv6_for_each_option(h->options, end, otype, olen, odata) {
		if (otype == DHCPV6_OPT_INTERFACE_ID
				&& olen == sizeof(ifaceidx)) {
			memcpy(&ifaceidx, odata, sizeof(ifaceidx));
		} else if (otype == DHCPV6_OPT_RELAY_MSG) {
			payload_data = odata;
			payload_len = olen;
		}
	}

	/* Invalid interface-id or basic payload */
	struct interface *iface = odhcpd_get_interface_by_index(ifaceidx);
	if (!iface || iface->master || !payload_data || payload_len < 4)
		return;

	bool is_authenticated = false;
	struct in6_addr *dns_ptr = NULL;
	size_t dns_count = 0;

	/* If the payload is relay-reply we have to send to the server port */
	if (payload_data[0] == DHCPV6_MSG_RELAY_REPL) {
		target.sin6_port = htons(DHCPV6_SERVER_PORT);
	} else { /* Go through the payload data */
		struct dhcpv6_client_header *h = (void*)payload_data;
		end = payload_data + payload_len;

		dhcpv6_for_each_option(&h[1], end, otype, olen, odata) {
			if (otype == DHCPV6_OPT_DNS_SERVERS && olen >= 16) {
				dns_ptr = (struct in6_addr*)odata;
				dns_count = olen / 16;
			} else if (otype == DHCPV6_OPT_AUTH) {
				is_authenticated = true;
			}
		}
	}

	/* Rewrite DNS servers if requested */
	if (iface->always_rewrite_dns && dns_ptr && dns_count > 0) {
		if (is_authenticated)
			return; /* Impossible to rewrite */

		const struct in6_addr *rewrite = iface->dns;
		struct in6_addr addr;
		size_t rewrite_cnt = iface->dns_cnt;

		if (rewrite_cnt == 0) {
			if (odhcpd_get_interface_dns_addr(iface, &addr))
				return; /* Unable to get interface address */

			rewrite = &addr;
			rewrite_cnt = 1;
		}

		/* Copy over any other addresses */
		for (size_t i = 0; i < dns_count; ++i) {
			size_t j = (i < rewrite_cnt) ? i : rewrite_cnt - 1;
			memcpy(&dns_ptr[i], &rewrite[j], sizeof(*rewrite));
		}
	}

	struct iovec iov = {payload_data, payload_len};

	// TODO: store the relayed message.

	debug("Sending a DHCPv6-reply on %s", iface->name);

	odhcpd_send(iface->dhcpv6_event.uloop.fd, &target, &iov, 1, iface);
}

static struct odhcpd_ipaddr *relay_link_address(struct interface *iface)
{
	struct odhcpd_ipaddr *addr = NULL;
	time_t now = odhcpd_time();

	for (size_t i = 0; i < iface->addr6_len; i++) {
		if (iface->addr6[i].valid_lt <= (uint32_t)now)
			continue;

		if (iface->addr6[i].preferred_lt > (uint32_t)now) {
			addr = &iface->addr6[i];
			break;
		}

		if (!addr || (iface->addr6[i].valid_lt > addr->valid_lt))
			addr = &iface->addr6[i];
	}

	return addr;
}

/* Relay client request (regular DHCPv6-relay) */
static void relay_client_request(struct sockaddr_in6 *source,
		const void *data, size_t len, struct interface *iface)
{
	const struct dhcpv6_relay_header *h = data;
	/* Construct our forwarding envelope */
	struct dhcpv6_relay_forward_envelope hdr = {
		.msg_type = DHCPV6_MSG_RELAY_FORW,
		.hop_count = 0,
		.interface_id_type = htons(DHCPV6_OPT_INTERFACE_ID),
		.interface_id_len = htons(sizeof(uint32_t)),
		.relay_message_type = htons(DHCPV6_OPT_RELAY_MSG),
		.relay_message_len = htons(len),
	};
	struct iovec iov[2] = {{&hdr, sizeof(hdr)}, {(void *)data, len}};
	struct interface *c;
	struct odhcpd_ipaddr *ip;
	struct sockaddr_in6 s;

	switch (h->msg_type) {
	/* Valid message types from clients */
	case DHCPV6_MSG_SOLICIT:
	case DHCPV6_MSG_REQUEST:
	case DHCPV6_MSG_CONFIRM:
	case DHCPV6_MSG_RENEW:
	case DHCPV6_MSG_REBIND:
	case DHCPV6_MSG_RELEASE:
	case DHCPV6_MSG_DECLINE:
	case DHCPV6_MSG_INFORMATION_REQUEST:
	case DHCPV6_MSG_RELAY_FORW:
	case DHCPV6_MSG_DHCPV4_QUERY:
		break;
	/* Invalid message types from clients i.e. server messages */
	case DHCPV6_MSG_ADVERTISE:
	case DHCPV6_MSG_REPLY:
	case DHCPV6_MSG_RECONFIGURE:
	case DHCPV6_MSG_RELAY_REPL:
	case DHCPV6_MSG_DHCPV4_RESPONSE:
		return;
	default:
		break;
	}

	debug("Got a DHCPv6-request on %s", iface->name);

	if (h->msg_type == DHCPV6_MSG_RELAY_FORW) { /* handle relay-forward */
		if (h->hop_count >= DHCPV6_HOP_COUNT_LIMIT)
			return; /* Invalid hop count */

		hdr.hop_count = h->hop_count + 1;
	}

	/* use memcpy here as the destination fields are unaligned */
	memcpy(&hdr.peer_address, &source->sin6_addr, sizeof(struct in6_addr));
	memcpy(&hdr.interface_id_data, &iface->ifindex, sizeof(iface->ifindex));

	/* Detect public IP of slave interface to use as link-address */
	ip = relay_link_address(iface);
	if (ip)
		memcpy(&hdr.link_address, &ip->addr.in6, sizeof(hdr.link_address));

	memset(&s, 0, sizeof(s));
	s.sin6_family = AF_INET6;
	s.sin6_port = htons(DHCPV6_SERVER_PORT);
	inet_pton(AF_INET6, ALL_DHCPV6_SERVERS, &s.sin6_addr);

	avl_for_each_element(&interfaces, c, avl) {
		if (!c->master || c->dhcpv6 != MODE_RELAY)
			continue;

		if (!ip) {
			/* No suitable address! Is the slave not configured yet?
			 * Detect public IP of master interface and use it instead
			 * This is WRONG and probably violates the RFC. However
			 * otherwise we have a hen and egg problem because the
			 * slave-interface cannot be auto-configured. */
			ip = relay_link_address(c);
			if (!ip)
				continue; /* Could not obtain a suitable address */

			memcpy(&hdr.link_address, &ip->addr.in6, sizeof(hdr.link_address));
			ip = NULL;
		}

		debug("Sending a DHCPv6-relay-forward on %s", c->name);

		odhcpd_send(c->dhcpv6_event.uloop.fd, &s, iov, 2, c);
	}
}
