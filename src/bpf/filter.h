/*******************************************************************************
* Copyright (C) 2022-2024 Jonas Röckl <joroec@gmx.net>
* This program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public License
* as published by the Free Software Foundation; either version 2
* of the License, or (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License
* along with this program; If not, see <http://www.gnu.org/licenses/>.
*******************************************************************************/

#ifndef FILTER_H
#define FILTER_H

#include <stdbool.h>

// common packet headers
#include <net/ethernet.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>

#define ETH_HLEN	14		// Total octets in Ethernet header
#define IP_HLEN	20		// Total octets in IP header
#define TCP_HLEN 20		// Total octets in TCP header.

#define IP_P_ICMP 1
#define IP_P_TCP 6
#define IP_P_UDP 17

/* -----------------------------------------------------------------------------
* Constants
* --------------------------------------------------------------------------- */

#define DIRECTION_INBOUND 0x0
#define DIRECTION_OUTBOUND 0x1

#define DECISION_BLOCK false
#define DECISION_PASS true

// the packet contains two bytes of padding before the start of the ethernet
// header (since the ethernet header is only 14 bytes long, all following
// headers would be unaligned without this padding)
#define PACKET_OFFSET 2

/* -----------------------------------------------------------------------------
* Public Interface Declaration
* --------------------------------------------------------------------------- */

bool filter(uint8_t* packet, uint32_t total_size, uint32_t direction);

#endif /* FILTER_H */
