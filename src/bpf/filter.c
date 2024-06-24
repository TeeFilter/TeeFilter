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

#include "filter.h"

/* -----------------------------------------------------------------------------
* Helper Functions
* --------------------------------------------------------------------------- */

static struct ether_header* eth_header(uint8_t *packet) {
	return (struct ether_header*)(packet + PACKET_OFFSET);
}

static void* eth_payload(struct ether_header *eth) {
	return eth+1;
}

static void* ip_payload(struct iphdr *hdr) {
	if(hdr->ihl < 5) return (void*)0;
	return ((uint8_t*) hdr) + (hdr->ihl << 2);
}

/* -----------------------------------------------------------------------------
* Decision Function
* --------------------------------------------------------------------------- */

// We want to allow traffic to any host, EXCEPT the following:
// - Outgoing traffic to 1.1.1.1 is blocked
// - Incoming traffic from 8.8.4.4 is blocked
static bool decide(struct iphdr* ip, uint32_t dir) {
  if(dir >= 2){
    // invalid direction
    return DECISION_BLOCK;
  }

  // OUTBOUND filter
  if(dir == DIRECTION_OUTBOUND) {
    if(ip->daddr == __builtin_bswap32(0x01010101)) {
      return DECISION_BLOCK;
    }
  }

  // INBOUND filter
  if(dir == DIRECTION_INBOUND) {
    if(ip->saddr == __builtin_bswap32(0x08080404)) {
      return DECISION_BLOCK;
    }
  }

  // Allow everything else
  return DECISION_PASS;
}

// We want to allow traffic between laptop and device but block anything
// else.
/* static bool decide(struct iphdr* ip, uint32_t dir) {
  if(dir >= 2){
    // invalid direction
    return DECISION_BLOCK;
  }

  // Allow all ICMP traffic
  if(ip->protocol == IP_P_ICMP) {
    return DECISION_PASS;
  }

  // OUTBOUND filter
  if(dir == DIRECTION_OUTBOUND) {
    // Allow traffic to laptop
    // 192.168.188.21 = 0x c0 a8 bc 15
    // 192.168.188.29 = 0x c0 a8 bc 1d
    if(ip->daddr == __builtin_bswap32(0xc0a8bc1d)) {
      return DECISION_PASS;
    }
  }

  // INBOUND filter
  if(dir == DIRECTION_INBOUND) {
    // Allow traffic from laptop
    // 192.168.188.21 = 0x c0 a8 bc 15
    // 192.168.188.29 = 0x c0 a8 bc 1d
    if(ip->saddr == __builtin_bswap32(0xc0a8bc1d)) {
      return DECISION_PASS;
    }
  }

  // block everything else
  return DECISION_BLOCK;
} */

/* -----------------------------------------------------------------------------
* Public Interface Definition
* --------------------------------------------------------------------------- */

bool filter(uint8_t* packet, uint32_t total_size, uint32_t direction) {
  struct ether_header* eth = eth_header(packet);

  // Allow all ARP traffic
  if (eth->ether_type == __builtin_bswap16(ETH_P_ARP))
    return DECISION_PASS;

  // Otherwise block everything except IP
  if (eth->ether_type != __builtin_bswap16(ETH_P_IP))
    return DECISION_BLOCK;

  struct iphdr* ip = eth_payload(eth);
  //Only allow IPv4
  if (ip->version != 4) {
    return DECISION_BLOCK;
  }

  return decide(ip, direction);
}
