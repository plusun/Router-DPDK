/*-
 *   BSD LICENSE
 *
 *   Copyright(c) 2010-2014 Intel Corporation. All rights reserved.
 *   All rights reserved.
 *
 *   Redistribution and use in source and binary forms, with or without
 *   modification, are permitted provided that the following conditions
 *   are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *     * Neither the name of Intel Corporation nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>

#include <rte_common.h>
#include <rte_common_vect.h>
#include <rte_byteorder.h>
#include <rte_log.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_memzone.h>
#include <rte_tailq.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_pci.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ring.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include <rte_udp.h>
#include <rte_string_fns.h>

#include "main.h"

#define PORT 0
static const struct rte_eth_conf port_conf =
  {
    .rxmode =
    {
      .mq_mode = ETH_MQ_RX_RSS,
      .max_rx_pkt_len = ETHER_MAX_LEN,
      .split_hdr_size = 0,
      .header_split   = 0, /**< Header Split disabled */
      .hw_ip_checksum = 0, /**< IP checksum offload enabled */
      .hw_vlan_filter = 0, /**< VLAN filtering disabled */
      .jumbo_frame    = 0, /**< Jumbo Frame Support disabled */
      .hw_strip_crc   = 0, /**< CRC stripped by hardware */
    },
    .rx_adv_conf =
    {
      .rss_conf =
      {
	.rss_key = NULL,
	.rss_hf = ETH_RSS_IP,
      },
    },
    .txmode =
    {
      .mq_mode = ETH_MQ_TX_NONE,
    },
  };

static struct rte_mempool * pktmbuf_pool = NULL;

#define RX_PTHRESH 8 /**< Default values of RX prefetch threshold reg. */
#define RX_HTHRESH 8 /**< Default values of RX host threshold reg. */
#define RX_WTHRESH 4 /**< Default values of RX write-back threshold reg. */

#define TX_PTHRESH 36 /**< Default values of TX prefetch threshold reg. */
#define TX_HTHRESH 0  /**< Default values of TX host threshold reg. */
#define TX_WTHRESH 0  /**< Default values of TX write-back threshold reg. */


static const struct rte_eth_rxconf rx_conf =
  {
    .rx_thresh =
    {
      .pthresh = RX_PTHRESH,
      .hthresh = RX_HTHRESH,
      .wthresh = RX_WTHRESH,
    },
  };

static const struct rte_eth_txconf tx_conf =
  {
    .tx_thresh =
    {
      .pthresh = TX_PTHRESH,
      .hthresh = TX_HTHRESH,
      .wthresh = TX_WTHRESH,
    },
    .tx_free_thresh = 0, /* Use PMD default values */
    .tx_rs_thresh = 0, /* Use PMD default values */
    /*
     * As the example won't handle mult-segments and offload cases,
     * set the flag by default.
     */
    .txq_flags = ETH_TXQ_FLAGS_NOMULTSEGS | ETH_TXQ_FLAGS_NOOFFLOADS,
  };


#define MAX_PKT_BURST 32

static inline void free_mbuf(struct rte_mbuf **rx, unsigned nb_rx)
{
  while (nb_rx > 0)
    rte_pktmbuf_free(rx[--nb_rx]);
}

static inline void
dissect(struct rte_mbuf *mbuf,
	struct ether_hdr **eth_hdr, struct ipv4_hdr **ipv4_hdr)
{
  *eth_hdr = NULL;
  *ipv4_hdr = NULL;
  if (!mbuf)
    return;
  unsigned char *data;
  data = rte_pktmbuf_mtod(mbuf, unsigned char *);
  *eth_hdr = (struct ether_hdr *)data;
  *ipv4_hdr = (struct ipv4_hdr *)(data + sizeof(struct ether_hdr));
}

static inline void
print_mac(struct ether_addr *addr)
{
  printf("%02x:%02x:%02x:%02x:%02x:%02x",
	 addr->addr_bytes[0],
	 addr->addr_bytes[1],
	 addr->addr_bytes[2],
	 addr->addr_bytes[3],
	 addr->addr_bytes[4],
	 addr->addr_bytes[5]);
  
}

#define IPVER(PTR) (((struct ipv4_hdr *)(PTR))->version_ihl >> 4)

static inline int
recv_packets(uint8_t port)
{
  uint8_t port_out, portid = PORT;
  uint64_t stat;
  unsigned nb_rx, nb_tx;
  struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
  /* struct ipv4_hdr *ipv4_hdr; */
  /* struct ether_hdr *ether_hdr; */
  stat = 0;
  printf("%u ports in total.\n", port);
  while (1)
    {
      for (portid = 0; portid < port; ++portid)
	{
	  nb_rx = rte_eth_rx_burst(portid, 0, pkts_burst, MAX_PKT_BURST);
	  stat += nb_rx;
	  if (nb_rx > 0)
	    printf("%u: %u of %" PRIu64 ":\n",
		   portid, nb_rx, stat);
	  if (nb_rx > 0)
	    {
	      port_out = portid ^ 1;
	      nb_tx = rte_eth_tx_burst(port_out, 0, pkts_burst, nb_rx);
	      nb_rx -= nb_tx;
	      printf("\t%u forwarded to port %u\n", nb_tx, port_out);
	    }
	  /* for (i = 0; i < nb_rx; ++i) */
	  /*   { */
	  /*     dissect(pkts_burst[i], &ether_hdr, &ipv4_hdr); */
	  /*     print_mac(&ether_hdr->s_addr); */
	  /*     printf("->"); */
	  /*     print_mac(&ether_hdr->d_addr); */
	  /*     printf(": %d\n", IPVER(ipv4_hdr)); */
	  /*   } */
	  free_mbuf(pkts_burst, nb_rx);
	}

    }
  return 0;

}

static int
lcore_hello(void *arg)
{
  uint8_t nb_port = *(uint8_t *)arg;

  recv_packets(nb_port);
  
  return 0;
}

#define NB_MBUF 4096
#define MBUF_SIZE (2048 + sizeof(struct rte_mbuf) + RTE_PKTMBUF_HEADROOM)

int
MAIN(int argc, char **argv)
{
  int ret;
  //unsigned lcore_id;
  uint8_t nb_ports, portid = PORT;
  uint16_t nb_rxd = 128;
  uint16_t nb_txd = 128;

  ret = rte_eal_init(argc, argv);
  if (ret < 0)
    rte_panic("Cannot init EAL\n");

  pktmbuf_pool =
    rte_mempool_create("mbuf_pool", NB_MBUF,
		       MBUF_SIZE, 32,
		       sizeof(struct rte_pktmbuf_pool_private),
		       rte_pktmbuf_pool_init, NULL,
		       rte_pktmbuf_init, NULL,
		       rte_socket_id(), 0);
  if (pktmbuf_pool == NULL)
    rte_exit(EXIT_FAILURE, "Cannot create mempool\n");
  if (rte_eal_pci_probe() < 0)
    rte_exit(EXIT_FAILURE, "Cannot probe PCI\n");
  nb_ports = rte_eth_dev_count();
  if (nb_ports <= 0)
    rte_exit(EXIT_FAILURE, "No Ethernet port\n");

  for (portid = 0; portid < nb_ports; portid++)
    {
      ret = rte_eth_dev_configure(portid, 1, 1, &port_conf);
      if (ret < 0)
	rte_exit(EXIT_FAILURE, "Cannot configure device: err = %d\n", ret);
      rte_eth_promiscuous_enable(portid);
      ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
				   rte_eth_dev_socket_id(portid), &rx_conf, pktmbuf_pool);
      if (ret < 0)
	rte_exit(EXIT_FAILURE, "Cannot setup rx queue: err = %d\n", ret);
      ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
				   rte_eth_dev_socket_id(portid), &tx_conf);
      if (ret < 0)
	rte_exit(EXIT_FAILURE, "Cannot setup tx queue: err = %d\n", ret);
      ret = rte_eth_dev_start(portid);
      if (ret < 0)
	rte_exit(EXIT_FAILURE, "Cannot start device: err = %d\n", ret);
    }
  lcore_hello((void *)&nb_ports);
  return 0;
}
