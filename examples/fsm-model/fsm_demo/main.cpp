// 
// Copyright (C) 2017, Rockwell Collins
// All rights reserved.
// 
// This software may be modified and distributed under the terms
// of the 3-clause BSD license.  See the LICENSE file for details.
// 
#include <iostream>
#include "fsm.hpp"
#include <strings.h>
#include <unistd.h>
#include <iostream>

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <netdb.h>
#include <sys/types.h> 
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

using namespace std;

#ifdef network
int main() {
	FSM fsm = FSM();

	struct sockaddr_in myaddr;      /* our address */
        struct sockaddr_in remaddr;     /* remote address */
        socklen_t addrlen = sizeof(remaddr);            /* length of addresses */
        int recvlen;                    /* # bytes received */
        int fd;                         /* our socket */
        unsigned char buf[12800];     /* receive buffer */

        /* create a UDP socket */

        if ((fd = socket(AF_INET, SOCK_DGRAM, 0)) < 0) {
                perror("cannot create socket\n");
                return 0;
        }

        /* bind the socket to any valid IP address and a specific port */

        memset((char *)&myaddr, 0, sizeof(myaddr));
        myaddr.sin_family = AF_INET;
        myaddr.sin_addr.s_addr = htonl(INADDR_ANY);
        myaddr.sin_port = htons(1515);

        if (bind(fd, (struct sockaddr *)&myaddr, sizeof(myaddr)) < 0) {
                perror("bind failed");
                return 0;
        }

        /* now loop, receiving data and printing what we received */
	printf("waiting on port %d\n", 1515);
	fflush(stdout);
        for (;;) {
                
                recvlen = recvfrom(fd, buf, 12800, 0, (struct sockaddr *)&remaddr, &addrlen);
                std::cerr << " + " << recvlen << " bytes" << std::endl;
                if (recvlen > 0) {
                        fsm.evalPkt(buf, recvlen);
                }
        }
}
#endif

#ifdef honggfuzz
FSM *fsm;

extern "C" int LLVMFuzzerInitialize( char ***argv, int *argc) {
	fsm = new FSM();
	return 0;
}

extern "C" int LLVMFuzzerTestOneInput( const unsigned char *data, size_t len) {
	fsm->evalPkt(data, len);
	return 0;
}

#endif

#ifdef AFL
int main(int argc, char **argv) {
	FSM fsm = FSM();
	unsigned char buf[8192];

	while(__AFL_LOOP(1000)) {
		bzero(buf, 8192);

		int len = read(0, buf, 8192);

		fsm.evalPkt(buf, len);
	}
}
#endif
