// 
// Copyright (C) 2017, Rockwell Collins
// All rights reserved.
// 
// This software may be modified and distributed under the terms
// of the 3-clause BSD license.  See the LICENSE file for details.
// 
#include "fsm.hpp"
#include <iomanip>

FSM::FSM() {
	state = 0;
	seqId = 0;
}

bool FSM::validPkt(const unsigned char *pkt, const unsigned int len) {
	if (len < 4) { //4 is smallest size possible [magic, magic, seq, req] 
		std::cerr << "Packet length too small ";
		return false;
	}

	if (pkt[0] != 0xAA || pkt[1] != 0xBB) {
		std::cerr << "Invalid magic value ";
		return false; //Missing magic value
	}

	if (pkt[3] == 0x02) {
		std::cerr << "Received reset request ";
		return false; //Reset request
	}

	if ((unsigned int)pkt[2] != seqId) {
                std::cerr << "Invalid sequence number ";
		return false; //Invalid sequence number
	}

	//FSM Request Validation
	
	if (pkt[3] == 0x05) { //Keep-alive packet valid anywhere
		return true;
	}

	if (state == 0) {
		if (pkt[3] != 0x01 || len != 4) { // 0->1 only if pkt[3] == 0x01
			std::cerr << "4th byte was != 1 or the length was != 4 ";
			return false;
		}
	}

	else if (state == 1) {
		if (pkt[3] != 0x3 || len != 4) { // 1->2 only if pkt[3] == 0x03
			std::cerr << "4th byte was != 3 or the length was != 4 ";
			return false;
		}
	}

	else if (state == 2) {
		if (pkt[3] != 0x04 || len < 11) { // 2->3 only if pkt[3] == 0x04 && len >= 11
			std::cerr << "4th byte was != 4 or the length was < 11 ";
			return false; //Invalid request
		}

		//Check if filename is > 6 ASCII characters

		for (int i = 4; i < 11; i++) {
			if (pkt[i] < 65 || pkt[i] > 123) {
				std::cerr << "The filename did not consist of valid ascii values ";
				return false;
			}
		}
	}

	else if (state == 3) {
                std::cerr << "   Cmand : " << ((int) pkt[3]) << std::endl;
                if (pkt[3] != 0x07 || len != 4) { //Disconnect method
			std::cerr << "Received a disconnect request ";
			return false;
		}
		std::cerr << "Bug hit! Aaarg!" << std::endl;
		FSM::segfault(); //Here is our fake vulnerability
		return false;
	}
	
	state++;
        std::cerr << "   State : " << state << std::endl;
	return true;
}

int hist[4] = { 0, 0, 0, 0};
int pktCount = 0;

void FSM::evalPkt(const unsigned char *pkt, const unsigned int len) {
	if (!validPkt(pkt, len)) { //Invalid packet -> Reset state & seq ID
		state = 0;
		seqId = 0;
		std::cerr << "resetting state" << std::endl;
                std::cerr << "   State : " << state << std::endl;
	}
	else {
		seqId++;
	}
        hist[state % 4]++;
        pktCount++;
        if (pktCount % 1024 == 0) {
          std::cout << "STATS: ";
          std::cout        << std::setfill('.') << setw(10) << internal << hist[0];
          std::cout << ":" << std::setfill('.') << setw(10) << internal << hist[1];
          std::cout << ":" << std::setfill('.') << setw(10) << internal << hist[2];
          std::cout << ":" << std::setfill('.') << setw(10) << internal << hist[3];
          std::cout << std::endl;;
        }
}

void FSM::segfault() {
	unsigned char *p = (unsigned char*)0x0001;
	p[1] = 0x2;
}

void FSM::printInfo() {
  cout << "State: " << state << " seqID: " << seqId << std::endl;
}

