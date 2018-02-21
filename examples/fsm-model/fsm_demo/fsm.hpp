#ifndef FSM_H
#define FSM_H

#include <iostream>

using namespace std;

class FSM {
	unsigned int state;
	unsigned int seqId;

	bool validPkt(const unsigned char *pkt, const unsigned int len);

public:
	FSM();
	void evalPkt(const unsigned char *pkt, const unsigned int len);
	static void segfault();
	void printInfo();
};

#endif
