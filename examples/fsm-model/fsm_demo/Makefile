all: fsm.cpp fsm.hpp main.cpp
	g++ fsm.cpp main.cpp -D network -g -o fsm

fuzz: fsm.cpp fsm.hpp main.cpp
	hfuzz-clang++ fsm.cpp main.cpp -D honggfuzz -g -o fsm-hongg
	afl-clang-fast++ fsm.cpp main.cpp -D AFL -g -o fsm-afl
clean:
	$(RM) fsm fsm-hongg fsm-afl
