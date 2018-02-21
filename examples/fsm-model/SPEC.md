```
FSM Protocol Demo

Magic Field:
	-bytes[0] = 0xaa, bytes[1] = 0xbb
Sequence Field:
    - byte[2]
	-Starts at 0, increments by 1 for each packet sent, resets to 0 when state resets to 0
Command:
    - byte[3]
      - Reset command (0x02) returns machine to State 0
      - Keep-Alive command (0x05) stays in current State.
Payload:
    - byte[4:19]



State 0 -> 1:
	-Packet must contain magic field 0xaabb for bytes [0,1]
	-Sequence field must be correct, byte[2]
	-Request field must be a valid request, byte [3]
		-Requests @ state 0: hello (0x01), reset (0x02), keep-alive (0x05)
			-If request hello, transition to state 1

State 1 -> 2:
        -Packet must contain magic field 0xaabb for bytes [0, 1]
	-Sequence field must be correct, byte [2]
	-Request field must be a valid request, byte [3]
		-Requests @ state 1: request data (0x03), reset (0x02), keep-alive (0x05)
			-If request data, transition to state 2

State 2 -> 3:
	-Packet must contain magic field 0xaabb for bytes [0, 1]
	-Sequence field must be correct, byte [2]
	-Request field must be a valid request, byte [3]
		-Requests @ state 2: request file (0x04), reset(0x02), keep-alive (0x05)
			-If request file, then byte [4..n] is ASCII filename with length > 6
				-If the above is valid, transition to state 3

State  3-> 4:
	-Packet must contain magic field 0xaabb for bytes [0, 1]
	-Sequence field must be correct, byte [2]
	-Request field must be a valid request, byte [3]
		-Requests @ state 3: disconnect (0x07), reset(0x02), keep-alive (0x05)
			-If requests disconnect, then transition to state 4 (crash occurs)

```