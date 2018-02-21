# 
# Copyright (C) 2017, Rockwell Collins
# All rights reserved.
# 
# This software may be modified and distributed under the terms
# of the 3-clause BSD license.  See the LICENSE file for details.
# 
import sys

MAX_PAYLOAD_LENGTH = 514;

TFTP_MODEL_BODY_FORMAT = '''
-- 
-- Copyright (C) 2017, Rockwell Collins
-- All rights reserved.
-- 
-- This software may be modified and distributed under the terms
-- of the 3-clause BSD license.  See the LICENSE file for details.
-- 
type uint16 = int;

const tftp_max_payload_size : int = %(max_payload_length)d;

const opcode_wrq = 1;
const opcode_rrq = 2;
const opcode_data = 3;
const opcode_ack = 4;
const opcode_error = 5;

const mode_fuzzed = 0;
const mode_netascii = 1;
const mode_octet = 2;
const mode_mail = 3;

const ascii_uc_a = 65;
const ascii_uc_c = 67;
const ascii_uc_e = 69;
const ascii_uc_i = 73;
const ascii_uc_l = 76;
const ascii_uc_m = 77;
const ascii_uc_n = 78;
const ascii_uc_o = 79;
const ascii_uc_s = 83;
const ascii_uc_t = 84;

const ascii_lc_a = 97;
const ascii_lc_c = 99;
const ascii_lc_e = 101;
const ascii_lc_i = 105;
const ascii_lc_l = 108;
const ascii_lc_m = 109;
const ascii_lc_n = 110;
const ascii_lc_o = 111;
const ascii_lc_s = 115;
const ascii_lc_t = 116;

node historically(x: bool) returns (r: bool);
let
 r = x and (true -> (pre r));
tel

node once(x: bool) returns (r: bool);
let
 r = x or (false -> (pre r));
tel

type TftpPacket = struct
{
   opcode : uint16;
   payload : int[%(max_payload_length)d]
};

function file_size() returns (r : int);
function filename_length() returns (r : int);
function mode_num() returns (r : int);
function mode_length() returns (r : int);
function error_msg_length(clock : int) returns (r : int);
function fuzz_block_number(clock : int) returns (r : bool);
function fuzz_block_size(clock : int) returns (r : bool);
function fuzzy_block_number(clock : int) returns (r : int);
function fuzzy_block_size(clock : int) returns (r : int);
function ascii_case(clock : int; offset : int) returns (r : int);

function payload(clock : int; addr : int) returns (r : int);

node mode_fuzzed_constraint(clock : int; offset : int) returns (r : bool);
let
 r = (payload(clock, offset + mode_length()) = 0);
tel

node mode_netascii_constraint(clock : int; offset : int) returns (r : bool);
let
 r = (mode_length() = 8)
     and (payload(clock, offset + 0) = ascii_uc_n + (ascii_case(clock, 0) * (ascii_lc_n - ascii_uc_n)))
     and (payload(clock, offset + 1) = ascii_uc_e + (ascii_case(clock, 1) * (ascii_lc_e - ascii_uc_e)))
     and (payload(clock, offset + 2) = ascii_uc_t + (ascii_case(clock, 2) * (ascii_lc_t - ascii_uc_t)))
     and (payload(clock, offset + 3) = ascii_uc_a + (ascii_case(clock, 3) * (ascii_lc_a - ascii_uc_a)))
     and (payload(clock, offset + 4) = ascii_uc_s + (ascii_case(clock, 4) * (ascii_lc_s - ascii_uc_s)))
     and (payload(clock, offset + 5) = ascii_uc_c + (ascii_case(clock, 5) * (ascii_lc_c - ascii_uc_c)))
     and (payload(clock, offset + 6) = ascii_uc_i + (ascii_case(clock, 6) * (ascii_lc_i - ascii_uc_i)))
     and (payload(clock, offset + 7) = ascii_uc_i + (ascii_case(clock, 7) * (ascii_lc_i - ascii_uc_i)))
     and (payload(clock, offset + mode_length()) = 0);
tel

node mode_octet_constraint(clock : int; offset : int) returns (r : bool);
let
 r = (mode_length() = 5)
     and (payload(clock, offset + 0) = ascii_uc_o + (ascii_case(clock, 0) * (ascii_lc_o - ascii_uc_o)))
     and (payload(clock, offset + 1) = ascii_uc_c + (ascii_case(clock, 1) * (ascii_lc_c - ascii_uc_c)))
     and (payload(clock, offset + 2) = ascii_uc_t + (ascii_case(clock, 2) * (ascii_lc_t - ascii_uc_t)))
     and (payload(clock, offset + 3) = ascii_uc_e + (ascii_case(clock, 3) * (ascii_lc_e - ascii_uc_e)))
     and (payload(clock, offset + 4) = ascii_uc_t + (ascii_case(clock, 4) * (ascii_lc_t - ascii_uc_t)))
     and (payload(clock, offset + mode_length()) = 0);
tel

node mode_mail_constraint(clock : int; offset : int) returns (r : bool);
let
 r = (mode_length() = 4)
     and (payload(clock, offset + 0) = ascii_uc_m + (ascii_case(clock, 0) * (ascii_lc_m - ascii_uc_m)))
     and (payload(clock, offset + 1) = ascii_uc_a + (ascii_case(clock, 1) * (ascii_lc_a - ascii_uc_a)))
     and (payload(clock, offset + 2) = ascii_uc_i + (ascii_case(clock, 2) * (ascii_lc_i - ascii_uc_i)))
     and (payload(clock, offset + 3) = ascii_uc_l + (ascii_case(clock, 3) * (ascii_lc_l - ascii_uc_l)))
     and (payload(clock, offset + mode_length()) = 0);
tel

node mode_constraint(clock : int; offset : int) returns (r : bool);
let
 r = if (mode_num() = mode_fuzzed) then mode_fuzzed_constraint(clock, offset)
     else if (mode_num() = mode_netascii) then mode_netascii_constraint(clock, offset)
         else if (mode_num() = mode_octet) then mode_octet_constraint(clock, offset)
             else if (mode_num() = mode_mail) then mode_mail_constraint(clock, offset)
                 else true;
tel

node main(msg: TftpPacket; payload_length : int) returns ();
var
 clock : int;
 block_number : int;
 current_size : int;
 remaining_size : int;
 rrq_constraint : bool;
 wrq_constraint : bool;
 data_constraint : bool;
 ack_constraint : bool;
 error_constraint : bool;
 fuzz_rrq : bool;
 fuzz_wrq : bool;
 fuzz_rrq_protocol : bool;
 fuzz_wrq_protocol : bool;
 fuzz_rrq_protocol_fuzzy_block_numbers : bool;
 fuzz_wrq_protocol_fuzzy_block_numbers : bool;
 fuzz_wrq_protocol_fuzzy_block_sizes : bool;
let
 clock = 0 -> ((pre clock) + 1);

 -- Input type assertions
 -- TODO: Fuzz overflowing the payload size

 -- Uninterpreted function assertions
 assert(0 <= msg.opcode and msg.opcode < 65536);
 assert(0 <= payload_length);
 assert(0 < file_size());
 assert(0 <= filename_length());
 assert(mode_fuzzed <= mode_num() and mode_num() <= mode_mail);
 assert(0 <= mode_length());
 assert(0 <= error_msg_length(clock));
 assert(0 <= fuzzy_block_number(clock) and fuzzy_block_number(clock) < 65536);
 assert(0 <= fuzzy_block_size(clock));
 assert(0 <= ascii_case(clock, 0) and ascii_case(clock, 0) <= 1);
 assert(0 <= ascii_case(clock, 1) and ascii_case(clock, 1) <= 1);
 assert(0 <= ascii_case(clock, 2) and ascii_case(clock, 2) <= 1);
 assert(0 <= ascii_case(clock, 3) and ascii_case(clock, 3) <= 1);
 assert(0 <= ascii_case(clock, 4) and ascii_case(clock, 4) <= 1);
 assert(0 <= ascii_case(clock, 5) and ascii_case(clock, 5) <= 1);
 assert(0 <= ascii_case(clock, 6) and ascii_case(clock, 6) <= 1);
 assert(0 <= ascii_case(clock, 7) and ascii_case(clock, 7) <= 1);
%(payload_range_assertions)s
%(payload_uf_assertions)s

 -- Block sizes are all 512 execept for the last in the file.
 current_size = if (fuzz_block_size(clock))
   then fuzzy_block_size(clock)
   else (0 -> if (msg.opcode = opcode_data)
       then (if ((pre remaining_size) < 512) then (pre remaining_size) else 512)
       else 0);
 remaining_size = file_size() -> ((pre remaining_size) - current_size);

 -- Block numbers start with 1 and increment at each data message (sent or acked)
 block_number = if (fuzz_block_number(clock))
   then fuzzy_block_number(clock)
   else (0 -> (pre block_number) + (if (msg.opcode = opcode_data or msg.opcode = opcode_ack) then 1 else 0));

 rrq_constraint = (msg.opcode = opcode_rrq)
   and (payload_length = 2 + filename_length() + 1 + mode_length() + 1)
   and (payload(clock, filename_length()) = 0)
   and mode_constraint(clock, 2 + filename_length() + 1);

 wrq_constraint = (msg.opcode = opcode_wrq) 
   and (payload_length = 2 + filename_length() + 1 + mode_length() + 1)
   and (payload(clock, filename_length()) = 0)
   and mode_constraint(clock, 2 + filename_length() + 1);

 data_constraint = (msg.opcode = opcode_data)
   and (payload_length = 2 + current_size)
   and ((256 * payload(clock, 0)) + payload(clock, 1) = block_number);

 ack_constraint = (msg.opcode = opcode_ack)
   and (payload_length = 2)
   and ((256 * payload(clock, 0)) + payload(clock, 1) = block_number);

 error_constraint = (msg.opcode = opcode_error)
   and (payload_length = 2 + error_msg_length(clock) + 1)
   and (payload(clock, 2 + error_msg_length(clock)) = 0);

 -- Fuzz the server with a RRQ followed by a series of either ACK or ERROR 
 fuzz_rrq = rrq_constraint -> (ack_constraint or error_constraint);
 fuzz_rrq_protocol = (historically(fuzz_rrq) and once(ack_constraint) and historically(not fuzz_block_number(clock)));

 -- Fuzz the server with a WRQ followed by a series of either DATA or ERROR 
 fuzz_wrq = wrq_constraint -> (data_constraint or error_constraint);
 fuzz_wrq_protocol = (historically(fuzz_wrq) and once(data_constraint) and remaining_size = 0
                          and historically(not fuzz_block_number(clock)) and historically(not fuzz_block_size(clock)));

 -- Fuzz the server with a RRQ followed by a series of either ACK or ERROR with fuzzy block numbers
 fuzz_rrq_protocol_fuzzy_block_numbers = not (historically(fuzz_rrq) and once(ack_constraint));

 -- Fuzz the server with a WRQ followed by a series of either DATA or ERROR and fuzzy block numbers 
 fuzz_wrq_protocol_fuzzy_block_numbers = not (historically(fuzz_wrq) and once(data_constraint) and remaining_size = 0
                          and historically(not fuzz_block_size(clock)));

 -- Fuzz the server with a WRQ followed by a series of either DATA or ERROR and fuzzy block numbers 
 fuzz_wrq_protocol_fuzzy_block_sizes = not (historically(fuzz_wrq) and once(data_constraint) and remaining_size = 0
                          and historically(not fuzz_block_number(clock)));

 --%%PROPERTY fuzz_rrq_protocol;
 --%%PROPERTY fuzz_wrq_protocol;
 -- -- %%PROPERTY fuzz_rrq_protocol_fuzzy_block_numbers;
 -- -- %%PROPERTY fuzz_wrq_protocol_fuzzy_block_numbers;
 -- -- %%PROPERTY fuzz_wrq_protocol_fuzzy_block_sizes;

tel'''


###############################################################################
def generate_payload_uf_assertions():
    result = ""
    for index in range(0,MAX_PAYLOAD_LENGTH):
        result = result + ("  assert(msg.payload[" + str(index) + "] = payload(clock, " + str(index) + "));\n")
    return result


###############################################################################
def generate_payload_range_assertions():
    result = ""
    for index in range(0,MAX_PAYLOAD_LENGTH):
        result = result + ("  assert(msg.payload[" + str(index) + "] >= 0 and msg.payload["+ str(index) +"] < 256);\n")
    return result


###############################################################################
def main():
    print(TFTP_MODEL_BODY_FORMAT %
       { 'max_payload_length' : MAX_PAYLOAD_LENGTH,
         'payload_uf_assertions' : generate_payload_uf_assertions(),
         'payload_range_assertions' : generate_payload_range_assertions() })


###############################################################################
if __name__ == "__main__":
    sys.exit(main())
