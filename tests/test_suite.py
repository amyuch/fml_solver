import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from fml.parser.rtl_parser import RTLParser
from fml.engine.bmc import bmc_incremental
from fml.engine.kind import check_kinduction
from fml.engine.ic3 import IC3
import time, traceback

def test(name, code, bmc_max=20, kind_k=12, ic3_frames=12,
         expected_bmc=None, expected_kind=None, expected_ic3=None):
    try:
        ts = RTLParser().parse_text_to_ts(code)
        bmc_r = bmc_incremental(ts, bmc_max, verbose=False)["result"]
        kind_r = check_kinduction(ts, kind_k, verbose=False)["result"]
        ic3_r = IC3(ts, max_frames=ic3_frames).prove(verbose=False)["result"]
        ok = True
        if expected_bmc and bmc_r != expected_bmc:
            ok = False
        if expected_kind and kind_r != expected_kind:
            ok = False
        if expected_ic3 and ic3_r != expected_ic3:
            ok = False
        status = "OK" if ok else "UNEXPECTED"
        print(f"  {status:10s} | {name:40s} | BMC={bmc_r:6s} | kind={kind_r:6s} | IC3={ic3_r:6s}")
    except Exception as e:
        print(f"  ERROR     | {name:40s} | {type(e).__name__}: {str(e)[:60]}")

# Safe counter
COUNTER_SAFE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) c <= 8'd255);
endmodule
"""

print("=== SAFE PROPERTIES ===")
test("c <= 255 (state prop)", COUNTER_SAFE)

# Buggy counter (wraps at 10)
COUNTER_BUGGY = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0;
        else if (c == 8'd10) c <= 8'd0;
        else c <= c + 8'd1;
    end
    assert property (@(posedge clk) rst_n |=> c != 8'd0);
endmodule
"""

print("\n=== BUGGY PROPERTIES ===")
test("|=> c!=0 (wrap bug at 11)", COUNTER_BUGGY, 15, 11)

# |-> overlapped implication
COUNTER_OVERLAP = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) rst_n |-> c != 8'd5);
endmodule
"""

test("|-> c != 5 (fail at 5)", COUNTER_OVERLAP, 10)

# Simple register
REG_SIMPLE = """
module m(input logic clk, rst_n, input logic [7:0] d, output logic [7:0] q);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 8'd0; else q <= d;
    end
    assert property (@(posedge clk) rst_n |=> q == d);
endmodule
"""

print("\n=== REGISTER TESTS ===")
test("|=> q == d (register)", REG_SIMPLE, 10)

# Trans property safe
TRANS_SAFE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) rst_n |=> c >= 8'd0);
endmodule
"""

print("\n=== TRANSITION PROPERTIES ===")
test("|=> c >= 0 (safe)", TRANS_SAFE)

# k-induction can prove (true: 8-bit wraps at 256, always ≤ 255)
KIND_PROVE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) c <= 8'd255);
endmodule
"""

print("\n=== K-INDUCTION PROVABLE ===")
test("c <= 255 (k-ind prove)", KIND_PROVE)

# State property fail
STATE_FAIL = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) c <= 8'd9);
endmodule
"""

test("c <= 9 (fail at 10)", STATE_FAIL, 15)

# Generate block tests
GEN_IF = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        if (1) begin : gen
            assert property (@(posedge clk) c <= 8'd255);
        end
    endgenerate
endmodule
"""

print("\n=== GENERATE BLOCKS ===")
test("generate if(1) prop", GEN_IF)

GEN_PARAM = """
module m(input logic clk, rst_n, output logic [7:0] c);
    parameter LIMIT = 200;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        if (LIMIT > 100) begin : gen
            assert property (@(posedge clk) c <= 8'd255);
        end else begin : gen_else
            assert property (@(posedge clk) c <= 8'd255);
        end
    endgenerate
endmodule
"""

test("generate param if", GEN_PARAM)

GEN_LOOP = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        for (genvar i = 0; i < 1; i++) begin : gen
            assert property (@(posedge clk) c <= 8'd255);
        end
    endgenerate
endmodule
"""

print("\n=== GENERATE LOOP ===")
test("generate loop prop", GEN_LOOP)

GEN_CASE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    parameter MODE = 1;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        case (MODE)
            0: begin : m0
                assert property (@(posedge clk) c <= 8'd255);
            end
            1: begin : m1
                assert property (@(posedge clk) c <= 8'd255);
            end
            default: begin : md
                assert property (@(posedge clk) c <= 8'd255);
            end
        endcase
    endgenerate
endmodule
"""

test("generate case prop", GEN_CASE)

# Named sequence/property tests
NAMED_SEQ = """
module m(input logic [7:0] a, input logic [7:0] b);
    sequence s_eq;
        a == b;
    endsequence
    assert property (s_eq);
endmodule
"""

NAMED_PROP = """
module m(input logic [7:0] a, input logic [7:0] b);
    property p_eq;
        a == b;
    endproperty
    assert property (p_eq);
endmodule
"""

NAMED_PROP_SAFE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    property c_max;
        @(posedge clk) disable iff (!rst_n) c <= 8'd255;
    endproperty
    assert property (c_max);
endmodule
"""

print("\n=== NAMED SEQUENCE/PROPERTY ===")
test("named sequence (comb)", NAMED_SEQ, 5, 5)
test("named property (comb)", NAMED_PROP, 5, 5)
test("named property (clocked)", NAMED_PROP_SAFE, 20, 12)

# Local variable in SVA tests
LOCAL_VAR_COMB = """
module m(input logic [7:0] a, input logic [7:0] d);
    sequence s;
        logic [7:0] v;
        (a, v = d);
    endsequence
    assert property (s);
endmodule
"""

LOCAL_VAR_TEMP = """
module m(input logic clk, rst_n, input logic [7:0] a, input logic [7:0] b, input logic [7:0] d);
    sequence s;
        logic [7:0] v;
        (a, v = d) ##1 (b, v == d);
    endsequence
    assert property (@(posedge clk) disable iff (!rst_n) s);
endmodule
"""

print("\n=== LOCAL VARIABLES IN SVA ===")
test("local var (comb seq)", LOCAL_VAR_COMB, 5, 5)
test("local var (temp seq)", LOCAL_VAR_TEMP, 10, 8)

# Interface / Modport tests
IFACE_BASIC = """
interface simple_if;
    logic [7:0] data;
    modport host (output data);
endinterface

module top(simple_if.host bus, input [7:0] val);
    assign bus.data = val;
endmodule
"""

IFACE_INPUT = """
interface simple_if;
    logic [7:0] data;
    modport device (input data);
endinterface

module top(simple_if.device bus, output [7:0] val);
    assign val = bus.data;
endmodule
"""

# Parameterized interface test
IFACE_PARAM = """
interface tl_if #(parameter int DW = 32);
    logic [DW-1:0] a_req, a_grant;
    modport host (input a_req, output a_grant);
endinterface

module top(tl_if #(.DW(16)).host bus, input [15:0] val);
    assign bus.a_grant = val;
endmodule
"""

print("\n=== INTERFACE / MODPORT ===")
test("iface basic (output)", IFACE_BASIC, 5, 5)
test("iface input", IFACE_INPUT, 5, 5)
test("iface parameterized", IFACE_PARAM, 5, 5)

print("\nDone.")
