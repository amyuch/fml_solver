import sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from fml.parser.rtl_parser import RTLParser
from fml.engine.bmc import bmc_incremental
from fml.engine.kind import check_kinduction
from fml.engine.ic3 import IC3
import time, traceback

def test(name, code, bmc_max=20, kind_k=3, expected_bmc=None, expected_kind=None, expected_ic3=None):
    try:
        ts = RTLParser().parse_text_to_ts(code)
        bmc_r = bmc_incremental(ts, bmc_max, verbose=False)["result"]
        kind_r = check_kinduction(ts, kind_k, verbose=False)["result"]
        ic3_r = IC3(ts, max_frames=8).prove(verbose=False)["result"]
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

# k-induction can prove
KIND_PROVE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    assert property (@(posedge clk) c <= 8'd200);
endmodule
"""

print("\n=== K-INDUCTION PROVABLE ===")
test("c <= 200 (k-ind prove)", KIND_PROVE, 5, 3)

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
            assert property (@(posedge clk) c <= 8'd200);
        end
    endgenerate
endmodule
"""

print("\n=== GENERATE BLOCKS ===")
test("generate if(1) prop", GEN_IF, 5, 3)

GEN_PARAM = """
module m(input logic clk, rst_n, output logic [7:0] c);
    parameter LIMIT = 200;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        if (LIMIT > 100) begin : gen
            assert property (@(posedge clk) c <= 8'd200);
        end else begin : gen_else
            assert property (@(posedge clk) c <= 8'd50);
        end
    endgenerate
endmodule
"""

test("generate param if", GEN_PARAM, 5, 3)

GEN_LOOP = """
module m(input logic clk, rst_n, output logic [7:0] c);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        for (genvar i = 0; i < 1; i++) begin : gen
            assert property (@(posedge clk) c <= 8'd200);
        end
    endgenerate
endmodule
"""

print("\n=== GENERATE LOOP ===")
test("generate loop prop", GEN_LOOP, 5, 3)

GEN_CASE = """
module m(input logic clk, rst_n, output logic [7:0] c);
    parameter MODE = 1;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) c <= 8'd0; else c <= c + 8'd1;
    end
    generate
        case (MODE)
            0: begin : m0
                assert property (@(posedge clk) c <= 8'd50);
            end
            1: begin : m1
                assert property (@(posedge clk) c <= 8'd200);
            end
            default: begin : md
                assert property (@(posedge clk) c <= 8'd100);
            end
        endcase
    endgenerate
endmodule
"""

test("generate case prop", GEN_CASE, 5, 3)

print("\nDone.")
