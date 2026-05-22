module assign_basic (
    input logic clk,
    input logic [7:0] a, b,
    output logic [7:0] q
);
    assign q = a & b;
    assert property (@(posedge clk) q == (a & b));
endmodule
