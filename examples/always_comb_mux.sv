module always_comb_mux (
    input logic clk,
    input logic rst_n,
    input logic [1:0] sel,
    input logic [7:0] a, b, c,
    output logic [7:0] q
);
    always_comb begin
        if (sel == 2'd0) q = a;
        else if (sel == 2'd1) q = b;
        else q = c;
    end
    assert property (@(posedge clk) q == 
        (sel == 2'd0 ? a : sel == 2'd1 ? b : c));
endmodule
