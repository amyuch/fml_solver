module if_else_nested (
    input logic clk,
    input logic rst_n,
    input logic [1:0] sel,
    input logic [7:0] a, b, c,
    output logic [7:0] q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 8'd0;
        else if (sel == 2'd0) q <= a;
        else if (sel == 2'd1) q <= b;
        else q <= c;
    end

    // Property: q should always be one of the inputs or 0
    assert property (@(posedge clk) rst_n |-> 
        (q == a) || (q == b) || (q == c));
endmodule
