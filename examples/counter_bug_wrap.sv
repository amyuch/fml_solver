module counter_bug_wrap (
    input logic clk,
    input logic rst_n,
    output logic [7:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) count <= 8'd0;
        else if (count == 8'd10) count <= 8'd0;
        else count <= count + 8'd1;
    end

    // BUG: counter wraps to 0 at 10, violating:
    assert property (@(posedge clk) rst_n |=> count != 8'd0);
endmodule
