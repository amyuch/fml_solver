module counter_overflow (
    input logic clk,
    input logic rst_n,
    output logic [3:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) count <= 4'd0;
        else count <= count + 4'd1;
    end

    // BUG: 4-bit counter overflows after 15
    assert property (@(posedge clk) count <= 4'd9);
endmodule
