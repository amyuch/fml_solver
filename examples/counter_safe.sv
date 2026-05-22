module counter_safe (
    input logic clk,
    input logic rst_n,
    output logic [7:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) count <= 8'd0;
        else count <= count + 8'd1;
    end

    // Property: count should never exceed 255 (trivially true for 8-bit)
    assert property (@(posedge clk) count <= 8'd255);
endmodule
