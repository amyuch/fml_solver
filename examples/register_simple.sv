module register_simple (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) data_out <= 8'd0;
        else data_out <= data_in;
    end

    // Property: after reset, data_out should hold data_in
    assert property (@(posedge clk) rst_n |=> data_out == data_in);
endmodule
