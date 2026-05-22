module counter_sub (
    input logic clk,
    input logic rst_n,
    output logic [7:0] count,
    output logic flag
);
    logic [7:0] inner_val;
    logic inner_done;

    // Inlined: counter u_counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            inner_val <= 0;
            inner_done <= 0;
        end else if (inner_val >= 8'd10) begin
            inner_val <= 0;
            inner_done <= 1;
        end else begin
            inner_val <= inner_val + 1;
            inner_done <= 0;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 0;
            flag <= 0;
        end else if (inner_done) begin
            count <= count + 1;
            flag <= 1;
        end else begin
            flag <= 0;
        end
    end

    assert property (@(posedge clk) count <= 8'd20);
endmodule
