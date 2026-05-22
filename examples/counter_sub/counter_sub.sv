module counter (
    input logic clk,
    input logic rst_n,
    input logic [7:0] max,
    output logic [7:0] val,
    output logic done
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            val <= 0;
            done <= 0;
        end else if (val >= max) begin
            val <= 0;
            done <= 1;
        end else begin
            val <= val + 1;
            done <= 0;
        end
    end
endmodule

module counter_sub (
    input logic clk,
    input logic rst_n,
    output logic [7:0] count,
    output logic flag
);
    logic [7:0] inner_val;
    logic inner_done;

    counter u_counter (
        .clk(clk),
        .rst_n(rst_n),
        .max(8'd10),
        .val(inner_val),
        .done(inner_done)
    );

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
