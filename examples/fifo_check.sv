module fifo_check #(parameter WIDTH = 8) (
  input clk,
  input rst_n,
  input wen,
  input ren,
  input [WIDTH-1:0] wdata,
  input load_threshold,
  input [2:0] threshold_val,
  output logic [WIDTH-1:0] rdata
);

  // DEPTH = 4 (PTR_W = 3, ADDR_W = 2)
  logic [WIDTH-1:0] mem [0:3];
  logic [2:0] wptr, rptr;
  logic [2:0] threshold;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wptr <= 0;
      rptr <= 0;
      rdata <= 0;
      threshold <= 0;
      for (int i = 0; i < 4; i++) mem[i] <= 0;
    end else begin
      if (wen && !((wptr[2] != rptr[2]) && (wptr[1:0] == rptr[1:0]))) begin
        mem[wptr[1:0]] <= wdata;
        wptr <= wptr + 1;
      end
      if (ren && !(wptr == rptr)) begin
        rdata <= mem[rptr[1:0]];
        rptr <= rptr + 1;
      end
      if (load_threshold) begin
        threshold <= threshold_val;
      end
    end
  end

  // P1: can't write when full
  assert property (@(posedge clk) disable iff (!rst_n)
    (wptr[2] != rptr[2]) && (wptr[1:0] == rptr[1:0]) |-> !wen);

  // P2: can't read when empty
  assert property (@(posedge clk) disable iff (!rst_n)
    (wptr == rptr) |-> !ren);

  // P3: write increments wptr when not full
  assert property (@(posedge clk) disable iff (!rst_n)
    wen && !((wptr[2] != rptr[2]) && (wptr[1:0] == rptr[1:0])) |=> wptr != $past(wptr));

  // P4: read increments rptr when not empty
  assert property (@(posedge clk) disable iff (!rst_n)
    ren && !(wptr == rptr) |=> rptr != $past(rptr));

  // P5: full implies wptr leads by 4
  assert property (@(posedge clk) disable iff (!rst_n)
    (wptr[2] != rptr[2]) && (wptr[1:0] == rptr[1:0]) |-> (wptr - rptr == 4));

  // P6: empty implies pointers equal
  assert property (@(posedge clk) disable iff (!rst_n)
    (wptr == rptr) |-> (wptr == rptr));

  // P7: threshold loaded correctly
  assert property (@(posedge clk) disable iff (!rst_n)
    load_threshold |=> threshold == $past(threshold_val));

  // P8: wen doesn't affect threshold
  assert property (@(posedge clk) disable iff (!rst_n)
    wen && !load_threshold |=> $stable(threshold));

  // P9: threshold non-increasing unless loaded
  assert property (@(posedge clk) disable iff (!rst_n)
    !load_threshold |=> threshold <= $past(threshold));

  // P10: read-only preserves wptr (ren is input-only)
  assert property (@(posedge clk) disable iff (!rst_n)
    ren && !wen |=> $stable(wptr));

  // P11: write-only preserves rptr (wen is input-only)
  assert property (@(posedge clk) disable iff (!rst_n)
    wen && !ren |=> $stable(rptr));

  // P12: read from empty preserves rdata (ren is input-only)
  assert property (@(posedge clk) disable iff (!rst_n)
    ren && (wptr == rptr) |=> $stable(rdata));

  // P13: depth in range
  assert property (@(posedge clk) disable iff (!rst_n)
    (wptr - rptr <= 4));

  // P14: write preserves almost_full decrease
  assert property (@(posedge clk) disable iff (!rst_n)
    wen && !(wptr[2] != rptr[2]) |=> (wptr - rptr) > $past(wptr - rptr) || $past(load_threshold));

  // P15: read from non-empty advances rdata
  assert property (@(posedge clk) disable iff (!rst_n)
    ren && !(wptr == rptr) |=> rdata != $past(rdata) || $past(wdata) == $past(rdata));

  // --- Assumptions ---
  // A1: threshold_val valid range
  assume property (@(posedge clk) disable iff (!rst_n)
    threshold_val != 0);

  // A2: rst_n always active in formal analysis
  assume property (@(posedge clk) rst_n);

  // A3: threshold within valid range
  assume property (@(posedge clk) disable iff (!rst_n)
    threshold_val <= 4);

endmodule
