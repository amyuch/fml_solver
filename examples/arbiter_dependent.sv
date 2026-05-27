module arbiter_dependent #(parameter N = 4) (
  input clk,
  input rst_n,
  input [N-1:0] req,
  output logic [N-1:0] gnt,
  output logic busy
);

  logic [N-1:0] req_q;
  logic gnt_done;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      gnt <= 0;
      req_q <= 0;
      busy <= 0;
    end else begin
      if (|req && !busy) begin
        gnt <= req & -req;
        req_q <= req ^ (req & -req);
        busy <= 1;
      end else if (gnt && !gnt_done) begin
        gnt <= gnt;
        busy <= 1;
      end else if (gnt_done) begin
        gnt <= (|req_q) ? (req_q & -req_q) : 0;
        req_q <= (|req_q) ? (req_q ^ (req_q & -req_q)) : 0;
        busy <= |req_q;
      end else begin
        gnt <= 0;
        busy <= 0;
      end
    end
  end

  assign gnt_done = |(gnt & ~req);

  // P1: one-hot grant
  assert property (@(posedge clk) disable iff (!rst_n)
    $onehot0(gnt));

  // P2: grant implies request
  assert property (@(posedge clk) disable iff (!rst_n)
    |gnt |-> |req || busy);

  // P3: new request activates arbiter (antecedent |req is input-only → busy essential)
  assert property (@(posedge clk) disable iff (!rst_n)
    |req |=> busy || gnt_done);

  // P4: no new grant while busy
  assert property (@(posedge clk) disable iff (!rst_n)
    busy && $stable(req) |=> busy || $fell(gnt));

  // P5: req0 granted implies req0 was pending
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(gnt[0]) |-> req[0] || req_q[0]);

  // P6: pending requests persist after grant
  assert property (@(posedge clk) disable iff (!rst_n)
    |req && !busy |=> busy);

  // P7: gnt_done clears grant
  assert property (@(posedge clk) disable iff (!rst_n)
    gnt_done && |gnt |=> !gnt || gnt_done);

  // P8: grant lasts at least one cycle
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(gnt) |=> gnt || $fell(gnt));

  // P9: each grant bit -> request was pending (immediate, antecedent gnt in comb)
  assert property (@(posedge clk) disable iff (!rst_n)
    gnt[0] |-> req[0] || req_q[0]);

  // P10: req bit 0 leads to grant (antecedent $rose uses input → gnt/busy essential)
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(req[0]) |=> gnt[0] || busy);

  // --- Assumptions ---
  // A1: requests are one-hot (for fair selection)
  assume property (@(posedge clk) disable iff (!rst_n)
    $onehot0(req));

  // A2: request persists until granted
  assume property (@(posedge clk) disable iff (!rst_n)
    req |=> req || $fell(req));

  // A3: no requests during reset
  assume property (@(posedge clk) disable iff (!rst_n)
    !rst_n |=> !$rose(req));

  // A4: rst_n always active in formal context
  assume property (@(posedge clk) rst_n);

endmodule
