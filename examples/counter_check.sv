module counter_check #(parameter WIDTH = 8) (
  input clk,
  input rst_n,
  input en,
  input load,
  input [WIDTH-1:0] load_val,
  output logic [WIDTH-1:0] cnt,
  output logic wrap
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cnt <= 0;
      wrap <= 0;
    end else begin
      wrap <= 0;
      if (load) begin
        cnt <= load_val;
      end else if (en) begin
        if (cnt > 0) begin
          cnt <= cnt - 1;
          if (cnt == 1) wrap <= 1;
        end
      end
    end
  end

  // P1: enable when cnt>0 decrements cnt
  assert property (@(posedge clk) disable iff (!rst_n)
    en && !load && cnt != 0 |=> cnt == $past(cnt) - 1);

  // P2: load writes load_val to cnt (antecedent load is input-only → cnt essential)
  assert property (@(posedge clk) disable iff (!rst_n)
    load |=> cnt == $past(load_val));

  // P3: wrap only on reaching 1 from above
  assert property (@(posedge clk) disable iff (!rst_n)
    $rose(wrap) |-> cnt == 1);

  // P4: no underflow below 0 when en
  assert property (@(posedge clk) disable iff (!rst_n)
    en && cnt == 0 |=> cnt == 0);

  // P5: cnt always onehot (structural)
  assert property (@(posedge clk) disable iff (!rst_n)
    $onehot0(cnt));

  // P6: load makes cnt stable after write
  assert property (@(posedge clk) disable iff (!rst_n)
    load && cnt == load_val |=> cnt == $past(cnt));

  // P7: en monotonic decrease (antecedent en is input-only → cnt essential)
  //     Without cnt's trans: cnt_next free → cnt_next > cnt possible → SAT
  assert property (@(posedge clk) disable iff (!rst_n)
    en && !load |=> cnt <= $past(cnt));

  // P8: load and en not both active
  assert property (@(posedge clk) disable iff (!rst_n)
    !(en && load));

  // P9: wrap resets after one cycle
  assert property (@(posedge clk) disable iff (!rst_n)
    wrap |=> !wrap);

  // P10: cnt changes iff en or load (antecedent uses input only)
  assert property (@(posedge clk) disable iff (!rst_n)
    !en && !load |=> $stable(cnt));

  // P11: load makes specific cnt value (antecedent load is input-only)
  assert property (@(posedge clk) disable iff (!rst_n)
    load |-> load_val != 0);

  // P12: en cannot fire when cnt is already minimal
  assert property (@(posedge clk) disable iff (!rst_n)
    en && cnt == 1 |=> wrap || cnt == 0);

  // --- Assumptions ---
  // A1: load and en mutually exclusive
  assume property (@(posedge clk) disable iff (!rst_n)
    !en || !load);

  // A2: load_val stable while load asserted
  assume property (@(posedge clk) disable iff (!rst_n)
    load |=> $stable(load_val));

  // A3: load_val non-zero for meaningful countdown
  assume property (@(posedge clk) disable iff (!rst_n)
    load_val != 0);

  // A4: rst_n always active in formal context
  assume property (@(posedge clk) rst_n);

endmodule
