module arbiter_with_sva (
    input  logic        clk,
    input  logic        rst_n,
    input  logic  [1:0] req,
    output logic  [1:0] gnt
);

    // ==========================================
    // RTL: Priority Arbiter (req[1] > req[0])
    // ==========================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gnt <= 2'b00;
        end else begin
            if (req[1])      gnt <= 2'b10;
            else if (req[0]) gnt <= 2'b01;
            else             gnt <= 2'b00;
        end
    end

    // ==========================================
    // SYSTEMVERILO ASSERTIONS (SVA)
    // ==========================================

    // 1. SAFETY: Mutual Exclusion
    // Only one grant may be active at any time
    assert property (@(posedge clk) disable iff (!rst_n)
        $onehot0(gnt))
    else $error("SAFETY_VIOLATION: Mutual exclusion failed!");

    // 2. PROTOCOL: Grant requires prior request
    // A grant can only occur if the matching request was asserted 1 cycle ago
    assert property (@(posedge clk) disable iff (!rst_n)
        gnt[0] |-> $past(req[0], 1))
    else $warning("PROTOCOL_VIOLATION: Grant[0] without prior Request[0]!");

    assert property (@(posedge clk) disable iff (!rst_n)
        gnt[1] |-> $past(req[1], 1))
    else $warning("PROTOCOL_VIOLATION: Grant[1] without prior Request[1]!");

    // 3. TIMING: Bounded Response Time
    // If req[0] is asserted and req[1] is low, gnt[0] must assert within 2 cycles
    // Note: Bounded (##[1:2]) is simulation-safe. Use ##[*] for formal verification.
    assert property (@(posedge clk) disable iff (!rst_n)
        (req[0] && !req[1]) |=> ##[1:2] gnt[0])
    else $error("TIMING_VIOLATION: Request[0] not granted within 2 cycles!");

    // 4. RESET: Clean reset behavior
    // No grants should be active during or immediately after reset deassertion
    assert property (@(posedge clk)
        !rst_n |=> gnt == 2'b00)
    else $error("RESET_VIOLATION: Grants active during reset!");

    // 5. SEQUENTIAL: Priority Enforcement
    // When both requests are high, req[1] must win
    sequence seq_both_req = (req == 2'b11);
    assert property (@(posedge clk) disable iff (!rst_n)
        seq_both_req |=> gnt == 2'b10)
    else $warning("PRIORITY_VIOLATION: req[1] should win when both asserted!");

    // 6. SAFETY: No spurious grants
    // Grant cannot be active if no requests are present
    assert property (@(posedge clk) disable iff (!rst_n)
        (req == 2'b00) |=> gnt == 2'b00)
    else $error("SAFETY_VIOLATION: Spurious grant detected!");

endmodule
