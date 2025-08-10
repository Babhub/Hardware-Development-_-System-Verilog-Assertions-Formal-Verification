// assert.sv
module assertions(input clk, input sop, input vld, input eop, input [3:0] len);

    // SOP implies VLD
    assert property (@(posedge clk) sop |-> vld)
    else $error("Assertion Failed: sop high but vld not high");

    // EOP implies VLD
    assert property (@(posedge clk) eop |-> vld)
    else $error("Assertion Failed: eop high but vld not high");

    // len remains constant during VLD
    logic [3:0] len_saved;
    always @(posedge clk) begin
        if (sop && vld)
            len_saved <= len;

        if (vld)
            assert(len == len_saved)
            else $error("Assertion Failed: len changed during vld");
    end

endmodule
