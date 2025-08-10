// top_xp.sv
module top_xp (
    input  logic         clk,
    input  logic         rstn,
    input  logic         enq,
    input  logic         deq,
    input  logic [31:0]  din
);

    // Instance 1 outputs
    logic [31:0] dout1;
    logic        full1;
    logic        empty1;

    // Instance 2 outputs
    logic [31:0] dout2;
    logic        full2;
    logic        empty2;

    // Instantiate DUT (two copies)
    queue dut1 (
        .clk(clk),
        .rstn(rstn),
        .enq(enq),
        .deq(deq),
        .din(din),
        .dout(dout1),
        .full(full1),
        .empty(empty1)
    );

    queue dut2 (
        .clk(clk),
        .rstn(rstn),
        .enq(enq),
        .deq(deq),
        .din(din),
        .dout(dout2),
        .full(full2),
        .empty(empty2)
    );

    // Formal-friendly assertion: compare outputs cycle-by-cycle.
    // Using case-equality (===) ensures X/Z differences are considered.
    property outputs_match;
      @(posedge clk) disable iff (!rstn)
        (dout1 === dout2) && (full1 === full2) && (empty1 === empty2);
    endproperty

    // Check the property (formal will try to prove it)
    assert property (outputs_match);

endmodule
