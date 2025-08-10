// tb.v
`timescale 1ns/1ps

module tb;

reg clk = 0;
always #5 clk = ~clk; // 10ns clock period

wire sop, vld, eop;
wire [3:0] len;

protocol dut (
    .clk(clk),
    .sop(sop),
    .vld(vld),
    .eop(eop),
    .len(len)
);

assertions a (
    .clk(clk),
    .sop(sop),
    .vld(vld),
    .eop(eop),
    .len(len)
);

initial begin
    $vcdplusfile("vcdplus.vpd");
    $vcdpluson(0, tb);
    #200 $finish;
end

endmodule
