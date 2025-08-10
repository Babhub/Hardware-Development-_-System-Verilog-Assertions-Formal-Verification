module tb_top_xp;

  logic clk = 0;
  logic rstn = 0;
  logic enq = 0;
  logic deq = 0;
  logic [31:0] din = 0;

  // Clock generation
  always #5 clk = ~clk;  // 10 time units period

  // Instantiate your DUT
  top_xp dut (
    .clk(clk),
    .rstn(rstn),
    .enq(enq),
    .deq(deq),
    .din(din)
  );

  initial begin
    // Apply reset
    rstn = 0;
    #20;
    rstn = 1;

    // Simple stimulus example
    repeat (10) begin
      @(posedge clk);
      enq = 1;
      din = $random;
      deq = 0;
    end

    repeat (10) begin
      @(posedge clk);
      enq = 0;
      deq = 1;
    end

    // Stop simulation
    #100;
    $finish;
  end

endmodule

