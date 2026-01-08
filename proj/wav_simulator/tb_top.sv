module tb_top;

  localparam int DATA_W = 32;

  logic clk, rst_n;

  // DUT ports
  logic               s_valid;
  logic               s_ready;
  logic [DATA_W-1:0]  s_data;
  logic               s_last;

  logic               m_valid;
  logic               m_ready;
  logic [DATA_W-1:0]  m_data;
  logic               m_last;

  // Clock
  initial clk = 0;
  always #5 clk = ~clk;

  // DUT
  skid_buffer #(.DATA_W(DATA_W)) dut (
    .clk(clk), .rst_n(rst_n),
    .s_valid(s_valid), .s_ready(s_ready), .s_data(s_data), .s_last(s_last),
    .m_valid(m_valid), .m_ready(m_ready), .m_data(m_data), .m_last(m_last)
  );

  // ----------------------------
  // Simple "transaction" type
  // ----------------------------
  typedef struct packed {
    logic [DATA_W-1:0] data;
    logic              last;
  } beat_t;

  beat_t exp_q[$];  // expected beats FIFO

  // ----------------------------
  // Monitor + scoreboard
  // ----------------------------
  int got_count;

  // NOTE: Declare exp at module scope to avoid block-declaration quirks in some sims
  beat_t exp;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      got_count <= 0;
    end else begin
      if (m_valid && m_ready) begin
        if (exp_q.size() == 0) begin
          $fatal(1, "[SB] Unexpected output beat! data=%h last=%0d", m_data, m_last);
        end else begin
          // assignment MUST be separate from declaration for ModelSim
          exp = exp_q.pop_front();

          if ((m_data !== exp.data) || (m_last !== exp.last)) begin
            $fatal(1, "[SB] Mismatch: got data=%h last=%0d exp data=%h last=%0d",
                   m_data, m_last, exp.data, exp.last);
          end
          got_count <= got_count + 1;
        end
      end
    end
  end

  // ----------------------------
  // Driver tasks
  // ----------------------------
  task automatic drive_beat(input logic [DATA_W-1:0] data, input logic last);
    begin
      s_valid <= 1'b1;
      s_data  <= data;
      s_last  <= last;

      // Wait until transfer occurs (s_valid && s_ready)
      while (!(s_valid && s_ready)) @(posedge clk);

      // Beat accepted; deassert valid next cycle
      @(posedge clk);
      s_valid <= 1'b0;
      s_data  <= '0;
      s_last  <= 1'b0;
    end
  endtask

  task automatic send_packet(input int n_beats, input logic [DATA_W-1:0] base);
    int i;
    logic is_last;
    logic [DATA_W-1:0] d;

    begin
      for (i = 0; i < n_beats; i++) begin
        is_last = (i == n_beats-1);
        d       = base + i;

        // push expected
        exp_q.push_back('{data: d, last: is_last});

        // drive
        drive_beat(d, is_last);
      end
    end
  endtask

  // ----------------------------
  // Test sequence
  // ----------------------------
  initial begin
    // init
    s_valid = 0;
    s_data  = '0;
    s_last  = 0;
    m_ready = 1;   // no stalls directed test

    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
    repeat (2) @(posedge clk);

    $display("[TB] Starting directed no-stall smoke...");

    // A few packets (vary lengths)
    send_packet(3, 32'h1000);
    send_packet(1, 32'h2000);
    send_packet(5, 32'h3000);

    // Wait for all expected to drain
    wait (exp_q.size() == 0);
    repeat (5) @(posedge clk);

    $display("[TB] PASS. got_count=%0d", got_count);
    $finish;
  end

endmodule
