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

  // note: Declare exp at module scope to avoid block-declaration quirks in some sims
  beat_t exp;

  // ----------------------------
  // coverage helper signals
  // ---------------------------
  logic skid_take;

  logic stall_active_d;
  int   stall_len;
  int   last_stall_len;
  logic stall_end;          // 1-cycle pulse when a stall ends

  int cov_skid_take;
  int cov_skid_take_last;
  int cov_stall_1;
  int cov_stall_2_3;
  int cov_stall_4p;

  // input accepted while downstream not ready
  assign skid_take = (s_valid && s_ready && !m_ready);

  // stall length tracker (and a clean "stall ended" pulse)
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      stall_active_d <= 0;
      stall_len      <= 0;
      last_stall_len <= 0;
      stall_end      <= 0;
    end else begin
      stall_end      <= 0;
      stall_active_d <= (m_valid && !m_ready);

      if (m_valid && !m_ready) begin
        stall_len <= stall_len + 1;
      end

      // stall just ended: capture length and raise pulse
      if (stall_active_d && !(m_valid && !m_ready)) begin
        last_stall_len <= stall_len;
        stall_len      <= 0;
        stall_end      <= 1;
      end

      // fully idle (not stalled now, not stalled last cycle)
      if (!(m_valid && !m_ready) && !stall_active_d) begin
        stall_len <= 0;
      end
    end
  end

  // simple 0/1 hit flags for covg bins
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cov_skid_take      <= 0;
      cov_skid_take_last <= 0;
      cov_stall_1        <= 0;
      cov_stall_2_3      <= 0;
      cov_stall_4p       <= 0;
    end else begin
      if (skid_take) cov_skid_take <= 1;
      if (skid_take && s_last) cov_skid_take_last <= 1;

      // only update bins once per stall end
      if (stall_end) begin
        if (last_stall_len == 1)
          cov_stall_1 <= 1;
        else if (last_stall_len <= 3)
          cov_stall_2_3 <= 1;
        else
          cov_stall_4p <= 1;
      end
    end
  end

    // ----------------------------
  // Weighted constrained-random stall generator
  // ----------------------------
  class stall_gen_c;
    rand bit do_stall;
    rand int unsigned hold;

    // tune these weights
    constraint c_do_stall {
      // ~30% chance to start a stall
      do_stall dist { 0 := 7, 1 := 3 };
    }

    constraint c_hold {
      // weighted bins for stall length
      hold dist {
        1      := 3,          // hit stall_1
        [2:3]  := 5,          // hit stall_2_3 more often
        [4:6]  := 2           // still get stall_4p sometimes
      };
    }
  endclass

  stall_gen_c sg = new();
  logic staller_enable;


  final begin
    $display("// cov skid_take=%0d skid_take_last=%0d stall_1=%0d stall_2_3=%0d stall_4p=%0d",
             cov_skid_take, cov_skid_take_last,
             cov_stall_1, cov_stall_2_3, cov_stall_4p);
    $display("// total coverage = %0.2f%%", $get_coverage());
  end

  
  covergroup cg_min @(posedge clk);
    // did we ever take skid
    cp_skid_take: coverpoint skid_take { bins yes = {1}; }

    // did we ever take skid on last beat
    cp_skid_take_last: coverpoint (skid_take && s_last) { bins yes = {1}; }

    // sample stall length exactly when a stall ends
    cp_stall_len: coverpoint last_stall_len iff (stall_end) {
      bins one       = {1};
      bins two_three = {[2:3]};
      // avoid {[4:$]} because some tools dislike '$' in bins
      bins four_plus = {[4:32]};
    }
  endgroup

  cg_min cov = new();

  // ----------------------------
  // Scoreboard: compare DUT output vs expected queue
  // ----------------------------
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

  default clocking cb @(posedge clk); endclocking

  // if downstream isn’t ready, the dut must not wiggle outputs while m_valid stays high.
  property p_m_hold_when_stalled;
    disable iff (!rst_n)
    (m_valid && !m_ready) |=> (m_valid && $stable(m_data) && $stable(m_last));
  endproperty

  assert property (p_m_hold_when_stalled)
    else $fatal(1, "// m side changed while stalled");

  // checks driver + interface behavior and randomized source.
  property p_s_hold_when_stalled;
    disable iff (!rst_n)
    (s_valid && !s_ready) |=> (s_valid && $stable(s_data) && $stable(s_last));
  endproperty

  assert property (p_s_hold_when_stalled)
    else $fatal(1, "// s side changed while stalled");

  // catch junk on handshake signals
  property p_no_x_handshake;
    disable iff (!rst_n)
    !$isunknown({s_valid, s_ready, m_valid, m_ready, m_last, s_last});
  endproperty

  assert property (p_no_x_handshake)
    else $fatal(1, "// x detected on handshake signals");

  // ----------------------------
  // Driver tasks
  // ----------------------------
  task automatic drive_beat(input logic [DATA_W-1:0] data, input logic last);
  begin
    // wait until we're allowed to change payload (not currently stalled)
    while (s_valid && !s_ready) @(negedge clk);

    // drive beat
    @(negedge clk);
    s_valid <= 1'b1;
    s_data  <= data;
    s_last  <= last;

    // hold until accepted
    while (!(s_valid && s_ready)) @(posedge clk);

    // if you want continuous streaming, do not drop valid here
    // send_packet will update data/last for the next beat on the next negedge
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

        exp_q.push_back('{data: d, last: is_last});
        drive_beat(d, is_last);
      end

          // drop valid after packet
    // NOTE: don't change payload/valid while stalled
    while (s_valid && !s_ready) @(negedge clk);

    @(negedge clk);
    s_valid <= 1'b0;
    s_data  <= '0;
    s_last  <= 1'b0;

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
    m_ready = 1;
    staller_enable = 1;

    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
    repeat (2) @(posedge clk);

    $display("[TB] Starting stalled smoke...");

    // stall m_ready sometimes to force skid behavior (weighted constrained-random)
    fork
      begin : ready_staller
        m_ready <= 1'b1;
        forever begin
          @(posedge clk);

          if (!staller_enable) begin
            m_ready <= 1'b1;
            continue;
          end

          // pick whether to stall + how long (weighted)
          if (!sg.randomize()) $fatal(1, "[TB] stall_gen randomize failed");

          if (sg.do_stall) begin
            m_ready <= 1'b0;
            repeat (sg.hold) @(posedge clk);
            m_ready <= 1'b1;
          end
        end
      end
    join_none


    // A few packets (vary lengths)
    send_packet(3, 32'h1000);
    send_packet(1, 32'h2000);
    send_packet(5, 32'h3000);
    send_packet(13, 32'h1020);

    // Wait for all expected to drain
    wait (exp_q.size() == 0);
    repeat (5) @(posedge clk);

    // stop stalling
    disable ready_staller;
    m_ready = 1'b1;

    $display("[TB] PASS. got_count=%0d", got_count);

    $finish;
  end

endmodule
