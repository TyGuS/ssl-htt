From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_sll_nxtlen1lo1hi1_576,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_576 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_576.

Lemma pure54 : (0) = (0). Admitted.
Hint Resolve pure54: ssl_pure.
Lemma pure55 : (7) = (7). Admitted.
Hint Resolve pure55: ssl_pure.
Lemma pure56 len1x2 : (0) <= (len1x2) -> (0) <= ((1) + (len1x2)) -> ((1) + (len1x2)) = ((1) + (len1x2)). Admitted.
Hint Resolve pure56: ssl_pure.
Lemma pure57 hi1x vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure57: ssl_pure.
Lemma pure58 vx2 lo1x : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure58: ssl_pure.

Definition sll_len_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_577,
      (0) <= (n) /\ h = r :-> a \+ h_sll_xnlohi_577 /\ sll x n lo hi h_sll_xnlohi_577,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_578,
      h = r :-> n \+ h_sll_xnlohi_578 /\ sll x n lo hi h_sll_xnlohi_578
    ]).

Program Definition sll_len : sll_len_type :=
  Fix (fun (sll_len : sll_len_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      if (x) == (null)
      then
        r ::= 0;;
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_len (nxtx2, r);;
        len1x2 <-- @read nat r;
        r ::= (1) + (len1x2);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_577.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_577.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open ((x) == (null)) H_sll_xnlohi_577.
move=>[phi_sll_xnlohi_5770] [phi_sll_xnlohi_5771] [phi_sll_xnlohi_5772].
move=>[sigma_sll_xnlohi_577].
subst h_sll_xnlohi_577.
try rename h_sll_xnlohi_577 into h_sll_xnlo_577.
try rename H_sll_xnlohi_577 into H_sll_xnlo_577.
try rename h_sll_xnlohi_578 into h_sll_xnlo_578.
try rename H_sll_xnlohi_578 into H_sll_xnlo_578.
try rename h_sll_xnlo_577 into h_sll_xn_577.
try rename H_sll_xnlo_577 into H_sll_xn_577.
try rename h_sll_xnlo_578 into h_sll_xn_578.
try rename H_sll_xnlo_578 into H_sll_xn_578.
try rename h_sll_xn_577 into h_sll_x_577.
try rename H_sll_xn_577 into H_sll_x_577.
try rename h_sll_xn_578 into h_sll_x_578.
try rename H_sll_xn_578 into H_sll_x_578.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_576x.
move=>[phi_sll_xnlohi_5770] [phi_sll_xnlohi_5771] [phi_sll_xnlohi_5772] [phi_sll_xnlohi_5773] [phi_sll_xnlohi_5774] [phi_sll_xnlohi_5775].
move=>[sigma_sll_xnlohi_577].
subst h_sll_xnlohi_577.
move=>H_sll_nxtxlen1xlo1xhi1x_576x.
try rename h_sll_xnlohi_577 into h_sll_xnlohi1xvxvxhi1x_577.
try rename H_sll_xnlohi_577 into H_sll_xnlohi1xvxvxhi1x_577.
try rename h_sll_xnlohi_578 into h_sll_xnlohi1xvxvxhi1x_578.
try rename H_sll_xnlohi_578 into H_sll_xnlohi1xvxvxhi1x_578.
try rename h_sll_xnlohi1xvxvxhi1x_577 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_577.
try rename H_sll_xnlohi1xvxvxhi1x_577 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_577.
try rename h_sll_xnlohi1xvxvxhi1x_578 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_578.
try rename H_sll_xnlohi1xvxvxhi1x_578 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_578.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_578 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_578.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_578 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_578.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_577 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_577.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_577 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_577.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_577 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_577.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_577 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_577.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_578 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_578.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_578 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_578.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_576x into h_sll_nxtx2len1xlo1xhi1x_576x.
try rename H_sll_nxtxlen1xlo1xhi1x_576x into H_sll_nxtx2len1xlo1xhi1x_576x.
try rename h_sll_x1n1lo1hi1_5771 into h_sll_nxtx2len1xlo1xhi1x_576x.
try rename H_sll_x1n1lo1hi1_5771 into H_sll_nxtx2len1xlo1xhi1x_576x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_576x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_576x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5781.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5781.
store_valid.
ssl_read r.
try rename len1x into len1x2.
try rename h_sll_nxtx2len1xlo1xhi1x_576x into h_sll_nxtx2len1x2lo1xhi1x_576x.
try rename H_sll_nxtx2len1xlo1xhi1x_576x into H_sll_nxtx2len1x2lo1xhi1x_576x.
try rename h_sll_nxtx2len1xlo1xhi1x_5781 into h_sll_nxtx2len1x2lo1xhi1x_5781.
try rename H_sll_nxtx2len1xlo1xhi1x_5781 into H_sll_nxtx2len1x2lo1xhi1x_5781.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_577 into h_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_577.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_577 into H_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_577.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_578 into h_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_578.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_578 into H_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_578.
try rename h_sll_nxtx1len1x1lo11xhi11x_576x1 into h_sll_nxtx2len1x2lo1xhi1x_5781.
try rename H_sll_nxtx1len1x1lo11xhi11x_576x1 into H_sll_nxtx2len1x2lo1xhi1x_5781.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1x2lo1xhi1x_5781);
sslauto.
ssl_close 2;
exists (len1x2), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1x2lo1xhi1x_5781);
sslauto.
ssl_frame_unfold.
Qed.