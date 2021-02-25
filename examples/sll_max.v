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
  exists h_sll_nxtlen1lo1hi1_579,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_579 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_579.

Lemma pure59 : (0) = (0). Admitted.
Hint Resolve pure59: ssl_pure.
Lemma pure60 : (7) = (7). Admitted.
Hint Resolve pure60: ssl_pure.
Lemma pure61 len1x : (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). Admitted.
Hint Resolve pure61: ssl_pure.
Lemma pure62 hi1x2 vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x2) <= (vx2) then vx2 else hi1x2)) = ((if (hi1x2) <= (vx2) then vx2 else hi1x2)). Admitted.
Hint Resolve pure62: ssl_pure.
Lemma pure63 vx2 lo1x : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure63: ssl_pure.

Definition sll_max_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_580,
      h = r :-> a \+ h_sll_xnlohi_580 /\ sll x n lo hi h_sll_xnlohi_580,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_581,
      h = r :-> hi \+ h_sll_xnlohi_581 /\ sll x n lo hi h_sll_xnlohi_581
    ]).

Program Definition sll_max : sll_max_type :=
  Fix (fun (sll_max : sll_max_type) vprogs =>
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
        sll_max (nxtx2, r);;
        hi1x2 <-- @read nat r;
        r ::= (if (hi1x2) <= (vx2) then vx2 else hi1x2);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_580.
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_580.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open ((x) == (null)) H_sll_xnlohi_580.
move=>[phi_sll_xnlohi_5800] [phi_sll_xnlohi_5801] [phi_sll_xnlohi_5802].
move=>[sigma_sll_xnlohi_580].
subst h_sll_xnlohi_580.
try rename h_sll_xnlohi_580 into h_sll_xnlo_580.
try rename H_sll_xnlohi_580 into H_sll_xnlo_580.
try rename h_sll_xnlohi_581 into h_sll_xnlo_581.
try rename H_sll_xnlohi_581 into H_sll_xnlo_581.
try rename h_sll_xnlo_580 into h_sll_xn_580.
try rename H_sll_xnlo_580 into H_sll_xn_580.
try rename h_sll_xnlo_581 into h_sll_xn_581.
try rename H_sll_xnlo_581 into H_sll_xn_581.
try rename h_sll_xn_580 into h_sll_x_580.
try rename H_sll_xn_580 into H_sll_x_580.
try rename h_sll_xn_581 into h_sll_x_581.
try rename H_sll_xn_581 into H_sll_x_581.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_579x.
move=>[phi_sll_xnlohi_5800] [phi_sll_xnlohi_5801] [phi_sll_xnlohi_5802] [phi_sll_xnlohi_5803] [phi_sll_xnlohi_5804] [phi_sll_xnlohi_5805].
move=>[sigma_sll_xnlohi_580].
subst h_sll_xnlohi_580.
move=>H_sll_nxtxlen1xlo1xhi1x_579x.
try rename h_sll_xnlohi_580 into h_sll_xnlohi1xvxvxhi1x_580.
try rename H_sll_xnlohi_580 into H_sll_xnlohi1xvxvxhi1x_580.
try rename h_sll_xnlohi_581 into h_sll_xnlohi1xvxvxhi1x_581.
try rename H_sll_xnlohi_581 into H_sll_xnlohi1xvxvxhi1x_581.
try rename h_sll_xnlohi1xvxvxhi1x_580 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_580.
try rename H_sll_xnlohi1xvxvxhi1x_580 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_580.
try rename h_sll_xnlohi1xvxvxhi1x_581 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_581.
try rename H_sll_xnlohi1xvxvxhi1x_581 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_581.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_580 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_580.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_580 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_580.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_581 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_581.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_581 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_581.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_581 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_581.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_581 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_581.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_580 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_580.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_580 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_580.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_579x into h_sll_nxtx2len1xlo1xhi1x_579x.
try rename H_sll_nxtxlen1xlo1xhi1x_579x into H_sll_nxtx2len1xlo1xhi1x_579x.
try rename h_sll_x1n1lo1hi1_5801 into h_sll_nxtx2len1xlo1xhi1x_579x.
try rename H_sll_x1n1lo1hi1_5801 into H_sll_nxtx2len1xlo1xhi1x_579x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_579x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_579x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5811.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5811.
store_valid.
ssl_read r.
try rename hi1x into hi1x2.
try rename h_sll_nxtx2len1xlo1xhi1x_579x into h_sll_nxtx2len1xlo1xhi1x2_579x.
try rename H_sll_nxtx2len1xlo1xhi1x_579x into H_sll_nxtx2len1xlo1xhi1x2_579x.
try rename h_sll_nxtx2len1xlo1xhi1x_5811 into h_sll_nxtx2len1xlo1xhi1x2_5811.
try rename H_sll_nxtx2len1xlo1xhi1x_5811 into H_sll_nxtx2len1xlo1xhi1x2_5811.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_580 into h_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_580.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_580 into H_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_580.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_581 into h_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_581.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_581 into H_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_581.
try rename h_sll_nxtx1len1x1lo11xhi11x_579x1 into h_sll_nxtx2len1xlo1xhi1x2_5811.
try rename H_sll_nxtx1len1x1lo11xhi11x_579x1 into H_sll_nxtx2len1xlo1xhi1x2_5811.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x2_5811);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x2), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x2_5811);
sslauto.
ssl_frame_unfold.
Qed.