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
  exists h_sll_nxtlen1lo1hi1_527,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_527 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_527.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_528,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_528 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_528.

Lemma pure26 : (0) == (0). Admitted.
Hint Resolve pure26: ssl_pure.
Lemma pure27 : (7) == (7). Admitted.
Hint Resolve pure27: ssl_pure.
Lemma pure28 vx2 lo1x : (0) <= (vx2) -> (vx2) <= (7) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) == ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure28: ssl_pure.
Lemma pure29 hi1x vx2 : (0) <= (vx2) -> (vx2) <= (7) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) == ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure29: ssl_pure.
Lemma pure30 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> ((1) + (len1x)) == ((1) + (len1x)). Admitted.
Hint Resolve pure30: ssl_pure.
Lemma pure31 hi1x vx2 : (0) <= (vx2) -> (vx2) <= (7) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) == ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure31: ssl_pure.
Lemma pure32 vx2 lo1x : (0) <= (vx2) -> (vx2) <= (7) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) == ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure32: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_529,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_529 /\ srtl x n lo hi h_srtl_xnlohi_529,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_530,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((1) + (n)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_530 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_530
    ]).

Variable srtl_insert : srtl_insert_type.

Definition insertion_sort_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_531,
      (0) <= (n) /\ h = r :-> null \+ h_sll_xnlohi_531 /\ sll x n lo hi h_sll_xnlohi_531,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_sll_xnlohi_532 h_srtl_ynlohi_533,
      h = r :-> y \+ h_sll_xnlohi_532 \+ h_srtl_ynlohi_533 /\ sll x n lo hi h_sll_xnlohi_532 /\ srtl y n lo hi h_srtl_ynlohi_533
    ]).

Program Definition insertion_sort : insertion_sort_type :=
  Fix (fun (insertion_sort : insertion_sort_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        insertion_sort (nxtx2, r);;
        y12 <-- @read ptr r;
        r ::= vx2;;
        srtl_insert (y12, r);;
        y22 <-- @read ptr r;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[n lo] hi].
ex_elim h_sll_xnlohi_531.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_531.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xnlohi_531.
move=>[phi_sll_xnlohi_5310] [phi_sll_xnlohi_5311] [phi_sll_xnlohi_5312].
move=>[sigma_sll_xnlohi_531].
subst h_sll_xnlohi_531.
try rename h_sll_xnlohi_531 into h_sll_xnlo_531.
try rename H_sll_xnlohi_531 into H_sll_xnlo_531.
try rename h_sll_xnlohi_532 into h_sll_xnlo_532.
try rename H_sll_xnlohi_532 into H_sll_xnlo_532.
try rename h_srtl_ynlohi_533 into h_srtl_ynlo_533.
try rename H_srtl_ynlohi_533 into H_srtl_ynlo_533.
try rename h_srtl_ynlo_533 into h_srtl_yn_533.
try rename H_srtl_ynlo_533 into H_srtl_yn_533.
try rename h_sll_xnlo_532 into h_sll_xn_532.
try rename H_sll_xnlo_532 into H_sll_xn_532.
try rename h_sll_xnlo_531 into h_sll_xn_531.
try rename H_sll_xnlo_531 into H_sll_xn_531.
try rename h_sll_xn_532 into h_sll_x_532.
try rename H_sll_xn_532 into H_sll_x_532.
try rename h_sll_xn_531 into h_sll_x_531.
try rename H_sll_xn_531 into H_sll_x_531.
try rename h_srtl_yn_533 into h_srtl_y_533.
try rename H_srtl_yn_533 into H_srtl_y_533.
try rename h_srtl_y_533 into h_srtl__533.
try rename H_srtl_y_533 into H_srtl__533.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
unfold_constructor 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_527x.
move=>[phi_sll_xnlohi_5310] [phi_sll_xnlohi_5311] [phi_sll_xnlohi_5312] [phi_sll_xnlohi_5313] [phi_sll_xnlohi_5314] [phi_sll_xnlohi_5315].
move=>[sigma_sll_xnlohi_531].
subst h_sll_xnlohi_531.
move=>H_sll_nxtxlen1xlo1xhi1x_527x.
try rename h_sll_xnlohi_531 into h_sll_xnlohi1xvxvxhi1x_531.
try rename H_sll_xnlohi_531 into H_sll_xnlohi1xvxvxhi1x_531.
try rename h_sll_xnlohi_532 into h_sll_xnlohi1xvxvxhi1x_532.
try rename H_sll_xnlohi_532 into H_sll_xnlohi1xvxvxhi1x_532.
try rename h_srtl_ynlohi_533 into h_srtl_ynlohi1xvxvxhi1x_533.
try rename H_srtl_ynlohi_533 into H_srtl_ynlohi1xvxvxhi1x_533.
try rename h_srtl_ynlohi1xvxvxhi1x_533 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_533.
try rename H_srtl_ynlohi1xvxvxhi1x_533 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_533.
try rename h_sll_xnlohi1xvxvxhi1x_532 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_532.
try rename H_sll_xnlohi1xvxvxhi1x_532 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_532.
try rename h_sll_xnlohi1xvxvxhi1x_531 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_531.
try rename H_sll_xnlohi1xvxvxhi1x_531 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_531.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_533 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_533.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_533 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_533.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_532 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_532.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_532 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_532.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_531 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_531.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_531 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_531.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_531 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_531.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_531 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_531.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_532 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_532.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_532 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_532.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_533 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_533.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_533 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_533.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_527x into h_sll_nxtx2len1xlo1xhi1x_527x.
try rename H_sll_nxtxlen1xlo1xhi1x_527x into H_sll_nxtx2len1xlo1xhi1x_527x.
try rename h_sll_x1n1lo1hi1_5311 into h_sll_nxtx2len1xlo1xhi1x_527x.
try rename H_sll_x1n1lo1hi1_5311 into H_sll_nxtx2len1xlo1xhi1x_527x.
ssl_call_pre (r :-> null \+ h_sll_nxtx2len1xlo1xhi1x_527x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx2len1xlo1xhi1x_527x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5321 h_srtl_y1len1xlo1xhi1x_5331.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx2len1xlo1xhi1x_5321 H_srtl_y1len1xlo1xhi1x_5331].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xlo1xhi1x_5331 into h_srtl_y12len1xlo1xhi1x_5331.
try rename H_srtl_y1len1xlo1xhi1x_5331 into H_srtl_y12len1xlo1xhi1x_5331.
try rename h_srtl_x2n2lo2hi2_529 into h_srtl_y12len1xlo1xhi1x_5331.
try rename H_srtl_x2n2lo2hi2_529 into H_srtl_y12len1xlo1xhi1x_5331.
ssl_write r.
ssl_call_pre (r :-> vx2 \+ h_srtl_y12len1xlo1xhi1x_5331).
ssl_call (vx2, len1x, lo1x, hi1x).
exists (h_srtl_y12len1xlo1xhi1x_5331);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_530.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_530.
store_valid.
try rename h_srtl_y2n11lo11hi11_530 into h_srtl_y2n11lo11hi1xvx2vx2hi1x_530.
try rename H_srtl_y2n11lo11hi11_530 into H_srtl_y2n11lo11hi1xvx2vx2hi1x_530.
try rename h_srtl_y2n11lo11hi1xvx2vx2hi1x_530 into h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename H_srtl_y2n11lo11hi1xvx2vx2hi1x_530 into H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_530 into h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_530 into H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
ssl_read r.
try rename y2 into y22.
try rename h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_533 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_533 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530.
try rename h_sll_nxtx1len1x1lo12xhi12x_527x1 into h_sll_nxtx2len1xlo1xhi1x_5321.
try rename H_sll_nxtx1len1x1lo12xhi12x_527x1 into H_sll_nxtx2len1xlo1xhi1x_5321.
ssl_emp;
exists (y22);
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x_5321);
exists (h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_530);
sslauto.
unfold_constructor 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x_5321);
sslauto.
shelve.
ssl_frame_unfold.
Unshelve.
ssl_frame_unfold.
Qed.