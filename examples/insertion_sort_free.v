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
  exists h_sll_nxtlen1lo1hi1_618,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_618 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_618.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_619,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_619 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_619.

Lemma pure128 : (0) = (0). Admitted.
Hint Resolve pure128: ssl_pure.
Lemma pure129 : (7) = (7). Admitted.
Hint Resolve pure129: ssl_pure.
Lemma pure130 hi1x vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure130: ssl_pure.
Lemma pure131 vx2 lo1x : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure131: ssl_pure.
Lemma pure132 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). Admitted.
Hint Resolve pure132: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_620,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_620 /\ srtl x n lo hi h_srtl_xnlohi_620,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_621,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((1) + (n)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_621 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_621
    ]).

Variable srtl_insert : srtl_insert_type.

Definition insertion_sort_free_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_622,
      (0) <= (n) /\ h = r :-> null \+ h_sll_xnlohi_622 /\ sll x n lo hi h_sll_xnlohi_622,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_srtl_ynlohi_623,
      h = r :-> y \+ h_srtl_ynlohi_623 /\ srtl y n lo hi h_srtl_ynlohi_623
    ]).

Program Definition insertion_sort_free : insertion_sort_free_type :=
  Fix (fun (insertion_sort_free : insertion_sort_free_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        insertion_sort_free (nxtx2, r);;
        y12 <-- @read ptr r;
        r ::= vx2;;
        srtl_insert (y12, r);;
        y22 <-- @read ptr r;
        dealloc x;;
        dealloc (x .+ 1);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[n lo] hi].
ex_elim h_sll_xnlohi_622.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_622.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xnlohi_622.
move=>[phi_sll_xnlohi_6220] [phi_sll_xnlohi_6221] [phi_sll_xnlohi_6222].
move=>[sigma_sll_xnlohi_622].
subst h_sll_xnlohi_622.
try rename h_sll_xnlohi_622 into h_sll_xnlo_622.
try rename H_sll_xnlohi_622 into H_sll_xnlo_622.
try rename h_srtl_ynlohi_623 into h_srtl_ynlo_623.
try rename H_srtl_ynlohi_623 into H_srtl_ynlo_623.
try rename h_sll_xnlo_622 into h_sll_xn_622.
try rename H_sll_xnlo_622 into H_sll_xn_622.
try rename h_srtl_ynlo_623 into h_srtl_yn_623.
try rename H_srtl_ynlo_623 into H_srtl_yn_623.
try rename h_sll_xn_622 into h_sll_x_622.
try rename H_sll_xn_622 into H_sll_x_622.
try rename h_srtl_yn_623 into h_srtl_y_623.
try rename H_srtl_yn_623 into H_srtl_y_623.
try rename h_srtl_y_623 into h_srtl__623.
try rename H_srtl_y_623 into H_srtl__623.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_618x.
move=>[phi_sll_xnlohi_6220] [phi_sll_xnlohi_6221] [phi_sll_xnlohi_6222] [phi_sll_xnlohi_6223] [phi_sll_xnlohi_6224] [phi_sll_xnlohi_6225].
move=>[sigma_sll_xnlohi_622].
subst h_sll_xnlohi_622.
move=>H_sll_nxtxlen1xlo1xhi1x_618x.
try rename h_sll_xnlohi_622 into h_sll_xnlohi1xvxvxhi1x_622.
try rename H_sll_xnlohi_622 into H_sll_xnlohi1xvxvxhi1x_622.
try rename h_srtl_ynlohi_623 into h_srtl_ynlohi1xvxvxhi1x_623.
try rename H_srtl_ynlohi_623 into H_srtl_ynlohi1xvxvxhi1x_623.
try rename h_sll_xnlohi1xvxvxhi1x_622 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_622.
try rename H_sll_xnlohi1xvxvxhi1x_622 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_622.
try rename h_srtl_ynlohi1xvxvxhi1x_623 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_623.
try rename H_srtl_ynlohi1xvxvxhi1x_623 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_623.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_622 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_622.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_622 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_622.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_623 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_623.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_623 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_623.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_622 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_622.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_622 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_622.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_623 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_623.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_623 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_623.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_618x into h_sll_nxtx2len1xlo1xhi1x_618x.
try rename H_sll_nxtxlen1xlo1xhi1x_618x into H_sll_nxtx2len1xlo1xhi1x_618x.
try rename h_sll_x1n1lo1hi1_6221 into h_sll_nxtx2len1xlo1xhi1x_618x.
try rename H_sll_x1n1lo1hi1_6221 into H_sll_nxtx2len1xlo1xhi1x_618x.
ssl_call_pre (r :-> null \+ h_sll_nxtx2len1xlo1xhi1x_618x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx2len1xlo1xhi1x_618x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_srtl_y1len1xlo1xhi1x_6231.
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1len1xlo1xhi1x_6231.
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xlo1xhi1x_6231 into h_srtl_y12len1xlo1xhi1x_6231.
try rename H_srtl_y1len1xlo1xhi1x_6231 into H_srtl_y12len1xlo1xhi1x_6231.
try rename h_srtl_x2n2lo2hi2_620 into h_srtl_y12len1xlo1xhi1x_6231.
try rename H_srtl_x2n2lo2hi2_620 into H_srtl_y12len1xlo1xhi1x_6231.
ssl_write r.
ssl_call_pre (r :-> vx2 \+ h_srtl_y12len1xlo1xhi1x_6231).
ssl_call (vx2, len1x, lo1x, hi1x).
exists (h_srtl_y12len1xlo1xhi1x_6231);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_621.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_621.
store_valid.
try rename h_srtl_y2n11lo11hi11_621 into h_srtl_y2n11lo11hi1xvx2vx2hi1x_621.
try rename H_srtl_y2n11lo11hi11_621 into H_srtl_y2n11lo11hi1xvx2vx2hi1x_621.
try rename h_srtl_y2n11lo11hi1xvx2vx2hi1x_621 into h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename H_srtl_y2n11lo11hi1xvx2vx2hi1x_621 into H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_621 into h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_621 into H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
ssl_read r.
try rename y2 into y22.
try rename h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_623 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_623 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_emp;
exists (y22);
exists (h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_621);
sslauto.
ssl_frame_unfold.
Qed.