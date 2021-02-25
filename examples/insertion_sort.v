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
  exists h_sll_nxtlen1lo1hi1_632,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_632 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_632.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_633,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_633 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_633.

Lemma pure153 : (0) = (0). Admitted.
Hint Resolve pure153: ssl_pure.
Lemma pure154 : (7) = (7). Admitted.
Hint Resolve pure154: ssl_pure.
Lemma pure155 vx2 lo1x : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure155: ssl_pure.
Lemma pure156 hi1x vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure156: ssl_pure.
Lemma pure157 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). Admitted.
Hint Resolve pure157: ssl_pure.
Lemma pure158 hi1x vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure158: ssl_pure.
Lemma pure159 vx2 lo1x : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure159: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_634,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_634 /\ srtl x n lo hi h_srtl_xnlohi_634,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_635,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((1) + (n)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_635 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_635
    ]).

Variable srtl_insert : srtl_insert_type.

Definition insertion_sort_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_636,
      (0) <= (n) /\ h = r :-> null \+ h_sll_xnlohi_636 /\ sll x n lo hi h_sll_xnlohi_636,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_sll_xnlohi_637 h_srtl_ynlohi_638,
      h = r :-> y \+ h_sll_xnlohi_637 \+ h_srtl_ynlohi_638 /\ sll x n lo hi h_sll_xnlohi_637 /\ srtl y n lo hi h_srtl_ynlohi_638
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
ex_elim h_sll_xnlohi_636.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_636.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xnlohi_636.
move=>[phi_sll_xnlohi_6360] [phi_sll_xnlohi_6361] [phi_sll_xnlohi_6362].
move=>[sigma_sll_xnlohi_636].
subst h_sll_xnlohi_636.
try rename h_sll_xnlohi_636 into h_sll_xnlo_636.
try rename H_sll_xnlohi_636 into H_sll_xnlo_636.
try rename h_sll_xnlohi_637 into h_sll_xnlo_637.
try rename H_sll_xnlohi_637 into H_sll_xnlo_637.
try rename h_srtl_ynlohi_638 into h_srtl_ynlo_638.
try rename H_srtl_ynlohi_638 into H_srtl_ynlo_638.
try rename h_srtl_ynlo_638 into h_srtl_yn_638.
try rename H_srtl_ynlo_638 into H_srtl_yn_638.
try rename h_sll_xnlo_637 into h_sll_xn_637.
try rename H_sll_xnlo_637 into H_sll_xn_637.
try rename h_sll_xnlo_636 into h_sll_xn_636.
try rename H_sll_xnlo_636 into H_sll_xn_636.
try rename h_srtl_yn_638 into h_srtl_y_638.
try rename H_srtl_yn_638 into H_srtl_y_638.
try rename h_sll_xn_637 into h_sll_x_637.
try rename H_sll_xn_637 into H_sll_x_637.
try rename h_sll_xn_636 into h_sll_x_636.
try rename H_sll_xn_636 into H_sll_x_636.
try rename h_srtl_y_638 into h_srtl__638.
try rename H_srtl_y_638 into H_srtl__638.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_632x.
move=>[phi_sll_xnlohi_6360] [phi_sll_xnlohi_6361] [phi_sll_xnlohi_6362] [phi_sll_xnlohi_6363] [phi_sll_xnlohi_6364] [phi_sll_xnlohi_6365].
move=>[sigma_sll_xnlohi_636].
subst h_sll_xnlohi_636.
move=>H_sll_nxtxlen1xlo1xhi1x_632x.
try rename h_sll_xnlohi_636 into h_sll_xnlohi1xvxvxhi1x_636.
try rename H_sll_xnlohi_636 into H_sll_xnlohi1xvxvxhi1x_636.
try rename h_sll_xnlohi_637 into h_sll_xnlohi1xvxvxhi1x_637.
try rename H_sll_xnlohi_637 into H_sll_xnlohi1xvxvxhi1x_637.
try rename h_srtl_ynlohi_638 into h_srtl_ynlohi1xvxvxhi1x_638.
try rename H_srtl_ynlohi_638 into H_srtl_ynlohi1xvxvxhi1x_638.
try rename h_srtl_ynlohi1xvxvxhi1x_638 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_638.
try rename H_srtl_ynlohi1xvxvxhi1x_638 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_638.
try rename h_sll_xnlohi1xvxvxhi1x_636 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_636.
try rename H_sll_xnlohi1xvxvxhi1x_636 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_636.
try rename h_sll_xnlohi1xvxvxhi1x_637 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_637.
try rename H_sll_xnlohi1xvxvxhi1x_637 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_637.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_638 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_638.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_638 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_638.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_636 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_636.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_636 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_636.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_637 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_637.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_637 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_637.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_636 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_636.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_636 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_636.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_638 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_638.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_638 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_638.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_637 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_637.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_637 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_637.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_632x into h_sll_nxtx2len1xlo1xhi1x_632x.
try rename H_sll_nxtxlen1xlo1xhi1x_632x into H_sll_nxtx2len1xlo1xhi1x_632x.
try rename h_sll_x1n1lo1hi1_6361 into h_sll_nxtx2len1xlo1xhi1x_632x.
try rename H_sll_x1n1lo1hi1_6361 into H_sll_nxtx2len1xlo1xhi1x_632x.
ssl_call_pre (r :-> null \+ h_sll_nxtx2len1xlo1xhi1x_632x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx2len1xlo1xhi1x_632x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx2len1xlo1xhi1x_6371 h_srtl_y1len1xlo1xhi1x_6381.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx2len1xlo1xhi1x_6371 H_srtl_y1len1xlo1xhi1x_6381].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xlo1xhi1x_6381 into h_srtl_y12len1xlo1xhi1x_6381.
try rename H_srtl_y1len1xlo1xhi1x_6381 into H_srtl_y12len1xlo1xhi1x_6381.
try rename h_srtl_x2n2lo2hi2_634 into h_srtl_y12len1xlo1xhi1x_6381.
try rename H_srtl_x2n2lo2hi2_634 into H_srtl_y12len1xlo1xhi1x_6381.
ssl_write r.
ssl_call_pre (r :-> vx2 \+ h_srtl_y12len1xlo1xhi1x_6381).
ssl_call (vx2, len1x, lo1x, hi1x).
exists (h_srtl_y12len1xlo1xhi1x_6381);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_635.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_635.
store_valid.
try rename h_srtl_y2n11lo11hi11_635 into h_srtl_y2n11lo11hi1xvx2vx2hi1x_635.
try rename H_srtl_y2n11lo11hi11_635 into H_srtl_y2n11lo11hi1xvx2vx2hi1x_635.
try rename h_srtl_y2n11lo11hi1xvx2vx2hi1x_635 into h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename H_srtl_y2n11lo11hi1xvx2vx2hi1x_635 into H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_635 into h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_635 into H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
ssl_read r.
try rename y2 into y22.
try rename h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_638 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_638 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635.
try rename h_sll_nxtx1len1x1lo12xhi12x_632x1 into h_sll_nxtx2len1xlo1xhi1x_6371.
try rename H_sll_nxtx1len1x1lo12xhi12x_632x1 into H_sll_nxtx2len1xlo1xhi1x_6371.
ssl_emp;
exists (y22);
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x_6371);
exists (h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_635);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x_6371);
sslauto.
shelve.
ssl_frame_unfold.
Unshelve.
ssl_frame_unfold.
Qed.