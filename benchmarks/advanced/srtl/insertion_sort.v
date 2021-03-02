From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.
From Hammer Require Import Hammer.
(* Configure Hammer *)
Unset Hammer Eprover.
Unset Hammer Vampire.
Add Search Blacklist "fcsl.".
Add Search Blacklist "HTT.".
Add Search Blacklist "Coq.ssr.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.bigop".
Add Search Blacklist "mathcomp.ssreflect.choice".
Add Search Blacklist "mathcomp.ssreflect.div".
Add Search Blacklist "mathcomp.ssreflect.finfun".
Add Search Blacklist "mathcomp.ssreflect.fintype".
Add Search Blacklist "mathcomp.ssreflect.path".
Add Search Blacklist "mathcomp.ssreflect.tuple".


Require Import common.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_557,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_557 /\ srtl x n lo hi h_srtl_xnlohi_557,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_558,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((1) + (n)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_558 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_558
    ]).

Variable srtl_insert : srtl_insert_type.

Lemma pure85 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure85: ssl_pure.
Lemma pure86 : (7) = (7). intros; hammer. Qed.
Hint Resolve pure86: ssl_pure.
Lemma pure87 (hi1x : nat) (vx2 : nat) : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). intros; hammer. Qed.
Hint Resolve pure87: ssl_pure.
Lemma pure88 (len1x : nat) : (0) <= (len1x) -> (0) <= ((1) + (len1x)) -> ((1) + (len1x)) = ((1) + (len1x)). intros; hammer. Qed.
Hint Resolve pure88: ssl_pure.
Lemma pure89 (vx2 : nat) (lo1x : nat) : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure89: ssl_pure.
Lemma pure90 (hi1x : nat) (vx2 : nat) : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). intros; hammer. Qed.
Hint Resolve pure90: ssl_pure.
Lemma pure91 (vx2 : nat) (lo1x : nat) : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure91: ssl_pure.

Definition insertion_sort_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_559,
      (0) <= (n) /\ h = r :-> null \+ h_sll_xnlohi_559 /\ sll x n lo hi h_sll_xnlohi_559,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_sll_xnlohi_560 h_srtl_ynlohi_561,
      h = r :-> y \+ h_sll_xnlohi_560 \+ h_srtl_ynlohi_561 /\ sll x n lo hi h_sll_xnlohi_560 /\ srtl y n lo hi h_srtl_ynlohi_561
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
ex_elim h_sll_xnlohi_559.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_559.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xnlohi_559.
move=>[phi_sll_xnlohi_5590] [phi_sll_xnlohi_5591] [phi_sll_xnlohi_5592].
move=>[sigma_sll_xnlohi_559].
subst h_sll_xnlohi_559.
try rename h_sll_xnlohi_559 into h_sll_xnlo_559.
try rename H_sll_xnlohi_559 into H_sll_xnlo_559.
try rename h_sll_xnlohi_560 into h_sll_xnlo_560.
try rename H_sll_xnlohi_560 into H_sll_xnlo_560.
try rename h_srtl_ynlohi_561 into h_srtl_ynlo_561.
try rename H_srtl_ynlohi_561 into H_srtl_ynlo_561.
try rename h_srtl_ynlo_561 into h_srtl_yn_561.
try rename H_srtl_ynlo_561 into H_srtl_yn_561.
try rename h_sll_xnlo_559 into h_sll_xn_559.
try rename H_sll_xnlo_559 into H_sll_xn_559.
try rename h_sll_xnlo_560 into h_sll_xn_560.
try rename H_sll_xnlo_560 into H_sll_xn_560.
try rename h_sll_xn_560 into h_sll_x_560.
try rename H_sll_xn_560 into H_sll_x_560.
try rename h_sll_xn_559 into h_sll_x_559.
try rename H_sll_xn_559 into H_sll_x_559.
try rename h_srtl_yn_561 into h_srtl_y_561.
try rename H_srtl_yn_561 into H_srtl_y_561.
try rename h_srtl_y_561 into h_srtl__561.
try rename H_srtl_y_561 into H_srtl__561.
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
ex_elim h_sll_nxtxlen1xlo1xhi1x_555x.
move=>[phi_sll_xnlohi_5590] [phi_sll_xnlohi_5591] [phi_sll_xnlohi_5592] [phi_sll_xnlohi_5593] [phi_sll_xnlohi_5594] [phi_sll_xnlohi_5595].
move=>[sigma_sll_xnlohi_559].
subst h_sll_xnlohi_559.
move=>H_sll_nxtxlen1xlo1xhi1x_555x.
try rename h_sll_xnlohi_559 into h_sll_xnlohi1xvxvxhi1x_559.
try rename H_sll_xnlohi_559 into H_sll_xnlohi1xvxvxhi1x_559.
try rename h_sll_xnlohi_560 into h_sll_xnlohi1xvxvxhi1x_560.
try rename H_sll_xnlohi_560 into H_sll_xnlohi1xvxvxhi1x_560.
try rename h_srtl_ynlohi_561 into h_srtl_ynlohi1xvxvxhi1x_561.
try rename H_srtl_ynlohi_561 into H_srtl_ynlohi1xvxvxhi1x_561.
try rename h_sll_xnlohi1xvxvxhi1x_559 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_559.
try rename H_sll_xnlohi1xvxvxhi1x_559 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_559.
try rename h_sll_xnlohi1xvxvxhi1x_560 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_560.
try rename H_sll_xnlohi1xvxvxhi1x_560 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_560.
try rename h_srtl_ynlohi1xvxvxhi1x_561 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_561.
try rename H_srtl_ynlohi1xvxvxhi1x_561 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_561.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_561 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_561.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_561 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_561.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_560 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_560.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_560 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_560.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_559 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_559.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_559 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_559.
ssl_read x.
try rename vx into vx2.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_561 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_561.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_561 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_561.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_560 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_560.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_560 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_560.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_559 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_559.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_559 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_559.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_555x into h_sll_nxtx2len1xlo1xhi1x_555x.
try rename H_sll_nxtxlen1xlo1xhi1x_555x into H_sll_nxtx2len1xlo1xhi1x_555x.
try rename h_sll_x1n1lo1hi1_5591 into h_sll_nxtx2len1xlo1xhi1x_555x.
try rename H_sll_x1n1lo1hi1_5591 into H_sll_nxtx2len1xlo1xhi1x_555x.
ssl_call_pre (r :-> null \+ h_sll_nxtx2len1xlo1xhi1x_555x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx2len1xlo1xhi1x_555x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5601 h_srtl_y1len1xlo1xhi1x_5611.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx2len1xlo1xhi1x_5601 H_srtl_y1len1xlo1xhi1x_5611].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xlo1xhi1x_5611 into h_srtl_y12len1xlo1xhi1x_5611.
try rename H_srtl_y1len1xlo1xhi1x_5611 into H_srtl_y12len1xlo1xhi1x_5611.
try rename h_srtl_x2n2lo2hi2_557 into h_srtl_y12len1xlo1xhi1x_5611.
try rename H_srtl_x2n2lo2hi2_557 into H_srtl_y12len1xlo1xhi1x_5611.
ssl_write r.
ssl_call_pre (r :-> vx2 \+ h_srtl_y12len1xlo1xhi1x_5611).
ssl_call (vx2, len1x, lo1x, hi1x).
exists (h_srtl_y12len1xlo1xhi1x_5611);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_558.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_558.
store_valid.
try rename h_srtl_y2n11lo11hi11_558 into h_srtl_y2n11lo11hi1xvx2vx2hi1x_558.
try rename H_srtl_y2n11lo11hi11_558 into H_srtl_y2n11lo11hi1xvx2vx2hi1x_558.
try rename h_srtl_y2n11lo11hi1xvx2vx2hi1x_558 into h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename H_srtl_y2n11lo11hi1xvx2vx2hi1x_558 into H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_558 into h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_558 into H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
ssl_read r.
try rename y2 into y22.
try rename h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_561 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_561 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558.
try rename h_sll_nxtx1len1x1lo12xhi12x_555x1 into h_sll_nxtx2len1xlo1xhi1x_5601.
try rename H_sll_nxtx1len1x1lo12xhi12x_555x1 into H_sll_nxtx2len1xlo1xhi1x_5601.
ssl_emp;
exists (y22);
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x_5601);
exists (h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_558);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x_5601);
sslauto.
shelve.
ssl_frame_unfold.
Unshelve.
ssl_frame_unfold.
Qed.