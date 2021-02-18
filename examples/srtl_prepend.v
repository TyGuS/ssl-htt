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
  exists h_sll_nxtlen1lo1hi1_523,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_523 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_523.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_524,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_524 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_524.

Lemma pure24 n : (0) <= (n) -> ((n) + (1)) == ((1) + (n)). Admitted.
Hint Resolve pure24: ssl_pure.
Lemma pure25 k lo : (k) <= (7) -> (k) <= (lo) -> (0) <= (k) -> (k) == ((if (k) <= (lo) then k else lo)). Admitted.
Hint Resolve pure25: ssl_pure.

Definition srtl_prepend_type :=
  forall (vprogs : ptr * nat * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_srtl_xnlohi_525,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ (k) <= (lo) /\ h = r :-> a \+ h_srtl_xnlohi_525 /\ srtl x n lo hi h_srtl_xnlohi_525,
    [vfun (_: unit) h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists n1 y hi1,
      exists h_srtl_yn1khi1_526,
      (n1) == ((n) + (1)) /\ h = r :-> y \+ h_srtl_yn1khi1_526 /\ srtl y n1 k hi1 h_srtl_yn1khi1_526
    ]).

Program Definition srtl_prepend : srtl_prepend_type :=
  Fix (fun (srtl_prepend : srtl_prepend_type) vprogs =>
    let: (x, k, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      y2 <-- allocb null 2;
      r ::= y2;;
      (y2 .+ 1) ::= x;;
      y2 ::= k;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[x k] r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_srtl_xnlohi_525.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_525.
ssl_ghostelim_post.
try rename h_srtl_yn1khi1_526 into h_srtl_ynkhi1_526.
try rename H_srtl_yn1khi1_526 into H_srtl_ynkhi1_526.
ssl_read r.
try rename a into a2.
try rename h_srtl_ynkhi1_526 into h_srtl_ynkhi11yvyvyhi11y_526.
try rename H_srtl_ynkhi1_526 into H_srtl_ynkhi11yvyvyhi11y_526.
try rename h_srtl_nxtylen1ylo1yhi11y_524y into h_srtl_xnlohi_525.
try rename H_srtl_nxtylen1ylo1yhi11y_524y into H_srtl_xnlohi_525.
try rename h_srtl_ynkhi11yvyvyhi11y_526 into h_srtl_ynkhivyvyhi_526.
try rename H_srtl_ynkhi11yvyvyhi11y_526 into H_srtl_ynkhivyvyhi_526.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_ynkhivyvyhi_526 into h_srtl_y2nkhivyvyhi_526.
try rename H_srtl_ynkhivyvyhi_526 into H_srtl_y2nkhivyvyhi_526.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
try rename h_srtl_y2nkhivyvyhi_526 into h_srtl_y2nkhikkhi_526.
try rename H_srtl_y2nkhivyvyhi_526 into H_srtl_y2nkhikkhi_526.
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ((n) + (1)), (y2), ((if (hi) <= (k) then k else hi));
exists (y2 :-> k \+ y2 .+ 1 :-> x \+ h_srtl_xnlohi_525);
sslauto.
unfold_constructor 2;
exists (n), (k), (hi), (lo), (x), (h_srtl_xnlohi_525);
sslauto.
ssl_frame_unfold.
Qed.