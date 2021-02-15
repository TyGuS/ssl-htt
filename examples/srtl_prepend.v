From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| sll_1 of x == null of
  hi == 0 /\ len == 0 /\ lo == 7 /\ h = empty
| sll_2 of (x == null) = false of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_sll_nxtlen1lo1hi1_513,
  0 <= len1 /\ 0 <= v /\ hi == (if hi1 <= v then v else hi1) /\ len == 1 + len1 /\ lo == (if v <= lo1 then v else lo1) /\ v <= 7 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_513 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_513.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of x == null of
  hi == 0 /\ len == 0 /\ lo == 7 /\ h = empty
| srtl_2 of (x == null) = false of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_514,
  0 <= len1 /\ 0 <= v /\ hi == (if hi1 <= v then v else hi1) /\ len == 1 + len1 /\ lo == (if v <= lo1 then v else lo1) /\ v <= 7 /\ v <= lo1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_514 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_514.

Lemma pure1 n : 0 <= n -> n + 1 == 1 + n. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 k lo : k <= 7 -> 0 <= k -> k <= lo -> k == (if k <= lo then k else lo). Admitted.
Hint Resolve pure2: ssl_pure.

Definition srtl_prepend_type :=
  forall (vprogs : ptr * nat * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_srtl_xnlohi_515,
      0 <= k /\ 0 <= n /\ k <= 7 /\ k <= lo /\ h = r :-> a \+ h_srtl_xnlohi_515 /\ srtl x n lo hi h_srtl_xnlohi_515,
    [vfun (_: unit) h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists n1 y hi1,
      exists h_srtl_yn1khi1_516,
      n1 == n + 1 /\ h = r :-> y \+ h_srtl_yn1khi1_516 /\ srtl y n1 k hi1 h_srtl_yn1khi1_516
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
ex_elim h_srtl_xnlohi_515.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_515.
ssl_ghostelim_post.
try rename h_srtl_yn1khi1_516 into h_srtl_ynkhi1_516.
try rename H_srtl_yn1khi1_516 into H_srtl_ynkhi1_516.
ssl_read r.
try rename a into a2.
try rename h_srtl_ynkhi1_516 into h_srtl_ynkhi11yvyvyhi11y_516.
try rename H_srtl_ynkhi1_516 into H_srtl_ynkhi11yvyvyhi11y_516.
try rename h_srtl_nxtylen1ylo1yhi11y_514y into h_srtl_nxtylen1ylo1yhi11y_515.
try rename H_srtl_nxtylen1ylo1yhi11y_514y into H_srtl_nxtylen1ylo1yhi11y_515.
try rename h_srtl_nxtylen1ylo1yhi11y_515 into h_srtl_nxtylen1ylo1yhi_515.
try rename H_srtl_nxtylen1ylo1yhi11y_515 into H_srtl_nxtylen1ylo1yhi_515.
try rename h_srtl_ynkhi11yvyvyhi11y_516 into h_srtl_ynkhivyvyhi_516.
try rename H_srtl_ynkhi11yvyvyhi11y_516 into H_srtl_ynkhivyvyhi_516.
try rename h_srtl_nxtylen1ylo1yhi_515 into h_srtl_nxtynlo1yhi_515.
try rename H_srtl_nxtylen1ylo1yhi_515 into H_srtl_nxtynlo1yhi_515.
try rename h_srtl_nxtynlo1yhi_515 into h_srtl_nxtynlohi_515.
try rename H_srtl_nxtynlo1yhi_515 into H_srtl_nxtynlohi_515.
try rename h_srtl_nxtynlohi_515 into h_srtl_xnlohi_515.
try rename H_srtl_nxtynlohi_515 into H_srtl_xnlohi_515.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_ynkhivyvyhi_516 into h_srtl_y2nkhivyvyhi_516.
try rename H_srtl_ynkhivyvyhi_516 into H_srtl_y2nkhivyvyhi_516.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
try rename h_srtl_y2nkhivyvyhi_516 into h_srtl_y2nkhikkhi_516.
try rename H_srtl_y2nkhivyvyhi_516 into H_srtl_y2nkhikkhi_516.
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists (n + 1), (y2), ((if hi <= k then k else hi));
exists (y2 :-> k \+ y2 .+ 1 :-> x \+ h_srtl_xnlohi_515);
sslauto.
unfold_constructor 2;
exists (n), (k), (hi), (lo), (x), (h_srtl_xnlohi_515);
sslauto.
Qed.
