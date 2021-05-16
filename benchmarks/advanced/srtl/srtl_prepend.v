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

Lemma pure83 (n : nat) : (0) <= (n) -> ((n) + (1)) = ((1) + (n)). intros; hammer. Qed.
Hint Resolve pure83: ssl_pure.
Lemma pure84 (k : nat) (lo : nat) : (k) <= (7) -> (k) <= (lo) -> (0) <= (k) -> (k) = ((if (k) <= (lo) then k else lo)). intros; hammer. Qed.
Hint Resolve pure84: ssl_pure.

Definition srtl_prepend_type :=
  forall (vprogs : ptr * nat * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_srtl_xnlohi_553,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ (k) <= (lo) /\ h = r :-> a \+ h_srtl_xnlohi_553 /\ srtl x n lo hi h_srtl_xnlohi_553,
    [vfun (_: unit) h =>
      let: (x, k, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists n1 y hi1,
      exists h_srtl_yn1khi1_554,
      (n1) == ((n) + (1)) /\ h = r :-> y \+ h_srtl_yn1khi1_554 /\ srtl y n1 k hi1 h_srtl_yn1khi1_554
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
ex_elim h_srtl_xnlohi_553.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_553.
ssl_ghostelim_post.
try rename h_srtl_yn1khi1_554 into h_srtl_ynkhi1_554.
try rename H_srtl_yn1khi1_554 into H_srtl_ynkhi1_554.
ssl_read r.
try rename a into a2.
try rename h_srtl_ynkhi1_554 into h_srtl_ynkhi11yvyvyhi11y_554.
try rename H_srtl_ynkhi1_554 into H_srtl_ynkhi11yvyvyhi11y_554.
try rename h_srtl_nxtylen1ylo1yhi11y_552y into h_srtl_xnlohi_553.
try rename H_srtl_nxtylen1ylo1yhi11y_552y into H_srtl_xnlohi_553.
try rename h_srtl_ynkhi11yvyvyhi11y_554 into h_srtl_ynkhivyvyhi_554.
try rename H_srtl_ynkhi11yvyvyhi11y_554 into H_srtl_ynkhivyvyhi_554.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_ynkhivyvyhi_554 into h_srtl_y2nkhivyvyhi_554.
try rename H_srtl_ynkhivyvyhi_554 into H_srtl_y2nkhivyvyhi_554.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
try rename h_srtl_y2nkhivyvyhi_554 into h_srtl_y2nkhikkhi_554.
try rename H_srtl_y2nkhivyvyhi_554 into H_srtl_y2nkhikkhi_554.
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ((n) + (1)), (y2), ((if (hi) <= (k) then k else hi));
exists (y2 :-> k \+ y2 .+ 1 :-> x \+ h_srtl_xnlohi_553);
sslauto.
ssl_close 2;
exists (n), (k), (hi), (lo), (x), (h_srtl_xnlohi_553);
sslauto.
ssl_frame_unfold.
Qed.