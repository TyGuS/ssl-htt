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

Lemma pure28 (x : nat) : ([:: x]) = ([:: x]). intros; hammer. Qed.
Hint Resolve pure28: ssl_pure.

Definition sll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      h = p :-> a,
    [vfun (_: unit) h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      exists elems y,
      exists h_sll_yelems_532,
      (elems) == ([:: x]) /\ h = p :-> y \+ h_sll_yelems_532 /\ sll y elems h_sll_yelems_532
    ]).

Program Definition sll_singleton : sll_singleton_type :=
  Fix (fun (sll_singleton : sll_singleton_type) vprogs =>
    let: (x, p) := vprogs in
    Do (
      a2 <-- @read ptr p;
      y2 <-- allocb null 2;
      p ::= y2;;
      (y2 .+ 1) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x p]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_sll_yelems_532 into h_sll_yx_532.
try rename H_sll_yelems_532 into H_sll_yx_532.
ssl_read p.
try rename a into a2.
try rename h_sll_nxtys1y_531y into h_sll_s1y_531y.
try rename H_sll_nxtys1y_531y into H_sll_s1y_531y.
try rename h_sll_s1y_531y into h_sll__531y.
try rename H_sll_s1y_531y into H_sll__531y.
ssl_alloc y2.
try rename y into y2.
try rename h_sll_yx_532 into h_sll_y2x_532.
try rename H_sll_yx_532 into H_sll_y2x_532.
ssl_write p.
ssl_write_post p.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null);
sslauto.
ssl_close 2;
exists (x), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.