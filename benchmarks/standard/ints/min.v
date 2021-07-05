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
Set Hammer ATPLimit 60.
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

Lemma pure1 (x : nat) (y : nat) : (x) <= (y) -> (x) <= (x). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (y : nat) (x : nat) : ~~ ((x) <= (y)) -> (y) <= (x). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (y : nat) (x : nat) : ~~ ((x) <= (y)) -> (y) <= (y). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.

Definition min_type :=
  forall (vprogs : ptr * nat * nat),
  STsep (
    fun h =>
      let: (r, x, y) := vprogs in
      h = r :-> (null),
    [vfun (_: unit) h =>
      let: (r, x, y) := vprogs in
      exists m,
      (m) <= (x) /\ (m) <= (y) /\ h = r :-> (m)
    ]).

Program Definition min : min_type :=
  Fix (fun (min : min_type) vprogs =>
    let: (r, x, y) := vprogs in
    Do (
      if (x) <= (y)
      then
        r ::= x;;
        ret tt
      else
        r ::= y;;
        ret tt
    )).
Obligation Tactic := intro; move=>[[r x] y]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
ssl_branch ((x) <= (y)).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x);
sslauto.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (y);
sslauto.
Qed.