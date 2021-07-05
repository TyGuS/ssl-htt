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

Definition swap2_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : ptr * ptr)},
  STsep (
    fun h =>
      let: (x, y) := vprogs in
      let: (a, b) := vghosts in
      h = x :-> (a) \+ y :-> (b),
    [vfun (_: unit) h =>
      let: (x, y) := vprogs in
      let: (a, b) := vghosts in
      h = x :-> (b) \+ y :-> (a)
    ]).

Program Definition swap2 : swap2_type :=
  Fix (fun (swap2 : swap2_type) vprogs =>
    let: (x, y) := vprogs in
    Do (
      a1 <-- @read ptr x;
      b1 <-- @read ptr y;
      y ::= a1;;
      x ::= b1;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x y]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[a b].
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
ssl_read x.
try rename a into a1.
ssl_read y.
try rename b into b1.
ssl_write y.
ssl_write_post y.
ssl_write x.
ssl_write_post x.
ssl_emp;
sslauto.
Qed.