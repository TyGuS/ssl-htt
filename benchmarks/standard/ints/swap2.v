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

Definition swap2_type :=
  forall (vprogs : ptr * ptr * ptr * ptr),
  {(vghosts : ptr * ptr * ptr * ptr)},
  STsep (
    fun h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
    [vfun (_: unit) h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> q \+ z :-> c \+ t :-> a \+ y :-> b
    ]).

Program Definition swap2 : swap2_type :=
  Fix (fun (swap2 : swap2_type) vprogs =>
    let: (x, z, y, t) := vprogs in
    Do (
      a2 <-- @read ptr x;
      c2 <-- @read ptr y;
      b2 <-- @read ptr z;
      q2 <-- @read ptr t;
      x ::= q2;;
      y ::= b2;;
      z ::= c2;;
      t ::= a2;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[[x z] y] t]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[a c] b] q].
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
ssl_read x.
try rename a into a2.
ssl_read y.
try rename c into c2.
ssl_read z.
try rename b into b2.
ssl_read t.
try rename q into q2.
ssl_write x.
ssl_write_post x.
ssl_write y.
ssl_write_post y.
ssl_write z.
ssl_write_post z.
ssl_write t.
ssl_write_post t.
ssl_emp;
sslauto.
Qed.