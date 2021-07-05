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

Definition swap4_type :=
  forall (vprogs : ptr * ptr * ptr * ptr),
  {(vghosts : ptr * ptr * ptr * ptr)},
  STsep (
    fun h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> (a) \+ y :-> (c) \+ z :-> (b) \+ t :-> (q),
    [vfun (_: unit) h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> (q) \+ z :-> (c) \+ t :-> (a) \+ y :-> (b)
    ]).

Program Definition swap4 : swap4_type :=
  Fix (fun (swap4 : swap4_type) vprogs =>
    let: (x, z, y, t) := vprogs in
    Do (
      a1 <-- @read ptr x;
      c1 <-- @read ptr y;
      b1 <-- @read ptr z;
      q1 <-- @read ptr t;
      t ::= a1;;
      z ::= c1;;
      y ::= b1;;
      x ::= q1;;
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
try rename a into a1.
ssl_read y.
try rename c into c1.
ssl_read z.
try rename b into b1.
ssl_read t.
try rename q into q1.
ssl_write t.
ssl_write_post t.
ssl_write z.
ssl_write_post z.
ssl_write y.
ssl_write_post y.
ssl_write x.
ssl_write_post x.
ssl_emp;
sslauto.
Qed.