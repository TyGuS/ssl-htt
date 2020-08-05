From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition swap1_type :=
  forall (vprogs : ptr * ptr * ptr * ptr),
  {(vghosts : ptr * ptr * ptr * ptr)},
  STsep (
    fun h =>
      let: (x, z, y, t) := vprogs in
      let: (q, a, b, c) := vghosts in
      h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
    [vfun (_: unit) h =>
      let: (x, z, y, t) := vprogs in
      let: (q, a, b, c) := vghosts in
      h = x :-> c \+ z :-> b \+ t :-> q \+ y :-> 41
    ]).
Program Definition swap1 : swap1_type :=
  Fix (fun (swap1 : swap1_type) vprogs =>
    let: (x, z, y, t) := vprogs in
    Do (
      c2 <-- @read ptr y;
      x ::= c2;;
      y ::= 41;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[[x z] y] t]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[q2 a2] b2] c2].
move=>[sigma_self].
rewrite->sigma_self in *.
ssl_ghostelim_post.
ssl_read.
ssl_write.
ssl_write_post x.
ssl_write.
ssl_write_post y.
ssl_emp;
ssl_emp_post.

Qed.
