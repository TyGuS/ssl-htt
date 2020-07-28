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
        let: (b, c, q, a) := vghosts in
          h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
      [vfun (_: unit) h =>
        let: (x, z, y, t) := vprogs in
        let: (b, c, q, a) := vghosts in
          h = x :-> c \+ z :-> b \+ t :-> q \+ y :-> 41
      ]).
Program Definition swap1 : swap1_type :=
  fun vprogs =>
  let: (x, z, y, t) := vprogs in
    Do (
  c2 <-- @read ptr y;
  x ::= c2;;
  y ::= 41;;
  ret tt    ).
Obligation Tactic := move=>[[[x z] y] t]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[a c] b] q].
move=>[sigma_root].
rewrite->sigma_root in *.
ssl_ghostelim_post.
ssl_read.
ssl_write.
ssl_write_post x.
ssl_write.
ssl_write_post y.
ssl_emp;
ssl_emp_post.

Qed.
