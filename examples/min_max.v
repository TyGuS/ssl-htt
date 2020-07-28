From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition min2_type :=
  forall (vprogs : ptr * nat * nat),
    STsep (
      fun h =>
        let: (r, x, y) := vprogs in
          h = r :-> null,
      [vfun (_: unit) h =>
        let: (r, x, y) := vprogs in
        exists m,
          m <= x /\ m <= y /\ h = r :-> m
      ]).
Program Definition min2 : min2_type :=
  fun vprogs =>
  let: (r, x, y) := vprogs in
    Do (
  if x <= y
  then
    r ::= x;;
    ret tt
  else
    r ::= y;;
    ret tt
    ).
Obligation Tactic := move=>[[r x] y]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[sigma_root].
rewrite->sigma_root in *.
ssl_ghostelim_post.
case: ifP=>H_cond.
ssl_write.
ssl_write_post r.
ssl_emp;
exists (x);
ssl_emp_post.
ssl_write.
ssl_write_post r.
ssl_emp;
exists (y);
ssl_emp_post.

Qed.
