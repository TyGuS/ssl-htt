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
  Fix (fun (min2 : min2_type) vprogs =>
    let: (r, x, y) := vprogs in
    Do (
      if x <= y
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
rewrite->sigma_self in *.
ssl_ghostelim_post.
ssl_abduce_branch.
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
