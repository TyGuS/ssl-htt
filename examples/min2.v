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
subst.
ssl_ghostelim_post.
ssl_abduce_branch.
Hypothesis pure1 : forall x y, x <= y -> x <= x.
Hint Resolve pure1: ssl_pure.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x);
sslauto.
Hypothesis pure2 : forall y x, ~~ (x <= y) -> y <= x.
Hint Resolve pure2: ssl_pure.
Hypothesis pure3 : forall y x, ~~ (x <= y) -> y <= y.
Hint Resolve pure3: ssl_pure.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (y);
sslauto.
Qed.
