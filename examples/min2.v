From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Lemma pure1 x y : x <= y -> x <= x. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 y x : (x <= y) = false -> y <= x. Admitted.
Hint Resolve pure2: ssl_pure.
Lemma pure3 y x : (x <= y) = false -> y <= y. Admitted.
Hint Resolve pure3: ssl_pure.

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
subst h_self.
ssl_ghostelim_post.
ssl_abduce_branch (x <= y).
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
