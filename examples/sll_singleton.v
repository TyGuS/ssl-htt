From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == 0 of
  s = nil /\ h = empty
| sll2 of ~~ (x == 0) of
  exists v s1 nxt,
  exists h_sll524,
  s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll524 /\ sll nxt s1 h_sll524.

Definition sll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      h = p :-> a,
    [vfun (_: unit) h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      exists (elems : seq nat) y,
      exists h_sll525,
      elems = [:: x] /\ h = p :-> y \+ h_sll525 /\ sll y elems h_sll525
    ]).
Program Definition sll_singleton : sll_singleton_type :=
  Fix (fun (sll_singleton : sll_singleton_type) vprogs =>
    let: (x, p) := vprogs in
    Do (
      y2 <-- allocb null 2;
      p ::= y2;;
      (y2 .+ 1) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x p]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a2.
move=>[sigma_self].
rewrite->sigma_self in *.
ssl_ghostelim_post.
ssl_alloc y2.
ssl_write.
ssl_write_post p.
ssl_write.
ssl_write_post (y2 .+ 1).
ssl_write.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null);
ssl_emp_post.
unfold_constructor 2;
exists (x), (nil), (0);
exists (empty);
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.

Qed.
