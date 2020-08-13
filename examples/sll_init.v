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
  exists h_sll526,
  s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll526 /\ sll nxt s1 h_sll526.

Definition sll_init_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists h_sll527,
      h = h_sll527 /\ sll x s h_sll527,
    [vfun (_: unit) h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists s1,
      exists h_sll528,
      {subset s1 <= [:: v]} /\ h = h_sll528 /\ sll x s1 h_sll528
    ]).
Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) vprogs =>
    let: (x, v) := vprogs in
    Do (
      if x == 0
      then
        ret tt
      else
        nxtx2 <-- @read ptr (x .+ 1);
        sll_init (nxtx2, v);;
        x ::= v;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x v]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
move=>[h_sll527].
move=>[sigma_self].
rewrite->sigma_self in *.
move=>H_sll527.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll527.
move=>[phi_sll527].
move=>[sigma_sll527].
rewrite->sigma_sll527 in *.
ssl_emp;
exists (nil);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_sll527.
move=>[vx2] [s1x] [nxtx2].
move=>[h_sll526x].
move=>[phi_sll527].
move=>[sigma_sll527].
rewrite->sigma_sll527 in *.
move=>H_sll526x.
ssl_read.
ssl_call_pre (h_sll526x).
ssl_call (s1x).
exists (h_sll526x);
sslauto.
move=>h_call6.
move=>[s11].
move=>[h_sll5281].
move=>[phi_call6].
move=>[sigma_call6].
rewrite->sigma_call6 in *.
move=>H_sll5281.
store_valid.
ssl_write.
ssl_write_post x.
ssl_emp;
exists ([:: v] ++ s11);
exists (x :-> v \+ x .+ 1 :-> nxtx2 \+ h_sll5281);
sslauto.
unfold_constructor 2;
exists (v), (s11), (nxtx2);
exists (h_sll5281);
sslauto.

Qed.
