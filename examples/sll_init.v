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
  perm_eq (s) (nil) /\ h = empty
| sll2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_543,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_543 /\ sll nxt s1 h_sll_nxts1_543.

Definition sll_init_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_544,
      h = h_sll_xs_544 /\ sll x s h_sll_xs_544,
    [vfun (_: unit) h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists s1,
      exists h_sll_xs1_545,
      {subset s1 <= [:: v]} /\ h = h_sll_xs1_545 /\ sll x s1 h_sll_xs1_545
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
ex_elim h_sll_xs_544.
move=>[sigma_self].
subst.
move=>H_sll_xs_544.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_xs_544.
move=>[phi_sll_xs_544].
move=>[sigma_sll_xs_544].
subst.
ssl_emp;
exists (nil);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_sll_xs_544.
ex_elim vx2 s1x nxtx2.
ex_elim h_sll_nxtx2s1x_543x.
move=>[phi_sll_xs_544].
move=>[sigma_sll_xs_544].
subst.
move=>H_sll_nxtx2s1x_543x.
ssl_read (x .+ 1).
ssl_call_pre (h_sll_nxtx2s1x_543x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_543x);
sslauto.
move=>h_call12.
ex_elim s11.
ex_elim h_sll_nxtx2s11_5451.
move=>[phi_call12].
move=>[sigma_call12].
subst.
move=>H_sll_nxtx2s11_5451.
store_valid.
ssl_write x.
ssl_write_post x.
ssl_emp;
exists ([:: v] ++ s11);
exists (x :-> v \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2s11_5451);
sslauto.
unfold_constructor 2;
exists (v), (s11), (nxtx2);
exists (h_sll_nxtx2s11_5451);
sslauto.

Qed.
