From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_543,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_543 /\ sll nxt s1 h_sll_nxts1_543.

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
      @sub_mem nat_eqType (mem (s1)) (mem ([:: v])) /\ h = h_sll_xs1_545 /\ sll x s1 h_sll_xs1_545
    ]).
Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) vprogs =>
    let: (x, v) := vprogs in
    Do (
      if x == null
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
Hypothesis sll_perm_eq_trans29: forall x h s_1 s_2, perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
Hint Resolve sll_perm_eq_trans29: ssl_pred.
ssl_ghostelim_pre.
move=>s.
ex_elim h_sll_xs_544.
move=>[sigma_self].
subst.
move=>H_sll_xs_544.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_xs_544.
move=>[phi_sll_xs_5440].
move=>[sigma_sll_xs_544].
subst.
Hypothesis pure30 : forall v, @sub_mem nat_eqType (mem (nil)) (mem ([:: v])).
Hint Resolve pure30: ssl_pure.
ssl_emp;
exists (nil);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_sll_xs_544.
ex_elim vx2 s1x nxtx2.
ex_elim h_sll_nxtx2s1x_543x.
move=>[phi_sll_xs_5440].
move=>[sigma_sll_xs_544].
subst.
move=>H_sll_nxtx2s1x_543x.
ssl_read (x .+ 1).
ssl_call_pre (h_sll_nxtx2s1x_543x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_543x);
sslauto.
move=>h_call1.
ex_elim s11.
ex_elim h_sll_nxtx2s11_5451.
move=>[phi_call10].
move=>[sigma_call1].
subst.
move=>H_sll_nxtx2s11_5451.
store_valid.
Hypothesis pure31 : forall v s11, @sub_mem nat_eqType (mem (s11)) (mem ([:: v])) -> @sub_mem nat_eqType (mem ([:: v] ++ s11)) (mem ([:: v])).
Hint Resolve pure31: ssl_pure.
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
