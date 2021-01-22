From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_549,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_549 /\ sll nxt s1 h_sll_nxts1_549.

Lemma sll_perm_eq_trans36 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans36: ssl_pred.
Lemma pure37 v : @sub_mem nat_eqType (mem (nil)) (mem ([:: v])). Admitted.
Hint Resolve pure37: ssl_pure.
Lemma pure38 v s11 : @sub_mem nat_eqType (mem (s11)) (mem ([:: v])) -> @sub_mem nat_eqType (mem ([:: v] ++ s11)) (mem ([:: v])). Admitted.
Hint Resolve pure38: ssl_pure.

Definition sll_init_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_550,
      h = h_sll_xs_550 /\ sll x s h_sll_xs_550,
    [vfun (_: unit) h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists s1,
      exists h_sll_xs1_551,
      @sub_mem nat_eqType (mem (s1)) (mem ([:: v])) /\ h = h_sll_xs1_551 /\ sll x s1 h_sll_xs1_551
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
ssl_ghostelim_pre.
move=>s.
ex_elim h_sll_xs_550.
move=>[sigma_self].
subst.
move=>H_sll_xs_550.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_xs_550.
move=>[phi_sll_xs_5500].
move=>[sigma_sll_xs_550].
subst.
ssl_emp;
exists (nil);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_sll_xs_550.
ex_elim vx2 s1x nxtx2.
ex_elim h_sll_nxtx2s1x_549x.
move=>[phi_sll_xs_5500].
move=>[sigma_sll_xs_550].
subst.
move=>H_sll_nxtx2s1x_549x.
ssl_read (x .+ 1).
ssl_call_pre (h_sll_nxtx2s1x_549x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_549x);
sslauto.
move=>h_call1.
ex_elim s11.
ex_elim h_sll_nxtx2s11_5511.
move=>[phi_call10].
move=>[sigma_call1].
subst.
move=>H_sll_nxtx2s11_5511.
store_valid.
ssl_write x.
ssl_write_post x.
ssl_emp;
exists ([:: v] ++ s11);
exists (x :-> v \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2s11_5511);
sslauto.
unfold_constructor 2;
exists (v), (s11), (nxtx2);
exists (h_sll_nxtx2s11_5511);
sslauto.
Qed.
