From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_570,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_570 /\ sll nxt s1 h_sll_nxts1_570.

Lemma sll_perm_eq_trans46 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans46: ssl_pred.
Lemma pure47 v : @sub_mem nat_eqType (mem (nil)) (mem ([:: v])). Admitted.
Hint Resolve pure47: ssl_pure.
Lemma pure48 v s11 : @sub_mem nat_eqType (mem (s11)) (mem ([:: v])) -> @sub_mem nat_eqType (mem (([:: v]) ++ (s11))) (mem ([:: v])). Admitted.
Hint Resolve pure48: ssl_pure.

Definition sll_init_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_571,
      h = h_sll_xs_571 /\ sll x s h_sll_xs_571,
    [vfun (_: unit) h =>
      let: (x, v) := vprogs in
      let: (s) := vghosts in
      exists s1,
      exists h_sll_xs1_572,
      @sub_mem nat_eqType (mem (s1)) (mem ([:: v])) /\ h = h_sll_xs1_572 /\ sll x s1 h_sll_xs1_572
    ]).

Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) vprogs =>
    let: (x, v) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_init (nxtx2, v);;
        x ::= v;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x v]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_sll_xs_571.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_571.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xs_571.
move=>[phi_sll_xs_5710].
move=>[sigma_sll_xs_571].
subst h_sll_xs_571.
try rename h_sll_xs_571 into h_sll_x_571.
try rename H_sll_xs_571 into H_sll_x_571.
try rename h_sll_xs1_572 into h_sll_x_572.
try rename H_sll_xs1_572 into H_sll_x_572.
ssl_emp;
exists (nil);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx s1x nxtx.
ex_elim h_sll_nxtxs1x_570x.
move=>[phi_sll_xs_5710].
move=>[sigma_sll_xs_571].
subst h_sll_xs_571.
move=>H_sll_nxtxs1x_570x.
try rename h_sll_xs_571 into h_sll_xvxs1x_571.
try rename H_sll_xs_571 into H_sll_xvxs1x_571.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xvxs1x_571 into h_sll_xvx2s1x_571.
try rename H_sll_xvxs1x_571 into H_sll_xvx2s1x_571.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxs1x_570x into h_sll_nxtx2s1x_570x.
try rename H_sll_nxtxs1x_570x into H_sll_nxtx2s1x_570x.
try rename h_sll_x1s2_5711 into h_sll_nxtx2s1x_570x.
try rename H_sll_x1s2_5711 into H_sll_nxtx2s1x_570x.
ssl_call_pre (h_sll_nxtx2s1x_570x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_570x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim s11.
ex_elim h_sll_nxtx2s11_5721.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2s11_5721.
store_valid.
try rename h_sll_xs1_572 into h_sll_xv2xs12x_572.
try rename H_sll_xs1_572 into H_sll_xv2xs12x_572.
try rename h_sll_nxtx1s12x_570x1 into h_sll_nxtx2s11_5721.
try rename H_sll_nxtx1s12x_570x1 into H_sll_nxtx2s11_5721.
try rename h_sll_xv2xs12x_572 into h_sll_xv2xs11_572.
try rename H_sll_xv2xs12x_572 into H_sll_xv2xs11_572.
try rename h_sll_xv2xs11_572 into h_sll_xvs11_572.
try rename H_sll_xv2xs11_572 into H_sll_xvs11_572.
ssl_write x.
ssl_write_post x.
ssl_emp;
exists (([:: v]) ++ (s11));
exists (x :-> v \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2s11_5721);
sslauto.
ssl_close 2;
exists (v), (s11), (nxtx2), (h_sll_nxtx2s11_5721);
sslauto.
ssl_frame_unfold.
Qed.