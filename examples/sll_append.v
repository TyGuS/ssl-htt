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
  exists h_sll_nxts1_537,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_537 /\ sll nxt s1 h_sll_nxts1_537.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_538 h_sll_x2s2_539,
      h = r :-> x2 \+ h_sll_x1s1_538 \+ h_sll_x2s2_539 /\ sll x1 s1 h_sll_x1s1_538 /\ sll x2 s2 h_sll_x2s2_539,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_540,
      @perm_eq nat_eqType (s) (s1 ++ s2) /\ h = r :-> y \+ h_sll_ys_540 /\ sll y s h_sll_ys_540
    ]).
Program Definition sll_append : sll_append_type :=
  Fix (fun (sll_append : sll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      if x1 == null
      then
        ret tt
      else
        nxtx12 <-- @read ptr (x1 .+ 1);
        sll_append (nxtx12, r);;
        y12 <-- @read ptr r;
        (x1 .+ 1) ::= y12;;
        r ::= x1;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x1 r]; ssl_program_simpl.
Next Obligation.
Hypothesis sll_perm_eq_trans25: forall x h s_1 s_2, perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
Hint Resolve sll_perm_eq_trans25: ssl_pred.
ssl_ghostelim_pre.
move=>[[s1 x22] s2].
ex_elim h_sll_x1s1_538 h_sll_x22s2_539.
move=>[sigma_self].
subst.
move=>[H_sll_x1s1_538 H_sll_x22s2_539].
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_x1s1_538.
move=>[phi_sll_x1s1_5380].
move=>[sigma_sll_x1s1_538].
subst.
ssl_emp;
exists (nil ++ s2), (x22);
exists (h_sll_x22s2_539);
sslauto.
ssl_open_post H_sll_x1s1_538.
ex_elim vx12 s1x1 nxtx12.
ex_elim h_sll_nxtx12s1x1_537x1.
move=>[phi_sll_x1s1_5380].
move=>[sigma_sll_x1s1_538].
subst.
move=>H_sll_nxtx12s1x1_537x1.
ssl_read (x1 .+ 1).
ssl_call_pre (r :-> x22 \+ h_sll_nxtx12s1x1_537x1 \+ h_sll_x22s2_539).
ssl_call (s1x1, x22, s2).
exists (h_sll_nxtx12s1x1_537x1);
exists (h_sll_x22s2_539);
sslauto.
move=>h_call1.
ex_elim s3 y12.
ex_elim h_sll_y12s1x1s2_5401.
move=>[phi_call10].
move=>[sigma_call1].
subst.
move=>H_sll_y12s3_5401.
store_valid.
ssl_read r.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
Hypothesis pure26 : forall vx12 s1x1 s2, @perm_eq nat_eqType ([:: vx12] ++ s1x1 ++ s2) ([:: vx12] ++ s1x1 ++ s2).
Hint Resolve pure26: ssl_pure.
ssl_emp;
exists ([:: vx12] ++ s1x1 ++ s2), (x1);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ h_sll_y12s1x1s2_5401);
sslauto.
unfold_constructor 2;
exists (vx12), (s1x1 ++ s2), (y12);
exists (h_sll_y12s1x1s2_5401);
sslauto.
Qed.
