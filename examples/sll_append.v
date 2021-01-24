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
  exists h_sll_nxts1_543,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_543 /\ sll nxt s1 h_sll_nxts1_543.

Lemma sll_perm_eq_trans32 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans32: ssl_pred.
Lemma pure33 vx12 s1x1 s2 : @perm_eq nat_eqType ([:: vx12] ++ s1x1 ++ s2) ([:: vx12] ++ s1x1 ++ s2). Admitted.
Hint Resolve pure33: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_544 h_sll_x2s2_545,
      h = r :-> x2 \+ h_sll_x1s1_544 \+ h_sll_x2s2_545 /\ sll x1 s1 h_sll_x1s1_544 /\ sll x2 s2 h_sll_x2s2_545,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_546,
      @perm_eq nat_eqType (s) (s1 ++ s2) /\ h = r :-> y \+ h_sll_ys_546 /\ sll y s h_sll_ys_546
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
ssl_ghostelim_pre.
move=>[[s1 x22] s2].
ex_elim h_sll_x1s1_544 h_sll_x22s2_545.
move=>[sigma_self].
subst h_self.
move=>[H_sll_x1s1_544 H_sll_x22s2_545].
ssl_ghostelim_post.
ssl_open (x1 == null);
ssl_open_post H_sll_x1s1_544.
move=>[phi_sll_x1s1_5440].
move=>[sigma_sll_x1s1_544].
subst h_sll_x1s1_544.
ssl_emp;
exists (nil ++ s2), (x22);
exists (h_sll_x22s2_545);
sslauto.
ex_elim vx12 s1x1 nxtx12.
ex_elim h_sll_nxtx12s1x1_543x1.
move=>[phi_sll_x1s1_5440].
move=>[sigma_sll_x1s1_544].
subst h_sll_x1s1_544.
move=>H_sll_nxtx12s1x1_543x1.
ssl_read (x1 .+ 1).
ssl_call_pre (r :-> x22 \+ h_sll_nxtx12s1x1_543x1 \+ h_sll_x22s2_545).
ssl_call (s1x1, x22, s2).
exists (h_sll_nxtx12s1x1_543x1);
exists (h_sll_x22s2_545);
sslauto.
move=>h_call1.
ex_elim s3 y12.
ex_elim h_sll_y12s1x1s2_5461.
move=>[phi_call10].
move=>[sigma_call1].
subst h_call1.
move=>H_sll_y12s3_5461.
store_valid.
ssl_read r.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ([:: vx12] ++ s1x1 ++ s2), (x1);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ h_sll_y12s1x1s2_5461);
sslauto;
solve [
unfold_constructor 2;
exists (vx12), (s1x1 ++ s2), (y12);
exists (h_sll_y12s1x1s2_5461);
sslauto ].
Qed.
