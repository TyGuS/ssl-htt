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
  exists h_sll_nxts1_564,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_564 /\ sll nxt s1 h_sll_nxts1_564.

Lemma sll_perm_eq_trans42 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans42: ssl_pred.
Lemma pure43 vx12 s1x1 s2 : @perm_eq nat_eqType ((([:: vx12]) ++ (s1x1)) ++ (s2)) (([:: vx12]) ++ ((s1x1) ++ (s2))). Admitted.
Hint Resolve pure43: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_565 h_sll_x2s2_566,
      h = r :-> x2 \+ h_sll_x1s1_565 \+ h_sll_x2s2_566 /\ sll x1 s1 h_sll_x1s1_565 /\ sll x2 s2 h_sll_x2s2_566,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_567,
      @perm_eq nat_eqType (s) ((s1) ++ (s2)) /\ h = r :-> y \+ h_sll_ys_567 /\ sll y s h_sll_ys_567
    ]).

Program Definition sll_append : sll_append_type :=
  Fix (fun (sll_append : sll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x22 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx12 <-- @read nat x1;
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
move=>[[s1 x2] s2].
ex_elim h_sll_x1s1_565 h_sll_x2s2_566.
move=>[sigma_self].
subst h_self.
move=>[H_sll_x1s1_565 H_sll_x2s2_566].
ssl_ghostelim_post.
try rename h_sll_ys_567 into h_sll_ys1s2_567.
try rename H_sll_ys_567 into H_sll_ys1s2_567.
ssl_read r.
try rename x2 into x22.
try rename h_sll_x2s2_566 into h_sll_x22s2_566.
try rename H_sll_x2s2_566 into H_sll_x22s2_566.
ssl_open ((x1) == (null)) H_sll_x1s1_565.
move=>[phi_sll_x1s1_5650].
move=>[sigma_sll_x1s1_565].
subst h_sll_x1s1_565.
try rename h_sll_x1s1_565 into h_sll_x1_565.
try rename H_sll_x1s1_565 into H_sll_x1_565.
try rename h_sll_ys1s2_567 into h_sll_ys2_567.
try rename H_sll_ys1s2_567 into H_sll_ys2_567.
try rename h_sll_ys2_567 into h_sll_x22s2_566.
try rename H_sll_ys2_567 into H_sll_x22s2_566.
ssl_emp;
exists (s2), (x22);
exists (h_sll_x22s2_566);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 nxtx1.
ex_elim h_sll_nxtx1s1x1_564x1.
move=>[phi_sll_x1s1_5650].
move=>[sigma_sll_x1s1_565].
subst h_sll_x1s1_565.
move=>H_sll_nxtx1s1x1_564x1.
try rename h_sll_x1s1_565 into h_sll_x1vx1s1x1_565.
try rename H_sll_x1s1_565 into H_sll_x1vx1s1x1_565.
try rename h_sll_ys1s2_567 into h_sll_yvx1s1x1s2_567.
try rename H_sll_ys1s2_567 into H_sll_yvx1s1x1s2_567.
ssl_read x1.
try rename vx1 into vx12.
try rename h_sll_x1vx1s1x1_565 into h_sll_x1vx12s1x1_565.
try rename H_sll_x1vx1s1x1_565 into H_sll_x1vx12s1x1_565.
try rename h_sll_yvx1s1x1s2_567 into h_sll_yvx12s1x1s2_567.
try rename H_sll_yvx1s1x1s2_567 into H_sll_yvx12s1x1s2_567.
ssl_read (x1 .+ 1).
try rename nxtx1 into nxtx12.
try rename h_sll_nxtx1s1x1_564x1 into h_sll_nxtx12s1x1_564x1.
try rename H_sll_nxtx1s1x1_564x1 into H_sll_nxtx12s1x1_564x1.
try rename h_sll_x11s11_5651 into h_sll_nxtx12s1x1_564x1.
try rename H_sll_x11s11_5651 into H_sll_nxtx12s1x1_564x1.
try rename h_sll_x21s21_5661 into h_sll_x22s2_566.
try rename H_sll_x21s21_5661 into H_sll_x22s2_566.
ssl_call_pre (r :-> x22 \+ h_sll_nxtx12s1x1_564x1 \+ h_sll_x22s2_566).
ssl_call (s1x1, x22, s2).
exists (h_sll_nxtx12s1x1_564x1), (h_sll_x22s2_566);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1.
ex_elim h_sll_y1s3_5671.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s3_5671.
store_valid.
try rename h_sll_y1s3_5671 into h_sll_y1s1x1s2_5671.
try rename H_sll_y1s3_5671 into H_sll_y1s1x1s2_5671.
ssl_read r.
try rename y1 into y12.
try rename h_sll_y1s1x1s2_5671 into h_sll_y12s1x1s2_5671.
try rename H_sll_y1s1x1s2_5671 into H_sll_y12s1x1s2_5671.
try rename h_sll_nxtys12y_564y into h_sll_y12s1x1s2_5671.
try rename H_sll_nxtys12y_564y into H_sll_y12s1x1s2_5671.
try rename h_sll_yvx12s1x1s2_567 into h_sll_x1vx12s1x1s2_567.
try rename H_sll_yvx12s1x1s2_567 into H_sll_x1vx12s1x1s2_567.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ h_sll_y12s1x1s2_5671);
sslauto.
ssl_close 2;
exists (vx12), ((s1x1) ++ (s2)), (y12), (h_sll_y12s1x1s2_5671);
sslauto.
ssl_frame_unfold.
Qed.