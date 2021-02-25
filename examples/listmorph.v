From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| lseg_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_lseg_nxts1_521,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg_nxts1_521 /\ lseg nxt s1 h_lseg_nxts1_521.

Inductive lseg2 (x : ptr) (y : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg2_1 of (x) == (y) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| lseg2_2 of ~~ ((x) == (y)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_lseg2_nxtys1_522,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg2_nxtys1_522 /\ lseg2 nxt y s1 h_lseg2_nxtys1_522.

Lemma lseg_perm_eq_trans11 x h s_1 s_2 : perm_eq s_1 s_2 -> lseg x s_1 h -> lseg x s_2 h. Admitted.
Hint Resolve lseg_perm_eq_trans11: ssl_pred.
Lemma lseg2_perm_eq_trans12 x y h s_1 s_2 : perm_eq s_1 s_2 -> lseg2 x y s_1 h -> lseg2 x y s_2 h. Admitted.
Hint Resolve lseg2_perm_eq_trans12: ssl_pred.
Lemma pure13 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure13: ssl_pure.
Lemma pure14 : (null) = (null). Admitted.
Hint Resolve pure14: ssl_pure.
Lemma pure15 vx2 s1x : @perm_eq nat_eqType (([:: vx2]) ++ (s1x)) (([:: vx2]) ++ (s1x)). Admitted.
Hint Resolve pure15: ssl_pure.

Definition listmorph_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (s) := vghosts in
      exists h_lseg2_xs_523,
      h = r :-> null \+ h_lseg2_xs_523 /\ lseg2 x null s h_lseg2_xs_523,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (s) := vghosts in
      exists y,
      exists h_lseg_ys_524,
      h = r :-> y \+ h_lseg_ys_524 /\ lseg y s h_lseg_ys_524
    ]).

Program Definition listmorph : listmorph_type :=
  Fix (fun (listmorph : listmorph_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        listmorph (nxtx2, r);;
        y12 <-- @read ptr r;
        (x .+ 1) ::= y12;;
        r ::= x;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_lseg2_xs_523.
move=>[sigma_self].
subst h_self.
move=>H_lseg2_xs_523.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_lseg2_xs_523.
move=>[phi_lseg2_xs_5230].
move=>[sigma_lseg2_xs_523].
subst h_lseg2_xs_523.
try rename h_lseg2_xs_523 into h_lseg2_x_523.
try rename H_lseg2_xs_523 into H_lseg2_x_523.
try rename h_lseg_ys_524 into h_lseg_y_524.
try rename H_lseg_ys_524 into H_lseg_y_524.
try rename h_lseg_y_524 into h_lseg__524.
try rename H_lseg_y_524 into H_lseg__524.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx s1x nxtx.
ex_elim h_lseg2_nxtxs1x_522x.
move=>[phi_lseg2_xs_5230].
move=>[sigma_lseg2_xs_523].
subst h_lseg2_xs_523.
move=>H_lseg2_nxtxs1x_522x.
try rename h_lseg2_xs_523 into h_lseg2_xvxs1x_523.
try rename H_lseg2_xs_523 into H_lseg2_xvxs1x_523.
try rename h_lseg_ys_524 into h_lseg_yvxs1x_524.
try rename H_lseg_ys_524 into H_lseg_yvxs1x_524.
ssl_read x.
try rename vx into vx2.
try rename h_lseg_yvxs1x_524 into h_lseg_yvx2s1x_524.
try rename H_lseg_yvxs1x_524 into H_lseg_yvx2s1x_524.
try rename h_lseg2_xvxs1x_523 into h_lseg2_xvx2s1x_523.
try rename H_lseg2_xvxs1x_523 into H_lseg2_xvx2s1x_523.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_lseg2_nxtxs1x_522x into h_lseg2_nxtx2s1x_522x.
try rename H_lseg2_nxtxs1x_522x into H_lseg2_nxtx2s1x_522x.
try rename h_lseg2_x1s1_5231 into h_lseg2_nxtx2s1x_522x.
try rename H_lseg2_x1s1_5231 into H_lseg2_nxtx2s1x_522x.
ssl_call_pre (r :-> null \+ h_lseg2_nxtx2s1x_522x).
ssl_call (s1x).
exists (h_lseg2_nxtx2s1x_522x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_lseg_y1s1x_5241.
move=>[sigma_call0].
subst h_call0.
move=>H_lseg_y1s1x_5241.
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_lseg_y1s1x_5241 into h_lseg_y12s1x_5241.
try rename H_lseg_y1s1x_5241 into H_lseg_y12s1x_5241.
try rename h_lseg_nxtys11y_521y into h_lseg_y12s1x_5241.
try rename H_lseg_nxtys11y_521y into H_lseg_y12s1x_5241.
try rename h_lseg_yvx2s1x_524 into h_lseg_xvx2s1x_524.
try rename H_lseg_yvx2s1x_524 into H_lseg_xvx2s1x_524.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x);
exists (x :-> vx2 \+ x .+ 1 :-> y12 \+ h_lseg_y12s1x_5241);
sslauto.
ssl_close 2;
exists (vx2), (s1x), (y12), (h_lseg_y12s1x_5241);
sslauto.
ssl_frame_unfold.
Qed.