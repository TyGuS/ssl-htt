From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| tree_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) (l : ptr) (r : ptr),
  exists h_tree_ls1_525 h_tree_rs2_526,
  @perm_eq nat_eqType (s) ((([:: v]) ++ (s1)) ++ (s2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_525 \+ h_tree_rs2_526 /\ tree l s1 h_tree_ls1_525 /\ tree r s2 h_tree_rs2_526.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of (x) == (null) of
  (n) == (0) /\ h = empty
| treeN_2 of ~~ ((x) == (null)) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_527 h_treeN_rn2_528,
  (0) <= (n1) /\ (0) <= (n2) /\ (n) == (((1) + (n1)) + (n2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_527 \+ h_treeN_rn2_528 /\ treeN l n1 h_treeN_ln1_527 /\ treeN r n2 h_treeN_rn2_528.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_529,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_529 /\ sll nxt s1 h_sll_nxts1_529.

Lemma tree_perm_eq_trans16 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans16: ssl_pred.
Lemma sll_perm_eq_trans17 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans17: ssl_pred.
Lemma pure18 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure18: ssl_pure.
Lemma pure19 vx22 s1x2 s2x2 : @perm_eq nat_eqType ((([:: vx22]) ++ (s1x2)) ++ (s2x2)) (([:: vx22]) ++ ((s1x2) ++ (s2x2))). Admitted.
Hint Resolve pure19: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_530 h_sll_x2s2_531,
      h = ret :-> x2 \+ h_sll_x1s1_530 \+ h_sll_x2s2_531 /\ sll x1 s1 h_sll_x1s1_530 /\ sll x2 s2 h_sll_x2s2_531,
    [vfun (_: unit) h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_532,
      @perm_eq nat_eqType (s) ((s1) ++ (s2)) /\ h = ret :-> y \+ h_sll_ys_532 /\ sll y s h_sll_ys_532
    ]).

Variable sll_append : sll_append_type.

Definition tree_flatten_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_533,
      h = z :-> x \+ h_tree_xs_533 /\ tree x s h_tree_xs_533,
    [vfun (_: unit) h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_ys_534,
      h = z :-> y \+ h_sll_ys_534 /\ sll y s h_sll_ys_534
    ]).

Program Definition tree_flatten : tree_flatten_type :=
  Fix (fun (tree_flatten : tree_flatten_type) vprogs =>
    let: (z) := vprogs in
    Do (
      x2 <-- @read ptr z;
      if (x2) == (null)
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        lx22 <-- @read ptr (x2 .+ 1);
        rx22 <-- @read ptr (x2 .+ 2);
        z ::= lx22;;
        tree_flatten (z);;
        y12 <-- @read ptr z;
        z ::= rx22;;
        tree_flatten (z);;
        y22 <-- @read ptr z;
        sll_append (y12, z);;
        y32 <-- @read ptr z;
        y4 <-- allocb null 2;
        dealloc x2;;
        dealloc (x2 .+ 1);;
        dealloc (x2 .+ 2);;
        z ::= y4;;
        (y4 .+ 1) ::= y32;;
        y4 ::= vx22;;
        ret tt
    )).
Obligation Tactic := intro; move=>z; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_tree_xs_533.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_533.
ssl_ghostelim_post.
ssl_read z.
try rename x into x2.
try rename h_tree_xs_533 into h_tree_x2s_533.
try rename H_tree_xs_533 into H_tree_x2s_533.
ssl_open ((x2) == (null)) H_tree_x2s_533.
move=>[phi_tree_x2s_5330].
move=>[sigma_tree_x2s_533].
subst h_tree_x2s_533.
try rename h_sll_ys_534 into h_sll_y_534.
try rename H_sll_ys_534 into H_sll_y_534.
try rename h_tree_x2s_533 into h_tree_x2_533.
try rename H_tree_x2s_533 into H_tree_x2_533.
try rename h_sll_y_534 into h_sll__534.
try rename H_sll_y_534 into H_sll__534.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx2 s1x2 s2x2 lx2 rx2.
ex_elim h_tree_lx2s1x2_525x2 h_tree_rx2s2x2_526x2.
move=>[phi_tree_x2s_5330].
move=>[sigma_tree_x2s_533].
subst h_tree_x2s_533.
move=>[H_tree_lx2s1x2_525x2 H_tree_rx2s2x2_526x2].
try rename h_tree_x2s_533 into h_tree_x2vx2s1x2s2x2_533.
try rename H_tree_x2s_533 into H_tree_x2vx2s1x2s2x2_533.
try rename h_sll_ys_534 into h_sll_yvx2s1x2s2x2_534.
try rename H_sll_ys_534 into H_sll_yvx2s1x2s2x2_534.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_yvx2s1x2s2x2_534 into h_sll_yvx22s1x2s2x2_534.
try rename H_sll_yvx2s1x2s2x2_534 into H_sll_yvx22s1x2s2x2_534.
try rename h_tree_x2vx2s1x2s2x2_533 into h_tree_x2vx22s1x2s2x2_533.
try rename H_tree_x2vx2s1x2s2x2_533 into H_tree_x2vx22s1x2s2x2_533.
ssl_read (x2 .+ 1).
try rename lx2 into lx22.
try rename h_tree_lx2s1x2_525x2 into h_tree_lx22s1x2_525x2.
try rename H_tree_lx2s1x2_525x2 into H_tree_lx22s1x2_525x2.
ssl_read (x2 .+ 2).
try rename rx2 into rx22.
try rename h_tree_rx2s2x2_526x2 into h_tree_rx22s2x2_526x2.
try rename H_tree_rx2s2x2_526x2 into H_tree_rx22s2x2_526x2.
try rename h_tree_x1s1_5331 into h_tree_lx22s1x2_525x2.
try rename H_tree_x1s1_5331 into H_tree_lx22s1x2_525x2.
ssl_write z.
ssl_call_pre (z :-> lx22 \+ h_tree_lx22s1x2_525x2).
ssl_call (lx22, s1x2).
exists (h_tree_lx22s1x2_525x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_y1s1x2_5341.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s1x2_5341.
store_valid.
ssl_read z.
try rename y1 into y12.
try rename h_sll_y1s1x2_5341 into h_sll_y12s1x2_5341.
try rename H_sll_y1s1x2_5341 into H_sll_y12s1x2_5341.
try rename h_tree_x3s2_5332 into h_tree_rx22s2x2_526x2.
try rename H_tree_x3s2_5332 into H_tree_rx22s2x2_526x2.
ssl_write z.
ssl_call_pre (z :-> rx22 \+ h_tree_rx22s2x2_526x2).
ssl_call (rx22, s2x2).
exists (h_tree_rx22s2x2_526x2);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim y2.
ex_elim h_sll_y2s2x2_5342.
move=>[sigma_call1].
subst h_call1.
move=>H_sll_y2s2x2_5342.
store_valid.
ssl_read z.
try rename y2 into y22.
try rename h_sll_y2s2x2_5342 into h_sll_y22s2x2_5342.
try rename H_sll_y2s2x2_5342 into H_sll_y22s2x2_5342.
try rename h_sll_x11s11_530 into h_sll_y12s1x2_5341.
try rename H_sll_x11s11_530 into H_sll_y12s1x2_5341.
try rename h_sll_x21s21_531 into h_sll_y22s2x2_5342.
try rename H_sll_x21s21_531 into H_sll_y22s2x2_5342.
ssl_call_pre (z :-> y22 \+ h_sll_y12s1x2_5341 \+ h_sll_y22s2x2_5342).
ssl_call (s1x2, y22, s2x2).
exists (h_sll_y12s1x2_5341), (h_sll_y22s2x2_5342);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call2.
ex_elim s3 y3.
ex_elim h_sll_y3s3_532.
move=>[phi_call20].
move=>[sigma_call2].
subst h_call2.
move=>H_sll_y3s3_532.
store_valid.
try rename h_sll_y3s3_532 into h_sll_y3s1x2s2x2_532.
try rename H_sll_y3s3_532 into H_sll_y3s1x2s2x2_532.
ssl_read z.
try rename y3 into y32.
try rename h_sll_y3s1x2s2x2_532 into h_sll_y32s1x2s2x2_532.
try rename H_sll_y3s1x2s2x2_532 into H_sll_y32s1x2s2x2_532.
try rename h_sll_nxtys12y_529y into h_sll_y32s1x2s2x2_532.
try rename H_sll_nxtys12y_529y into H_sll_y32s1x2s2x2_532.
ssl_alloc y4.
try rename y into y4.
try rename h_sll_yvx22s1x2s2x2_534 into h_sll_y4vx22s1x2s2x2_534.
try rename H_sll_yvx22s1x2s2x2_534 into H_sll_y4vx22s1x2s2x2_534.
ssl_dealloc x2.
ssl_dealloc (x2 .+ 1).
ssl_dealloc (x2 .+ 2).
ssl_write z.
ssl_write_post z.
ssl_write (y4 .+ 1).
ssl_write_post (y4 .+ 1).
ssl_write y4.
ssl_write_post y4.
ssl_emp;
exists (y4);
exists (y4 :-> vx22 \+ y4 .+ 1 :-> y32 \+ h_sll_y32s1x2s2x2_532);
sslauto.
ssl_close 2;
exists (vx22), ((s1x2) ++ (s2x2)), (y32), (h_sll_y32s1x2s2x2_532);
sslauto.
ssl_frame_unfold.
Qed.