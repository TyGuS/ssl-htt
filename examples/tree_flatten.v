From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| tree_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) (l : ptr) (r : ptr),
  exists h_tree_ls1_513 h_tree_rs2_514,
  @perm_eq nat_eqType (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_513 \+ h_tree_rs2_514 /\ tree l s1 h_tree_ls1_513 /\ tree r s2 h_tree_rs2_514.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of x == null of
  n == 0 /\ h = empty
| treeN_2 of (x == null) = false of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_515 h_treeN_rn2_516,
  0 <= n1 /\ 0 <= n2 /\ n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_515 \+ h_treeN_rn2_516 /\ treeN l n1 h_treeN_ln1_515 /\ treeN r n2 h_treeN_rn2_516.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_517,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_517 /\ sll nxt s1 h_sll_nxts1_517.

Lemma tree_perm_eq_trans1 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans1: ssl_pred.
Lemma sll_perm_eq_trans2 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans2: ssl_pred.
Lemma pure3 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 vx22 s1x2 s2x2 : @perm_eq nat_eqType ([:: vx22] ++ s1x2 ++ s2x2) ([:: vx22] ++ s1x2 ++ s2x2). Admitted.
Hint Resolve pure4: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_518 h_sll_x2s2_519,
      h = ret :-> x2 \+ h_sll_x1s1_518 \+ h_sll_x2s2_519 /\ sll x1 s1 h_sll_x1s1_518 /\ sll x2 s2 h_sll_x2s2_519,
    [vfun (_: unit) h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_520,
      @perm_eq nat_eqType (s) (s1 ++ s2) /\ h = ret :-> y \+ h_sll_ys_520 /\ sll y s h_sll_ys_520
    ]).

Variable sll_append : sll_append_type.

Definition tree_flatten_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_521,
      h = z :-> x \+ h_tree_xs_521 /\ tree x s h_tree_xs_521,
    [vfun (_: unit) h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_ys_522,
      h = z :-> y \+ h_sll_ys_522 /\ sll y s h_sll_ys_522
    ]).

Program Definition tree_flatten : tree_flatten_type :=
  Fix (fun (tree_flatten : tree_flatten_type) vprogs =>
    let: (z) := vprogs in
    Do (
      x2 <-- @read ptr z;
      if x2 == null
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
        x2 ::= y22;;
        sll_append (y12, x2);;
        y32 <-- @read ptr x2;
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
ex_elim h_tree_xs_521.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_521.
ssl_ghostelim_post.
ssl_read z.
try rename x into x2.
try rename h_tree_xs_521 into h_tree_x2s_521.
try rename H_tree_xs_521 into H_tree_x2s_521.
ssl_open (x2 == null) H_tree_x2s_521.
move=>[phi_tree_x2s_5210].
move=>[sigma_tree_x2s_521].
subst h_tree_x2s_521.
shelve.
ex_elim vx2 s1x2 s2x2 lx2 rx2.
ex_elim h_tree_lx2s1x2_513x2 h_tree_rx2s2x2_514x2.
move=>[phi_tree_x2s_5210].
move=>[sigma_tree_x2s_521].
subst h_tree_x2s_521.
move=>[H_tree_lx2s1x2_513x2 H_tree_rx2s2x2_514x2].
shelve.
Unshelve.
try rename h_sll_ys_522 into h_sll_y_522.
try rename H_sll_ys_522 into H_sll_y_522.
try rename h_tree_x2s_521 into h_tree_x2_521.
try rename H_tree_x2s_521 into H_tree_x2_521.
try rename h_sll_y_522 into h_sll__522.
try rename H_sll_y_522 into H_sll__522.
ssl_emp;
exists (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_sll_ys_522 into h_sll_yvx2s1x2s2x2_522.
try rename H_sll_ys_522 into H_sll_yvx2s1x2s2x2_522.
try rename h_tree_x2s_521 into h_tree_x2vx2s1x2s2x2_521.
try rename H_tree_x2s_521 into H_tree_x2vx2s1x2s2x2_521.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_yvx2s1x2s2x2_522 into h_sll_yvx22s1x2s2x2_522.
try rename H_sll_yvx2s1x2s2x2_522 into H_sll_yvx22s1x2s2x2_522.
try rename h_tree_x2vx2s1x2s2x2_521 into h_tree_x2vx22s1x2s2x2_521.
try rename H_tree_x2vx2s1x2s2x2_521 into H_tree_x2vx22s1x2s2x2_521.
ssl_read (x2 .+ 1).
try rename lx2 into lx22.
try rename h_tree_lx2s1x2_513x2 into h_tree_lx22s1x2_513x2.
try rename H_tree_lx2s1x2_513x2 into H_tree_lx22s1x2_513x2.
ssl_read (x2 .+ 2).
try rename rx2 into rx22.
try rename h_tree_rx2s2x2_514x2 into h_tree_rx22s2x2_514x2.
try rename H_tree_rx2s2x2_514x2 into H_tree_rx22s2x2_514x2.
ssl_write z.
ssl_call_pre (z :-> lx22 \+ h_tree_lx22s1x2_513x2).
ssl_call (lx22, s1x2).
exists (h_tree_lx22s1x2_513x2);
sslauto.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_y1s1x2_5221.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s1x2_5221.
store_valid.
ssl_read z.
try rename y1 into y12.
try rename h_sll_y1s1x2_5221 into h_sll_y12s1x2_5221.
try rename H_sll_y1s1x2_5221 into H_sll_y12s1x2_5221.
ssl_write z.
ssl_call_pre (z :-> rx22 \+ h_tree_rx22s2x2_514x2).
ssl_call (rx22, s2x2).
exists (h_tree_rx22s2x2_514x2);
sslauto.
move=>h_call1.
ex_elim y2.
ex_elim h_sll_y2s2x2_5222.
move=>[sigma_call1].
subst h_call1.
move=>H_sll_y2s2x2_5222.
store_valid.
ssl_read z.
try rename y2 into y22.
try rename h_sll_y2s2x2_5222 into h_sll_y22s2x2_5222.
try rename H_sll_y2s2x2_5222 into H_sll_y22s2x2_5222.
ssl_write x2.
ssl_call_pre (x2 :-> y22 \+ h_sll_y12s1x2_5221 \+ h_sll_y22s2x2_5222).
ssl_call (s1x2, y22, s2x2).
exists (h_sll_y12s1x2_5221), (h_sll_y22s2x2_5222);
sslauto.
move=>h_call2.
ex_elim s3 y3.
ex_elim h_sll_y3s3_520.
move=>[phi_call20].
move=>[sigma_call2].
subst h_call2.
move=>H_sll_y3s3_520.
store_valid.
try rename h_sll_y3s3_520 into h_sll_y3s1x2s2x2_520.
try rename H_sll_y3s3_520 into H_sll_y3s1x2s2x2_520.
ssl_read x2.
try rename y3 into y32.
try rename h_sll_y3s1x2s2x2_520 into h_sll_y32s1x2s2x2_520.
try rename H_sll_y3s1x2s2x2_520 into H_sll_y32s1x2s2x2_520.
try rename h_sll_nxtys12y_517y into h_sll_nxtys12y_520.
try rename H_sll_nxtys12y_517y into H_sll_nxtys12y_520.
try rename h_sll_nxtys12y_520 into h_sll_y32s12y_520.
try rename H_sll_nxtys12y_520 into H_sll_y32s12y_520.
try rename h_sll_y32s12y_520 into h_sll_y32s1x2s2x2_520.
try rename H_sll_y32s12y_520 into H_sll_y32s1x2s2x2_520.
ssl_alloc y4.
try rename y into y4.
try rename h_sll_yvx22s1x2s2x2_522 into h_sll_y4vx22s1x2s2x2_522.
try rename H_sll_yvx22s1x2s2x2_522 into H_sll_y4vx22s1x2s2x2_522.
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
exists (y4 :-> vx22 \+ y4 .+ 1 :-> y32 \+ h_sll_y32s1x2s2x2_520);
sslauto.
unfold_constructor 2;
exists (vx22), (s1x2 ++ s2x2), (y32), (h_sll_y32s1x2s2x2_520);
sslauto.
Qed.
