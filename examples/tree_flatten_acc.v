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
  exists h_tree_ls1_535 h_tree_rs2_536,
  @perm_eq nat_eqType (s) ((([:: v]) ++ (s1)) ++ (s2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_535 \+ h_tree_rs2_536 /\ tree l s1 h_tree_ls1_535 /\ tree r s2 h_tree_rs2_536.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of (x) == (null) of
  (n) == (0) /\ h = empty
| treeN_2 of ~~ ((x) == (null)) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_537 h_treeN_rn2_538,
  (0) <= (n1) /\ (0) <= (n2) /\ (n) == (((1) + (n1)) + (n2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_537 \+ h_treeN_rn2_538 /\ treeN l n1 h_treeN_ln1_537 /\ treeN r n2 h_treeN_rn2_538.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_539,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_539 /\ sll nxt s1 h_sll_nxts1_539.

Lemma tree_perm_eq_trans20 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans20: ssl_pred.
Lemma sll_perm_eq_trans21 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans21: ssl_pred.
Lemma pure22 vx2 s1x s2x acc : @perm_eq nat_eqType (((([:: vx2]) ++ (s1x)) ++ (s2x)) ++ (acc)) (([:: vx2]) ++ ((s2x) ++ ((s1x) ++ (acc)))). Admitted.
Hint Resolve pure22: ssl_pure.

Definition tree_flatten_acc_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x, z) := vprogs in
      let: (s, y, acc) := vghosts in
      exists h_tree_xs_540 h_sll_yacc_541,
      h = z :-> y \+ h_tree_xs_540 \+ h_sll_yacc_541 /\ tree x s h_tree_xs_540 /\ sll y acc h_sll_yacc_541,
    [vfun (_: unit) h =>
      let: (x, z) := vprogs in
      let: (s, y, acc) := vghosts in
      exists s1 t,
      exists h_sll_ts1_542,
      @perm_eq nat_eqType (s1) ((s) ++ (acc)) /\ h = z :-> t \+ h_sll_ts1_542 /\ sll t s1 h_sll_ts1_542
    ]).

Program Definition tree_flatten_acc : tree_flatten_acc_type :=
  Fix (fun (tree_flatten_acc : tree_flatten_acc_type) vprogs =>
    let: (x, z) := vprogs in
    Do (
      y2 <-- @read ptr z;
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        lx2 <-- @read ptr (x .+ 1);
        rx2 <-- @read ptr (x .+ 2);
        tree_flatten_acc (lx2, z);;
        t12 <-- @read ptr z;
        tree_flatten_acc (rx2, z);;
        t22 <-- @read ptr z;
        t3 <-- allocb null 2;
        dealloc x;;
        dealloc (x .+ 1);;
        dealloc (x .+ 2);;
        z ::= t3;;
        (t3 .+ 1) ::= t22;;
        t3 ::= vx2;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x z]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[s y] acc].
ex_elim h_tree_xs_540 h_sll_yacc_541.
move=>[sigma_self].
subst h_self.
move=>[H_tree_xs_540 H_sll_yacc_541].
ssl_ghostelim_post.
try rename h_sll_ts1_542 into h_sll_tsacc_542.
try rename H_sll_ts1_542 into H_sll_tsacc_542.
ssl_read z.
try rename y into y2.
try rename h_sll_yacc_541 into h_sll_y2acc_541.
try rename H_sll_yacc_541 into H_sll_y2acc_541.
ssl_open ((x) == (null)) H_tree_xs_540.
move=>[phi_tree_xs_5400].
move=>[sigma_tree_xs_540].
subst h_tree_xs_540.
try rename h_tree_xs_540 into h_tree_x_540.
try rename H_tree_xs_540 into H_tree_x_540.
try rename h_sll_tsacc_542 into h_sll_tacc_542.
try rename H_sll_tsacc_542 into H_sll_tacc_542.
try rename h_sll_tacc_542 into h_sll_y2acc_541.
try rename H_sll_tacc_542 into H_sll_y2acc_541.
ssl_emp;
exists (acc), (y2);
exists (h_sll_y2acc_541);
sslauto.
ssl_frame_unfold.
ex_elim vx s1x s2x lx rx.
ex_elim h_tree_lxs1x_535x h_tree_rxs2x_536x.
move=>[phi_tree_xs_5400].
move=>[sigma_tree_xs_540].
subst h_tree_xs_540.
move=>[H_tree_lxs1x_535x H_tree_rxs2x_536x].
try rename h_tree_xs_540 into h_tree_xvxs1xs2x_540.
try rename H_tree_xs_540 into H_tree_xvxs1xs2x_540.
try rename h_sll_tsacc_542 into h_sll_tvxs1xs2xacc_542.
try rename H_sll_tsacc_542 into H_sll_tvxs1xs2xacc_542.
ssl_read x.
try rename vx into vx2.
try rename h_tree_xvxs1xs2x_540 into h_tree_xvx2s1xs2x_540.
try rename H_tree_xvxs1xs2x_540 into H_tree_xvx2s1xs2x_540.
try rename h_sll_tvxs1xs2xacc_542 into h_sll_tvx2s1xs2xacc_542.
try rename H_sll_tvxs1xs2xacc_542 into H_sll_tvx2s1xs2xacc_542.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_tree_lxs1x_535x into h_tree_lx2s1x_535x.
try rename H_tree_lxs1x_535x into H_tree_lx2s1x_535x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_tree_rxs2x_536x into h_tree_rx2s2x_536x.
try rename H_tree_rxs2x_536x into H_tree_rx2s2x_536x.
try rename h_tree_x1s2_5401 into h_tree_lx2s1x_535x.
try rename H_tree_x1s2_5401 into H_tree_lx2s1x_535x.
try rename h_sll_y1acc1_5411 into h_sll_y2acc_541.
try rename H_sll_y1acc1_5411 into H_sll_y2acc_541.
ssl_call_pre (z :-> y2 \+ h_tree_lx2s1x_535x \+ h_sll_y2acc_541).
ssl_call (s1x, y2, acc).
exists (h_tree_lx2s1x_535x), (h_sll_y2acc_541);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s11 t1.
ex_elim h_sll_t1s11_5421.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_sll_t1s11_5421.
store_valid.
try rename h_sll_t1s11_5421 into h_sll_t1s1xacc_5421.
try rename H_sll_t1s11_5421 into H_sll_t1s1xacc_5421.
ssl_read z.
try rename t1 into t12.
try rename h_sll_t1s1xacc_5421 into h_sll_t12s1xacc_5421.
try rename H_sll_t1s1xacc_5421 into H_sll_t12s1xacc_5421.
try rename h_tree_x2s3_5402 into h_tree_rx2s2x_536x.
try rename H_tree_x2s3_5402 into H_tree_rx2s2x_536x.
try rename h_sll_y3acc2_5412 into h_sll_t12s1xacc_5421.
try rename H_sll_y3acc2_5412 into H_sll_t12s1xacc_5421.
ssl_call_pre (z :-> t12 \+ h_tree_rx2s2x_536x \+ h_sll_t12s1xacc_5421).
ssl_call (s2x, t12, (s1x) ++ (acc)).
exists (h_tree_rx2s2x_536x), (h_sll_t12s1xacc_5421);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call1.
ex_elim s12 t2.
ex_elim h_sll_t2s12_5422.
move=>[phi_call10].
move=>[sigma_call1].
subst h_call1.
move=>H_sll_t2s12_5422.
store_valid.
try rename h_sll_t2s12_5422 into h_sll_t2s2xs1xacc_5422.
try rename H_sll_t2s12_5422 into H_sll_t2s2xs1xacc_5422.
ssl_read z.
try rename t2 into t22.
try rename h_sll_t2s2xs1xacc_5422 into h_sll_t22s2xs1xacc_5422.
try rename H_sll_t2s2xs1xacc_5422 into H_sll_t22s2xs1xacc_5422.
try rename h_sll_nxtts13t_539t into h_sll_t22s2xs1xacc_5422.
try rename H_sll_nxtts13t_539t into H_sll_t22s2xs1xacc_5422.
ssl_alloc t3.
try rename t into t3.
try rename h_sll_tvx2s1xs2xacc_542 into h_sll_t3vx2s1xs2xacc_542.
try rename H_sll_tvx2s1xs2xacc_542 into H_sll_t3vx2s1xs2xacc_542.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write z.
ssl_write_post z.
ssl_write (t3 .+ 1).
ssl_write_post (t3 .+ 1).
ssl_write t3.
ssl_write_post t3.
ssl_emp;
exists (((([:: vx2]) ++ (s1x)) ++ (s2x)) ++ (acc)), (t3);
exists (t3 :-> vx2 \+ t3 .+ 1 :-> t22 \+ h_sll_t22s2xs1xacc_5422);
sslauto.
unfold_constructor 2;
exists (vx2), ((s2x) ++ ((s1x) ++ (acc))), (t22), (h_sll_t22s2xs1xacc_5422);
sslauto.
ssl_frame_unfold.
Qed.