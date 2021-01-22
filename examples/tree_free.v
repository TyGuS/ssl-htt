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
  exists h_tree_ls1_533 h_tree_rs2_534,
  @perm_eq nat_eqType (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_533 \+ h_tree_rs2_534 /\ tree l s1 h_tree_ls1_533 /\ tree r s2 h_tree_rs2_534.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of x == null of
  n == 0 /\ h = empty
| treeN_2 of (x == null) = false of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_535 h_treeN_rn2_536,
  0 <= n1 /\ 0 <= n2 /\ n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_535 \+ h_treeN_rn2_536 /\ treeN l n1 h_treeN_ln1_535 /\ treeN r n2 h_treeN_rn2_536.

Lemma tree_perm_eq_trans23 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans23: ssl_pred.

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_537,
      h = h_tree_xs_537 /\ tree x s h_tree_xs_537,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).

Program Definition tree_free : tree_free_type :=
  Fix (fun (tree_free : tree_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if x == null
      then
        ret tt
      else
        lx2 <-- @read ptr (x .+ 1);
        rx2 <-- @read ptr (x .+ 2);
        tree_free (lx2);;
        tree_free (rx2);;
        dealloc x;;
        dealloc (x .+ 1);;
        dealloc (x .+ 2);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_tree_xs_537.
move=>[sigma_self].
subst.
move=>H_tree_xs_537.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_tree_xs_537.
move=>[phi_tree_xs_5370].
move=>[sigma_tree_xs_537].
subst.
ssl_emp;
sslauto.
ssl_open_post H_tree_xs_537.
ex_elim vx2 s1x s2x lx2 rx2.
ex_elim h_tree_lx2s1x_533x h_tree_rx2s2x_534x.
move=>[phi_tree_xs_5370].
move=>[sigma_tree_xs_537].
subst.
move=>[H_tree_lx2s1x_533x H_tree_rx2s2x_534x].
ssl_read (x .+ 1).
ssl_read (x .+ 2).
ssl_call_pre (h_tree_lx2s1x_533x).
ssl_call (s1x).
exists (h_tree_lx2s1x_533x);
sslauto.
move=>h_call1.
move=>[sigma_call1].
subst.
store_valid.
ssl_call_pre (h_tree_rx2s2x_534x).
ssl_call (s2x).
exists (h_tree_rx2s2x_534x);
sslauto.
move=>h_call2.
move=>[sigma_call2].
subst.
store_valid.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_emp;
sslauto.
Qed.
