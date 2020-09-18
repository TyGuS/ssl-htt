From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| tree2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) (l : ptr) (r : ptr),
  exists h_tree_ls1_527 h_tree_rs2_528,
  perm_eq (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_527 \+ h_tree_rs2_528 /\ tree l s1 h_tree_ls1_527 /\ tree r s2 h_tree_rs2_528.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN1 of x == 0 of
  n == 0 /\ h = empty
| treeN2 of ~~ (x == 0) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_529 h_treeN_rn2_530,
  n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_529 \+ h_treeN_rn2_530 /\ treeN l n1 h_treeN_ln1_529 /\ treeN r n2 h_treeN_rn2_530.

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_531,
      h = h_tree_xs_531 /\ tree x s h_tree_xs_531,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).
Program Definition tree_free : tree_free_type :=
  Fix (fun (tree_free : tree_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if x == 0
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
ex_elim h_tree_xs_531.
move=>[sigma_self].
subst.
move=>H_tree_xs_531.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_tree_xs_531.
move=>[phi_tree_xs_531].
move=>[sigma_tree_xs_531].
subst.
ssl_emp;
sslauto.
ssl_open_post H_tree_xs_531.
ex_elim vx2 s1x s2x lx2 rx2.
ex_elim h_tree_lx2s1x_527x h_tree_rx2s2x_528x.
move=>[phi_tree_xs_531].
move=>[sigma_tree_xs_531].
subst.
move=>[H_tree_lx2s1x_527x H_tree_rx2s2x_528x].
ssl_read.
ssl_read.
ssl_call_pre (h_tree_lx2s1x_527x).
ssl_call (s1x).
exists (h_tree_lx2s1x_527x);
sslauto.
move=>h_call7.
move=>[sigma_call7].
subst.
store_valid.
ssl_call_pre (h_tree_rx2s2x_528x).
ssl_call (s2x).
exists (h_tree_rx2s2x_528x);
sslauto.
move=>h_call8.
move=>[sigma_call8].
subst.
store_valid.
ssl_dealloc (x).
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_emp;
sslauto.

Qed.
