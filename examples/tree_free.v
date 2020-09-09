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
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) l r,
  exists h_tree_ls1_523 h_tree_rs2_524,
  perm_eq (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_523 \+ h_tree_rs2_524 /\ tree l s1 h_tree_ls1_523 /\ tree r s2 h_tree_rs2_524.

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_525,
      h = h_tree_xs_525 /\ tree x s h_tree_xs_525,
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
ex_elim h_tree_xs_525.
move=>[sigma_self].
subst.
move=>H_tree_xs_525.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_tree_xs_525.
move=>[phi_tree_xs_525].
move=>[sigma_tree_xs_525].
subst.
ssl_emp;
sslauto.
ssl_open_post H_tree_xs_525.
ex_elim vx2 s1x s2x lx2 rx2.
ex_elim h_tree_lx2s1x_523x h_tree_rx2s2x_524x.
move=>[phi_tree_xs_525].
move=>[sigma_tree_xs_525].
subst.
move=>[H_tree_lx2s1x_523x H_tree_rx2s2x_524x].
ssl_read.
ssl_read.
ssl_call_pre (h_tree_lx2s1x_523x).
ssl_call (s1x).
exists (h_tree_lx2s1x_523x);
sslauto.
move=>h_call5.
move=>[sigma_call5].
subst.
store_valid.
ssl_call_pre (h_tree_rx2s2x_524x).
ssl_call (s2x).
exists (h_tree_rx2s2x_524x);
sslauto.
move=>h_call6.
move=>[sigma_call6].
subst.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
sslauto.

Qed.
