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
  exists h_tree_ls1_519 h_tree_rs2_520,
  perm_eq (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_519 \+ h_tree_rs2_520 /\ tree l s1 h_tree_ls1_519 /\ tree r s2 h_tree_rs2_520.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN1 of x == 0 of
  n == 0 /\ h = empty
| treeN2 of ~~ (x == 0) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_521 h_treeN_rn2_522,
  n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_521 \+ h_treeN_rn2_522 /\ treeN l n1 h_treeN_ln1_521 /\ treeN r n2 h_treeN_rn2_522.

Definition tree_size_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n) := vghosts in
      exists h_treeN_xn_a,
      0 <= n /\ h = r :-> 0 \+ h_treeN_xn_a /\ treeN x n h_treeN_xn_a,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n) := vghosts in
      exists h_treeN_xn_a,
      h = r :-> n \+ h_treeN_xn_a /\ treeN x n h_treeN_xn_a
    ]).
Program Definition tree_size : tree_size_type :=
  Fix (fun (tree_size : tree_size_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if x == 0
      then
        ret tt
      else
        lx2 <-- @read ptr (x .+ 1);
        rx2 <-- @read ptr (x .+ 2);
        tree_size (lx2, r);;
        n1x2 <-- @read nat r;
        r ::= 0;;
        tree_size (rx2, r);;
        n2x2 <-- @read nat r;
        r ::= 1 + n1x2 + n2x2;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>n.
ex_elim h_treeN_xn_a.
move=>[phi_self].
move=>[sigma_self].
subst.
move=>H_treeN_xn_a.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_treeN_xn_a.
move=>[phi_treeN_xn_a].
move=>[sigma_treeN_xn_a].
subst.
ssl_emp;
exists (empty);
sslauto.
(**)move/eqP in phi_treeN_xn_a; subst=>//=.
unfold_constructor 1;
sslauto.
ssl_open_post H_treeN_xn_a.
ex_elim n1x2 n2x2 lx2 rx2 vx2.
ex_elim h_treeN_lx2n1x2_521x h_treeN_rx2n2x2_522x.
move=>[phi_treeN_xn_a].
move=>[sigma_treeN_xn_a].
subst.
move=>[H_treeN_lx2n1x2_521x H_treeN_rx2n2x2_522x].
ssl_read.
ssl_read.
ssl_call_pre (r :-> 0 \+ h_treeN_lx2n1x2_521x).
ssl_call (n1x2).
exists (h_treeN_lx2n1x2_521x);
sslauto.
move=>h_call3.
ex_elim h_treeN_lx2n1x2_521x.
move=>[sigma_call3].
subst.
move=>H_treeN_lx2n1x2_521x.
store_valid.
ssl_read.
ssl_write r.
ssl_call_pre (r :-> 0 \+ h_treeN_rx2n2x2_522x).
ssl_call (n2x2).
exists (h_treeN_rx2n2x2_522x);
sslauto.
move=>h_call4.
ex_elim h_treeN_rx2n2x2_522x.
move=>[sigma_call4].
subst.
move=>H_treeN_rx2n2x2_522x.
store_valid.
ssl_read.
ssl_write r.
ssl_write_post r.
(**)move/eqP in phi_treeN_xn_a; subst=>//=.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> lx2 \+ x .+ 2 :-> rx2 \+ h_treeN_lx2n1x2_521x \+ h_treeN_rx2n2x2_522x);
sslauto.
unfold_constructor 2;
exists (n1x2), (n2x2), (lx2), (rx2), (vx2);
exists (h_treeN_lx2n1x2_521x);
exists (h_treeN_rx2n2x2_522x);
sslauto.

Qed.
