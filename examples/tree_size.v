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
  exists h_tree_ls1_521 h_tree_rs2_522,
  @perm_eq nat_eqType (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_521 \+ h_tree_rs2_522 /\ tree l s1 h_tree_ls1_521 /\ tree r s2 h_tree_rs2_522.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of x == null of
  n == 0 /\ h = empty
| treeN_2 of (x == null) = false of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_523 h_treeN_rn2_524,
  0 <= n1 /\ 0 <= n2 /\ n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_523 \+ h_treeN_rn2_524 /\ treeN l n1 h_treeN_ln1_523 /\ treeN r n2 h_treeN_rn2_524.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_525,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_525 /\ sll nxt s1 h_sll_nxts1_525.

Lemma tree_perm_eq_trans4 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans4: ssl_pred.
Lemma sll_perm_eq_trans5 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans5: ssl_pred.
Lemma pure6 : 0 == 0. Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 n1x2 n2x2 : 0 <= 1 + n1x2 + n2x2 -> 0 <= n1x2 -> 0 <= n2x2 -> 1 + n1x2 + n2x2 == 1 + n1x2 + n2x2. Admitted.
Hint Resolve pure7: ssl_pure.

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
      if x == null
      then
        ret tt
      else
        vx2 <-- @read ptr x;
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
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_treeN_xn_a.
ssl_ghostelim_post.
ssl_open (x == null) H_treeN_xn_a.
move=>[phi_treeN_xn_a0].
move=>[sigma_treeN_xn_a].
subst h_treeN_xn_a.
shelve.
ex_elim n1x n2x lx rx vx.
ex_elim h_treeN_lxn1x_523x h_treeN_rxn2x_524x.
move=>[phi_treeN_xn_a0] [phi_treeN_xn_a1] [phi_treeN_xn_a2].
move=>[sigma_treeN_xn_a].
subst h_treeN_xn_a.
move=>[H_treeN_lxn1x_523x H_treeN_rxn2x_524x].
shelve.
Unshelve.
try rename h_treeN_xn_a into h_treeN_x_a.
try rename H_treeN_xn_a into H_treeN_x_a.
ssl_emp;
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_treeN_xn_a into h_treeN_xn1xn2x_a.
try rename H_treeN_xn_a into H_treeN_xn1xn2x_a.
ssl_read x.
try rename vx into vx2.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_treeN_lxn1x_523x into h_treeN_lx2n1x_523x.
try rename H_treeN_lxn1x_523x into H_treeN_lx2n1x_523x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_treeN_rxn2x_524x into h_treeN_rx2n2x_524x.
try rename H_treeN_rxn2x_524x into H_treeN_rx2n2x_524x.
ssl_call_pre (r :-> 0 \+ h_treeN_lx2n1x_523x).
ssl_call (n1x).
exists (h_treeN_lx2n1x_523x);
sslauto.
move=>h_call0.
ex_elim h_treeN_lx2n1x_523x.
move=>[sigma_call0].
subst h_call0.
move=>H_treeN_lx2n1x_523x.
store_valid.
ssl_read r.
try rename n1x into n1x2.
try rename h_treeN_lx2n1x_523x into h_treeN_lx2n1x2_523x.
try rename H_treeN_lx2n1x_523x into H_treeN_lx2n1x2_523x.
try rename h_treeN_xn1xn2x_a into h_treeN_xn1x2n2x_a.
try rename H_treeN_xn1xn2x_a into H_treeN_xn1x2n2x_a.
ssl_write r.
ssl_call_pre (r :-> 0 \+ h_treeN_rx2n2x_524x).
ssl_call (n2x).
exists (h_treeN_rx2n2x_524x);
sslauto.
move=>h_call1.
ex_elim h_treeN_rx2n2x_524x.
move=>[sigma_call1].
subst h_call1.
move=>H_treeN_rx2n2x_524x.
store_valid.
ssl_read r.
try rename n2x into n2x2.
try rename h_treeN_rx2n2x_524x into h_treeN_rx2n2x2_524x.
try rename H_treeN_rx2n2x_524x into H_treeN_rx2n2x2_524x.
try rename h_treeN_xn1x2n2x_a into h_treeN_xn1x2n2x2_a.
try rename H_treeN_xn1x2n2x_a into H_treeN_xn1x2n2x2_a.
try rename h_treeN_lx1n11x_523x1 into h_treeN_lx1n11x_523x.
try rename H_treeN_lx1n11x_523x1 into H_treeN_lx1n11x_523x.
try rename h_treeN_lx1n11x_523x into h_treeN_lx2n11x_523x.
try rename H_treeN_lx1n11x_523x into H_treeN_lx2n11x_523x.
try rename h_treeN_lx2n11x_523x into h_treeN_lx2n1x2_523x.
try rename H_treeN_lx2n11x_523x into H_treeN_lx2n1x2_523x.
try rename h_treeN_r3xn21x_524x1 into h_treeN_r3xn21x_524x.
try rename H_treeN_r3xn21x_524x1 into H_treeN_r3xn21x_524x.
try rename h_treeN_r3xn21x_524x into h_treeN_r3xn2x2_524x.
try rename H_treeN_r3xn21x_524x into H_treeN_r3xn2x2_524x.
try rename h_treeN_r3xn2x2_524x into h_treeN_rx2n2x2_524x.
try rename H_treeN_r3xn2x2_524x into H_treeN_rx2n2x2_524x.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> lx2 \+ x .+ 2 :-> rx2 \+ h_treeN_lx2n1x2_523x \+ h_treeN_rx2n2x2_524x);
sslauto.
unfold_constructor 2;
exists (n1x2), (n2x2), (lx2), (rx2), (vx2), (h_treeN_lx2n1x2_523x), (h_treeN_rx2n2x2_524x);
sslauto.
Qed.