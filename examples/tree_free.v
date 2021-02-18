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
  exists h_tree_ls1_553 h_tree_rs2_554,
  @perm_eq nat_eqType (s) ((([:: v]) ++ (s1)) ++ (s2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_553 \+ h_tree_rs2_554 /\ tree l s1 h_tree_ls1_553 /\ tree r s2 h_tree_rs2_554.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of (x) == (null) of
  (n) == (0) /\ h = empty
| treeN_2 of ~~ ((x) == (null)) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_555 h_treeN_rn2_556,
  (0) <= (n1) /\ (0) <= (n2) /\ (n) == (((1) + (n1)) + (n2)) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_555 \+ h_treeN_rn2_556 /\ treeN l n1 h_treeN_ln1_555 /\ treeN r n2 h_treeN_rn2_556.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_557,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_557 /\ sll nxt s1 h_sll_nxts1_557.

Lemma tree_perm_eq_trans32 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans32: ssl_pred.
Lemma sll_perm_eq_trans33 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans33: ssl_pred.

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_558,
      h = h_tree_xs_558 /\ tree x s h_tree_xs_558,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).

Program Definition tree_free : tree_free_type :=
  Fix (fun (tree_free : tree_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
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
ex_elim h_tree_xs_558.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_558.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_tree_xs_558.
move=>[phi_tree_xs_5580].
move=>[sigma_tree_xs_558].
subst h_tree_xs_558.
try rename h_tree_xs_558 into h_tree_x_558.
try rename H_tree_xs_558 into H_tree_x_558.
ssl_emp;
sslauto.
ex_elim vx s1x s2x lx rx.
ex_elim h_tree_lxs1x_553x h_tree_rxs2x_554x.
move=>[phi_tree_xs_5580].
move=>[sigma_tree_xs_558].
subst h_tree_xs_558.
move=>[H_tree_lxs1x_553x H_tree_rxs2x_554x].
try rename h_tree_xs_558 into h_tree_xvxs1xs2x_558.
try rename H_tree_xs_558 into H_tree_xvxs1xs2x_558.
ssl_read x.
try rename vx into vx2.
try rename h_tree_xvxs1xs2x_558 into h_tree_xvx2s1xs2x_558.
try rename H_tree_xvxs1xs2x_558 into H_tree_xvx2s1xs2x_558.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_tree_lxs1x_553x into h_tree_lx2s1x_553x.
try rename H_tree_lxs1x_553x into H_tree_lx2s1x_553x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_tree_rxs2x_554x into h_tree_rx2s2x_554x.
try rename H_tree_rxs2x_554x into H_tree_rx2s2x_554x.
try rename h_tree_x1s1_5581 into h_tree_lx2s1x_553x.
try rename H_tree_x1s1_5581 into H_tree_lx2s1x_553x.
ssl_call_pre (h_tree_lx2s1x_553x).
ssl_call (s1x).
exists (h_tree_lx2s1x_553x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
move=>[sigma_call0].
subst h_call0.
store_valid.
try rename h_tree_x2s2_5582 into h_tree_rx2s2x_554x.
try rename H_tree_x2s2_5582 into H_tree_rx2s2x_554x.
ssl_call_pre (h_tree_rx2s2x_554x).
ssl_call (s2x).
exists (h_tree_rx2s2x_554x);
sslauto.
ssl_frame_unfold.
move=>h_call1.
move=>[sigma_call1].
subst h_call1.
store_valid.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_emp;
sslauto.
Qed.