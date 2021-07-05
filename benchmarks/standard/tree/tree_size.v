From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.
From Hammer Require Import Hammer.
(* Configure Hammer *)
Set Hammer ATPLimit 60.
Unset Hammer Eprover.
Unset Hammer Vampire.
Add Search Blacklist "fcsl.".
Add Search Blacklist "HTT.".
Add Search Blacklist "Coq.ssr.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.bigop".
Add Search Blacklist "mathcomp.ssreflect.choice".
Add Search Blacklist "mathcomp.ssreflect.div".
Add Search Blacklist "mathcomp.ssreflect.finfun".
Add Search Blacklist "mathcomp.ssreflect.fintype".
Add Search Blacklist "mathcomp.ssreflect.path".
Add Search Blacklist "mathcomp.ssreflect.tuple".


Require Import common.

Lemma pure1 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (n1x1 : nat) (n2x1 : nat) : (0) <= (((1) + (n1x1)) + (n2x1)) -> (0) <= (n1x1) -> (0) <= (n2x1) -> (((1) + (n1x1)) + (n2x1)) = (((1) + (n1x1)) + (n2x1)). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.

Definition tree_size_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n) := vghosts in
      exists h_treeN_xn_a,
      (0) <= (n) /\ h = r :-> (0) \+ h_treeN_xn_a /\ treeN x n h_treeN_xn_a,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n) := vghosts in
      exists h_treeN_xn_a,
      h = r :-> (n) \+ h_treeN_xn_a /\ treeN x n h_treeN_xn_a
    ]).

Program Definition tree_size : tree_size_type :=
  Fix (fun (tree_size : tree_size_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx1 <-- @read ptr x;
        lx1 <-- @read ptr (x .+ 1);
        rx1 <-- @read ptr (x .+ 2);
        tree_size (lx1, r);;
        n1x1 <-- @read nat r;
        r ::= 0;;
        tree_size (rx1, r);;
        n2x1 <-- @read nat r;
        r ::= ((1) + (n1x1)) + (n2x1);;
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
ssl_open ((x) == (null)) H_treeN_xn_a.
move=>[phi_treeN_xn_a0].
move=>[sigma_treeN_xn_a].
subst h_treeN_xn_a.
try rename h_treeN_xn_a into h_treeN_x_a.
try rename H_treeN_xn_a into H_treeN_x_a.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim n1x n2x lx rx vx.
ex_elim h_treeN_lxn1x_2x h_treeN_rxn2x_3x.
move=>[phi_treeN_xn_a0] [phi_treeN_xn_a1] [phi_treeN_xn_a2].
move=>[sigma_treeN_xn_a].
subst h_treeN_xn_a.
move=>[H_treeN_lxn1x_2x H_treeN_rxn2x_3x].
try rename h_treeN_xn_a into h_treeN_xn1xn2x_a.
try rename H_treeN_xn_a into H_treeN_xn1xn2x_a.
ssl_read x.
try rename vx into vx1.
ssl_read (x .+ 1).
try rename lx into lx1.
try rename h_treeN_lxn1x_2x into h_treeN_lx1n1x_2x.
try rename H_treeN_lxn1x_2x into H_treeN_lx1n1x_2x.
ssl_read (x .+ 2).
try rename rx into rx1.
try rename h_treeN_rxn2x_3x into h_treeN_rx1n2x_3x.
try rename H_treeN_rxn2x_3x into H_treeN_rx1n2x_3x.
try rename h_treeN_x1n1_a1 into h_treeN_lx1n1x_2x.
try rename H_treeN_x1n1_a1 into H_treeN_lx1n1x_2x.
ssl_call_pre (r :-> (0) \+ h_treeN_lx1n1x_2x).
ssl_call (n1x).
exists (h_treeN_lx1n1x_2x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_treeN_lx1n1x_2x.
move=>[sigma_call0].
subst h_call0.
move=>H_treeN_lx1n1x_2x.
store_valid.
ssl_read r.
try rename n1x into n1x1.
try rename h_treeN_lx1n1x_2x into h_treeN_lx1n1x1_2x.
try rename H_treeN_lx1n1x_2x into H_treeN_lx1n1x1_2x.
try rename h_treeN_xn1xn2x_a into h_treeN_xn1x1n2x_a.
try rename H_treeN_xn1xn2x_a into H_treeN_xn1x1n2x_a.
try rename h_treeN_x2n2_a2 into h_treeN_rx1n2x_3x.
try rename H_treeN_x2n2_a2 into H_treeN_rx1n2x_3x.
ssl_write r.
ssl_call_pre (r :-> (0) \+ h_treeN_rx1n2x_3x).
ssl_call (n2x).
exists (h_treeN_rx1n2x_3x);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim h_treeN_rx1n2x_3x.
move=>[sigma_call1].
subst h_call1.
move=>H_treeN_rx1n2x_3x.
store_valid.
ssl_read r.
try rename n2x into n2x1.
try rename h_treeN_xn1x1n2x_a into h_treeN_xn1x1n2x1_a.
try rename H_treeN_xn1x1n2x_a into H_treeN_xn1x1n2x1_a.
try rename h_treeN_rx1n2x_3x into h_treeN_rx1n2x1_3x.
try rename H_treeN_rx1n2x_3x into H_treeN_rx1n2x1_3x.
try rename h_treeN_lx2n11x_2x1 into h_treeN_lx1n1x1_2x.
try rename H_treeN_lx2n11x_2x1 into H_treeN_lx1n1x1_2x.
try rename h_treeN_r3xn21x_3x1 into h_treeN_rx1n2x1_3x.
try rename H_treeN_r3xn21x_3x1 into H_treeN_rx1n2x1_3x.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> (vx1) \+ x .+ 1 :-> (lx1) \+ x .+ 2 :-> (rx1) \+ h_treeN_lx1n1x1_2x \+ h_treeN_rx1n2x1_3x);
sslauto.
ssl_close 2;
exists (n1x1), (n2x1), (lx1), (rx1), (vx1), (h_treeN_lx1n1x1_2x), (h_treeN_rx1n2x1_3x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.