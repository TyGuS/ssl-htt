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

Lemma pure34 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure34: ssl_pure.
Lemma pure35 (n1x2 : nat) (n2x2 : nat) : (0) <= (((1) + (n1x2)) + (n2x2)) -> (0) <= (n2x2) -> (0) <= (n1x2) -> (((1) + (n1x2)) + (n2x2)) = (((1) + (n1x2)) + (n2x2)). intros; hammer. Qed.
Hint Resolve pure35: ssl_pure.

Definition tree_size_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n) := vghosts in
      exists h_treeN_xn_a,
      (0) <= (n) /\ h = r :-> 0 \+ h_treeN_xn_a /\ treeN x n h_treeN_xn_a,
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
      if (x) == (null)
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
        r ::= ((1) + (n1x2)) + (n2x2);;
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
ex_elim h_treeN_lxn1x_551x h_treeN_rxn2x_552x.
move=>[phi_treeN_xn_a0] [phi_treeN_xn_a1] [phi_treeN_xn_a2].
move=>[sigma_treeN_xn_a].
subst h_treeN_xn_a.
move=>[H_treeN_lxn1x_551x H_treeN_rxn2x_552x].
try rename h_treeN_xn_a into h_treeN_xn1xn2x_a.
try rename H_treeN_xn_a into H_treeN_xn1xn2x_a.
ssl_read x.
try rename vx into vx2.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_treeN_lxn1x_551x into h_treeN_lx2n1x_551x.
try rename H_treeN_lxn1x_551x into H_treeN_lx2n1x_551x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_treeN_rxn2x_552x into h_treeN_rx2n2x_552x.
try rename H_treeN_rxn2x_552x into H_treeN_rx2n2x_552x.
try rename h_treeN_x1n1_a1 into h_treeN_lx2n1x_551x.
try rename H_treeN_x1n1_a1 into H_treeN_lx2n1x_551x.
ssl_call_pre (r :-> 0 \+ h_treeN_lx2n1x_551x).
ssl_call (n1x).
exists (h_treeN_lx2n1x_551x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_treeN_lx2n1x_551x.
move=>[sigma_call0].
subst h_call0.
move=>H_treeN_lx2n1x_551x.
store_valid.
ssl_read r.
try rename n1x into n1x2.
try rename h_treeN_lx2n1x_551x into h_treeN_lx2n1x2_551x.
try rename H_treeN_lx2n1x_551x into H_treeN_lx2n1x2_551x.
try rename h_treeN_xn1xn2x_a into h_treeN_xn1x2n2x_a.
try rename H_treeN_xn1xn2x_a into H_treeN_xn1x2n2x_a.
try rename h_treeN_x2n2_a2 into h_treeN_rx2n2x_552x.
try rename H_treeN_x2n2_a2 into H_treeN_rx2n2x_552x.
ssl_write r.
ssl_call_pre (r :-> 0 \+ h_treeN_rx2n2x_552x).
ssl_call (n2x).
exists (h_treeN_rx2n2x_552x);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim h_treeN_rx2n2x_552x.
move=>[sigma_call1].
subst h_call1.
move=>H_treeN_rx2n2x_552x.
store_valid.
ssl_read r.
try rename n2x into n2x2.
try rename h_treeN_rx2n2x_552x into h_treeN_rx2n2x2_552x.
try rename H_treeN_rx2n2x_552x into H_treeN_rx2n2x2_552x.
try rename h_treeN_xn1x2n2x_a into h_treeN_xn1x2n2x2_a.
try rename H_treeN_xn1x2n2x_a into H_treeN_xn1x2n2x2_a.
try rename h_treeN_lx1n11x_551x1 into h_treeN_lx2n1x2_551x.
try rename H_treeN_lx1n11x_551x1 into H_treeN_lx2n1x2_551x.
try rename h_treeN_r3xn21x_552x1 into h_treeN_rx2n2x2_552x.
try rename H_treeN_r3xn21x_552x1 into H_treeN_rx2n2x2_552x.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> lx2 \+ x .+ 2 :-> rx2 \+ h_treeN_lx2n1x2_551x \+ h_treeN_rx2n2x2_552x);
sslauto.
ssl_close 2;
exists (n1x2), (n2x2), (lx2), (rx2), (vx2), (h_treeN_lx2n1x2_551x), (h_treeN_rx2n2x2_552x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.