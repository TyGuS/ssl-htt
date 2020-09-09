From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

(*

predicate treeN(loc x, int n) {
|  x == 0        => { n == 0 ; emp }
|  not (x == 0)  => { n == 1 + n1 + n2  /\  0 <= n1  /\  0 <= n2 ;
  [x, 3] ** x :-> v ** (x + 1) :-> l ** (x + 2) :-> r ** treeN(l, n1) ** treeN(r, n2)}
}


{0 <= n ; r :-> 0 ** treeN(x, n)<a> }
void tree_size(loc x, loc r)
{true ; r :-> n ** treeN(x, n)<a> }

#####

void tree_size (loc x, loc r) {
  if (x == 0) {
  } else {
    let l = *(x + 1);
    let rx = *(x + 2);
    tree_size(l, r);
    let n1 = *r;
    *r = 0;
    tree_size(rx, r);
    let n = *r;
    *r = 1 + n1 + n;
  }
}

*)

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| tree2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) l r,
  exists h_tree_ls1_513 h_tree_rs2_514,
  perm_eq (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_513 \+ h_tree_rs2_514 /\ tree l s1 h_tree_ls1_513 /\ tree r s2 h_tree_rs2_514.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN1 of x == 0 of
  n == 0 /\ h = empty
| treeN2 of ~~ (x == 0) of
  exists n1 n2 l r (v: nat) (**),
  exists h_treeN_ln1_515 h_treeN_rn2_516,
  n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_515 \+ h_treeN_rn2_516 /\ treeN l n1 h_treeN_ln1_515 /\ treeN r n2 h_treeN_rn2_516.

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
(**)move/eqP in phi_treeN_xn_a.
rewrite phi_treeN_xn_a=>//=.
unfold_constructor 1;
sslauto.
ssl_open_post H_treeN_xn_a.
ex_elim n1x2 n2x2 lx2 rx2 vx2.
ex_elim h_treeN_lx2n1x2_515x h_treeN_rx2n2x2_516x.
move=>[phi_treeN_xn_a].
move=>[sigma_treeN_xn_a].
subst.
move=>[H_treeN_lx2n1x2_515x H_treeN_rx2n2x2_516x].
ssl_read.
ssl_read.
ssl_call_pre (r :-> 0 \+ h_treeN_lx2n1x2_515x).
ssl_call (n1x2).
exists (h_treeN_lx2n1x2_515x);
sslauto.
move=>h_call1.
ex_elim h_treeN_lx2n1x2_515x.
move=>[sigma_call1].
subst.
move=>H_treeN_lx2n1x2_515x.
store_valid.
ssl_read.
ssl_write r.
ssl_call_pre (r :-> 0 \+ h_treeN_rx2n2x2_516x).
ssl_call (n2x2).
exists (h_treeN_rx2n2x2_516x);
sslauto.
move=>h_call2.
ex_elim h_treeN_rx2n2x2_516x.
move=>[sigma_call2].
subst.
move=>H_treeN_rx2n2x2_516x.
store_valid.
ssl_read.
ssl_write r.
ssl_write_post r.
(**)move/eqP in phi_treeN_xn_a.
subst.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> lx2 \+ x .+ 2 :-> rx2 \+ h_treeN_lx2n1x2_515x \+ h_treeN_rx2n2x2_516x).
split.
hhauto.
unfold_constructor 2;
exists (n1x2), (n2x2), (lx2), (rx2), (vx2);
exists (h_treeN_lx2n1x2_515x);
exists (h_treeN_rx2n2x2_516x);
sslauto.
Qed.
