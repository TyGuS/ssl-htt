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
  exists h_tree_ls1_529 h_tree_rs2_530,
  @perm_eq nat_eqType (s) ([:: v] ++ s1 ++ s2) /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree_ls1_529 \+ h_tree_rs2_530 /\ tree l s1 h_tree_ls1_529 /\ tree r s2 h_tree_rs2_530.

Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of x == null of
  n == 0 /\ h = empty
| treeN_2 of (x == null) = false of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_531 h_treeN_rn2_532,
  0 <= n1 /\ 0 <= n2 /\ n == 1 + n1 + n2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_treeN_ln1_531 \+ h_treeN_rn2_532 /\ treeN l n1 h_treeN_ln1_531 /\ treeN r n2 h_treeN_rn2_532.

Lemma tree_perm_eq_trans19 x h s_1 s_2 : perm_eq s_1 s_2 -> tree x s_1 h -> tree x s_2 h. Admitted.
Hint Resolve tree_perm_eq_trans19: ssl_pred.
Lemma pure20 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure20: ssl_pure.
Lemma pure21 vx22 s1x2 s2x2 : @perm_eq nat_eqType ([:: vx22] ++ s1x2 ++ s2x2) ([:: vx22] ++ s1x2 ++ s2x2). Admitted.
Hint Resolve pure21: ssl_pure.
Lemma pure22 vx22 s1x2 s2x2 : @perm_eq nat_eqType ([:: vx22] ++ s1x2 ++ s2x2) ([:: vx22] ++ s1x2 ++ s2x2). Admitted.
Hint Resolve pure22: ssl_pure.

Definition tree_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_a,
      h = r :-> x \+ h_tree_xs_a /\ tree x s h_tree_xs_a,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_tree_xs_a h_tree_ys_a,
      h = r :-> y \+ h_tree_xs_a \+ h_tree_ys_a /\ tree x s h_tree_xs_a /\ tree y s h_tree_ys_a
    ]).

Program Definition tree_copy : tree_copy_type :=
  Fix (fun (tree_copy : tree_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        lx22 <-- @read ptr (x2 .+ 1);
        rx22 <-- @read ptr (x2 .+ 2);
        r ::= lx22;;
        tree_copy (r);;
        y12 <-- @read ptr r;
        r ::= rx22;;
        tree_copy (r);;
        y22 <-- @read ptr r;
        y3 <-- allocb null 3;
        r ::= y3;;
        (y3 .+ 1) ::= y12;;
        (y3 .+ 2) ::= y22;;
        y3 ::= vx22;;
        ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
ex_elim h_tree_x2s_a.
move=>[sigma_self].
subst h_self.
move=>H_tree_x2s_a.
ssl_ghostelim_post.
ssl_read r.
ssl_open (x2 == null);
ssl_open_post H_tree_x2s_a.
move=>[phi_tree_x2s_a0].
move=>[sigma_tree_x2s_a].
subst h_tree_x2s_a.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto |
unfold_constructor 1;
sslauto ].
ex_elim vx22 s1x2 s2x2 lx22 rx22.
ex_elim h_tree_lx22s1x2_529x2 h_tree_rx22s2x2_530x2.
move=>[phi_tree_x2s_a0].
move=>[sigma_tree_x2s_a].
subst h_tree_x2s_a.
move=>[H_tree_lx22s1x2_529x2 H_tree_rx22s2x2_530x2].
ssl_read x2.
ssl_read (x2 .+ 1).
ssl_read (x2 .+ 2).
ssl_write r.
ssl_call_pre (r :-> lx22 \+ h_tree_lx22s1x2_529x2).
ssl_call (lx22, s1x2).
exists (h_tree_lx22s1x2_529x2);
sslauto.
move=>h_call1.
ex_elim y12.
ex_elim h_tree_lx22s1x2_529x2 h_tree_y12s1x2_529x2.
move=>[sigma_call1].
subst h_call1.
move=>[H_tree_lx22s1x2_529x2 H_tree_y12s1x2_529x2].
store_valid.
ssl_read r.
ssl_write r.
ssl_call_pre (r :-> rx22 \+ h_tree_rx22s2x2_530x2).
ssl_call (rx22, s2x2).
exists (h_tree_rx22s2x2_530x2);
sslauto.
move=>h_call2.
ex_elim y22.
ex_elim h_tree_rx22s2x2_530x2 h_tree_y22s2x2_530x2.
move=>[sigma_call2].
subst h_call2.
move=>[H_tree_rx22s2x2_530x2 H_tree_y22s2x2_530x2].
store_valid.
ssl_read r.
ssl_alloc y3.
ssl_write r.
ssl_write_post r.
ssl_write (y3 .+ 1).
ssl_write_post (y3 .+ 1).
ssl_write (y3 .+ 2).
ssl_write_post (y3 .+ 2).
ssl_write y3.
ssl_write_post y3.
ssl_emp;
exists (y3);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> lx22 \+ x2 .+ 2 :-> rx22 \+ h_tree_lx22s1x2_529x2 \+ h_tree_rx22s2x2_530x2);
exists (y3 :-> vx22 \+ y3 .+ 1 :-> y12 \+ y3 .+ 2 :-> y22 \+ h_tree_y12s1x2_529x2 \+ h_tree_y22s2x2_530x2);
sslauto;
solve [
unfold_constructor 2;
exists (vx22), (s1x2), (s2x2), (lx22), (rx22);
exists (h_tree_lx22s1x2_529x2);
exists (h_tree_rx22s2x2_530x2);
sslauto |
unfold_constructor 2;
exists (vx22), (s1x2), (s2x2), (y12), (y22);
exists (h_tree_y12s1x2_529x2);
exists (h_tree_y22s2x2_530x2);
sslauto ].
Qed.
