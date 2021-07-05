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

Lemma pure1 : (@nil nat) = (@nil nat). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (vx11 : nat) (s1x1 : seq nat) (s2x1 : seq nat) : ((([:: vx11]) ++ (s1x1)) ++ (s2x1)) = ((([:: vx11]) ++ (s1x1)) ++ (s2x1)). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (vx11 : nat) (s1x1 : seq nat) (s2x1 : seq nat) : ((([:: vx11]) ++ (s1x1)) ++ (s2x1)) = ((([:: vx11]) ++ (s1x1)) ++ (s2x1)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.

Definition tree_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_a,
      h = r :-> (x) \+ h_tree_xs_a /\ tree x s h_tree_xs_a,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_tree_xs_a h_tree_ys_a,
      h = r :-> (y) \+ h_tree_xs_a \+ h_tree_ys_a /\ tree x s h_tree_xs_a /\ tree y s h_tree_ys_a
    ]).

Program Definition tree_copy : tree_copy_type :=
  Fix (fun (tree_copy : tree_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x1 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        lx11 <-- @read ptr (x1 .+ 1);
        rx11 <-- @read ptr (x1 .+ 2);
        r ::= lx11;;
        tree_copy (r);;
        y11 <-- @read ptr r;
        r ::= rx11;;
        tree_copy (r);;
        y21 <-- @read ptr r;
        y3 <-- allocb null 3;
        r ::= y3;;
        (y3 .+ 1) ::= y11;;
        (y3 .+ 2) ::= y21;;
        y3 ::= vx11;;
        ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_tree_xs_a.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_a.
ssl_ghostelim_post.
ssl_read r.
try rename x into x1.
try rename h_tree_xs_a into h_tree_x1s_a.
try rename H_tree_xs_a into H_tree_x1s_a.
ssl_open ((x1) == (null)) H_tree_x1s_a.
move=>[phi_tree_x1s_a0].
move=>[sigma_tree_x1s_a].
subst h_tree_x1s_a.
try rename h_tree_ys_a into h_tree_y_a.
try rename H_tree_ys_a into H_tree_y_a.
try rename h_tree_x1s_a into h_tree_x1_a.
try rename H_tree_x1s_a into H_tree_x1_a.
try rename h_tree_y_a into h_tree__a.
try rename H_tree_y_a into H_tree__a.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ssl_close 1;
sslauto.
ex_elim vx1 s1x1 s2x1 lx1 rx1.
ex_elim h_tree_lx1s1x1_0x1 h_tree_rx1s2x1_1x1.
move=>[phi_tree_x1s_a0].
move=>[sigma_tree_x1s_a].
subst h_tree_x1s_a.
move=>[H_tree_lx1s1x1_0x1 H_tree_rx1s2x1_1x1].
try rename h_tree_x1s_a into h_tree_x1vx1s1x1s2x1_a.
try rename H_tree_x1s_a into H_tree_x1vx1s1x1s2x1_a.
try rename h_tree_ys_a into h_tree_yvx1s1x1s2x1_a.
try rename H_tree_ys_a into H_tree_yvx1s1x1s2x1_a.
ssl_read x1.
try rename vx1 into vx11.
try rename h_tree_x1vx1s1x1s2x1_a into h_tree_x1vx11s1x1s2x1_a.
try rename H_tree_x1vx1s1x1s2x1_a into H_tree_x1vx11s1x1s2x1_a.
try rename h_tree_yvx1s1x1s2x1_a into h_tree_yvx11s1x1s2x1_a.
try rename H_tree_yvx1s1x1s2x1_a into H_tree_yvx11s1x1s2x1_a.
ssl_read (x1 .+ 1).
try rename lx1 into lx11.
try rename h_tree_lx1s1x1_0x1 into h_tree_lx11s1x1_0x1.
try rename H_tree_lx1s1x1_0x1 into H_tree_lx11s1x1_0x1.
ssl_read (x1 .+ 2).
try rename rx1 into rx11.
try rename h_tree_rx1s2x1_1x1 into h_tree_rx11s2x1_1x1.
try rename H_tree_rx1s2x1_1x1 into H_tree_rx11s2x1_1x1.
try rename h_tree_x2s1_a1 into h_tree_lx11s1x1_0x1.
try rename H_tree_x2s1_a1 into H_tree_lx11s1x1_0x1.
ssl_write r.
ssl_call_pre (r :-> (lx11) \+ h_tree_lx11s1x1_0x1).
ssl_call (lx11, s1x1).
exists (h_tree_lx11s1x1_0x1);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_tree_lx11s1x1_0x1 h_tree_y1s1x1_0x1.
move=>[sigma_call0].
subst h_call0.
move=>[H_tree_lx11s1x1_0x1 H_tree_y1s1x1_0x1].
store_valid.
ssl_read r.
try rename y1 into y11.
try rename h_tree_y1s1x1_0x1 into h_tree_y11s1x1_0x1.
try rename H_tree_y1s1x1_0x1 into H_tree_y11s1x1_0x1.
try rename h_tree_x3s2_a2 into h_tree_rx11s2x1_1x1.
try rename H_tree_x3s2_a2 into H_tree_rx11s2x1_1x1.
ssl_write r.
ssl_call_pre (r :-> (rx11) \+ h_tree_rx11s2x1_1x1).
ssl_call (rx11, s2x1).
exists (h_tree_rx11s2x1_1x1);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim y2.
ex_elim h_tree_rx11s2x1_1x1 h_tree_y2s2x1_1x1.
move=>[sigma_call1].
subst h_call1.
move=>[H_tree_rx11s2x1_1x1 H_tree_y2s2x1_1x1].
store_valid.
ssl_read r.
try rename y2 into y21.
try rename h_tree_y2s2x1_1x1 into h_tree_y21s2x1_1x1.
try rename H_tree_y2s2x1_1x1 into H_tree_y21s2x1_1x1.
try rename h_tree_lx12s11x1_0x11 into h_tree_lx11s1x1_0x1.
try rename H_tree_lx12s11x1_0x11 into H_tree_lx11s1x1_0x1.
try rename h_tree_r3x1s21x1_1x11 into h_tree_rx11s2x1_1x1.
try rename H_tree_r3x1s21x1_1x11 into H_tree_rx11s2x1_1x1.
try rename h_tree_lys11y_0y into h_tree_y11s1x1_0x1.
try rename H_tree_lys11y_0y into H_tree_y11s1x1_0x1.
try rename h_tree_r3ys21y_1y into h_tree_y21s2x1_1x1.
try rename H_tree_r3ys21y_1y into H_tree_y21s2x1_1x1.
ssl_alloc y3.
try rename y into y3.
try rename h_tree_yvx11s1x1s2x1_a into h_tree_y3vx11s1x1s2x1_a.
try rename H_tree_yvx11s1x1s2x1_a into H_tree_y3vx11s1x1s2x1_a.
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
exists (x1 :-> (vx11) \+ x1 .+ 1 :-> (lx11) \+ x1 .+ 2 :-> (rx11) \+ h_tree_lx11s1x1_0x1 \+ h_tree_rx11s2x1_1x1);
exists (y3 :-> (vx11) \+ y3 .+ 1 :-> (y11) \+ y3 .+ 2 :-> (y21) \+ h_tree_y11s1x1_0x1 \+ h_tree_y21s2x1_1x1);
sslauto.
ssl_close 2;
exists (vx11), (s1x1), (s2x1), (lx11), (rx11), (h_tree_lx11s1x1_0x1), (h_tree_rx11s2x1_1x1);
sslauto.
shelve.
shelve.
ssl_close 2;
exists (vx11), (s1x1), (s2x1), (y11), (y21), (h_tree_y11s1x1_0x1), (h_tree_y21s2x1_1x1);
sslauto.
shelve.
shelve.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.