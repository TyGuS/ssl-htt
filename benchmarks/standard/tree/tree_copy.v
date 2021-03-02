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

Lemma pure36 : (@nil nat) = (@nil nat). intros; hammer. Qed.
Hint Resolve pure36: ssl_pure.
Lemma pure37 (vx22 : nat) (s1x2 : seq nat) (s2x2 : seq nat) : ((([:: vx22]) ++ (s1x2)) ++ (s2x2)) = ((([:: vx22]) ++ (s1x2)) ++ (s2x2)). intros; hammer. Qed.
Hint Resolve pure37: ssl_pure.
Lemma pure38 (vx22 : nat) (s1x2 : seq nat) (s2x2 : seq nat) : ((([:: vx22]) ++ (s1x2)) ++ (s2x2)) = ((([:: vx22]) ++ (s1x2)) ++ (s2x2)). intros; hammer. Qed.
Hint Resolve pure38: ssl_pure.

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
      if (x2) == (null)
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
move=>[x s].
ex_elim h_tree_xs_a.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_a.
ssl_ghostelim_post.
ssl_read r.
try rename x into x2.
try rename h_tree_xs_a into h_tree_x2s_a.
try rename H_tree_xs_a into H_tree_x2s_a.
ssl_open ((x2) == (null)) H_tree_x2s_a.
move=>[phi_tree_x2s_a0].
move=>[sigma_tree_x2s_a].
subst h_tree_x2s_a.
try rename h_tree_ys_a into h_tree_y_a.
try rename H_tree_ys_a into H_tree_y_a.
try rename h_tree_x2s_a into h_tree_x2_a.
try rename H_tree_x2s_a into H_tree_x2_a.
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
ex_elim vx2 s1x2 s2x2 lx2 rx2.
ex_elim h_tree_lx2s1x2_554x2 h_tree_rx2s2x2_555x2.
move=>[phi_tree_x2s_a0].
move=>[sigma_tree_x2s_a].
subst h_tree_x2s_a.
move=>[H_tree_lx2s1x2_554x2 H_tree_rx2s2x2_555x2].
try rename h_tree_x2s_a into h_tree_x2vx2s1x2s2x2_a.
try rename H_tree_x2s_a into H_tree_x2vx2s1x2s2x2_a.
try rename h_tree_ys_a into h_tree_yvx2s1x2s2x2_a.
try rename H_tree_ys_a into H_tree_yvx2s1x2s2x2_a.
ssl_read x2.
try rename vx2 into vx22.
try rename h_tree_x2vx2s1x2s2x2_a into h_tree_x2vx22s1x2s2x2_a.
try rename H_tree_x2vx2s1x2s2x2_a into H_tree_x2vx22s1x2s2x2_a.
try rename h_tree_yvx2s1x2s2x2_a into h_tree_yvx22s1x2s2x2_a.
try rename H_tree_yvx2s1x2s2x2_a into H_tree_yvx22s1x2s2x2_a.
ssl_read (x2 .+ 1).
try rename lx2 into lx22.
try rename h_tree_lx2s1x2_554x2 into h_tree_lx22s1x2_554x2.
try rename H_tree_lx2s1x2_554x2 into H_tree_lx22s1x2_554x2.
ssl_read (x2 .+ 2).
try rename rx2 into rx22.
try rename h_tree_rx2s2x2_555x2 into h_tree_rx22s2x2_555x2.
try rename H_tree_rx2s2x2_555x2 into H_tree_rx22s2x2_555x2.
try rename h_tree_x1s1_a1 into h_tree_lx22s1x2_554x2.
try rename H_tree_x1s1_a1 into H_tree_lx22s1x2_554x2.
ssl_write r.
ssl_call_pre (r :-> lx22 \+ h_tree_lx22s1x2_554x2).
ssl_call (lx22, s1x2).
exists (h_tree_lx22s1x2_554x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_tree_lx22s1x2_554x2 h_tree_y1s1x2_554x2.
move=>[sigma_call0].
subst h_call0.
move=>[H_tree_lx22s1x2_554x2 H_tree_y1s1x2_554x2].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_tree_y1s1x2_554x2 into h_tree_y12s1x2_554x2.
try rename H_tree_y1s1x2_554x2 into H_tree_y12s1x2_554x2.
try rename h_tree_x3s2_a2 into h_tree_rx22s2x2_555x2.
try rename H_tree_x3s2_a2 into H_tree_rx22s2x2_555x2.
ssl_write r.
ssl_call_pre (r :-> rx22 \+ h_tree_rx22s2x2_555x2).
ssl_call (rx22, s2x2).
exists (h_tree_rx22s2x2_555x2);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim y2.
ex_elim h_tree_rx22s2x2_555x2 h_tree_y2s2x2_555x2.
move=>[sigma_call1].
subst h_call1.
move=>[H_tree_rx22s2x2_555x2 H_tree_y2s2x2_555x2].
store_valid.
ssl_read r.
try rename y2 into y22.
try rename h_tree_y2s2x2_555x2 into h_tree_y22s2x2_555x2.
try rename H_tree_y2s2x2_555x2 into H_tree_y22s2x2_555x2.
try rename h_tree_lx21s11x2_554x21 into h_tree_lx22s1x2_554x2.
try rename H_tree_lx21s11x2_554x21 into H_tree_lx22s1x2_554x2.
try rename h_tree_r3x2s21x2_555x21 into h_tree_rx22s2x2_555x2.
try rename H_tree_r3x2s21x2_555x21 into H_tree_rx22s2x2_555x2.
try rename h_tree_lys11y_554y into h_tree_y12s1x2_554x2.
try rename H_tree_lys11y_554y into H_tree_y12s1x2_554x2.
try rename h_tree_r3ys21y_555y into h_tree_y22s2x2_555x2.
try rename H_tree_r3ys21y_555y into H_tree_y22s2x2_555x2.
ssl_alloc y3.
try rename y into y3.
try rename h_tree_yvx22s1x2s2x2_a into h_tree_y3vx22s1x2s2x2_a.
try rename H_tree_yvx22s1x2s2x2_a into H_tree_y3vx22s1x2s2x2_a.
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
exists (x2 :-> vx22 \+ x2 .+ 1 :-> lx22 \+ x2 .+ 2 :-> rx22 \+ h_tree_lx22s1x2_554x2 \+ h_tree_rx22s2x2_555x2);
exists (y3 :-> vx22 \+ y3 .+ 1 :-> y12 \+ y3 .+ 2 :-> y22 \+ h_tree_y12s1x2_554x2 \+ h_tree_y22s2x2_555x2);
sslauto.
ssl_close 2;
exists (vx22), (s1x2), (s2x2), (lx22), (rx22), (h_tree_lx22s1x2_554x2), (h_tree_rx22s2x2_555x2);
sslauto.
shelve.
shelve.
ssl_close 2;
exists (vx22), (s1x2), (s2x2), (y12), (y22), (h_tree_y12s1x2_554x2), (h_tree_y22s2x2_555x2);
sslauto.
shelve.
shelve.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.