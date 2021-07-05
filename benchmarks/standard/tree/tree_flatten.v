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
Lemma pure2 (vx11 : nat) (s1x1 : seq nat) (s2x1 : seq nat) : ((([:: vx11]) ++ (s1x1)) ++ (s2x1)) = (([:: vx11]) ++ ((s1x1) ++ (s2x1))). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_5 h_sll_x2s2_6,
      h = ret :-> (x2) \+ h_sll_x1s1_5 \+ h_sll_x2s2_6 /\ sll x1 s1 h_sll_x1s1_5 /\ sll x2 s2 h_sll_x2s2_6,
    [vfun (_: unit) h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_7,
      (s) == ((s1) ++ (s2)) /\ h = ret :-> (y) \+ h_sll_ys_7 /\ sll y s h_sll_ys_7
    ]).

Variable sll_append : sll_append_type.

Definition tree_flatten_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_8,
      h = z :-> (x) \+ h_tree_xs_8 /\ tree x s h_tree_xs_8,
    [vfun (_: unit) h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_ys_9,
      h = z :-> (y) \+ h_sll_ys_9 /\ sll y s h_sll_ys_9
    ]).

Program Definition tree_flatten : tree_flatten_type :=
  Fix (fun (tree_flatten : tree_flatten_type) vprogs =>
    let: (z) := vprogs in
    Do (
      x1 <-- @read ptr z;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        lx11 <-- @read ptr (x1 .+ 1);
        rx11 <-- @read ptr (x1 .+ 2);
        z ::= lx11;;
        tree_flatten (z);;
        y11 <-- @read ptr z;
        z ::= rx11;;
        tree_flatten (z);;
        y21 <-- @read ptr z;
        sll_append (y11, z);;
        y31 <-- @read ptr z;
        y4 <-- allocb null 2;
        dealloc x1;;
        dealloc (x1 .+ 1);;
        dealloc (x1 .+ 2);;
        z ::= y4;;
        (y4 .+ 1) ::= y31;;
        y4 ::= vx11;;
        ret tt
    )).
Obligation Tactic := intro; move=>z; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_tree_xs_8.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_8.
ssl_ghostelim_post.
ssl_read z.
try rename x into x1.
try rename h_tree_xs_8 into h_tree_x1s_8.
try rename H_tree_xs_8 into H_tree_x1s_8.
ssl_open ((x1) == (null)) H_tree_x1s_8.
move=>[phi_tree_x1s_80].
move=>[sigma_tree_x1s_8].
subst h_tree_x1s_8.
try rename h_sll_ys_9 into h_sll_y_9.
try rename H_sll_ys_9 into H_sll_y_9.
try rename h_tree_x1s_8 into h_tree_x1_8.
try rename H_tree_x1s_8 into H_tree_x1_8.
try rename h_sll_y_9 into h_sll__9.
try rename H_sll_y_9 into H_sll__9.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx1 s1x1 s2x1 lx1 rx1.
ex_elim h_tree_lx1s1x1_0x1 h_tree_rx1s2x1_1x1.
move=>[phi_tree_x1s_80].
move=>[sigma_tree_x1s_8].
subst h_tree_x1s_8.
move=>[H_tree_lx1s1x1_0x1 H_tree_rx1s2x1_1x1].
try rename h_sll_ys_9 into h_sll_yvx1s1x1s2x1_9.
try rename H_sll_ys_9 into H_sll_yvx1s1x1s2x1_9.
try rename h_tree_x1s_8 into h_tree_x1vx1s1x1s2x1_8.
try rename H_tree_x1s_8 into H_tree_x1vx1s1x1s2x1_8.
ssl_read x1.
try rename vx1 into vx11.
try rename h_tree_x1vx1s1x1s2x1_8 into h_tree_x1vx11s1x1s2x1_8.
try rename H_tree_x1vx1s1x1s2x1_8 into H_tree_x1vx11s1x1s2x1_8.
try rename h_sll_yvx1s1x1s2x1_9 into h_sll_yvx11s1x1s2x1_9.
try rename H_sll_yvx1s1x1s2x1_9 into H_sll_yvx11s1x1s2x1_9.
ssl_read (x1 .+ 1).
try rename lx1 into lx11.
try rename h_tree_lx1s1x1_0x1 into h_tree_lx11s1x1_0x1.
try rename H_tree_lx1s1x1_0x1 into H_tree_lx11s1x1_0x1.
ssl_read (x1 .+ 2).
try rename rx1 into rx11.
try rename h_tree_rx1s2x1_1x1 into h_tree_rx11s2x1_1x1.
try rename H_tree_rx1s2x1_1x1 into H_tree_rx11s2x1_1x1.
try rename h_tree_x2s1_81 into h_tree_lx11s1x1_0x1.
try rename H_tree_x2s1_81 into H_tree_lx11s1x1_0x1.
ssl_write z.
ssl_call_pre (z :-> (lx11) \+ h_tree_lx11s1x1_0x1).
ssl_call (lx11, s1x1).
exists (h_tree_lx11s1x1_0x1);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_y1s1x1_91.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s1x1_91.
store_valid.
ssl_read z.
try rename y1 into y11.
try rename h_sll_y1s1x1_91 into h_sll_y11s1x1_91.
try rename H_sll_y1s1x1_91 into H_sll_y11s1x1_91.
try rename h_tree_x3s2_82 into h_tree_rx11s2x1_1x1.
try rename H_tree_x3s2_82 into H_tree_rx11s2x1_1x1.
ssl_write z.
ssl_call_pre (z :-> (rx11) \+ h_tree_rx11s2x1_1x1).
ssl_call (rx11, s2x1).
exists (h_tree_rx11s2x1_1x1);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim y2.
ex_elim h_sll_y2s2x1_92.
move=>[sigma_call1].
subst h_call1.
move=>H_sll_y2s2x1_92.
store_valid.
ssl_read z.
try rename y2 into y21.
try rename h_sll_y2s2x1_92 into h_sll_y21s2x1_92.
try rename H_sll_y2s2x1_92 into H_sll_y21s2x1_92.
try rename h_sll_x11s11_5 into h_sll_y11s1x1_91.
try rename H_sll_x11s11_5 into H_sll_y11s1x1_91.
try rename h_sll_x21s21_6 into h_sll_y21s2x1_92.
try rename H_sll_x21s21_6 into H_sll_y21s2x1_92.
ssl_call_pre (z :-> (y21) \+ h_sll_y11s1x1_91 \+ h_sll_y21s2x1_92).
ssl_call (s1x1, y21, s2x1).
exists (h_sll_y11s1x1_91), (h_sll_y21s2x1_92);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call2.
ex_elim s3 y3.
ex_elim h_sll_y3s3_7.
move=>[phi_call20].
move=>[sigma_call2].
subst h_call2.
move=>H_sll_y3s3_7.
store_valid.
try rename h_sll_y3s3_7 into h_sll_y3s1x1s2x1_7.
try rename H_sll_y3s3_7 into H_sll_y3s1x1s2x1_7.
ssl_read z.
try rename y3 into y31.
try rename h_sll_y3s1x1s2x1_7 into h_sll_y31s1x1s2x1_7.
try rename H_sll_y3s1x1s2x1_7 into H_sll_y31s1x1s2x1_7.
try rename h_sll_nxtys12y_4y into h_sll_y31s1x1s2x1_7.
try rename H_sll_nxtys12y_4y into H_sll_y31s1x1s2x1_7.
ssl_alloc y4.
try rename y into y4.
try rename h_sll_yvx11s1x1s2x1_9 into h_sll_y4vx11s1x1s2x1_9.
try rename H_sll_yvx11s1x1s2x1_9 into H_sll_y4vx11s1x1s2x1_9.
ssl_dealloc x1.
ssl_dealloc (x1 .+ 1).
ssl_dealloc (x1 .+ 2).
ssl_write z.
ssl_write_post z.
ssl_write (y4 .+ 1).
ssl_write_post (y4 .+ 1).
ssl_write y4.
ssl_write_post y4.
ssl_emp;
exists (y4);
exists (y4 :-> (vx11) \+ y4 .+ 1 :-> (y31) \+ h_sll_y31s1x1s2x1_7);
sslauto.
ssl_close 2;
exists (vx11), ((s1x1) ++ (s2x1)), (y31), (h_sll_y31s1x1s2x1_7);
sslauto.
ssl_frame_unfold.
Qed.