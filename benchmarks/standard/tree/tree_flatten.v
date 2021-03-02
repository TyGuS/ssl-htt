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

Lemma pure32 : (@nil nat) = (@nil nat). intros; hammer. Qed.
Hint Resolve pure32: ssl_pure.
Lemma pure33 (vx22 : nat) (s1x2 : seq nat) (s2x2 : seq nat) : ((([:: vx22]) ++ (s1x2)) ++ (s2x2)) = (([:: vx22]) ++ ((s1x2) ++ (s2x2))). intros; hammer. Qed.
Hint Resolve pure33: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_544 h_sll_x2s2_545,
      h = ret :-> x2 \+ h_sll_x1s1_544 \+ h_sll_x2s2_545 /\ sll x1 s1 h_sll_x1s1_544 /\ sll x2 s2 h_sll_x2s2_545,
    [vfun (_: unit) h =>
      let: (x1, ret) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_546,
      (s) == ((s1) ++ (s2)) /\ h = ret :-> y \+ h_sll_ys_546 /\ sll y s h_sll_ys_546
    ]).

Variable sll_append : sll_append_type.

Definition tree_flatten_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists h_tree_xs_547,
      h = z :-> x \+ h_tree_xs_547 /\ tree x s h_tree_xs_547,
    [vfun (_: unit) h =>
      let: (z) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_ys_548,
      h = z :-> y \+ h_sll_ys_548 /\ sll y s h_sll_ys_548
    ]).

Program Definition tree_flatten : tree_flatten_type :=
  Fix (fun (tree_flatten : tree_flatten_type) vprogs =>
    let: (z) := vprogs in
    Do (
      x2 <-- @read ptr z;
      if (x2) == (null)
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        lx22 <-- @read ptr (x2 .+ 1);
        rx22 <-- @read ptr (x2 .+ 2);
        z ::= lx22;;
        tree_flatten (z);;
        y12 <-- @read ptr z;
        z ::= rx22;;
        tree_flatten (z);;
        y22 <-- @read ptr z;
        sll_append (y12, z);;
        y32 <-- @read ptr z;
        y4 <-- allocb null 2;
        dealloc x2;;
        dealloc (x2 .+ 1);;
        dealloc (x2 .+ 2);;
        z ::= y4;;
        (y4 .+ 1) ::= y32;;
        y4 ::= vx22;;
        ret tt
    )).
Obligation Tactic := intro; move=>z; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_tree_xs_547.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_547.
ssl_ghostelim_post.
ssl_read z.
try rename x into x2.
try rename h_tree_xs_547 into h_tree_x2s_547.
try rename H_tree_xs_547 into H_tree_x2s_547.
ssl_open ((x2) == (null)) H_tree_x2s_547.
move=>[phi_tree_x2s_5470].
move=>[sigma_tree_x2s_547].
subst h_tree_x2s_547.
try rename h_sll_ys_548 into h_sll_y_548.
try rename H_sll_ys_548 into H_sll_y_548.
try rename h_tree_x2s_547 into h_tree_x2_547.
try rename H_tree_x2s_547 into H_tree_x2_547.
try rename h_sll_y_548 into h_sll__548.
try rename H_sll_y_548 into H_sll__548.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx2 s1x2 s2x2 lx2 rx2.
ex_elim h_tree_lx2s1x2_539x2 h_tree_rx2s2x2_540x2.
move=>[phi_tree_x2s_5470].
move=>[sigma_tree_x2s_547].
subst h_tree_x2s_547.
move=>[H_tree_lx2s1x2_539x2 H_tree_rx2s2x2_540x2].
try rename h_tree_x2s_547 into h_tree_x2vx2s1x2s2x2_547.
try rename H_tree_x2s_547 into H_tree_x2vx2s1x2s2x2_547.
try rename h_sll_ys_548 into h_sll_yvx2s1x2s2x2_548.
try rename H_sll_ys_548 into H_sll_yvx2s1x2s2x2_548.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_yvx2s1x2s2x2_548 into h_sll_yvx22s1x2s2x2_548.
try rename H_sll_yvx2s1x2s2x2_548 into H_sll_yvx22s1x2s2x2_548.
try rename h_tree_x2vx2s1x2s2x2_547 into h_tree_x2vx22s1x2s2x2_547.
try rename H_tree_x2vx2s1x2s2x2_547 into H_tree_x2vx22s1x2s2x2_547.
ssl_read (x2 .+ 1).
try rename lx2 into lx22.
try rename h_tree_lx2s1x2_539x2 into h_tree_lx22s1x2_539x2.
try rename H_tree_lx2s1x2_539x2 into H_tree_lx22s1x2_539x2.
ssl_read (x2 .+ 2).
try rename rx2 into rx22.
try rename h_tree_rx2s2x2_540x2 into h_tree_rx22s2x2_540x2.
try rename H_tree_rx2s2x2_540x2 into H_tree_rx22s2x2_540x2.
try rename h_tree_x1s1_5471 into h_tree_lx22s1x2_539x2.
try rename H_tree_x1s1_5471 into H_tree_lx22s1x2_539x2.
ssl_write z.
ssl_call_pre (z :-> lx22 \+ h_tree_lx22s1x2_539x2).
ssl_call (lx22, s1x2).
exists (h_tree_lx22s1x2_539x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_y1s1x2_5481.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s1x2_5481.
store_valid.
ssl_read z.
try rename y1 into y12.
try rename h_sll_y1s1x2_5481 into h_sll_y12s1x2_5481.
try rename H_sll_y1s1x2_5481 into H_sll_y12s1x2_5481.
try rename h_tree_x3s2_5472 into h_tree_rx22s2x2_540x2.
try rename H_tree_x3s2_5472 into H_tree_rx22s2x2_540x2.
ssl_write z.
ssl_call_pre (z :-> rx22 \+ h_tree_rx22s2x2_540x2).
ssl_call (rx22, s2x2).
exists (h_tree_rx22s2x2_540x2);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim y2.
ex_elim h_sll_y2s2x2_5482.
move=>[sigma_call1].
subst h_call1.
move=>H_sll_y2s2x2_5482.
store_valid.
ssl_read z.
try rename y2 into y22.
try rename h_sll_y2s2x2_5482 into h_sll_y22s2x2_5482.
try rename H_sll_y2s2x2_5482 into H_sll_y22s2x2_5482.
try rename h_sll_x11s11_544 into h_sll_y12s1x2_5481.
try rename H_sll_x11s11_544 into H_sll_y12s1x2_5481.
try rename h_sll_x21s21_545 into h_sll_y22s2x2_5482.
try rename H_sll_x21s21_545 into H_sll_y22s2x2_5482.
ssl_call_pre (z :-> y22 \+ h_sll_y12s1x2_5481 \+ h_sll_y22s2x2_5482).
ssl_call (s1x2, y22, s2x2).
exists (h_sll_y12s1x2_5481), (h_sll_y22s2x2_5482);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call2.
ex_elim s3 y3.
ex_elim h_sll_y3s3_546.
move=>[phi_call20].
move=>[sigma_call2].
subst h_call2.
move=>H_sll_y3s3_546.
store_valid.
try rename h_sll_y3s3_546 into h_sll_y3s1x2s2x2_546.
try rename H_sll_y3s3_546 into H_sll_y3s1x2s2x2_546.
ssl_read z.
try rename y3 into y32.
try rename h_sll_y3s1x2s2x2_546 into h_sll_y32s1x2s2x2_546.
try rename H_sll_y3s1x2s2x2_546 into H_sll_y32s1x2s2x2_546.
try rename h_sll_nxtys12y_543y into h_sll_y32s1x2s2x2_546.
try rename H_sll_nxtys12y_543y into H_sll_y32s1x2s2x2_546.
ssl_alloc y4.
try rename y into y4.
try rename h_sll_yvx22s1x2s2x2_548 into h_sll_y4vx22s1x2s2x2_548.
try rename H_sll_yvx22s1x2s2x2_548 into H_sll_y4vx22s1x2s2x2_548.
ssl_dealloc x2.
ssl_dealloc (x2 .+ 1).
ssl_dealloc (x2 .+ 2).
ssl_write z.
ssl_write_post z.
ssl_write (y4 .+ 1).
ssl_write_post (y4 .+ 1).
ssl_write y4.
ssl_write_post y4.
ssl_emp;
exists (y4);
exists (y4 :-> vx22 \+ y4 .+ 1 :-> y32 \+ h_sll_y32s1x2s2x2_546);
sslauto.
ssl_close 2;
exists (vx22), ((s1x2) ++ (s2x2)), (y32), (h_sll_y32s1x2s2x2_546);
sslauto.
ssl_frame_unfold.
Qed.