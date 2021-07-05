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
Lemma pure2 (b1 : nat) : (b1) < ((b1) + (1)). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (vx11 : nat) (s1x1 : seq nat) : (([:: vx11]) ++ (s1x1)) = (([:: vx11]) ++ (s1x1)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (vx11 : nat) (s1x1 : seq nat) : (([:: vx11]) ++ (s1x1)) = (([:: vx11]) ++ (s1x1)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.

Definition sll_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_a,
      h = r :-> (x) \+ h_sll_xs_a /\ sll x s h_sll_xs_a,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_xs_a h_sll_ys_b,
      h = r :-> (y) \+ h_sll_xs_a \+ h_sll_ys_b /\ sll x s h_sll_xs_a /\ sll y s h_sll_ys_b
    ]).

Program Definition sll_copy : sll_copy_type :=
  Fix (fun (sll_copy : sll_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x1 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        nxtx11 <-- @read ptr (x1 .+ 1);
        r ::= nxtx11;;
        sll_copy (r);;
        y11 <-- @read ptr r;
        y2 <-- allocb null 2;
        r ::= y2;;
        (y2 .+ 1) ::= y11;;
        y2 ::= vx11;;
        ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_sll_xs_a.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_a.
ssl_ghostelim_post.
ssl_read r.
try rename x into x1.
try rename h_sll_xs_a into h_sll_x1s_a.
try rename H_sll_xs_a into H_sll_x1s_a.
ssl_open ((x1) == (null)) H_sll_x1s_a.
move=>[phi_sll_x1s_a0].
move=>[sigma_sll_x1s_a].
subst h_sll_x1s_a.
try rename h_sll_ys_b into h_sll_y_b.
try rename H_sll_ys_b into H_sll_y_b.
try rename h_sll_x1s_a into h_sll_x1_a.
try rename H_sll_x1s_a into H_sll_x1_a.
try rename h_sll_y_b into h_sll__b.
try rename H_sll_y_b into H_sll__b.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ssl_close 1;
sslauto.
ex_elim vx1 s1x1 nxtx1.
ex_elim h_sll_nxtx1s1x1_0x1.
move=>[phi_sll_x1s_a0].
move=>[sigma_sll_x1s_a].
subst h_sll_x1s_a.
move=>H_sll_nxtx1s1x1_0x1.
try rename h_sll_ys_b into h_sll_yvx1s1x1_b.
try rename H_sll_ys_b into H_sll_yvx1s1x1_b.
try rename h_sll_x1s_a into h_sll_x1vx1s1x1_a.
try rename H_sll_x1s_a into H_sll_x1vx1s1x1_a.
ssl_read x1.
try rename vx1 into vx11.
try rename h_sll_yvx1s1x1_b into h_sll_yvx11s1x1_b.
try rename H_sll_yvx1s1x1_b into H_sll_yvx11s1x1_b.
try rename h_sll_x1vx1s1x1_a into h_sll_x1vx11s1x1_a.
try rename H_sll_x1vx1s1x1_a into H_sll_x1vx11s1x1_a.
ssl_read (x1 .+ 1).
try rename nxtx1 into nxtx11.
try rename h_sll_nxtx1s1x1_0x1 into h_sll_nxtx11s1x1_0x1.
try rename H_sll_nxtx1s1x1_0x1 into H_sll_nxtx11s1x1_0x1.
try rename h_sll_x2s1_a1 into h_sll_nxtx11s1x1_0x1.
try rename H_sll_x2s1_a1 into H_sll_nxtx11s1x1_0x1.
ssl_write r.
ssl_call_pre (r :-> (nxtx11) \+ h_sll_nxtx11s1x1_0x1).
ssl_call (nxtx11, s1x1).
exists (h_sll_nxtx11s1x1_0x1);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx11s1x1_0x1 h_sll_y1s1x1_b1.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx11s1x1_0x1 H_sll_y1s1x1_b1].
store_valid.
ssl_read r.
try rename y1 into y11.
try rename h_sll_y1s1x1_b1 into h_sll_y11s1x1_b1.
try rename H_sll_y1s1x1_b1 into H_sll_y11s1x1_b1.
try rename h_sll_nxtx12s11x1_0x11 into h_sll_nxtx11s1x1_0x1.
try rename H_sll_nxtx12s11x1_0x11 into H_sll_nxtx11s1x1_0x1.
try rename h_sll_nxtys11y_0y into h_sll_y11s1x1_b1.
try rename H_sll_nxtys11y_0y into H_sll_y11s1x1_b1.
ssl_alloc y2.
try rename y into y2.
try rename h_sll_yvx11s1x1_b into h_sll_y2vx11s1x1_b.
try rename H_sll_yvx11s1x1_b into H_sll_y2vx11s1x1_b.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists (y2);
exists (x1 :-> (vx11) \+ x1 .+ 1 :-> (nxtx11) \+ h_sll_nxtx11s1x1_0x1);
exists (y2 :-> (vx11) \+ y2 .+ 1 :-> (y11) \+ h_sll_y11s1x1_b1);
sslauto.
ssl_close 2;
exists (vx11), (s1x1), (nxtx11), (h_sll_nxtx11s1x1_0x1);
sslauto.
shelve.
ssl_close 2;
exists (vx11), (s1x1), (y11), (h_sll_y11s1x1_b1);
sslauto.
shelve.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.