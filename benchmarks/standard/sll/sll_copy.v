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

Lemma pure23 : (@nil nat) = (@nil nat). intros; hammer. Qed.
Hint Resolve pure23: ssl_pure.
Lemma pure24 (b1 : nat) : (b1) < ((b1) + (1)). intros; hammer. Qed.
Hint Resolve pure24: ssl_pure.
Lemma pure25 (vx22 : nat) (s1x2 : seq nat) : (([:: vx22]) ++ (s1x2)) = (([:: vx22]) ++ (s1x2)). intros; hammer. Qed.
Hint Resolve pure25: ssl_pure.
Lemma pure26 (vx22 : nat) (s1x2 : seq nat) : (([:: vx22]) ++ (s1x2)) = (([:: vx22]) ++ (s1x2)). intros; hammer. Qed.
Hint Resolve pure26: ssl_pure.

Definition sll_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_a,
      h = r :-> x \+ h_sll_xs_a /\ sll x s h_sll_xs_a,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_xs_a h_sll_ys_b,
      h = r :-> y \+ h_sll_xs_a \+ h_sll_ys_b /\ sll x s h_sll_xs_a /\ sll y s h_sll_ys_b
    ]).

Program Definition sll_copy : sll_copy_type :=
  Fix (fun (sll_copy : sll_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if (x2) == (null)
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        r ::= nxtx22;;
        sll_copy (r);;
        y12 <-- @read ptr r;
        y2 <-- allocb null 2;
        r ::= y2;;
        (y2 .+ 1) ::= y12;;
        y2 ::= vx22;;
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
try rename x into x2.
try rename h_sll_xs_a into h_sll_x2s_a.
try rename H_sll_xs_a into H_sll_x2s_a.
ssl_open ((x2) == (null)) H_sll_x2s_a.
move=>[phi_sll_x2s_a0].
move=>[sigma_sll_x2s_a].
subst h_sll_x2s_a.
try rename h_sll_ys_b into h_sll_y_b.
try rename H_sll_ys_b into H_sll_y_b.
try rename h_sll_x2s_a into h_sll_x2_a.
try rename H_sll_x2s_a into H_sll_x2_a.
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
ex_elim vx2 s1x2 nxtx2.
ex_elim h_sll_nxtx2s1x2_524x2.
move=>[phi_sll_x2s_a0].
move=>[sigma_sll_x2s_a].
subst h_sll_x2s_a.
move=>H_sll_nxtx2s1x2_524x2.
try rename h_sll_ys_b into h_sll_yvx2s1x2_b.
try rename H_sll_ys_b into H_sll_yvx2s1x2_b.
try rename h_sll_x2s_a into h_sll_x2vx2s1x2_a.
try rename H_sll_x2s_a into H_sll_x2vx2s1x2_a.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_yvx2s1x2_b into h_sll_yvx22s1x2_b.
try rename H_sll_yvx2s1x2_b into H_sll_yvx22s1x2_b.
try rename h_sll_x2vx2s1x2_a into h_sll_x2vx22s1x2_a.
try rename H_sll_x2vx2s1x2_a into H_sll_x2vx22s1x2_a.
ssl_read (x2 .+ 1).
try rename nxtx2 into nxtx22.
try rename h_sll_nxtx2s1x2_524x2 into h_sll_nxtx22s1x2_524x2.
try rename H_sll_nxtx2s1x2_524x2 into H_sll_nxtx22s1x2_524x2.
try rename h_sll_x1s1_a1 into h_sll_nxtx22s1x2_524x2.
try rename H_sll_x1s1_a1 into H_sll_nxtx22s1x2_524x2.
ssl_write r.
ssl_call_pre (r :-> nxtx22 \+ h_sll_nxtx22s1x2_524x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_524x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx22s1x2_524x2 h_sll_y1s1x2_b1.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx22s1x2_524x2 H_sll_y1s1x2_b1].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_sll_y1s1x2_b1 into h_sll_y12s1x2_b1.
try rename H_sll_y1s1x2_b1 into H_sll_y12s1x2_b1.
try rename h_sll_nxtx21s11x2_524x21 into h_sll_nxtx22s1x2_524x2.
try rename H_sll_nxtx21s11x2_524x21 into H_sll_nxtx22s1x2_524x2.
try rename h_sll_nxtys11y_524y into h_sll_y12s1x2_b1.
try rename H_sll_nxtys11y_524y into H_sll_y12s1x2_b1.
ssl_alloc y2.
try rename y into y2.
try rename h_sll_yvx22s1x2_b into h_sll_y2vx22s1x2_b.
try rename H_sll_yvx22s1x2_b into H_sll_y2vx22s1x2_b.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists (y2);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> nxtx22 \+ h_sll_nxtx22s1x2_524x2);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> y12 \+ h_sll_y12s1x2_b1);
sslauto.
ssl_close 2;
exists (vx22), (s1x2), (nxtx22), (h_sll_nxtx22s1x2_524x2);
sslauto.
shelve.
ssl_close 2;
exists (vx22), (s1x2), (y12), (h_sll_y12s1x2_b1);
sslauto.
shelve.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.