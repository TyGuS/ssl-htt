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

Lemma pure27 (vx12 : nat) (s1x1 : seq nat) (s2 : seq nat) : ((([:: vx12]) ++ (s1x1)) ++ (s2)) = (([:: vx12]) ++ ((s1x1) ++ (s2))). intros; hammer. Qed.
Hint Resolve pure27: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_528 h_sll_x2s2_529,
      h = r :-> x2 \+ h_sll_x1s1_528 \+ h_sll_x2s2_529 /\ sll x1 s1 h_sll_x1s1_528 /\ sll x2 s2 h_sll_x2s2_529,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_530,
      (s) == ((s1) ++ (s2)) /\ h = r :-> y \+ h_sll_ys_530 /\ sll y s h_sll_ys_530
    ]).

Program Definition sll_append : sll_append_type :=
  Fix (fun (sll_append : sll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x22 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx12 <-- @read nat x1;
        nxtx12 <-- @read ptr (x1 .+ 1);
        sll_append (nxtx12, r);;
        y12 <-- @read ptr r;
        (x1 .+ 1) ::= y12;;
        r ::= x1;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x1 r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[s1 x2] s2].
ex_elim h_sll_x1s1_528 h_sll_x2s2_529.
move=>[sigma_self].
subst h_self.
move=>[H_sll_x1s1_528 H_sll_x2s2_529].
ssl_ghostelim_post.
try rename h_sll_ys_530 into h_sll_ys1s2_530.
try rename H_sll_ys_530 into H_sll_ys1s2_530.
ssl_read r.
try rename x2 into x22.
try rename h_sll_x2s2_529 into h_sll_x22s2_529.
try rename H_sll_x2s2_529 into H_sll_x22s2_529.
ssl_open ((x1) == (null)) H_sll_x1s1_528.
move=>[phi_sll_x1s1_5280].
move=>[sigma_sll_x1s1_528].
subst h_sll_x1s1_528.
try rename h_sll_x1s1_528 into h_sll_x1_528.
try rename H_sll_x1s1_528 into H_sll_x1_528.
try rename h_sll_ys1s2_530 into h_sll_ys2_530.
try rename H_sll_ys1s2_530 into H_sll_ys2_530.
try rename h_sll_ys2_530 into h_sll_x22s2_529.
try rename H_sll_ys2_530 into H_sll_x22s2_529.
ssl_emp;
exists (s2), (x22);
exists (h_sll_x22s2_529);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 nxtx1.
ex_elim h_sll_nxtx1s1x1_527x1.
move=>[phi_sll_x1s1_5280].
move=>[sigma_sll_x1s1_528].
subst h_sll_x1s1_528.
move=>H_sll_nxtx1s1x1_527x1.
try rename h_sll_x1s1_528 into h_sll_x1vx1s1x1_528.
try rename H_sll_x1s1_528 into H_sll_x1vx1s1x1_528.
try rename h_sll_ys1s2_530 into h_sll_yvx1s1x1s2_530.
try rename H_sll_ys1s2_530 into H_sll_yvx1s1x1s2_530.
ssl_read x1.
try rename vx1 into vx12.
try rename h_sll_yvx1s1x1s2_530 into h_sll_yvx12s1x1s2_530.
try rename H_sll_yvx1s1x1s2_530 into H_sll_yvx12s1x1s2_530.
try rename h_sll_x1vx1s1x1_528 into h_sll_x1vx12s1x1_528.
try rename H_sll_x1vx1s1x1_528 into H_sll_x1vx12s1x1_528.
ssl_read (x1 .+ 1).
try rename nxtx1 into nxtx12.
try rename h_sll_nxtx1s1x1_527x1 into h_sll_nxtx12s1x1_527x1.
try rename H_sll_nxtx1s1x1_527x1 into H_sll_nxtx12s1x1_527x1.
try rename h_sll_x11s11_5281 into h_sll_nxtx12s1x1_527x1.
try rename H_sll_x11s11_5281 into H_sll_nxtx12s1x1_527x1.
try rename h_sll_x21s21_5291 into h_sll_x22s2_529.
try rename H_sll_x21s21_5291 into H_sll_x22s2_529.
ssl_call_pre (r :-> x22 \+ h_sll_nxtx12s1x1_527x1 \+ h_sll_x22s2_529).
ssl_call (s1x1, x22, s2).
exists (h_sll_nxtx12s1x1_527x1), (h_sll_x22s2_529);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1.
ex_elim h_sll_y1s3_5301.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s3_5301.
store_valid.
try rename h_sll_y1s3_5301 into h_sll_y1s1x1s2_5301.
try rename H_sll_y1s3_5301 into H_sll_y1s1x1s2_5301.
ssl_read r.
try rename y1 into y12.
try rename h_sll_y1s1x1s2_5301 into h_sll_y12s1x1s2_5301.
try rename H_sll_y1s1x1s2_5301 into H_sll_y12s1x1s2_5301.
try rename h_sll_nxtys12y_527y into h_sll_y12s1x1s2_5301.
try rename H_sll_nxtys12y_527y into H_sll_y12s1x1s2_5301.
try rename h_sll_yvx12s1x1s2_530 into h_sll_x1vx12s1x1s2_530.
try rename H_sll_yvx12s1x1s2_530 into H_sll_x1vx12s1x1s2_530.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ h_sll_y12s1x1s2_5301);
sslauto.
ssl_close 2;
exists (vx12), ((s1x1) ++ (s2)), (y12), (h_sll_y12s1x1s2_5301);
sslauto.
ssl_frame_unfold.
Qed.