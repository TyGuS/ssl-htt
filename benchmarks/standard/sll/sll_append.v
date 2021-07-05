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

Lemma pure1 (vx11 : nat) (s1x1 : seq nat) (s2 : seq nat) : ((([:: vx11]) ++ (s1x1)) ++ (s2)) = (([:: vx11]) ++ ((s1x1) ++ (s2))). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.

Definition sll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : seq nat * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists h_sll_x1s1_1 h_sll_x2s2_2,
      h = r :-> (x2) \+ h_sll_x1s1_1 \+ h_sll_x2s2_2 /\ sll x1 s1 h_sll_x1s1_1 /\ sll x2 s2 h_sll_x2s2_2,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (s1, x2, s2) := vghosts in
      exists s y,
      exists h_sll_ys_3,
      (s) == ((s1) ++ (s2)) /\ h = r :-> (y) \+ h_sll_ys_3 /\ sll y s h_sll_ys_3
    ]).

Program Definition sll_append : sll_append_type :=
  Fix (fun (sll_append : sll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x21 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        nxtx11 <-- @read ptr (x1 .+ 1);
        sll_append (nxtx11, r);;
        y11 <-- @read ptr r;
        r ::= x1;;
        (x1 .+ 1) ::= y11;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x1 r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[s1 x2] s2].
ex_elim h_sll_x1s1_1 h_sll_x2s2_2.
move=>[sigma_self].
subst h_self.
move=>[H_sll_x1s1_1 H_sll_x2s2_2].
ssl_ghostelim_post.
try rename h_sll_ys_3 into h_sll_ys1s2_3.
try rename H_sll_ys_3 into H_sll_ys1s2_3.
ssl_read r.
try rename x2 into x21.
try rename h_sll_x2s2_2 into h_sll_x21s2_2.
try rename H_sll_x2s2_2 into H_sll_x21s2_2.
ssl_open ((x1) == (null)) H_sll_x1s1_1.
move=>[phi_sll_x1s1_10].
move=>[sigma_sll_x1s1_1].
subst h_sll_x1s1_1.
try rename h_sll_x1s1_1 into h_sll_x1_1.
try rename H_sll_x1s1_1 into H_sll_x1_1.
try rename h_sll_ys1s2_3 into h_sll_ys2_3.
try rename H_sll_ys1s2_3 into H_sll_ys2_3.
try rename h_sll_ys2_3 into h_sll_x21s2_2.
try rename H_sll_ys2_3 into H_sll_x21s2_2.
ssl_emp;
exists (s2), (x21);
exists (h_sll_x21s2_2);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 nxtx1.
ex_elim h_sll_nxtx1s1x1_0x1.
move=>[phi_sll_x1s1_10].
move=>[sigma_sll_x1s1_1].
subst h_sll_x1s1_1.
move=>H_sll_nxtx1s1x1_0x1.
try rename h_sll_x1s1_1 into h_sll_x1vx1s1x1_1.
try rename H_sll_x1s1_1 into H_sll_x1vx1s1x1_1.
try rename h_sll_ys1s2_3 into h_sll_yvx1s1x1s2_3.
try rename H_sll_ys1s2_3 into H_sll_yvx1s1x1s2_3.
ssl_read x1.
try rename vx1 into vx11.
try rename h_sll_yvx1s1x1s2_3 into h_sll_yvx11s1x1s2_3.
try rename H_sll_yvx1s1x1s2_3 into H_sll_yvx11s1x1s2_3.
try rename h_sll_x1vx1s1x1_1 into h_sll_x1vx11s1x1_1.
try rename H_sll_x1vx1s1x1_1 into H_sll_x1vx11s1x1_1.
ssl_read (x1 .+ 1).
try rename nxtx1 into nxtx11.
try rename h_sll_nxtx1s1x1_0x1 into h_sll_nxtx11s1x1_0x1.
try rename H_sll_nxtx1s1x1_0x1 into H_sll_nxtx11s1x1_0x1.
try rename h_sll_x11s11_11 into h_sll_nxtx11s1x1_0x1.
try rename H_sll_x11s11_11 into H_sll_nxtx11s1x1_0x1.
try rename h_sll_x22s21_21 into h_sll_x21s2_2.
try rename H_sll_x22s21_21 into H_sll_x21s2_2.
ssl_call_pre (r :-> (x21) \+ h_sll_nxtx11s1x1_0x1 \+ h_sll_x21s2_2).
ssl_call (s1x1, x21, s2).
exists (h_sll_nxtx11s1x1_0x1), (h_sll_x21s2_2);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1.
ex_elim h_sll_y1s3_31.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_sll_y1s3_31.
store_valid.
try rename h_sll_y1s3_31 into h_sll_y1s1x1s2_31.
try rename H_sll_y1s3_31 into H_sll_y1s1x1s2_31.
ssl_read r.
try rename y1 into y11.
try rename h_sll_y1s1x1s2_31 into h_sll_y11s1x1s2_31.
try rename H_sll_y1s1x1s2_31 into H_sll_y11s1x1s2_31.
try rename h_sll_nxtys12y_0y into h_sll_y11s1x1s2_31.
try rename H_sll_nxtys12y_0y into H_sll_y11s1x1s2_31.
try rename h_sll_yvx11s1x1s2_3 into h_sll_x1vx11s1x1s2_3.
try rename H_sll_yvx11s1x1s2_3 into H_sll_x1vx11s1x1s2_3.
ssl_write r.
ssl_write_post r.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_emp;
exists ((([:: vx11]) ++ (s1x1)) ++ (s2)), (x1);
exists (x1 :-> (vx11) \+ x1 .+ 1 :-> (y11) \+ h_sll_y11s1x1s2_31);
sslauto.
ssl_close 2;
exists (vx11), ((s1x1) ++ (s2)), (y11), (h_sll_y11s1x1s2_31);
sslauto.
ssl_frame_unfold.
Qed.