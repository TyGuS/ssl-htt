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

Lemma pure1 (l1 : ptr) : (l1) = (null) -> ((if (null) == (null) then (if (l1) == (null) then 0 else 0) else 0)) = (0). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (l1 : ptr) : (l1) = (null) -> ((if (l1) == (null) then (if (null) == (null) then 7 else 7) else 7)) = (7). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (sz1l1 : nat) (sz2l1 : nat) : (0) <= (((1) + (sz1l1)) + (sz2l1)) -> (0) <= (sz1l1) -> (0) <= (sz2l1) -> (((1) + (sz1l1)) + (sz2l1)) = (((1) + (sz1l1)) + (sz2l1)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (hi2l1 : nat) (hi1l1 : nat) (lo1l1 : nat) (l1 : ptr) (retv : ptr) (v1 : nat) (lo2l1 : nat) (x : ptr) (vl11 : nat) : ((if (hi2l1) <= (vl11) then vl11 else hi2l1)) <= (v1) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (vl11) <= (lo2l1) -> (0) <= (vl11) -> ~~ ((l1) == (null)) -> ~~ ((l1) == (retv)) -> (0) <= (v1) -> ~~ ((l1) == (x)) -> (vl11) <= (7) -> (hi1l1) <= (vl11) -> ~~ ((retv) == (x)) -> (v1) <= (7) -> ((if (l1) == (null) then (if (null) == (null) then 7 else 7) else (if (vl11) <= (lo1l1) then vl11 else lo1l1))) = ((if (vl11) <= (lo1l1) then vl11 else lo1l1)).
  (* intros; hammer. *)
  intros.
  destruct (l1 == null) eqn:H12=>//=.
Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (hi2l1 : nat) (hi1l1 : nat) (l1 : ptr) (retv : ptr) (v1 : nat) (lo2l1 : nat) (x : ptr) (vl11 : nat) : ((if (hi2l1) <= (vl11) then vl11 else hi2l1)) <= (v1) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (vl11) <= (lo2l1) -> (0) <= (vl11) -> ~~ ((l1) == (null)) -> ~~ ((l1) == (retv)) -> (0) <= (v1) -> ~~ ((l1) == (x)) -> (vl11) <= (7) -> (hi1l1) <= (vl11) -> ~~ ((retv) == (x)) -> (v1) <= (7) -> ((if (null) == (null) then (if (l1) == (null) then 0 else (if (hi2l1) <= (vl11) then vl11 else hi2l1)) else 0)) = ((if (hi2l1) <= (vl11) then vl11 else hi2l1)).
  (* intros; hammer. *)
  intros.
  destruct (l1 == null) eqn:H12=>//=.
Qed.
Hint Resolve pure6: ssl_pure.

Definition bst_remove_root_no_right_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * ptr * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (0) <= (sz1) /\ (0) <= (sz2) /\ (0) <= (v) /\ (hi1) <= (v) /\ (r) == (null) /\ (v) <= (7) /\ (v) <= (lo2) /\ h = retv :-> (unused) \+ x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists hi lo n1 y,
      exists h_bst_yn1lohi_c,
      (hi) == ((if (r) == (null) then (if (l) == (null) then 0 else hi1) else hi2)) /\ (lo) == ((if (l) == (null) then (if (r) == (null) then 7 else lo2) else lo1)) /\ (n1) == ((sz1) + (sz2)) /\ h = retv :-> (y) \+ h_bst_yn1lohi_c /\ bst y n1 lo hi h_bst_yn1lohi_c
    ]).

Program Definition bst_remove_root_no_right : bst_remove_root_no_right_type :=
  Fix (fun (bst_remove_root_no_right : bst_remove_root_no_right_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused1 <-- @read ptr retv;
      v1 <-- @read nat x;
      l1 <-- @read ptr (x .+ 1);
      if (null) == (null)
      then
        if (l1) == (null)
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
          vl11 <-- @read nat l1;
          ll11 <-- @read ptr (l1 .+ 1);
          rl11 <-- @read ptr (l1 .+ 2);
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= l1;;
          ret tt
      else
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[[[[[[sz1 sz2] v] hi1] r] lo2] l] lo1] hi2] unused].
ex_elim h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3] [phi_self4] [phi_self5] [phi_self6].
move=>[sigma_self].
subst h_self.
move=>[H_bst_lsz1lo1hi1_a H_bst_rsz2lo2hi2_b].
ssl_ghostelim_post.
try rename h_bst_rsz2lo2hi2_b into h_bst_sz2lo2hi2_b.
try rename H_bst_rsz2lo2hi2_b into H_bst_sz2lo2hi2_b.
try rename h_bst_yn1lohi_c into h_bst_yn1lolhi1hi2_c.
try rename H_bst_yn1lohi_c into H_bst_yn1lolhi1hi2_c.
try rename h_bst_yn1lolhi1hi2_c into h_bst_yn1llo2lo1lhi1hi2_c.
try rename H_bst_yn1lolhi1hi2_c into H_bst_yn1llo2lo1lhi1hi2_c.
try rename h_bst_yn1llo2lo1lhi1hi2_c into h_bst_ysz1sz2llo2lo1lhi1hi2_c.
try rename H_bst_yn1llo2lo1lhi1hi2_c into H_bst_ysz1sz2llo2lo1lhi1hi2_c.
ssl_read retv.
try rename unused into unused1.
ssl_read x.
try rename v into v1.
ssl_read (x .+ 1).
try rename l into l1.
try rename h_bst_ysz1sz2llo2lo1lhi1hi2_c into h_bst_ysz1sz2l1lo2lo1l1hi1hi2_c.
try rename H_bst_ysz1sz2llo2lo1lhi1hi2_c into H_bst_ysz1sz2l1lo2lo1l1hi1hi2_c.
try rename h_bst_lsz1lo1hi1_a into h_bst_l1sz1lo1hi1_a.
try rename H_bst_lsz1lo1hi1_a into H_bst_l1sz1lo1hi1_a.
ssl_open ((null) == (null)) H_bst_sz2lo2hi2_b.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
try rename h_bst_sz2lo2hi2_b into h_bst_sz2lo2_b.
try rename H_bst_sz2lo2hi2_b into H_bst_sz2lo2_b.
try rename h_bst_ysz1sz2l1lo2lo1l1hi1hi2_c into h_bst_ysz1sz2l1lo2lo1l1hi1_c.
try rename H_bst_ysz1sz2l1lo2lo1l1hi1hi2_c into H_bst_ysz1sz2l1lo2lo1l1hi1_c.
try rename h_bst_ysz1sz2l1lo2lo1l1hi1_c into h_bst_ysz1sz2l1lo1l1hi1_c.
try rename H_bst_ysz1sz2l1lo2lo1l1hi1_c into H_bst_ysz1sz2l1lo1l1hi1_c.
try rename h_bst_sz2lo2_b into h_bst_sz2_b.
try rename H_bst_sz2lo2_b into H_bst_sz2_b.
try rename h_bst_sz2_b into h_bst__b.
try rename H_bst_sz2_b into H_bst__b.
try rename h_bst_ysz1sz2l1lo1l1hi1_c into h_bst_ysz1l1lo1l1hi1_c.
try rename H_bst_ysz1sz2l1lo1l1hi1_c into H_bst_ysz1l1lo1l1hi1_c.
ssl_open ((l1) == (null)) H_bst_l1sz1lo1hi1_a.
move=>[phi_bst_l1sz1lo1hi1_a0] [phi_bst_l1sz1lo1hi1_a1] [phi_bst_l1sz1lo1hi1_a2].
move=>[sigma_bst_l1sz1lo1hi1_a].
subst h_bst_l1sz1lo1hi1_a.
try rename h_bst_l1sz1lo1hi1_a into h_bst_l1sz1lo1_a.
try rename H_bst_l1sz1lo1hi1_a into H_bst_l1sz1lo1_a.
try rename h_bst_ysz1l1lo1l1hi1_c into h_bst_ysz1l1lo1l1_c.
try rename H_bst_ysz1l1lo1l1hi1_c into H_bst_ysz1l1lo1l1_c.
try rename h_bst_ysz1l1lo1l1_c into h_bst_ysz1l1l1_c.
try rename H_bst_ysz1l1lo1l1_c into H_bst_ysz1l1l1_c.
try rename h_bst_l1sz1lo1_a into h_bst_l1sz1_a.
try rename H_bst_l1sz1lo1_a into H_bst_l1sz1_a.
try rename h_bst_l1sz1_a into h_bst_l1_a.
try rename H_bst_l1sz1_a into H_bst_l1_a.
try rename h_bst_ysz1l1l1_c into h_bst_yl1l1_c.
try rename H_bst_ysz1l1l1_c into H_bst_yl1l1_c.
try rename h_bst_yl1l1_c into h_bst_l1l1_c.
try rename H_bst_yl1l1_c into H_bst_l1l1_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (null) == (null) then (if (l1) == (null) then 0 else 0) else 0)), ((if (l1) == (null) then (if (null) == (null) then 7 else 7) else 7)), ((0) + (0)), (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1l1 sz2l1 vl1 hi2l1 hi1l1.
ex_elim lo1l1 lo2l1 ll1 rl1.
ex_elim h_bst_ll1sz1l1lo1l1hi1l1_0l1 h_bst_rl1sz2l1lo2l1hi2l1_1l1.
move=>[phi_bst_l1sz1lo1hi1_a0] [phi_bst_l1sz1lo1hi1_a1] [phi_bst_l1sz1lo1hi1_a2] [phi_bst_l1sz1lo1hi1_a3] [phi_bst_l1sz1lo1hi1_a4] [phi_bst_l1sz1lo1hi1_a5] [phi_bst_l1sz1lo1hi1_a6] [phi_bst_l1sz1lo1hi1_a7] [phi_bst_l1sz1lo1hi1_a8].
move=>[sigma_bst_l1sz1lo1hi1_a].
subst h_bst_l1sz1lo1hi1_a.
move=>[H_bst_ll1sz1l1lo1l1hi1l1_0l1 H_bst_rl1sz2l1lo2l1hi2l1_1l1].
try rename h_bst_l1sz1lo1hi1_a into h_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1lo1hi1_a into H_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a.
try rename h_bst_ysz1l1lo1l1hi1_c into h_bst_ysz1l1lo1l1hi2l1vl1vl1hi2l1_c.
try rename H_bst_ysz1l1lo1l1hi1_c into H_bst_ysz1l1lo1l1hi2l1vl1vl1hi2l1_c.
try rename h_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename h_bst_ysz1l1lo1l1hi2l1vl1vl1hi2l1_c into h_bst_ysz1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c.
try rename H_bst_ysz1l1lo1l1hi2l1vl1vl1hi2l1_c into H_bst_ysz1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c.
try rename h_bst_ysz1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c into h_bst_ysz1l1sz2l1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c.
try rename H_bst_ysz1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c into H_bst_ysz1l1sz2l1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c.
try rename h_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
ssl_read l1.
try rename vl1 into vl11.
try rename h_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1l1sz2l1vl11lo1l1vl11lo1l1hi2l1vl11vl11hi2l1_a.
try rename H_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1l1sz2l1vl11lo1l1vl11lo1l1hi2l1vl11vl11hi2l1_a.
try rename h_bst_ysz1l1sz2l1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c into h_bst_ysz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c.
try rename H_bst_ysz1l1sz2l1l1vl1lo1l1vl1lo1l1l1hi2l1vl1vl1hi2l1_c into H_bst_ysz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c.
ssl_read (l1 .+ 1).
try rename ll1 into ll11.
try rename h_bst_ll1sz1l1lo1l1hi1l1_0l1 into h_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename H_bst_ll1sz1l1lo1l1hi1l1_0l1 into H_bst_ll11sz1l1lo1l1hi1l1_0l1.
ssl_read (l1 .+ 2).
try rename rl1 into rl11.
try rename h_bst_rl1sz2l1lo2l1hi2l1_1l1 into h_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename H_bst_rl1sz2l1lo2l1hi2l1_1l1 into H_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename h_bst_l2ysz11ylo11yhi11y_0y into h_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename H_bst_l2ysz11ylo11yhi11y_0y into H_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename h_bst_r1ysz21ylo21yhi21y_1y into h_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename H_bst_r1ysz21ylo21yhi21y_1y into H_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename h_bst_ysz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c into h_bst_l1sz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c.
try rename H_bst_ysz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c into H_bst_l1sz1l1sz2l1l1vl11lo1l1vl11lo1l1l1hi2l1vl11vl11hi2l1_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (null) == (null) then (if (l1) == (null) then 0 else (if (hi2l1) <= (vl11) then vl11 else hi2l1)) else 0)), ((if (l1) == (null) then (if (null) == (null) then 7 else 7) else (if (vl11) <= (lo1l1) then vl11 else lo1l1))), ((((1) + (sz1l1)) + (sz2l1)) + (0)), (l1);
exists (l1 :-> (vl11) \+ l1 .+ 1 :-> (ll11) \+ l1 .+ 2 :-> (rl11) \+ h_bst_ll11sz1l1lo1l1hi1l1_0l1 \+ h_bst_rl11sz2l1lo2l1hi2l1_1l1);
sslauto.
ssl_close 2;
exists (sz1l1), (sz2l1), (vl11), (hi2l1), (hi1l1), (lo1l1), (lo2l1), (ll11), (rl11), (h_bst_ll11sz1l1lo1l1hi1l1_0l1), (h_bst_rl11sz2l1lo2l1hi2l1_1l1);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
ex_elim sz10 sz20 v0 hi20 hi10.
ex_elim lo10 lo20 l0 r0.
ex_elim h_bst_l0sz10lo10hi10_00 h_bst_r0sz20lo20hi20_10.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2] [phi_bst_sz2lo2hi2_b3] [phi_bst_sz2lo2hi2_b4] [phi_bst_sz2lo2hi2_b5] [phi_bst_sz2lo2hi2_b6] [phi_bst_sz2lo2hi2_b7] [phi_bst_sz2lo2hi2_b8].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
move=>[H_bst_l0sz10lo10hi10_00 H_bst_r0sz20lo20hi20_10].
ssl_inconsistency.
Qed.
