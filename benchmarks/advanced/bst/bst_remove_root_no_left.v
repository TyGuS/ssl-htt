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

Lemma pure1 (r1 : ptr) : (r1) = (null) -> ((if (null) == (null) then (if (r1) == (null) then 7 else 7) else 7)) = (7). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (r1 : ptr) : (r1) = (null) -> ((if (r1) == (null) then (if (null) == (null) then 0 else 0) else 0)) = (0). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (sz1r1 : nat) (sz2r1 : nat) : (0) <= (((1) + (sz1r1)) + (sz2r1)) -> (0) <= (sz2r1) -> (0) <= (sz1r1) -> (((1) + (sz1r1)) + (sz2r1)) = (((1) + (sz1r1)) + (sz2r1)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (r1 : ptr) (lo1r1 : nat) (retv : ptr) (hi2r1 : nat) (lo2r1 : nat) (v1 : nat) (hi1r1 : nat) (x : ptr) (vr11 : nat) : ~~ ((x) == (null)) -> (0) <= (vr11) -> ~~ ((retv) == (null)) -> ~~ ((r1) == (null)) -> ~~ ((r1) == (x)) -> (vr11) <= (7) -> (0) <= (v1) -> (hi1r1) <= (vr11) -> ~~ ((r1) == (retv)) -> (v1) <= ((if (vr11) <= (lo1r1) then vr11 else lo1r1)) -> ~~ ((retv) == (x)) -> (v1) <= (7) -> (vr11) <= (lo2r1) -> ((if (r1) == (null) then (if (null) == (null) then 0 else 0) else (if (hi2r1) <= (vr11) then vr11 else hi2r1))) = ((if (hi2r1) <= (vr11) then vr11 else hi2r1)).
  (* intros; hammer. *)
  intros.
  destruct (r1 == null) eqn:H12=>//=.
Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (r1 : ptr) (lo1r1 : nat) (retv : ptr) (lo2r1 : nat) (v1 : nat) (hi1r1 : nat) (x : ptr) (vr11 : nat) : ~~ ((x) == (null)) -> (0) <= (vr11) -> ~~ ((retv) == (null)) -> ~~ ((r1) == (null)) -> ~~ ((r1) == (x)) -> (vr11) <= (7) -> (0) <= (v1) -> (hi1r1) <= (vr11) -> ~~ ((r1) == (retv)) -> (v1) <= ((if (vr11) <= (lo1r1) then vr11 else lo1r1)) -> ~~ ((retv) == (x)) -> (v1) <= (7) -> (vr11) <= (lo2r1) -> ((if (null) == (null) then (if (r1) == (null) then 7 else (if (vr11) <= (lo1r1) then vr11 else lo1r1)) else 7)) = ((if (vr11) <= (lo1r1) then vr11 else lo1r1)).
  (* intros; hammer. *)
  intros.
  destruct (r1 == null) eqn:H12=>//=.
Qed.
Hint Resolve pure6: ssl_pure.

Definition bst_remove_root_no_left_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * nat * ptr * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (0) <= (sz1) /\ (0) <= (sz2) /\ (0) <= (v) /\ (hi1) <= (v) /\ (l) == (null) /\ (v) <= (7) /\ (v) <= (lo2) /\ h = retv :-> (unused) \+ x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists hi lo n1 y,
      exists h_bst_yn1lohi_c,
      (hi) == ((if (r) == (null) then (if (l) == (null) then 0 else hi1) else hi2)) /\ (lo) == ((if (l) == (null) then (if (r) == (null) then 7 else lo2) else lo1)) /\ (n1) == ((sz1) + (sz2)) /\ h = retv :-> (y) \+ h_bst_yn1lohi_c /\ bst y n1 lo hi h_bst_yn1lohi_c
    ]).

Program Definition bst_remove_root_no_left : bst_remove_root_no_left_type :=
  Fix (fun (bst_remove_root_no_left : bst_remove_root_no_left_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused1 <-- @read ptr retv;
      v1 <-- @read nat x;
      r1 <-- @read ptr (x .+ 2);
      if (null) == (null)
      then
        if (r1) == (null)
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
          vr11 <-- @read nat r1;
          lr11 <-- @read ptr (r1 .+ 1);
          rr11 <-- @read ptr (r1 .+ 2);
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= r1;;
          ret tt
      else
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[[[[[[sz1 sz2] v] hi1] l] lo2] lo1] r] hi2] unused].
ex_elim h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3] [phi_self4] [phi_self5] [phi_self6].
move=>[sigma_self].
subst h_self.
move=>[H_bst_lsz1lo1hi1_a H_bst_rsz2lo2hi2_b].
ssl_ghostelim_post.
try rename h_bst_lsz1lo1hi1_a into h_bst_sz1lo1hi1_a.
try rename H_bst_lsz1lo1hi1_a into H_bst_sz1lo1hi1_a.
try rename h_bst_yn1lohi_c into h_bst_yn1lorhi1hi2_c.
try rename H_bst_yn1lohi_c into H_bst_yn1lorhi1hi2_c.
try rename h_bst_yn1lorhi1hi2_c into h_bst_yn1rlo2lo1rhi1hi2_c.
try rename H_bst_yn1lorhi1hi2_c into H_bst_yn1rlo2lo1rhi1hi2_c.
try rename h_bst_yn1rlo2lo1rhi1hi2_c into h_bst_ysz1sz2rlo2lo1rhi1hi2_c.
try rename H_bst_yn1rlo2lo1rhi1hi2_c into H_bst_ysz1sz2rlo2lo1rhi1hi2_c.
ssl_read retv.
try rename unused into unused1.
ssl_read x.
try rename v into v1.
ssl_read (x .+ 2).
try rename r into r1.
try rename h_bst_ysz1sz2rlo2lo1rhi1hi2_c into h_bst_ysz1sz2r1lo2lo1r1hi1hi2_c.
try rename H_bst_ysz1sz2rlo2lo1rhi1hi2_c into H_bst_ysz1sz2r1lo2lo1r1hi1hi2_c.
try rename h_bst_rsz2lo2hi2_b into h_bst_r1sz2lo2hi2_b.
try rename H_bst_rsz2lo2hi2_b into H_bst_r1sz2lo2hi2_b.
ssl_open ((null) == (null)) H_bst_sz1lo1hi1_a.
move=>[phi_bst_sz1lo1hi1_a0] [phi_bst_sz1lo1hi1_a1] [phi_bst_sz1lo1hi1_a2].
move=>[sigma_bst_sz1lo1hi1_a].
subst h_bst_sz1lo1hi1_a.
try rename h_bst_ysz1sz2r1lo2lo1r1hi1hi2_c into h_bst_ysz1sz2r1lo2lo1r1hi2_c.
try rename H_bst_ysz1sz2r1lo2lo1r1hi1hi2_c into H_bst_ysz1sz2r1lo2lo1r1hi2_c.
try rename h_bst_sz1lo1hi1_a into h_bst_sz1lo1_a.
try rename H_bst_sz1lo1hi1_a into H_bst_sz1lo1_a.
try rename h_bst_ysz1sz2r1lo2lo1r1hi2_c into h_bst_ysz1sz2r1lo2r1hi2_c.
try rename H_bst_ysz1sz2r1lo2lo1r1hi2_c into H_bst_ysz1sz2r1lo2r1hi2_c.
try rename h_bst_sz1lo1_a into h_bst_sz1_a.
try rename H_bst_sz1lo1_a into H_bst_sz1_a.
try rename h_bst_ysz1sz2r1lo2r1hi2_c into h_bst_ysz2r1lo2r1hi2_c.
try rename H_bst_ysz1sz2r1lo2r1hi2_c into H_bst_ysz2r1lo2r1hi2_c.
try rename h_bst_sz1_a into h_bst__a.
try rename H_bst_sz1_a into H_bst__a.
ssl_open ((r1) == (null)) H_bst_r1sz2lo2hi2_b.
move=>[phi_bst_r1sz2lo2hi2_b0] [phi_bst_r1sz2lo2hi2_b1] [phi_bst_r1sz2lo2hi2_b2].
move=>[sigma_bst_r1sz2lo2hi2_b].
subst h_bst_r1sz2lo2hi2_b.
try rename h_bst_ysz2r1lo2r1hi2_c into h_bst_ysz2r1lo2r1_c.
try rename H_bst_ysz2r1lo2r1hi2_c into H_bst_ysz2r1lo2r1_c.
try rename h_bst_r1sz2lo2hi2_b into h_bst_r1sz2lo2_b.
try rename H_bst_r1sz2lo2hi2_b into H_bst_r1sz2lo2_b.
try rename h_bst_r1sz2lo2_b into h_bst_r1sz2_b.
try rename H_bst_r1sz2lo2_b into H_bst_r1sz2_b.
try rename h_bst_ysz2r1lo2r1_c into h_bst_ysz2r1r1_c.
try rename H_bst_ysz2r1lo2r1_c into H_bst_ysz2r1r1_c.
try rename h_bst_r1sz2_b into h_bst_r1_b.
try rename H_bst_r1sz2_b into H_bst_r1_b.
try rename h_bst_ysz2r1r1_c into h_bst_yr1r1_c.
try rename H_bst_ysz2r1r1_c into H_bst_yr1r1_c.
try rename h_bst_yr1r1_c into h_bst_r1r1_c.
try rename H_bst_yr1r1_c into H_bst_r1r1_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (r1) == (null) then (if (null) == (null) then 0 else 0) else 0)), ((if (null) == (null) then (if (r1) == (null) then 7 else 7) else 7)), ((0) + (0)), (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1r1 sz2r1 vr1 hi2r1 hi1r1.
ex_elim lo1r1 lo2r1 lr1 rr1.
ex_elim h_bst_lr1sz1r1lo1r1hi1r1_0r1 h_bst_rr1sz2r1lo2r1hi2r1_1r1.
move=>[phi_bst_r1sz2lo2hi2_b0] [phi_bst_r1sz2lo2hi2_b1] [phi_bst_r1sz2lo2hi2_b2] [phi_bst_r1sz2lo2hi2_b3] [phi_bst_r1sz2lo2hi2_b4] [phi_bst_r1sz2lo2hi2_b5] [phi_bst_r1sz2lo2hi2_b6] [phi_bst_r1sz2lo2hi2_b7] [phi_bst_r1sz2lo2hi2_b8].
move=>[sigma_bst_r1sz2lo2hi2_b].
subst h_bst_r1sz2lo2hi2_b.
move=>[H_bst_lr1sz1r1lo1r1hi1r1_0r1 H_bst_rr1sz2r1lo2r1hi2r1_1r1].
try rename h_bst_ysz2r1lo2r1hi2_c into h_bst_ysz2r1lo2r1hi2r1vr1vr1hi2r1_c.
try rename H_bst_ysz2r1lo2r1hi2_c into H_bst_ysz2r1lo2r1hi2r1vr1vr1hi2r1_c.
try rename h_bst_r1sz2lo2hi2_b into h_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2lo2hi2_b into H_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b.
try rename h_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b into h_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b into H_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename h_bst_ysz2r1lo2r1hi2r1vr1vr1hi2r1_c into h_bst_ysz2r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c.
try rename H_bst_ysz2r1lo2r1hi2r1vr1vr1hi2r1_c into H_bst_ysz2r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c.
try rename h_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into h_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into H_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename h_bst_ysz2r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c into h_bst_ysz1r1sz2r1r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c.
try rename H_bst_ysz2r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c into H_bst_ysz1r1sz2r1r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c.
ssl_read r1.
try rename vr1 into vr11.
try rename h_bst_ysz1r1sz2r1r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c into h_bst_ysz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c.
try rename H_bst_ysz1r1sz2r1r1vr1lo1r1vr1lo1r1r1hi2r1vr1vr1hi2r1_c into H_bst_ysz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c.
try rename h_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into h_bst_r1sz1r1sz2r1vr11lo1r1vr11lo1r1hi2r1vr11vr11hi2r1_b.
try rename H_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into H_bst_r1sz1r1sz2r1vr11lo1r1vr11lo1r1hi2r1vr11vr11hi2r1_b.
ssl_read (r1 .+ 1).
try rename lr1 into lr11.
try rename h_bst_lr1sz1r1lo1r1hi1r1_0r1 into h_bst_lr11sz1r1lo1r1hi1r1_0r1.
try rename H_bst_lr1sz1r1lo1r1hi1r1_0r1 into H_bst_lr11sz1r1lo1r1hi1r1_0r1.
ssl_read (r1 .+ 2).
try rename rr1 into rr11.
try rename h_bst_rr1sz2r1lo2r1hi2r1_1r1 into h_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename H_bst_rr1sz2r1lo2r1hi2r1_1r1 into H_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename h_bst_l1ysz11ylo11yhi11y_0y into h_bst_lr11sz1r1lo1r1hi1r1_0r1.
try rename H_bst_l1ysz11ylo11yhi11y_0y into H_bst_lr11sz1r1lo1r1hi1r1_0r1.
try rename h_bst_r2ysz21ylo21yhi21y_1y into h_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename H_bst_r2ysz21ylo21yhi21y_1y into H_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename h_bst_ysz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c into h_bst_r1sz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c.
try rename H_bst_ysz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c into H_bst_r1sz1r1sz2r1r1vr11lo1r1vr11lo1r1r1hi2r1vr11vr11hi2r1_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (r1) == (null) then (if (null) == (null) then 0 else 0) else (if (hi2r1) <= (vr11) then vr11 else hi2r1))), ((if (null) == (null) then (if (r1) == (null) then 7 else (if (vr11) <= (lo1r1) then vr11 else lo1r1)) else 7)), ((0) + (((1) + (sz1r1)) + (sz2r1))), (r1);
exists (r1 :-> (vr11) \+ r1 .+ 1 :-> (lr11) \+ r1 .+ 2 :-> (rr11) \+ h_bst_lr11sz1r1lo1r1hi1r1_0r1 \+ h_bst_rr11sz2r1lo2r1hi2r1_1r1);
sslauto.
ssl_close 2;
exists (sz1r1), (sz2r1), (vr11), (hi2r1), (hi1r1), (lo1r1), (lo2r1), (lr11), (rr11), (h_bst_lr11sz1r1lo1r1hi1r1_0r1), (h_bst_rr11sz2r1lo2r1hi2r1_1r1);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
ex_elim sz10 sz20 v0 hi20 hi10.
ex_elim lo10 lo20 l0 r0.
ex_elim h_bst_l0sz10lo10hi10_00 h_bst_r0sz20lo20hi20_10.
move=>[phi_bst_sz1lo1hi1_a0] [phi_bst_sz1lo1hi1_a1] [phi_bst_sz1lo1hi1_a2] [phi_bst_sz1lo1hi1_a3] [phi_bst_sz1lo1hi1_a4] [phi_bst_sz1lo1hi1_a5] [phi_bst_sz1lo1hi1_a6] [phi_bst_sz1lo1hi1_a7] [phi_bst_sz1lo1hi1_a8].
move=>[sigma_bst_sz1lo1hi1_a].
subst h_bst_sz1lo1hi1_a.
move=>[H_bst_l0sz10lo10hi10_00 H_bst_r0sz20lo20hi20_10].
ssl_inconsistency.
Qed.
