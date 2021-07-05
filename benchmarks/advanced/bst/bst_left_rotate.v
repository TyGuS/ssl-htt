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

Lemma pure1 (sz1 : nat) (sz1r1 : nat) (sz2r1 : nat) : (0) <= (sz2r1) -> (0) <= (((1) + (sz1r1)) + (sz2r1)) -> (0) <= (sz1) -> (0) <= (sz1r1) -> (0) <= (((1) + (sz1)) + (sz1r1)). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (sz1 : nat) (sz1r1 : nat) (sz2r1 : nat) : (0) <= (sz2r1) -> (0) <= (((1) + (sz1r1)) + (sz2r1)) -> (0) <= (sz1) -> (0) <= (sz1r1) -> ((((1) + (sz1)) + (sz1r1)) + (sz2r1)) = ((sz1) + (((1) + (sz1r1)) + (sz2r1))). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (lo1r1 : nat) (hi1 : nat) (lo2r1 : nat) (v1 : nat) (hi1r1 : nat) (vr11 : nat) : (0) <= (vr11) -> (vr11) <= (7) -> (0) <= (v1) -> (hi1) <= (v1) -> (hi1r1) <= (vr11) -> (v1) <= ((if (vr11) <= (lo1r1) then vr11 else lo1r1)) -> (v1) <= (7) -> (vr11) <= (lo2r1) -> (v1) <= (lo1r1).
  (* intros; hammer. *)
  intros.
  destruct (vr11 <= lo1r1) eqn:H7=>//.
  apply: (leq_trans H4)=>//.
Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (lo1r1 : nat) (hi1 : nat) (lo2r1 : nat) (v1 : nat) (hi1r1 : nat) (vr11 : nat) : (0) <= (vr11) -> (vr11) <= (7) -> (0) <= (v1) -> (hi1) <= (v1) -> (hi1r1) <= (vr11) -> (v1) <= ((if (vr11) <= (lo1r1) then vr11 else lo1r1)) -> (v1) <= (7) -> (vr11) <= (lo2r1) -> ((if (hi1r1) <= (v1) then v1 else hi1r1)) <= (vr11).
  (* intros; hammer. *)
  intros.
  case (hi1r1 <= v1); last by done.
  destruct (vr11 <= lo1r1) eqn:H7; first by done.
  apply negbT in H7.
  rewrite -ltnNge in H7.
  apply ltnW.
  exact (leq_ltn_trans H4 H7).
Qed.
Hint Resolve pure4: ssl_pure.

Definition bst_left_rotate_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * ptr * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (0) <= (sz1) /\ (0) <= (sz2) /\ (0) <= (v) /\ (hi1) <= (v) /\ ~~ ((r) == (null)) /\ (v) <= (7) /\ (v) <= (lo2) /\ h = retv :-> (unused) \+ x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists sz3 sz4 v3 hi3 lo4 lo3 r3 hi4 y,
      exists h_bst_xsz3lo3hi3_2 h_bst_r3sz4lo4hi4_3,
      (0) <= (sz3) /\ (0) <= (sz4) /\ (0) <= (v3) /\ (hi3) <= (v3) /\ ((sz3) + (sz4)) == ((sz1) + (sz2)) /\ (v3) <= (7) /\ (v3) <= (lo4) /\ h = retv :-> (y) \+ y :-> (v3) \+ y .+ 1 :-> (x) \+ y .+ 2 :-> (r3) \+ h_bst_xsz3lo3hi3_2 \+ h_bst_r3sz4lo4hi4_3 /\ bst x sz3 lo3 hi3 h_bst_xsz3lo3hi3_2 /\ bst r3 sz4 lo4 hi4 h_bst_r3sz4lo4hi4_3
    ]).

Program Definition bst_left_rotate : bst_left_rotate_type :=
  Fix (fun (bst_left_rotate : bst_left_rotate_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused1 <-- @read ptr retv;
      v1 <-- @read nat x;
      l1 <-- @read ptr (x .+ 1);
      r1 <-- @read ptr (x .+ 2);
      if (r1) == (null)
      then
        ret tt
      else
        vr11 <-- @read nat r1;
        lr11 <-- @read ptr (r1 .+ 1);
        rr11 <-- @read ptr (r1 .+ 2);
        (r1 .+ 1) ::= x;;
        (x .+ 2) ::= lr11;;
        retv ::= r1;;
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
ssl_read retv.
try rename unused into unused1.
ssl_read x.
try rename v into v1.
ssl_read (x .+ 1).
try rename l into l1.
try rename h_bst_lsz1lo1hi1_a into h_bst_l1sz1lo1hi1_a.
try rename H_bst_lsz1lo1hi1_a into H_bst_l1sz1lo1hi1_a.
ssl_read (x .+ 2).
try rename r into r1.
try rename h_bst_rsz2lo2hi2_b into h_bst_r1sz2lo2hi2_b.
try rename H_bst_rsz2lo2hi2_b into H_bst_r1sz2lo2hi2_b.
ssl_open ((r1) == (null)) H_bst_r1sz2lo2hi2_b.
move=>[phi_bst_r1sz2lo2hi2_b0] [phi_bst_r1sz2lo2hi2_b1] [phi_bst_r1sz2lo2hi2_b2].
move=>[sigma_bst_r1sz2lo2hi2_b].
subst h_bst_r1sz2lo2hi2_b.
ssl_inconsistency.
ex_elim sz1r1 sz2r1 vr1 hi2r1 hi1r1.
ex_elim lo1r1 lo2r1 lr1 rr1.
ex_elim h_bst_lr1sz1r1lo1r1hi1r1_0r1 h_bst_rr1sz2r1lo2r1hi2r1_1r1.
move=>[phi_bst_r1sz2lo2hi2_b0] [phi_bst_r1sz2lo2hi2_b1] [phi_bst_r1sz2lo2hi2_b2] [phi_bst_r1sz2lo2hi2_b3] [phi_bst_r1sz2lo2hi2_b4] [phi_bst_r1sz2lo2hi2_b5] [phi_bst_r1sz2lo2hi2_b6] [phi_bst_r1sz2lo2hi2_b7] [phi_bst_r1sz2lo2hi2_b8].
move=>[sigma_bst_r1sz2lo2hi2_b].
subst h_bst_r1sz2lo2hi2_b.
move=>[H_bst_lr1sz1r1lo1r1hi1r1_0r1 H_bst_rr1sz2r1lo2r1hi2r1_1r1].
try rename h_bst_r1sz2lo2hi2_b into h_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2lo2hi2_b into H_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b.
try rename h_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b into h_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2lo2hi2r1vr1vr1hi2r1_b into H_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename h_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into h_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
try rename H_bst_r1sz2vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b into H_bst_r1sz1r1sz2r1vr1lo1r1vr1lo1r1hi2r1vr1vr1hi2r1_b.
ssl_read r1.
try rename vr1 into vr11.
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
try rename h_bst_xsz3lo3hi3_2 into h_bst_xsz3lo3hi21xv2xv2xhi21x_2.
try rename H_bst_xsz3lo3hi3_2 into H_bst_xsz3lo3hi21xv2xv2xhi21x_2.
try rename h_bst_xsz3lo3hi21xv2xv2xhi21x_2 into h_bst_xsz3v2xlo11xv2xlo11xhi21xv2xv2xhi21x_2.
try rename H_bst_xsz3lo3hi21xv2xv2xhi21x_2 into H_bst_xsz3v2xlo11xv2xlo11xhi21xv2xv2xhi21x_2.
try rename h_bst_xsz3v2xlo11xv2xlo11xhi21xv2xv2xhi21x_2 into h_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_2.
try rename H_bst_xsz3v2xlo11xv2xlo11xhi21xv2xv2xhi21x_2 into H_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_2.
try rename h_bst_r3sz4lo4hi4_3 into h_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename H_bst_r3sz4lo4hi4_3 into H_bst_rr11sz2r1lo2r1hi2r1_1r1.
try rename h_bst_l2xsz11xlo11xhi11x_0x into h_bst_l1sz1lo1hi1_a.
try rename H_bst_l2xsz11xlo11xhi11x_0x into H_bst_l1sz1lo1hi1_a.
try rename h_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_2 into h_bst_xsz11xsz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2.
try rename H_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_2 into H_bst_xsz11xsz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2.
try rename h_bst_xsz11xsz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2 into h_bst_xsz1sz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2.
try rename H_bst_xsz11xsz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2 into H_bst_xsz1sz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2.
try rename h_bst_r2xsz21xlo21xhi21x_1x into h_bst_lr11sz1r1lo1r1hi1r1_0r1.
try rename H_bst_r2xsz21xlo21xhi21x_1x into H_bst_lr11sz1r1lo1r1hi1r1_0r1.
try rename h_bst_xsz1sz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2 into h_bst_xsz1sz21xv2xlo1v2xlo1hi1r1v2xv2xhi1r1_2.
try rename H_bst_xsz1sz21xv2xlo1v2xlo1hi21xv2xv2xhi21x_2 into H_bst_xsz1sz21xv2xlo1v2xlo1hi1r1v2xv2xhi1r1_2.
try rename h_bst_xsz1sz21xv2xlo1v2xlo1hi1r1v2xv2xhi1r1_2 into h_bst_xsz1sz1r1v2xlo1v2xlo1hi1r1v2xv2xhi1r1_2.
try rename H_bst_xsz1sz21xv2xlo1v2xlo1hi1r1v2xv2xhi1r1_2 into H_bst_xsz1sz1r1v2xlo1v2xlo1hi1r1v2xv2xhi1r1_2.
ssl_write (r1 .+ 1).
ssl_write_post (r1 .+ 1).
ssl_write (x .+ 2).
ssl_write_post (x .+ 2).
ssl_write retv.
ssl_write_post retv.
try rename h_bst_xsz1sz1r1v2xlo1v2xlo1hi1r1v2xv2xhi1r1_2 into h_bst_xsz1sz1r1v1lo1v1lo1hi1r1v1v1hi1r1_2.
try rename H_bst_xsz1sz1r1v2xlo1v2xlo1hi1r1v2xv2xhi1r1_2 into H_bst_xsz1sz1r1v1lo1v1lo1hi1r1v1v1hi1r1_2.
ssl_emp;
exists (((1) + (sz1)) + (sz1r1)), (sz2r1), (vr11), ((if (hi1r1) <= (v1) then v1 else hi1r1)), (lo2r1), ((if (v1) <= (lo1) then v1 else lo1)), (rr11), (hi2r1), (r1);
exists (x :-> (v1) \+ x .+ 1 :-> (l1) \+ x .+ 2 :-> (lr11) \+ h_bst_l1sz1lo1hi1_a \+ h_bst_lr11sz1r1lo1r1hi1r1_0r1);
exists (h_bst_rr11sz2r1lo2r1hi2r1_1r1);
sslauto.
ssl_close 2;
exists (sz1), (sz1r1), (v1), (hi1r1), (hi1), (lo1), (lo1r1), (l1), (lr11), (h_bst_l1sz1lo1hi1_a), (h_bst_lr11sz1r1lo1r1hi1r1_0r1);
sslauto.
shelve.
shelve.
ssl_frame_unfold.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.
