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

Lemma pure1 (sz1 : nat) (sz1r2 : nat) (sz2r2 : nat) : (0) <= (sz2r2) -> (0) <= (sz1r2) -> (0) <= (sz1) -> (0) <= (((1) + (sz1r2)) + (sz2r2)) -> (0) <= (((1) + (sz1)) + (sz1r2)). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (sz1 : nat) (sz1r2 : nat) (sz2r2 : nat) : (0) <= (sz2r2) -> (0) <= (sz1r2) -> (0) <= (sz1) -> (0) <= (((1) + (sz1r2)) + (sz2r2)) -> ((((1) + (sz1)) + (sz1r2)) + (sz2r2)) = ((sz1) + (((1) + (sz1r2)) + (sz2r2))). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (hi1r2 : nat) (vr22 : nat) (hi1 : nat) (v2 : nat) (lo1r2 : nat) (lo2r2 : nat) : (v2) <= (7) -> (0) <= (v2) -> (0) <= (vr22) -> (v2) <= ((if (vr22) <= (lo1r2) then vr22 else lo1r2)) -> (vr22) <= (7) -> (hi1r2) <= (vr22) -> (vr22) <= (lo2r2) -> (hi1) <= (v2) -> ((if (hi1r2) <= (v2) then v2 else hi1r2)) <= (vr22).
  (* intros; hammer. *)
  intros.
  case (hi1r2 <= v2); last by done.
  destruct (vr22 <= lo1r2) eqn:H7; first by done.
  apply negbT in H7.
  rewrite -ltnNge in H7.
  apply ltnW.
  exact (leq_ltn_trans H2 H7).
Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (hi1r2 : nat) (vr22 : nat) (hi1 : nat) (v2 : nat) (lo1r2 : nat) (lo2r2 : nat) : (v2) <= (7) -> (0) <= (v2) -> (0) <= (vr22) -> (v2) <= ((if (vr22) <= (lo1r2) then vr22 else lo1r2)) -> (vr22) <= (7) -> (hi1r2) <= (vr22) -> (vr22) <= (lo2r2) -> (hi1) <= (v2) -> (v2) <= (lo1r2).
  (* intros; hammer. *)
  intros.
  destruct (vr22 <= lo1r2) eqn: H7; last by done.
  apply (leq_trans H2 H7).  
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
      exists h_bst_xsz3lo3hi3_525 h_bst_r3sz4lo4hi4_526,
      (0) <= (sz3) /\ (0) <= (sz4) /\ (0) <= (v3) /\ (hi3) <= (v3) /\ ((sz3) + (sz4)) == ((sz1) + (sz2)) /\ (v3) <= (7) /\ (v3) <= (lo4) /\ h = retv :-> (y) \+ y :-> (v3) \+ y .+ 1 :-> (x) \+ y .+ 2 :-> (r3) \+ h_bst_xsz3lo3hi3_525 \+ h_bst_r3sz4lo4hi4_526 /\ bst x sz3 lo3 hi3 h_bst_xsz3lo3hi3_525 /\ bst r3 sz4 lo4 hi4 h_bst_r3sz4lo4hi4_526
    ]).

Program Definition bst_left_rotate : bst_left_rotate_type :=
  Fix (fun (bst_left_rotate : bst_left_rotate_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused2 <-- @read ptr retv;
      v2 <-- @read nat x;
      l2 <-- @read ptr (x .+ 1);
      r2 <-- @read ptr (x .+ 2);
      if (r2) == (null)
      then
        ret tt
      else
        vr22 <-- @read nat r2;
        lr22 <-- @read ptr (r2 .+ 1);
        rr22 <-- @read ptr (r2 .+ 2);
        (r2 .+ 1) ::= x;;
        retv ::= r2;;
        (x .+ 2) ::= lr22;;
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
try rename unused into unused2.
ssl_read x.
try rename v into v2.
ssl_read (x .+ 1).
try rename l into l2.
try rename h_bst_lsz1lo1hi1_a into h_bst_l2sz1lo1hi1_a.
try rename H_bst_lsz1lo1hi1_a into H_bst_l2sz1lo1hi1_a.
ssl_read (x .+ 2).
try rename r into r2.
try rename h_bst_rsz2lo2hi2_b into h_bst_r2sz2lo2hi2_b.
try rename H_bst_rsz2lo2hi2_b into H_bst_r2sz2lo2hi2_b.
ssl_open ((r2) == (null)) H_bst_r2sz2lo2hi2_b.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
ssl_inconsistency.
ex_elim sz1r2 sz2r2 vr2 hi2r2 hi1r2.
ex_elim lo1r2 lo2r2 lr2 rr2.
ex_elim h_bst_lr2sz1r2lo1r2hi1r2_523r2 h_bst_rr2sz2r2lo2r2hi2r2_524r2.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2] [phi_bst_r2sz2lo2hi2_b3] [phi_bst_r2sz2lo2hi2_b4] [phi_bst_r2sz2lo2hi2_b5] [phi_bst_r2sz2lo2hi2_b6] [phi_bst_r2sz2lo2hi2_b7] [phi_bst_r2sz2lo2hi2_b8].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
move=>[H_bst_lr2sz1r2lo1r2hi1r2_523r2 H_bst_rr2sz2r2lo2r2hi2r2_524r2].
try rename h_bst_r2sz2lo2hi2_b into h_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2lo2hi2_b into H_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b.
try rename h_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b into h_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b into H_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename h_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into h_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into H_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
ssl_read r2.
try rename vr2 into vr22.
try rename h_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into h_bst_r2sz1r2sz2r2vr22lo1r2vr22lo1r2hi2r2vr22vr22hi2r2_b.
try rename H_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into H_bst_r2sz1r2sz2r2vr22lo1r2vr22lo1r2hi2r2vr22vr22hi2r2_b.
ssl_read (r2 .+ 1).
try rename lr2 into lr22.
try rename h_bst_lr2sz1r2lo1r2hi1r2_523r2 into h_bst_lr22sz1r2lo1r2hi1r2_523r2.
try rename H_bst_lr2sz1r2lo1r2hi1r2_523r2 into H_bst_lr22sz1r2lo1r2hi1r2_523r2.
ssl_read (r2 .+ 2).
try rename rr2 into rr22.
try rename h_bst_rr2sz2r2lo2r2hi2r2_524r2 into h_bst_rr22sz2r2lo2r2hi2r2_524r2.
try rename H_bst_rr2sz2r2lo2r2hi2r2_524r2 into H_bst_rr22sz2r2lo2r2hi2r2_524r2.
try rename h_bst_xsz3lo3hi3_525 into h_bst_xsz3lo3hi21xv1xv1xhi21x_525.
try rename H_bst_xsz3lo3hi3_525 into H_bst_xsz3lo3hi21xv1xv1xhi21x_525.
try rename h_bst_xsz3lo3hi21xv1xv1xhi21x_525 into h_bst_xsz3v1xlo11xv1xlo11xhi21xv1xv1xhi21x_525.
try rename H_bst_xsz3lo3hi21xv1xv1xhi21x_525 into H_bst_xsz3v1xlo11xv1xlo11xhi21xv1xv1xhi21x_525.
try rename h_bst_xsz3v1xlo11xv1xlo11xhi21xv1xv1xhi21x_525 into h_bst_xsz11xsz21xv1xlo11xv1xlo11xhi21xv1xv1xhi21x_525.
try rename H_bst_xsz3v1xlo11xv1xlo11xhi21xv1xv1xhi21x_525 into H_bst_xsz11xsz21xv1xlo11xv1xlo11xhi21xv1xv1xhi21x_525.
try rename h_bst_r3sz4lo4hi4_526 into h_bst_rr22sz2r2lo2r2hi2r2_524r2.
try rename H_bst_r3sz4lo4hi4_526 into H_bst_rr22sz2r2lo2r2hi2r2_524r2.
try rename h_bst_l1xsz11xlo11xhi11x_523x into h_bst_l2sz1lo1hi1_a.
try rename H_bst_l1xsz11xlo11xhi11x_523x into H_bst_l2sz1lo1hi1_a.
try rename h_bst_xsz11xsz21xv1xlo11xv1xlo11xhi21xv1xv1xhi21x_525 into h_bst_xsz11xsz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525.
try rename H_bst_xsz11xsz21xv1xlo11xv1xlo11xhi21xv1xv1xhi21x_525 into H_bst_xsz11xsz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525.
try rename h_bst_xsz11xsz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525 into h_bst_xsz1sz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525.
try rename H_bst_xsz11xsz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525 into H_bst_xsz1sz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525.
try rename h_bst_r1xsz21xlo21xhi21x_524x into h_bst_lr22sz1r2lo1r2hi1r2_523r2.
try rename H_bst_r1xsz21xlo21xhi21x_524x into H_bst_lr22sz1r2lo1r2hi1r2_523r2.
try rename h_bst_xsz1sz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525 into h_bst_xsz1sz21xv1xlo1v1xlo1hi1r2v1xv1xhi1r2_525.
try rename H_bst_xsz1sz21xv1xlo1v1xlo1hi21xv1xv1xhi21x_525 into H_bst_xsz1sz21xv1xlo1v1xlo1hi1r2v1xv1xhi1r2_525.
try rename h_bst_xsz1sz21xv1xlo1v1xlo1hi1r2v1xv1xhi1r2_525 into h_bst_xsz1sz1r2v1xlo1v1xlo1hi1r2v1xv1xhi1r2_525.
try rename H_bst_xsz1sz21xv1xlo1v1xlo1hi1r2v1xv1xhi1r2_525 into H_bst_xsz1sz1r2v1xlo1v1xlo1hi1r2v1xv1xhi1r2_525.
ssl_write (r2 .+ 1).
ssl_write_post (r2 .+ 1).
ssl_write retv.
ssl_write_post retv.
ssl_write (x .+ 2).
ssl_write_post (x .+ 2).
try rename h_bst_xsz1sz1r2v1xlo1v1xlo1hi1r2v1xv1xhi1r2_525 into h_bst_xsz1sz1r2v2lo1v2lo1hi1r2v2v2hi1r2_525.
try rename H_bst_xsz1sz1r2v1xlo1v1xlo1hi1r2v1xv1xhi1r2_525 into H_bst_xsz1sz1r2v2lo1v2lo1hi1r2v2v2hi1r2_525.
ssl_emp;
exists (((1) + (sz1)) + (sz1r2)), (sz2r2), (vr22), ((if (hi1r2) <= (v2) then v2 else hi1r2)), (lo2r2), ((if (v2) <= (lo1) then v2 else lo1)), (rr22), (hi2r2), (r2);
exists (x :-> (v2) \+ x .+ 1 :-> (l2) \+ x .+ 2 :-> (lr22) \+ h_bst_l2sz1lo1hi1_a \+ h_bst_lr22sz1r2lo1r2hi1r2_523r2);
exists (h_bst_rr22sz2r2lo2r2hi2r2_524r2);
sslauto.
ssl_close 2;
exists (sz1), (sz1r2), (v2), (hi1r2), (hi1), (lo1), (lo1r2), (l2), (lr22), (h_bst_l2sz1lo1hi1_a), (h_bst_lr22sz1r2lo1r2hi1r2_523r2);
sslauto.
shelve.
shelve.
ssl_frame_unfold.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.