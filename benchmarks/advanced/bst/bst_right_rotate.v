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

Lemma pure1 (sz1l1 : nat) (sz2l1 : nat) (sz2 : nat) : (0) <= (sz1l1) -> (0) <= (((1) + (sz1l1)) + (sz2l1)) -> (0) <= (sz2) -> (0) <= (sz2l1) -> ((sz1l1) + (((1) + (sz2l1)) + (sz2))) = ((((1) + (sz1l1)) + (sz2l1)) + (sz2)). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (sz2l1 : nat) (sz2 : nat) (sz1l1 : nat) : (0) <= (sz1l1) -> (0) <= (((1) + (sz1l1)) + (sz2l1)) -> (0) <= (sz2) -> (0) <= (sz2l1) -> (0) <= (((1) + (sz2l1)) + (sz2)). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (hi2l1 : nat) (hi1l1 : nat) (lo2 : nat) (v1 : nat) (lo2l1 : nat) (vl11 : nat) : ((if (hi2l1) <= (vl11) then vl11 else hi2l1)) <= (v1) -> (vl11) <= (lo2l1) -> (0) <= (vl11) -> (v1) <= (lo2) -> (0) <= (v1) -> (vl11) <= (7) -> (hi1l1) <= (vl11) -> (v1) <= (7) -> (hi2l1) <= (v1).
  (* intros; hammer. *)
  intros.
  intros.
  destruct (hi2l1 <= vl11) eqn:H7; last by done.
  exact (leq_trans H7 H).
Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (hi2l1 : nat) (hi1l1 : nat) (lo2 : nat) (v1 : nat) (lo2l1 : nat) (vl11 : nat) : ((if (hi2l1) <= (vl11) then vl11 else hi2l1)) <= (v1) -> (vl11) <= (lo2l1) -> (0) <= (vl11) -> (v1) <= (lo2) -> (0) <= (v1) -> (vl11) <= (7) -> (hi1l1) <= (vl11) -> (v1) <= (7) -> (vl11) <= ((if (v1) <= (lo2l1) then v1 else lo2l1)).
  (* intros; hammer. *)
  intros.
  destruct (v1 <= lo2l1) eqn:H7; last by done.
  destruct (hi2l1 <= vl11) eqn:H8; first by done.
  apply negbT in H8.
  rewrite -ltnNge in H8.
  apply ltnW in H8.
  exact (leq_trans H8 H).
Qed.
Hint Resolve pure4: ssl_pure.

Definition bst_right_rotate_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * nat * ptr * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (0) <= (sz1) /\ (0) <= (sz2) /\ (0) <= (v) /\ (hi1) <= (v) /\ ~~ ((l) == (null)) /\ (v) <= (7) /\ (v) <= (lo2) /\ h = retv :-> (unused) \+ x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists sz3 sz4 v3 hi3 lo4 l3 lo3 hi4 y,
      exists h_bst_l3sz3lo3hi3_2 h_bst_xsz4lo4hi4_3,
      (0) <= (sz3) /\ (0) <= (sz4) /\ (0) <= (v3) /\ (hi3) <= (v3) /\ ((sz3) + (sz4)) == ((sz1) + (sz2)) /\ (v3) <= (7) /\ (v3) <= (lo4) /\ h = retv :-> (y) \+ y :-> (v3) \+ y .+ 1 :-> (l3) \+ y .+ 2 :-> (x) \+ h_bst_l3sz3lo3hi3_2 \+ h_bst_xsz4lo4hi4_3 /\ bst l3 sz3 lo3 hi3 h_bst_l3sz3lo3hi3_2 /\ bst x sz4 lo4 hi4 h_bst_xsz4lo4hi4_3
    ]).

Program Definition bst_right_rotate : bst_right_rotate_type :=
  Fix (fun (bst_right_rotate : bst_right_rotate_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused1 <-- @read ptr retv;
      v1 <-- @read nat x;
      l1 <-- @read ptr (x .+ 1);
      r1 <-- @read ptr (x .+ 2);
      if (l1) == (null)
      then
        ret tt
      else
        vl11 <-- @read nat l1;
        ll11 <-- @read ptr (l1 .+ 1);
        rl11 <-- @read ptr (l1 .+ 2);
        (l1 .+ 2) ::= x;;
        (x .+ 1) ::= rl11;;
        retv ::= l1;;
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
ssl_open ((l1) == (null)) H_bst_l1sz1lo1hi1_a.
move=>[phi_bst_l1sz1lo1hi1_a0] [phi_bst_l1sz1lo1hi1_a1] [phi_bst_l1sz1lo1hi1_a2].
move=>[sigma_bst_l1sz1lo1hi1_a].
subst h_bst_l1sz1lo1hi1_a.
ssl_inconsistency.
ex_elim sz1l1 sz2l1 vl1 hi2l1 hi1l1.
ex_elim lo1l1 lo2l1 ll1 rl1.
ex_elim h_bst_ll1sz1l1lo1l1hi1l1_0l1 h_bst_rl1sz2l1lo2l1hi2l1_1l1.
move=>[phi_bst_l1sz1lo1hi1_a0] [phi_bst_l1sz1lo1hi1_a1] [phi_bst_l1sz1lo1hi1_a2] [phi_bst_l1sz1lo1hi1_a3] [phi_bst_l1sz1lo1hi1_a4] [phi_bst_l1sz1lo1hi1_a5] [phi_bst_l1sz1lo1hi1_a6] [phi_bst_l1sz1lo1hi1_a7] [phi_bst_l1sz1lo1hi1_a8].
move=>[sigma_bst_l1sz1lo1hi1_a].
subst h_bst_l1sz1lo1hi1_a.
move=>[H_bst_ll1sz1l1lo1l1hi1l1_0l1 H_bst_rl1sz2l1lo2l1hi2l1_1l1].
try rename h_bst_l1sz1lo1hi1_a into h_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1lo1hi1_a into H_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a.
try rename h_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1lo1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename h_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
try rename H_bst_l1sz1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a.
ssl_read l1.
try rename vl1 into vl11.
try rename h_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into h_bst_l1sz1l1sz2l1vl11lo1l1vl11lo1l1hi2l1vl11vl11hi2l1_a.
try rename H_bst_l1sz1l1sz2l1vl1lo1l1vl1lo1l1hi2l1vl1vl1hi2l1_a into H_bst_l1sz1l1sz2l1vl11lo1l1vl11lo1l1hi2l1vl11vl11hi2l1_a.
ssl_read (l1 .+ 1).
try rename ll1 into ll11.
try rename h_bst_ll1sz1l1lo1l1hi1l1_0l1 into h_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename H_bst_ll1sz1l1lo1l1hi1l1_0l1 into H_bst_ll11sz1l1lo1l1hi1l1_0l1.
ssl_read (l1 .+ 2).
try rename rl1 into rl11.
try rename h_bst_rl1sz2l1lo2l1hi2l1_1l1 into h_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename H_bst_rl1sz2l1lo2l1hi2l1_1l1 into H_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename h_bst_xsz4lo4hi4_3 into h_bst_xsz4lo4hi21xv2xv2xhi21x_3.
try rename H_bst_xsz4lo4hi4_3 into H_bst_xsz4lo4hi21xv2xv2xhi21x_3.
try rename h_bst_xsz4lo4hi21xv2xv2xhi21x_3 into h_bst_xsz4v2xlo11xv2xlo11xhi21xv2xv2xhi21x_3.
try rename H_bst_xsz4lo4hi21xv2xv2xhi21x_3 into H_bst_xsz4v2xlo11xv2xlo11xhi21xv2xv2xhi21x_3.
try rename h_bst_xsz4v2xlo11xv2xlo11xhi21xv2xv2xhi21x_3 into h_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_3.
try rename H_bst_xsz4v2xlo11xv2xlo11xhi21xv2xv2xhi21x_3 into H_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_3.
try rename h_bst_l3sz3lo3hi3_2 into h_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename H_bst_l3sz3lo3hi3_2 into H_bst_ll11sz1l1lo1l1hi1l1_0l1.
try rename h_bst_l2xsz11xlo11xhi11x_0x into h_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename H_bst_l2xsz11xlo11xhi11x_0x into H_bst_rl11sz2l1lo2l1hi2l1_1l1.
try rename h_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_3 into h_bst_xsz11xsz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3.
try rename H_bst_xsz11xsz21xv2xlo11xv2xlo11xhi21xv2xv2xhi21x_3 into H_bst_xsz11xsz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3.
try rename h_bst_xsz11xsz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3 into h_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3.
try rename H_bst_xsz11xsz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3 into H_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3.
try rename h_bst_r2xsz21xlo21xhi21x_1x into h_bst_r1sz2lo2hi2_b.
try rename H_bst_r2xsz21xlo21xhi21x_1x into H_bst_r1sz2lo2hi2_b.
try rename h_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3 into h_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi2v2xv2xhi2_3.
try rename H_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi21xv2xv2xhi21x_3 into H_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi2v2xv2xhi2_3.
try rename h_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi2v2xv2xhi2_3 into h_bst_xsz2l1sz2v2xlo2l1v2xlo2l1hi2v2xv2xhi2_3.
try rename H_bst_xsz2l1sz21xv2xlo2l1v2xlo2l1hi2v2xv2xhi2_3 into H_bst_xsz2l1sz2v2xlo2l1v2xlo2l1hi2v2xv2xhi2_3.
ssl_write (l1 .+ 2).
ssl_write_post (l1 .+ 2).
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write retv.
ssl_write_post retv.
try rename h_bst_xsz2l1sz2v2xlo2l1v2xlo2l1hi2v2xv2xhi2_3 into h_bst_xsz2l1sz2v1lo2l1v1lo2l1hi2v1v1hi2_3.
try rename H_bst_xsz2l1sz2v2xlo2l1v2xlo2l1hi2v2xv2xhi2_3 into H_bst_xsz2l1sz2v1lo2l1v1lo2l1hi2v1v1hi2_3.
ssl_emp;
exists (sz1l1), (((1) + (sz2l1)) + (sz2)), (vl11), (hi1l1), ((if (v1) <= (lo2l1) then v1 else lo2l1)), (ll11), (lo1l1), ((if (hi2) <= (v1) then v1 else hi2)), (l1);
exists (h_bst_ll11sz1l1lo1l1hi1l1_0l1);
exists (x :-> (v1) \+ x .+ 1 :-> (rl11) \+ x .+ 2 :-> (r1) \+ h_bst_rl11sz2l1lo2l1hi2l1_1l1 \+ h_bst_r1sz2lo2hi2_b);
sslauto.
shelve.
ssl_close 2;
exists (sz2l1), (sz2), (v1), (hi2), (hi2l1), (lo2l1), (lo2), (rl11), (r1), (h_bst_rl11sz2l1lo2l1hi2l1_1l1), (h_bst_r1sz2lo2hi2_b);
sslauto.
shelve.
shelve.
Unshelve.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.
