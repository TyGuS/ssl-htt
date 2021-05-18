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

Lemma pure1 (r2 : ptr) : (r2) = (null) -> ((if (null) == (null) then (if (r2) == (null) then 7 else 7) else 7)) = (7). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (r2 : ptr) : (r2) = (null) -> ((if (r2) == (null) then (if (null) == (null) then 0 else 0) else 0)) = (0). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (sz1r2 : nat) (sz2r2 : nat) : (0) <= (((1) + (sz1r2)) + (sz2r2)) -> (0) <= (sz1r2) -> (0) <= (sz2r2) -> (((1) + (sz1r2)) + (sz2r2)) = (((1) + (sz1r2)) + (sz2r2)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (hi1r2 : nat) (r2 : ptr) (vr22 : nat) (retv : ptr) (v2 : nat) (lo1r2 : nat) (x : ptr) (lo2r2 : nat) : (v2) <= (7) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (0) <= (v2) -> ~~ ((r2) == (null)) -> (0) <= (vr22) -> (v2) <= ((if (vr22) <= (lo1r2) then vr22 else lo1r2)) -> (vr22) <= (7) -> (hi1r2) <= (vr22) -> ~~ ((r2) == (retv)) -> (vr22) <= (lo2r2) -> ~~ ((retv) == (x)) -> ~~ ((r2) == (x)) -> ((if (null) == (null) then (if (r2) == (null) then 7 else (if (vr22) <= (lo1r2) then vr22 else lo1r2)) else 7)) = ((if (vr22) <= (lo1r2) then vr22 else lo1r2)). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (hi1r2 : nat) (r2 : ptr) (vr22 : nat) (retv : ptr) (v2 : nat) (lo1r2 : nat) (x : ptr) (hi2r2 : nat) (lo2r2 : nat) : (v2) <= (7) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (0) <= (v2) -> ~~ ((r2) == (null)) -> (0) <= (vr22) -> (v2) <= ((if (vr22) <= (lo1r2) then vr22 else lo1r2)) -> (vr22) <= (7) -> (hi1r2) <= (vr22) -> ~~ ((r2) == (retv)) -> (vr22) <= (lo2r2) -> ~~ ((retv) == (x)) -> ~~ ((r2) == (x)) -> ((if (r2) == (null) then (if (null) == (null) then 0 else 0) else (if (hi2r2) <= (vr22) then vr22 else hi2r2))) = ((if (hi2r2) <= (vr22) then vr22 else hi2r2)). intros; hammer. Qed.
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
      unused2 <-- @read ptr retv;
      v2 <-- @read nat x;
      r2 <-- @read ptr (x .+ 2);
      if (null) == (null)
      then
        if (r2) == (null)
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
          vr22 <-- @read nat r2;
          lr22 <-- @read ptr (r2 .+ 1);
          rr22 <-- @read ptr (r2 .+ 2);
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= r2;;
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
try rename unused into unused2.
ssl_read x.
try rename v into v2.
ssl_read (x .+ 2).
try rename r into r2.
try rename h_bst_ysz1sz2rlo2lo1rhi1hi2_c into h_bst_ysz1sz2r2lo2lo1r2hi1hi2_c.
try rename H_bst_ysz1sz2rlo2lo1rhi1hi2_c into H_bst_ysz1sz2r2lo2lo1r2hi1hi2_c.
try rename h_bst_rsz2lo2hi2_b into h_bst_r2sz2lo2hi2_b.
try rename H_bst_rsz2lo2hi2_b into H_bst_r2sz2lo2hi2_b.
ssl_open ((null) == (null)) H_bst_sz1lo1hi1_a.
move=>[phi_bst_sz1lo1hi1_a0] [phi_bst_sz1lo1hi1_a1] [phi_bst_sz1lo1hi1_a2].
move=>[sigma_bst_sz1lo1hi1_a].
subst h_bst_sz1lo1hi1_a.
try rename h_bst_ysz1sz2r2lo2lo1r2hi1hi2_c into h_bst_ysz1sz2r2lo2lo1r2hi2_c.
try rename H_bst_ysz1sz2r2lo2lo1r2hi1hi2_c into H_bst_ysz1sz2r2lo2lo1r2hi2_c.
try rename h_bst_sz1lo1hi1_a into h_bst_sz1lo1_a.
try rename H_bst_sz1lo1hi1_a into H_bst_sz1lo1_a.
try rename h_bst_ysz1sz2r2lo2lo1r2hi2_c into h_bst_ysz1sz2r2lo2r2hi2_c.
try rename H_bst_ysz1sz2r2lo2lo1r2hi2_c into H_bst_ysz1sz2r2lo2r2hi2_c.
try rename h_bst_sz1lo1_a into h_bst_sz1_a.
try rename H_bst_sz1lo1_a into H_bst_sz1_a.
try rename h_bst_ysz1sz2r2lo2r2hi2_c into h_bst_ysz2r2lo2r2hi2_c.
try rename H_bst_ysz1sz2r2lo2r2hi2_c into H_bst_ysz2r2lo2r2hi2_c.
try rename h_bst_sz1_a into h_bst__a.
try rename H_bst_sz1_a into H_bst__a.
ssl_open ((r2) == (null)) H_bst_r2sz2lo2hi2_b.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
try rename h_bst_r2sz2lo2hi2_b into h_bst_r2sz2lo2_b.
try rename H_bst_r2sz2lo2hi2_b into H_bst_r2sz2lo2_b.
try rename h_bst_ysz2r2lo2r2hi2_c into h_bst_ysz2r2lo2r2_c.
try rename H_bst_ysz2r2lo2r2hi2_c into H_bst_ysz2r2lo2r2_c.
try rename h_bst_ysz2r2lo2r2_c into h_bst_ysz2r2r2_c.
try rename H_bst_ysz2r2lo2r2_c into H_bst_ysz2r2r2_c.
try rename h_bst_r2sz2lo2_b into h_bst_r2sz2_b.
try rename H_bst_r2sz2lo2_b into H_bst_r2sz2_b.
try rename h_bst_r2sz2_b into h_bst_r2_b.
try rename H_bst_r2sz2_b into H_bst_r2_b.
try rename h_bst_ysz2r2r2_c into h_bst_yr2r2_c.
try rename H_bst_ysz2r2r2_c into H_bst_yr2r2_c.
try rename h_bst_yr2r2_c into h_bst_r2r2_c.
try rename H_bst_yr2r2_c into H_bst_r2r2_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (r2) == (null) then (if (null) == (null) then 0 else 0) else 0)), ((if (null) == (null) then (if (r2) == (null) then 7 else 7) else 7)), ((0) + (0)), (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1r2 sz2r2 vr2 hi2r2 hi1r2.
ex_elim lo1r2 lo2r2 lr2 rr2.
ex_elim h_bst_lr2sz1r2lo1r2hi1r2_519r2 h_bst_rr2sz2r2lo2r2hi2r2_520r2.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2] [phi_bst_r2sz2lo2hi2_b3] [phi_bst_r2sz2lo2hi2_b4] [phi_bst_r2sz2lo2hi2_b5] [phi_bst_r2sz2lo2hi2_b6] [phi_bst_r2sz2lo2hi2_b7] [phi_bst_r2sz2lo2hi2_b8].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
move=>[H_bst_lr2sz1r2lo1r2hi1r2_519r2 H_bst_rr2sz2r2lo2r2hi2r2_520r2].
try rename h_bst_r2sz2lo2hi2_b into h_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2lo2hi2_b into H_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b.
try rename h_bst_ysz2r2lo2r2hi2_c into h_bst_ysz2r2lo2r2hi2r2vr2vr2hi2r2_c.
try rename H_bst_ysz2r2lo2r2hi2_c into H_bst_ysz2r2lo2r2hi2r2vr2vr2hi2r2_c.
try rename h_bst_ysz2r2lo2r2hi2r2vr2vr2hi2r2_c into h_bst_ysz2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c.
try rename H_bst_ysz2r2lo2r2hi2r2vr2vr2hi2r2_c into H_bst_ysz2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c.
try rename h_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b into h_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2lo2hi2r2vr2vr2hi2r2_b into H_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename h_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into h_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename H_bst_r2sz2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into H_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b.
try rename h_bst_ysz2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c into h_bst_ysz1r2sz2r2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c.
try rename H_bst_ysz2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c into H_bst_ysz1r2sz2r2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c.
ssl_read r2.
try rename vr2 into vr22.
try rename h_bst_ysz1r2sz2r2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c into h_bst_ysz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c.
try rename H_bst_ysz1r2sz2r2r2vr2lo1r2vr2lo1r2r2hi2r2vr2vr2hi2r2_c into H_bst_ysz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c.
try rename h_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into h_bst_r2sz1r2sz2r2vr22lo1r2vr22lo1r2hi2r2vr22vr22hi2r2_b.
try rename H_bst_r2sz1r2sz2r2vr2lo1r2vr2lo1r2hi2r2vr2vr2hi2r2_b into H_bst_r2sz1r2sz2r2vr22lo1r2vr22lo1r2hi2r2vr22vr22hi2r2_b.
ssl_read (r2 .+ 1).
try rename lr2 into lr22.
try rename h_bst_lr2sz1r2lo1r2hi1r2_519r2 into h_bst_lr22sz1r2lo1r2hi1r2_519r2.
try rename H_bst_lr2sz1r2lo1r2hi1r2_519r2 into H_bst_lr22sz1r2lo1r2hi1r2_519r2.
ssl_read (r2 .+ 2).
try rename rr2 into rr22.
try rename h_bst_rr2sz2r2lo2r2hi2r2_520r2 into h_bst_rr22sz2r2lo2r2hi2r2_520r2.
try rename H_bst_rr2sz2r2lo2r2hi2r2_520r2 into H_bst_rr22sz2r2lo2r2hi2r2_520r2.
try rename h_bst_l1ysz11ylo11yhi11y_519y into h_bst_lr22sz1r2lo1r2hi1r2_519r2.
try rename H_bst_l1ysz11ylo11yhi11y_519y into H_bst_lr22sz1r2lo1r2hi1r2_519r2.
try rename h_bst_r1ysz21ylo21yhi21y_520y into h_bst_rr22sz2r2lo2r2hi2r2_520r2.
try rename H_bst_r1ysz21ylo21yhi21y_520y into H_bst_rr22sz2r2lo2r2hi2r2_520r2.
try rename h_bst_ysz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c into h_bst_r2sz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c.
try rename H_bst_ysz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c into H_bst_r2sz1r2sz2r2r2vr22lo1r2vr22lo1r2r2hi2r2vr22vr22hi2r2_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (r2) == (null) then (if (null) == (null) then 0 else 0) else (if (hi2r2) <= (vr22) then vr22 else hi2r2))), ((if (null) == (null) then (if (r2) == (null) then 7 else (if (vr22) <= (lo1r2) then vr22 else lo1r2)) else 7)), ((0) + (((1) + (sz1r2)) + (sz2r2))), (r2);
exists (r2 :-> (vr22) \+ r2 .+ 1 :-> (lr22) \+ r2 .+ 2 :-> (rr22) \+ h_bst_lr22sz1r2lo1r2hi1r2_519r2 \+ h_bst_rr22sz2r2lo2r2hi2r2_520r2);
sslauto.
ssl_close 2;
exists (sz1r2), (sz2r2), (vr22), (hi2r2), (hi1r2), (lo1r2), (lo2r2), (lr22), (rr22), (h_bst_lr22sz1r2lo1r2hi1r2_519r2), (h_bst_rr22sz2r2lo2r2hi2r2_520r2);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
ex_elim sz10 sz20 v0 hi20 hi10.
ex_elim lo10 lo20 l0 r0.
ex_elim h_bst_l0sz10lo10hi10_5190 h_bst_r0sz20lo20hi20_5200.
move=>[phi_bst_sz1lo1hi1_a0] [phi_bst_sz1lo1hi1_a1] [phi_bst_sz1lo1hi1_a2] [phi_bst_sz1lo1hi1_a3] [phi_bst_sz1lo1hi1_a4] [phi_bst_sz1lo1hi1_a5] [phi_bst_sz1lo1hi1_a6] [phi_bst_sz1lo1hi1_a7] [phi_bst_sz1lo1hi1_a8].
move=>[sigma_bst_sz1lo1hi1_a].
subst h_bst_sz1lo1hi1_a.
move=>[H_bst_l0sz10lo10hi10_5190 H_bst_r0sz20lo20hi20_5200].
ssl_inconsistency.
Qed.