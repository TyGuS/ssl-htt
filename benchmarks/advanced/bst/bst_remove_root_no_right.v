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

Lemma pure50 (l2 : ptr) : (l2) = (null) -> ((if (null) == (null) then (if (l2) == (null) then 0 else 0) else 0)) = (0). intros; hammer. Qed.
Hint Resolve pure50: ssl_pure.
Lemma pure51 (l2 : ptr) : (l2) = (null) -> ((if (l2) == (null) then (if (null) == (null) then 7 else 7) else 7)) = (7). intros; hammer. Qed.
Hint Resolve pure51: ssl_pure.
Lemma pure52 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure52: ssl_pure.
Lemma pure53 (sz1l2 : nat) (sz2l2 : nat) : (0) <= (sz2l2) -> (0) <= (sz1l2) -> (0) <= (((1) + (sz1l2)) + (sz2l2)) -> (((1) + (sz1l2)) + (sz2l2)) = (((1) + (sz1l2)) + (sz2l2)). intros; hammer. Qed.
Hint Resolve pure53: ssl_pure.
Lemma pure54 (hi1l2 : nat) (retv : ptr) (lo2l2 : nat) (hi2l2 : nat) (l2 : ptr) (v2 : nat) (x : ptr) (lo1l2 : nat) (vl22 : nat) : (v2) <= (7) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (hi1l2) <= (vl22) -> ~~ ((l2) == (null)) -> ((if (hi2l2) <= (vl22) then vl22 else hi2l2)) <= (v2) -> (0) <= (v2) -> (vl22) <= (lo2l2) -> ~~ ((l2) == (retv)) -> (vl22) <= (7) -> ~~ ((retv) == (x)) -> (0) <= (vl22) -> ~~ ((l2) == (x)) -> ((if (l2) == (null) then (if (null) == (null) then 7 else 7) else (if (vl22) <= (lo1l2) then vl22 else lo1l2))) = ((if (vl22) <= (lo1l2) then vl22 else lo1l2)). intros; hammer. Qed.
Hint Resolve pure54: ssl_pure.
Lemma pure55 (hi1l2 : nat) (retv : ptr) (lo2l2 : nat) (hi2l2 : nat) (l2 : ptr) (v2 : nat) (x : ptr) (vl22 : nat) : (v2) <= (7) -> ~~ ((x) == (null)) -> ~~ ((retv) == (null)) -> (hi1l2) <= (vl22) -> ~~ ((l2) == (null)) -> ((if (hi2l2) <= (vl22) then vl22 else hi2l2)) <= (v2) -> (0) <= (v2) -> (vl22) <= (lo2l2) -> ~~ ((l2) == (retv)) -> (vl22) <= (7) -> ~~ ((retv) == (x)) -> (0) <= (vl22) -> ~~ ((l2) == (x)) -> ((if (null) == (null) then (if (l2) == (null) then 0 else (if (hi2l2) <= (vl22) then vl22 else hi2l2)) else 0)) = ((if (hi2l2) <= (vl22) then vl22 else hi2l2)). intros; hammer. Qed.
Hint Resolve pure55: ssl_pure.

Definition bst_remove_root_no_right_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * ptr * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (0) <= (sz1) /\ (0) <= (sz2) /\ (0) <= (v) /\ (hi1) <= (v) /\ (r) == (null) /\ (v) <= (7) /\ (v) <= (lo2) /\ h = retv :-> unused \+ x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists hi lo n1 y,
      exists h_bst_yn1lohi_c,
      (hi) == ((if (r) == (null) then (if (l) == (null) then 0 else hi1) else hi2)) /\ (lo) == ((if (l) == (null) then (if (r) == (null) then 7 else lo2) else lo1)) /\ (n1) == ((sz1) + (sz2)) /\ h = retv :-> y \+ h_bst_yn1lohi_c /\ bst y n1 lo hi h_bst_yn1lohi_c
    ]).

Program Definition bst_remove_root_no_right : bst_remove_root_no_right_type :=
  Fix (fun (bst_remove_root_no_right : bst_remove_root_no_right_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      unused2 <-- @read ptr retv;
      v2 <-- @read nat x;
      l2 <-- @read ptr (x .+ 1);
      if (l2) == (null)
      then
        if (null) == (null)
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
          ret tt
      else
        vl22 <-- @read nat l2;
        ll22 <-- @read ptr (l2 .+ 1);
        rl22 <-- @read ptr (l2 .+ 2);
        if (null) == (null)
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= l2;;
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
try rename unused into unused2.
ssl_read x.
try rename v into v2.
ssl_read (x .+ 1).
try rename l into l2.
try rename h_bst_lsz1lo1hi1_a into h_bst_l2sz1lo1hi1_a.
try rename H_bst_lsz1lo1hi1_a into H_bst_l2sz1lo1hi1_a.
try rename h_bst_ysz1sz2llo2lo1lhi1hi2_c into h_bst_ysz1sz2l2lo2lo1l2hi1hi2_c.
try rename H_bst_ysz1sz2llo2lo1lhi1hi2_c into H_bst_ysz1sz2l2lo2lo1l2hi1hi2_c.
ssl_open ((l2) == (null)) H_bst_l2sz1lo1hi1_a.
move=>[phi_bst_l2sz1lo1hi1_a0] [phi_bst_l2sz1lo1hi1_a1] [phi_bst_l2sz1lo1hi1_a2].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst h_bst_l2sz1lo1hi1_a.
try rename h_bst_l2sz1lo1hi1_a into h_bst_l2sz1lo1_a.
try rename H_bst_l2sz1lo1hi1_a into H_bst_l2sz1lo1_a.
try rename h_bst_ysz1sz2l2lo2lo1l2hi1hi2_c into h_bst_ysz1sz2l2lo2lo1l2hi2_c.
try rename H_bst_ysz1sz2l2lo2lo1l2hi1hi2_c into H_bst_ysz1sz2l2lo2lo1l2hi2_c.
try rename h_bst_ysz1sz2l2lo2lo1l2hi2_c into h_bst_ysz1sz2l2lo2l2hi2_c.
try rename H_bst_ysz1sz2l2lo2lo1l2hi2_c into H_bst_ysz1sz2l2lo2l2hi2_c.
try rename h_bst_l2sz1lo1_a into h_bst_l2sz1_a.
try rename H_bst_l2sz1lo1_a into H_bst_l2sz1_a.
try rename h_bst_ysz1sz2l2lo2l2hi2_c into h_bst_ysz2l2lo2l2hi2_c.
try rename H_bst_ysz1sz2l2lo2l2hi2_c into H_bst_ysz2l2lo2l2hi2_c.
try rename h_bst_l2sz1_a into h_bst_l2_a.
try rename H_bst_l2sz1_a into H_bst_l2_a.
ssl_open ((null) == (null)) H_bst_sz2lo2hi2_b.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
try rename h_bst_sz2lo2hi2_b into h_bst_sz2lo2_b.
try rename H_bst_sz2lo2hi2_b into H_bst_sz2lo2_b.
try rename h_bst_ysz2l2lo2l2hi2_c into h_bst_ysz2l2lo2l2_c.
try rename H_bst_ysz2l2lo2l2hi2_c into H_bst_ysz2l2lo2l2_c.
try rename h_bst_ysz2l2lo2l2_c into h_bst_ysz2l2l2_c.
try rename H_bst_ysz2l2lo2l2_c into H_bst_ysz2l2l2_c.
try rename h_bst_sz2lo2_b into h_bst_sz2_b.
try rename H_bst_sz2lo2_b into H_bst_sz2_b.
try rename h_bst_sz2_b into h_bst__b.
try rename H_bst_sz2_b into H_bst__b.
try rename h_bst_ysz2l2l2_c into h_bst_yl2l2_c.
try rename H_bst_ysz2l2l2_c into H_bst_yl2l2_c.
try rename h_bst_yl2l2_c into h_bst_l2l2_c.
try rename H_bst_yl2l2_c into H_bst_l2l2_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (null) == (null) then (if (l2) == (null) then 0 else 0) else 0)), ((if (l2) == (null) then (if (null) == (null) then 7 else 7) else 7)), ((0) + (0)), (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim sz10 sz20 v0 hi20 hi10.
ex_elim lo10 lo20 l0 r0.
ex_elim h_bst_l0sz10lo10hi10_5350 h_bst_r0sz20lo20hi20_5360.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2] [phi_bst_sz2lo2hi2_b3] [phi_bst_sz2lo2hi2_b4] [phi_bst_sz2lo2hi2_b5] [phi_bst_sz2lo2hi2_b6] [phi_bst_sz2lo2hi2_b7] [phi_bst_sz2lo2hi2_b8].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
move=>[H_bst_l0sz10lo10hi10_5350 H_bst_r0sz20lo20hi20_5360].
ssl_inconsistency.
ex_elim sz1l2 sz2l2 vl2 hi2l2 hi1l2.
ex_elim lo1l2 lo2l2 ll2 rl2.
ex_elim h_bst_ll2sz1l2lo1l2hi1l2_535l2 h_bst_rl2sz2l2lo2l2hi2l2_536l2.
move=>[phi_bst_l2sz1lo1hi1_a0] [phi_bst_l2sz1lo1hi1_a1] [phi_bst_l2sz1lo1hi1_a2] [phi_bst_l2sz1lo1hi1_a3] [phi_bst_l2sz1lo1hi1_a4] [phi_bst_l2sz1lo1hi1_a5] [phi_bst_l2sz1lo1hi1_a6] [phi_bst_l2sz1lo1hi1_a7] [phi_bst_l2sz1lo1hi1_a8].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst h_bst_l2sz1lo1hi1_a.
move=>[H_bst_ll2sz1l2lo1l2hi1l2_535l2 H_bst_rl2sz2l2lo2l2hi2l2_536l2].
try rename h_bst_l2sz1lo1hi1_a into h_bst_l2sz1lo1hi2l2vl2vl2hi2l2_a.
try rename H_bst_l2sz1lo1hi1_a into H_bst_l2sz1lo1hi2l2vl2vl2hi2l2_a.
try rename h_bst_ysz1sz2l2lo2lo1l2hi1hi2_c into h_bst_ysz1sz2l2lo2lo1l2hi2l2vl2vl2hi2l2hi2_c.
try rename H_bst_ysz1sz2l2lo2lo1l2hi1hi2_c into H_bst_ysz1sz2l2lo2lo1l2hi2l2vl2vl2hi2l2hi2_c.
try rename h_bst_l2sz1lo1hi2l2vl2vl2hi2l2_a into h_bst_l2sz1vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a.
try rename H_bst_l2sz1lo1hi2l2vl2vl2hi2l2_a into H_bst_l2sz1vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a.
try rename h_bst_ysz1sz2l2lo2lo1l2hi2l2vl2vl2hi2l2hi2_c into h_bst_ysz1sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c.
try rename H_bst_ysz1sz2l2lo2lo1l2hi2l2vl2vl2hi2l2hi2_c into H_bst_ysz1sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c.
try rename h_bst_ysz1sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c into h_bst_ysz1l2sz2l2sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c.
try rename H_bst_ysz1sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c into H_bst_ysz1l2sz2l2sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c.
try rename h_bst_l2sz1vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a into h_bst_l2sz1l2sz2l2vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a.
try rename H_bst_l2sz1vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a into H_bst_l2sz1l2sz2l2vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a.
ssl_read l2.
try rename vl2 into vl22.
try rename h_bst_ysz1l2sz2l2sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c into h_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2hi2_c.
try rename H_bst_ysz1l2sz2l2sz2l2lo2vl2lo1l2vl2lo1l2l2hi2l2vl2vl2hi2l2hi2_c into H_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2hi2_c.
try rename h_bst_l2sz1l2sz2l2vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a into h_bst_l2sz1l2sz2l2vl22lo1l2vl22lo1l2hi2l2vl22vl22hi2l2_a.
try rename H_bst_l2sz1l2sz2l2vl2lo1l2vl2lo1l2hi2l2vl2vl2hi2l2_a into H_bst_l2sz1l2sz2l2vl22lo1l2vl22lo1l2hi2l2vl22vl22hi2l2_a.
ssl_read (l2 .+ 1).
try rename ll2 into ll22.
try rename h_bst_ll2sz1l2lo1l2hi1l2_535l2 into h_bst_ll22sz1l2lo1l2hi1l2_535l2.
try rename H_bst_ll2sz1l2lo1l2hi1l2_535l2 into H_bst_ll22sz1l2lo1l2hi1l2_535l2.
ssl_read (l2 .+ 2).
try rename rl2 into rl22.
try rename h_bst_rl2sz2l2lo2l2hi2l2_536l2 into h_bst_rl22sz2l2lo2l2hi2l2_536l2.
try rename H_bst_rl2sz2l2lo2l2hi2l2_536l2 into H_bst_rl22sz2l2lo2l2hi2l2_536l2.
ssl_open ((null) == (null)) H_bst_sz2lo2hi2_b.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
try rename h_bst_sz2lo2hi2_b into h_bst_sz2lo2_b.
try rename H_bst_sz2lo2hi2_b into H_bst_sz2lo2_b.
try rename h_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2hi2_c into h_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename H_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2hi2_c into H_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename h_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into h_bst_ysz1l2sz2l2sz2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename H_bst_ysz1l2sz2l2sz2l2lo2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into H_bst_ysz1l2sz2l2sz2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename h_bst_sz2lo2_b into h_bst_sz2_b.
try rename H_bst_sz2lo2_b into H_bst_sz2_b.
try rename h_bst_sz2_b into h_bst__b.
try rename H_bst_sz2_b into H_bst__b.
try rename h_bst_ysz1l2sz2l2sz2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into h_bst_ysz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename H_bst_ysz1l2sz2l2sz2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into H_bst_ysz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename h_bst_l1ysz11ylo11yhi11y_535y into h_bst_ll22sz1l2lo1l2hi1l2_535l2.
try rename H_bst_l1ysz11ylo11yhi11y_535y into H_bst_ll22sz1l2lo1l2hi1l2_535l2.
try rename h_bst_r1ysz21ylo21yhi21y_536y into h_bst_rl22sz2l2lo2l2hi2l2_536l2.
try rename H_bst_r1ysz21ylo21yhi21y_536y into H_bst_rl22sz2l2lo2l2hi2l2_536l2.
try rename h_bst_ysz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into h_bst_l2sz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
try rename H_bst_ysz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c into H_bst_l2sz1l2sz2l2l2vl22lo1l2vl22lo1l2l2hi2l2vl22vl22hi2l2_c.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if (null) == (null) then (if (l2) == (null) then 0 else (if (hi2l2) <= (vl22) then vl22 else hi2l2)) else 0)), ((if (l2) == (null) then (if (null) == (null) then 7 else 7) else (if (vl22) <= (lo1l2) then vl22 else lo1l2))), ((((1) + (sz1l2)) + (sz2l2)) + (0)), (l2);
exists (l2 :-> vl22 \+ l2 .+ 1 :-> ll22 \+ l2 .+ 2 :-> rl22 \+ h_bst_ll22sz1l2lo1l2hi1l2_535l2 \+ h_bst_rl22sz2l2lo2l2hi2l2_536l2);
sslauto.
ssl_close 2;
exists (sz1l2), (sz2l2), (vl22), (hi2l2), (hi1l2), (lo1l2), (lo2l2), (ll22), (rl22), (h_bst_ll22sz1l2lo1l2hi1l2_535l2), (h_bst_rl22sz2l2lo2l2hi2l2_536l2);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
ex_elim sz10 sz20 v0 hi20 hi10.
ex_elim lo10 lo20 l0 r0.
ex_elim h_bst_l0sz10lo10hi10_5350 h_bst_r0sz20lo20hi20_5360.
move=>[phi_bst_sz2lo2hi2_b0] [phi_bst_sz2lo2hi2_b1] [phi_bst_sz2lo2hi2_b2] [phi_bst_sz2lo2hi2_b3] [phi_bst_sz2lo2hi2_b4] [phi_bst_sz2lo2hi2_b5] [phi_bst_sz2lo2hi2_b6] [phi_bst_sz2lo2hi2_b7] [phi_bst_sz2lo2hi2_b8].
move=>[sigma_bst_sz2lo2hi2_b].
subst h_bst_sz2lo2hi2_b.
move=>[H_bst_l0sz10lo10hi10_5350 H_bst_r0sz20lo20hi20_5360].
ssl_inconsistency.
Qed.