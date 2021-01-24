From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive bst (x : ptr) (sz : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| bst_1 of x == null of
  hi == 0 /\ lo == 7 /\ sz == 0 /\ h = empty
| bst_2 of (x == null) = false of
  exists (sz1 : nat) (sz2 : nat) (v : nat) (hi2 : nat) (hi1 : nat) (lo1 : nat) (lo2 : nat) (l : ptr) (r : ptr),
  exists h_bst_lsz1lo1hi1_566 h_bst_rsz2lo2hi2_567,
  0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi == (if hi2 <= v then v else hi2) /\ hi1 <= v /\ lo == (if v <= lo1 then v else lo1) /\ sz == 1 + sz1 + sz2 /\ v <= 7 /\ v <= lo2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_566 \+ h_bst_rsz2lo2hi2_567 /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_566 /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_567.

Lemma pure54 r2 : r2 == null -> (if null == null then (if r2 == null then 7 else 7) else 7) == 7. Admitted.
Hint Resolve pure54: ssl_pure.
Lemma pure55 r2 : r2 == null -> (if r2 == null then (if null == null then 0 else 0) else 0) == 0. Admitted.
Hint Resolve pure55: ssl_pure.
Lemma pure56 : 0 == 0. Admitted.
Hint Resolve pure56: ssl_pure.
Lemma pure57 sz1r2 sz2r2 : 0 <= sz2r2 -> 0 <= sz1r2 -> 0 <= 1 + sz1r2 + sz2r2 -> 1 + sz1r2 + sz2r2 == 1 + sz1r2 + sz2r2. Admitted.
Hint Resolve pure57: ssl_pure.
Lemma pure58 lo1r2 vr22 x v2 hi1r2 retv lo2r2 hi2r2 r2 : vr22 <= 7 -> (r2 == retv) = false -> (retv == null) = false -> v2 <= (if vr22 <= lo1r2 then vr22 else lo1r2) -> 0 <= v2 -> (r2 == null) = false -> vr22 <= lo2r2 -> 0 <= vr22 -> (r2 == x) = false -> hi1r2 <= vr22 -> (x == null) = false -> (retv == x) = false -> v2 <= 7 -> (if r2 == null then (if null == null then 0 else 0) else (if hi2r2 <= vr22 then vr22 else hi2r2)) == (if hi2r2 <= vr22 then vr22 else hi2r2). Admitted.
Hint Resolve pure58: ssl_pure.
Lemma pure59 lo1r2 vr22 x v2 hi1r2 retv lo2r2 r2 : vr22 <= 7 -> (r2 == retv) = false -> (retv == null) = false -> v2 <= (if vr22 <= lo1r2 then vr22 else lo1r2) -> 0 <= v2 -> (r2 == null) = false -> vr22 <= lo2r2 -> 0 <= vr22 -> (r2 == x) = false -> hi1r2 <= vr22 -> (x == null) = false -> (retv == x) = false -> v2 <= 7 -> (if null == null then (if r2 == null then 7 else (if vr22 <= lo1r2 then vr22 else lo1r2)) else 7) == (if vr22 <= lo1r2 then vr22 else lo1r2). Admitted.
Hint Resolve pure59: ssl_pure.

Definition bst_remove_root_no_left_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * nat * ptr * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi1 <= v /\ l == null /\ v <= 7 /\ v <= lo2 /\ h = retv :-> unused \+ x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists hi lo n1 y,
      exists h_bst_yn1lohi_c,
      hi == (if r == null then (if l == null then 0 else hi1) else hi2) /\ lo == (if l == null then (if r == null then 7 else lo2) else lo1) /\ n1 == sz1 + sz2 /\ h = retv :-> y \+ h_bst_yn1lohi_c /\ bst y n1 lo hi h_bst_yn1lohi_c
    ]).

Program Definition bst_remove_root_no_left : bst_remove_root_no_left_type :=
  Fix (fun (bst_remove_root_no_left : bst_remove_root_no_left_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      r2 <-- @read ptr (x .+ 2);
      if null == null
      then
        if r2 == null
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
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
move=>[[[[[[[[[sz1 sz2] v2] hi1] l] lo2] lo1] r2] hi2] unused2].
ex_elim h_bst_lsz1lo1hi1_a h_bst_r2sz2lo2hi2_b.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3] [phi_self4] [phi_self5] [phi_self6].
move=>[sigma_self].
subst h_self.
move=>[H_bst_lsz1lo1hi1_a H_bst_r2sz2lo2hi2_b].
ssl_ghostelim_post.
ssl_read (x .+ 2).
ssl_open (null == null);
ssl_open_post H_bst_lsz1lo1hi1_a.
move=>[phi_bst_lsz1lo1hi1_a0] [phi_bst_lsz1lo1hi1_a1] [phi_bst_lsz1lo1hi1_a2].
move=>[sigma_bst_lsz1lo1hi1_a].
subst h_bst_lsz1lo1hi1_a.
ssl_open (r2 == null);
ssl_open_post H_bst_r2sz2lo2hi2_b.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if r2 == null then (if null == null then 0 else 0) else 0)), ((if null == null then (if r2 == null then 7 else 7) else 7)), (0 + 0), (null);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto ].
ex_elim sz1r2 sz2r2 vr22 hi2r2 hi1r2.
ex_elim lo1r2 lo2r2 lr22 rr22.
ex_elim h_bst_lr22sz1r2lo1r2hi1r2_566r2 h_bst_rr22sz2r2lo2r2hi2r2_567r2.
move=>[phi_bst_r2sz2lo2hi2_b0] [phi_bst_r2sz2lo2hi2_b1] [phi_bst_r2sz2lo2hi2_b2] [phi_bst_r2sz2lo2hi2_b3] [phi_bst_r2sz2lo2hi2_b4] [phi_bst_r2sz2lo2hi2_b5] [phi_bst_r2sz2lo2hi2_b6] [phi_bst_r2sz2lo2hi2_b7] [phi_bst_r2sz2lo2hi2_b8].
move=>[sigma_bst_r2sz2lo2hi2_b].
subst h_bst_r2sz2lo2hi2_b.
move=>[H_bst_lr22sz1r2lo1r2hi1r2_566r2 H_bst_rr22sz2r2lo2r2hi2r2_567r2].
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if r2 == null then (if null == null then 0 else 0) else (if hi2r2 <= vr22 then vr22 else hi2r2))), ((if null == null then (if r2 == null then 7 else (if vr22 <= lo1r2 then vr22 else lo1r2)) else 7)), (0 + 1 + sz1r2 + sz2r2), (r2);
exists (r2 :-> vr22 \+ r2 .+ 1 :-> lr22 \+ r2 .+ 2 :-> rr22 \+ h_bst_lr22sz1r2lo1r2hi1r2_566r2 \+ h_bst_rr22sz2r2lo2r2hi2r2_567r2);
sslauto;
solve [
unfold_constructor 2;
exists (sz1r2), (sz2r2), (vr22), (hi2r2), (hi1r2), (lo1r2), (lo2r2), (lr22), (rr22);
exists (h_bst_lr22sz1r2lo1r2hi1r2_566r2);
exists (h_bst_rr22sz2r2lo2r2hi2r2_567r2);
sslauto ].
Qed.
