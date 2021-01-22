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
  exists h_bst_lsz1lo1hi1_513 h_bst_rsz2lo2hi2_514,
  0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi == (if hi2 <= v then v else hi2) /\ hi1 <= v /\ lo == (if v <= lo1 then v else lo1) /\ sz == 1 + sz1 + sz2 /\ v <= 7 /\ v <= lo2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_513 \+ h_bst_rsz2lo2hi2_514 /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_513 /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_514.

Lemma pure1 sz2l2 sz2 sz1l2 : 0 <= sz2l2 -> 0 <= sz2 -> 0 <= 1 + sz1l2 + sz2l2 -> 0 <= sz1l2 -> 0 <= 1 + sz2l2 + sz2. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 sz1l2 sz2l2 sz2 : 0 <= sz2l2 -> 0 <= sz2 -> 0 <= 1 + sz1l2 + sz2l2 -> 0 <= sz1l2 -> sz1l2 + 1 + sz2l2 + sz2 == 1 + sz1l2 + sz2l2 + sz2. Admitted.
Hint Resolve pure2: ssl_pure.
Lemma pure3 lo2l2 v2 vl22 hi2l2 lo2 hi1l2 : (if hi2l2 <= vl22 then vl22 else hi2l2) <= v2 -> hi1l2 <= vl22 -> vl22 <= 7 -> 0 <= v2 -> v2 <= lo2 -> 0 <= vl22 -> vl22 <= lo2l2 -> v2 <= 7 -> hi2l2 <= v2. Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 lo2l2 v2 vl22 hi2l2 lo2 hi1l2 : (if hi2l2 <= vl22 then vl22 else hi2l2) <= v2 -> hi1l2 <= vl22 -> vl22 <= 7 -> 0 <= v2 -> v2 <= lo2 -> 0 <= vl22 -> vl22 <= lo2l2 -> v2 <= 7 -> vl22 <= (if v2 <= lo2l2 then v2 else lo2l2). Admitted.
Hint Resolve pure4: ssl_pure.

Definition bst_right_rotate_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * nat * ptr * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi1 <= v /\ (l == null) = false /\ v <= 7 /\ v <= lo2 /\ h = retv :-> unused \+ x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, l, lo2, lo1, r, hi2, unused) := vghosts in
      exists sz3 sz4 v3 hi3 lo4 l3 lo3 hi4 y,
      exists h_bst_l3sz3lo3hi3_515 h_bst_xsz4lo4hi4_516,
      0 <= sz3 /\ 0 <= sz4 /\ 0 <= v3 /\ hi3 <= v3 /\ sz3 + sz4 == sz1 + sz2 /\ v3 <= 7 /\ v3 <= lo4 /\ h = retv :-> y \+ y :-> v3 \+ y .+ 1 :-> l3 \+ y .+ 2 :-> x \+ h_bst_l3sz3lo3hi3_515 \+ h_bst_xsz4lo4hi4_516 /\ bst l3 sz3 lo3 hi3 h_bst_l3sz3lo3hi3_515 /\ bst x sz4 lo4 hi4 h_bst_xsz4lo4hi4_516
    ]).

Program Definition bst_right_rotate : bst_right_rotate_type :=
  Fix (fun (bst_right_rotate : bst_right_rotate_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      l2 <-- @read ptr (x .+ 1);
      if l2 == null
      then
        ret tt
      else
        rl22 <-- @read ptr (l2 .+ 2);
        (l2 .+ 2) ::= x;;
        retv ::= l2;;
        (x .+ 1) ::= rl22;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[[[[[[sz1 sz2] v2] hi1] l2] lo2] lo1] r2] hi2] unused2].
ex_elim h_bst_l2sz1lo1hi1_a h_bst_r2sz2lo2hi2_b.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3] [phi_self4] [phi_self5] [phi_self6].
move=>[sigma_self].
subst.
move=>[H_bst_l2sz1lo1hi1_a H_bst_r2sz2lo2hi2_b].
ssl_ghostelim_post.
ssl_read (x .+ 1).
ssl_open.
ssl_open_post H_bst_l2sz1lo1hi1_a.
ssl_open_post H_bst_l2sz1lo1hi1_a.
ex_elim sz1l2 sz2l2 vl22 hi2l2 hi1l2.
ex_elim lo1l2 lo2l2 ll22 rl22.
ex_elim h_bst_ll22sz1l2lo1l2hi1l2_513l2 h_bst_rl22sz2l2lo2l2hi2l2_514l2.
move=>[phi_bst_l2sz1lo1hi1_a0] [phi_bst_l2sz1lo1hi1_a1] [phi_bst_l2sz1lo1hi1_a2] [phi_bst_l2sz1lo1hi1_a3] [phi_bst_l2sz1lo1hi1_a4] [phi_bst_l2sz1lo1hi1_a5] [phi_bst_l2sz1lo1hi1_a6] [phi_bst_l2sz1lo1hi1_a7] [phi_bst_l2sz1lo1hi1_a8].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst.
move=>[H_bst_ll22sz1l2lo1l2hi1l2_513l2 H_bst_rl22sz2l2lo2l2hi2l2_514l2].
ssl_read (l2 .+ 2).
ssl_write (l2 .+ 2).
ssl_write_post (l2 .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_emp;
exists (sz1l2), (1 + sz2l2 + sz2), (vl22), (hi1l2), ((if v2 <= lo2l2 then v2 else lo2l2)), (ll22), (lo1l2), ((if hi2 <= v2 then v2 else hi2)), (l2);
exists (h_bst_ll22sz1l2lo1l2hi1l2_513l2);
exists (x :-> v2 \+ x .+ 1 :-> rl22 \+ x .+ 2 :-> r2 \+ h_bst_rl22sz2l2lo2l2hi2l2_514l2 \+ h_bst_r2sz2lo2hi2_b);
sslauto.
unfold_constructor 2;
exists (sz2l2), (sz2), (v2), (hi2), (hi2l2), (lo2l2), (lo2), (rl22), (r2);
exists (h_bst_rl22sz2l2lo2l2hi2l2_514l2);
exists (h_bst_r2sz2lo2hi2_b);
sslauto.
Qed.
