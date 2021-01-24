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
  exists h_bst_lsz1lo1hi1_572 h_bst_rsz2lo2hi2_573,
  0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi == (if hi2 <= v then v else hi2) /\ hi1 <= v /\ lo == (if v <= lo1 then v else lo1) /\ sz == 1 + sz1 + sz2 /\ v <= 7 /\ v <= lo2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_572 \+ h_bst_rsz2lo2hi2_573 /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_572 /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_573.

Lemma pure82 l2 : l2 == null -> (if null == null then (if l2 == null then 0 else 0) else 0) == 0. Admitted.
Hint Resolve pure82: ssl_pure.
Lemma pure83 l2 : l2 == null -> (if l2 == null then (if null == null then 7 else 7) else 7) == 7. Admitted.
Hint Resolve pure83: ssl_pure.
Lemma pure84 : 0 == 0. Admitted.
Hint Resolve pure84: ssl_pure.
Lemma pure85 sz1l2 sz2l2 : 0 <= 1 + sz1l2 + sz2l2 -> 0 <= sz1l2 -> 0 <= sz2l2 -> 1 + sz1l2 + sz2l2 == 1 + sz1l2 + sz2l2. Admitted.
Hint Resolve pure85: ssl_pure.
Lemma pure86 lo2l2 x v2 retv vl22 l2 hi2l2 hi1l2 : (if hi2l2 <= vl22 then vl22 else hi2l2) <= v2 -> hi1l2 <= vl22 -> vl22 <= 7 -> (retv == null) = false -> (l2 == x) = false -> 0 <= v2 -> (l2 == retv) = false -> (l2 == null) = false -> (x == null) = false -> 0 <= vl22 -> (retv == x) = false -> vl22 <= lo2l2 -> v2 <= 7 -> (if null == null then (if l2 == null then 0 else (if hi2l2 <= vl22 then vl22 else hi2l2)) else 0) == (if hi2l2 <= vl22 then vl22 else hi2l2). Admitted.
Hint Resolve pure86: ssl_pure.
Lemma pure87 lo2l2 x v2 retv lo1l2 vl22 l2 hi2l2 hi1l2 : (if hi2l2 <= vl22 then vl22 else hi2l2) <= v2 -> hi1l2 <= vl22 -> vl22 <= 7 -> (retv == null) = false -> (l2 == x) = false -> 0 <= v2 -> (l2 == retv) = false -> (l2 == null) = false -> (x == null) = false -> 0 <= vl22 -> (retv == x) = false -> vl22 <= lo2l2 -> v2 <= 7 -> (if l2 == null then (if null == null then 7 else 7) else (if vl22 <= lo1l2 then vl22 else lo1l2)) == (if vl22 <= lo1l2 then vl22 else lo1l2). Admitted.
Hint Resolve pure87: ssl_pure.

Definition bst_remove_root_no_right_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat * ptr * nat * ptr * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi1 <= v /\ r == null /\ v <= 7 /\ v <= lo2 /\ h = retv :-> unused \+ x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (sz1, sz2, v, hi1, r, lo2, l, lo1, hi2, unused) := vghosts in
      exists hi lo n1 y,
      exists h_bst_yn1lohi_c,
      hi == (if r == null then (if l == null then 0 else hi1) else hi2) /\ lo == (if l == null then (if r == null then 7 else lo2) else lo1) /\ n1 == sz1 + sz2 /\ h = retv :-> y \+ h_bst_yn1lohi_c /\ bst y n1 lo hi h_bst_yn1lohi_c
    ]).

Program Definition bst_remove_root_no_right : bst_remove_root_no_right_type :=
  Fix (fun (bst_remove_root_no_right : bst_remove_root_no_right_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      l2 <-- @read ptr (x .+ 1);
      if l2 == null
      then
        if null == null
        then
          dealloc x;;
          dealloc (x .+ 1);;
          dealloc (x .+ 2);;
          retv ::= null;;
          ret tt
        else
          ret tt
      else
        if null == null
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
move=>[[[[[[[[[sz1 sz2] v2] hi1] r] lo2] l2] lo1] hi2] unused2].
ex_elim h_bst_l2sz1lo1hi1_a h_bst_rsz2lo2hi2_b.
move=>[phi_self0] [phi_self1] [phi_self2] [phi_self3] [phi_self4] [phi_self5] [phi_self6].
move=>[sigma_self].
subst h_self.
move=>[H_bst_l2sz1lo1hi1_a H_bst_rsz2lo2hi2_b].
ssl_ghostelim_post.
ssl_read (x .+ 1).
ssl_open (l2 == null);
ssl_open_post H_bst_l2sz1lo1hi1_a.
move=>[phi_bst_l2sz1lo1hi1_a0] [phi_bst_l2sz1lo1hi1_a1] [phi_bst_l2sz1lo1hi1_a2].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst h_bst_l2sz1lo1hi1_a.
ssl_open (null == null);
ssl_open_post H_bst_rsz2lo2hi2_b.
move=>[phi_bst_rsz2lo2hi2_b0] [phi_bst_rsz2lo2hi2_b1] [phi_bst_rsz2lo2hi2_b2].
move=>[sigma_bst_rsz2lo2hi2_b].
subst h_bst_rsz2lo2hi2_b.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if null == null then (if l2 == null then 0 else 0) else 0)), ((if l2 == null then (if null == null then 7 else 7) else 7)), (0 + 0), (null);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto ].
ex_elim sz1l2 sz2l2 vl22 hi2l2 hi1l2.
ex_elim lo1l2 lo2l2 ll22 rl22.
ex_elim h_bst_ll22sz1l2lo1l2hi1l2_572l2 h_bst_rl22sz2l2lo2l2hi2l2_573l2.
move=>[phi_bst_l2sz1lo1hi1_a0] [phi_bst_l2sz1lo1hi1_a1] [phi_bst_l2sz1lo1hi1_a2] [phi_bst_l2sz1lo1hi1_a3] [phi_bst_l2sz1lo1hi1_a4] [phi_bst_l2sz1lo1hi1_a5] [phi_bst_l2sz1lo1hi1_a6] [phi_bst_l2sz1lo1hi1_a7] [phi_bst_l2sz1lo1hi1_a8].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst h_bst_l2sz1lo1hi1_a.
move=>[H_bst_ll22sz1l2lo1l2hi1l2_572l2 H_bst_rl22sz2l2lo2l2hi2l2_573l2].
ssl_open (null == null);
ssl_open_post H_bst_rsz2lo2hi2_b.
move=>[phi_bst_rsz2lo2hi2_b0] [phi_bst_rsz2lo2hi2_b1] [phi_bst_rsz2lo2hi2_b2].
move=>[sigma_bst_rsz2lo2hi2_b].
subst h_bst_rsz2lo2hi2_b.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if null == null then (if l2 == null then 0 else (if hi2l2 <= vl22 then vl22 else hi2l2)) else 0)), ((if l2 == null then (if null == null then 7 else 7) else (if vl22 <= lo1l2 then vl22 else lo1l2))), (1 + sz1l2 + sz2l2 + 0), (l2);
exists (l2 :-> vl22 \+ l2 .+ 1 :-> ll22 \+ l2 .+ 2 :-> rl22 \+ h_bst_ll22sz1l2lo1l2hi1l2_572l2 \+ h_bst_rl22sz2l2lo2l2hi2l2_573l2);
sslauto;
solve [
unfold_constructor 2;
exists (sz1l2), (sz2l2), (vl22), (hi2l2), (hi1l2), (lo1l2), (lo2l2), (ll22), (rl22);
exists (h_bst_ll22sz1l2lo1l2hi1l2_572l2);
exists (h_bst_rl22sz2l2lo2l2hi2l2_573l2);
sslauto ].
Qed.
