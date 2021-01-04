From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive bst (x : ptr) (sz : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| bst1 of x == null of
  hi == 0 /\ lo == 7 /\ sz == 0 /\ h = empty
| bst2 of ~~ (x == null) of
  exists (sz1 : nat) (sz2 : nat) (v : nat) (hi2 : nat) (hi1 : nat) (lo1 : nat) (lo2 : nat) (l : ptr) (r : ptr),
  exists h_bst_lsz1lo1hi1_513 h_bst_rsz2lo2hi2_514,
  0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi == (if hi2 <= v then v else hi2) /\ hi1 <= v /\ lo == (if v <= lo1 then v else lo1) /\ sz == 1 + sz1 + sz2 /\ v <= 7 /\ v <= lo2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_513 \+ h_bst_rsz2lo2hi2_514 /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_513 /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_514.


Hypothesis pure1:
  forall v2 vr22 hi1 hi1r2 lo1r2 lo2r2,
    0 <= v2 ->
    0 <= vr22 ->
    hi1 <= v2 ->
    hi1r2 <= vr22 ->
    v2 <= (if vr22 <= lo1r2 then vr22 else lo1r2) ->
    v2 <= 7 ->
    vr22 <= 7 ->
    vr22 <= lo2r2 ->
    (if hi1r2 <= v2 then v2 else hi1r2) <= vr22.

Hypothesis pure2:
  forall v2 vr22 hi1 hi1r2 lo1r2 lo2r2,
    0 <= v2 ->
    0 <= vr22 ->
    hi1 <= v2 ->
    hi1r2 <= vr22 ->
    v2 <= (if vr22 <= lo1r2 then vr22 else lo1r2) ->
    v2 <= 7 ->
    vr22 <= 7 ->
    vr22 <= lo2r2 ->
    v2 <= lo1r2.

Hint Resolve pure1 : ssl_pure.
Hint Resolve pure2 : ssl_pure.

Definition bst_left_rotate_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr * nat * nat * ptr * nat * ptr * nat)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (v, sz2, hi2, unused, hi1, lo2, r, sz1, l, lo1) := vghosts in
      exists h_bst_lsz1lo1hi1_a h_bst_rsz2lo2hi2_b,
      (* TODO: detect and elide cardinality vars a and b  *)
      (*0 <= a /\ 0 <= b /\ *)0 <= sz1 /\ 0 <= sz2 /\ 0 <= v /\ hi1 <= v /\ ~~ (r == null) /\ v <= 7 /\ v <= lo2 /\ h = retv :-> unused \+ x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_bst_lsz1lo1hi1_a \+ h_bst_rsz2lo2hi2_b /\ bst l sz1 lo1 hi1 h_bst_lsz1lo1hi1_a /\ bst r sz2 lo2 hi2 h_bst_rsz2lo2hi2_b,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (v, sz2, hi2, unused, hi1, lo2, r, sz1, l, lo1) := vghosts in
      exists sz3 sz4 v3 hi3 lo4 lo3 r3 hi4 y,
      exists h_bst_xsz3lo3hi3_515 h_bst_r3sz4lo4hi4_516,
      0 <= sz3 /\ 0 <= sz4 /\ 0 <= v3 /\ hi3 <= v3 /\ sz3 + sz4 == sz1 + sz2 /\ v3 <= 7 /\ v3 <= lo4 /\ h = retv :-> y \+ y :-> v3 \+ y .+ 1 :-> x \+ y .+ 2 :-> r3 \+ h_bst_xsz3lo3hi3_515 \+ h_bst_r3sz4lo4hi4_516 /\ bst x sz3 lo3 hi3 h_bst_xsz3lo3hi3_515 /\ bst r3 sz4 lo4 hi4 h_bst_r3sz4lo4hi4_516
    ]).
Program Definition bst_left_rotate : bst_left_rotate_type :=
  Fix (fun (bst_left_rotate : bst_left_rotate_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      r2 <-- @read ptr (x .+ 2);
      if r2 == null
      then
        ret tt
      else
        lr22 <-- @read ptr (r2 .+ 1);
        (r2 .+ 1) ::= x;;
        retv ::= r2;;
        (x .+ 2) ::= lr22;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[[[[[[v2 sz2] hi2] unused2] hi1] lo2] r2] sz1] l2] lo1].
ex_elim h_bst_l2sz1lo1hi1_a h_bst_r2sz2lo2hi2_b.
move=>[phi_self0][phi_self1][phi_self2][phi_self3][phi_self4][phi_self5][phi_self6](*[phi_self7][phi_self8]*).
move=>[sigma_self].
subst.
move=>[H_bst_l2sz1lo1hi1_a H_bst_r2sz2lo2hi2_b].
ssl_ghostelim_post.
ssl_read (x .+ 2).
ssl_open.
(* TODO: why is the wrong hypothesis used *)
ssl_open_post H_bst_r2sz2lo2hi2_b. (* H_bst_l2sz1lo1hi1_a *)
ssl_open_post H_bst_r2sz2lo2hi2_b.
(*move=>[phi_bst_l2sz1lo1hi1_a].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst.
ssl_open_post H_bst_l2sz1lo1hi1_a.*)
ex_elim sz1r2 sz2r2 vr22 hi2r2 hi1r2.
ex_elim lo1r2 lo2r2 lr22 rr22.
ex_elim h_bst_lr22sz1r2lo1r2hi1r2_513r2 h_bst_rr22sz2r2lo2r2hi2r2_514r2.
move=>[phi_bst_l2sz1lo1hi1_a0][phi_bst_l2sz1lo1hi1_a1][phi_bst_l2sz1lo1hi1_a2][phi_bst_l2sz1lo1hi1_a3][phi_bst_l2sz1lo1hi1_a4][phi_bst_l2sz1lo1hi1_a5][phi_bst_l2sz1lo1hi1_a6][phi_bst_l2sz1lo1hi1_a7][phi_bst_l2sz1lo1hi1_a8].
move=>[sigma_bst_l2sz1lo1hi1_a].
subst.
move=>[H_bst_lr22sz1r2lo1r2hi1r2_513r2 H_bst_rr22sz2r2lo2r2hi2r2_514r2].
ssl_read (r2 .+ 1).
ssl_write (r2 .+ 1).
ssl_write_post (r2 .+ 1).
ssl_write retv.
ssl_write_post retv.
ssl_write (x .+ 2).
ssl_write_post (x .+ 2).
ssl_emp;
exists (1 + sz1 + sz1r2), (sz2r2), (vr22), ((if hi1r2 <= v2 then v2 else hi1r2)), (lo2r2), ((if v2 <= lo1 then v2 else lo1)), (rr22), (hi2r2), (r2);
exists (x :-> v2 \+ x .+ 1 :-> l2 \+ x .+ 2 :-> lr22 \+ h_bst_l2sz1lo1hi1_a \+ h_bst_lr22sz1r2lo1r2hi1r2_513r2);
exists (h_bst_rr22sz2r2lo2r2hi2r2_514r2);
sslauto.
rewrite (addnC 1) ?addnA; auto. (* why not solvable with //= ? *)
unfold_constructor 2;
exists (sz1), (sz1r2), (v2), (hi1r2), (hi1), (lo1), (lo1r2), (l2), (lr22);
exists (h_bst_l2sz1lo1hi1_a);
exists (h_bst_lr22sz1r2lo1r2hi1r2_513r2);
sslauto.
Qed.
