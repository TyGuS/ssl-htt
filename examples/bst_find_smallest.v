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

Lemma pure1 : 0 == 0. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 : 7 == 7. Admitted.
Hint Resolve pure2: ssl_pure.
Lemma pure3 hi2x lo2x hi1x vx2 lo1x : hi1x <= vx2 -> vx2 <= lo2x -> (if hi2x <= vx2 then vx2 else hi2x) <= 7 -> 0 <= vx2 -> vx2 <= 7 -> 0 <= (if vx2 <= lo1x then vx2 else lo1x) -> 0 <= lo1x. Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 hi2x lo2x hi1x vx2 lo1x : hi1x <= vx2 -> vx2 <= lo2x -> (if hi2x <= vx2 then vx2 else hi2x) <= 7 -> 0 <= vx2 -> vx2 <= 7 -> 0 <= (if vx2 <= lo1x then vx2 else lo1x) -> hi1x <= 7. Admitted.
Hint Resolve pure4: ssl_pure.
Lemma pure5 sz1x sz2x : 0 <= sz2x -> 0 <= sz1x -> 0 <= 1 + sz1x + sz2x -> 1 + sz1x + sz2x == 1 + sz1x + sz2x. Admitted.
Hint Resolve pure5: ssl_pure.
Lemma pure6 hi2x lo2x hi1x vx2 lo1x2 : 0 <= (if vx2 <= lo1x2 then vx2 else lo1x2) -> hi1x <= vx2 -> vx2 <= lo2x -> (if hi2x <= vx2 then vx2 else hi2x) <= 7 -> 0 <= vx2 -> vx2 <= 7 -> (if vx2 <= lo1x2 then vx2 else lo1x2) == (if vx2 <= lo1x2 then vx2 else lo1x2). Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 hi2x lo2x hi1x vx2 lo1x2 : 0 <= (if vx2 <= lo1x2 then vx2 else lo1x2) -> hi1x <= vx2 -> vx2 <= lo2x -> (if hi2x <= vx2 then vx2 else hi2x) <= 7 -> 0 <= vx2 -> vx2 <= 7 -> (if hi2x <= vx2 then vx2 else hi2x) == (if hi2x <= vx2 then vx2 else hi2x). Admitted.
Hint Resolve pure7: ssl_pure.

Definition bst_find_smallest_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (lo, sz, hi, unused) := vghosts in
      exists h_bst_xszlohi_a,
      0 <= lo /\ 0 <= sz /\ hi <= 7 /\ h = retv :-> unused \+ h_bst_xszlohi_a /\ bst x sz lo hi h_bst_xszlohi_a,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (lo, sz, hi, unused) := vghosts in
      exists h_bst_xszlohi_c,
      h = retv :-> lo \+ h_bst_xszlohi_c /\ bst x sz lo hi h_bst_xszlohi_c
    ]).

Program Definition bst_find_smallest : bst_find_smallest_type :=
  Fix (fun (bst_find_smallest : bst_find_smallest_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      if x == null
      then
        retv ::= 7;;
        ret tt
      else
        vx2 <-- @read nat x;
        lx2 <-- @read ptr (x .+ 1);
        bst_find_smallest (lx2, retv);;
        lo1x2 <-- @read nat retv;
        retv ::= (if vx2 <= lo1x2 then vx2 else lo1x2);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[lo sz] hi] unused2].
ex_elim h_bst_xszlohi_a.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst.
move=>H_bst_xszlohi_a.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_bst_xszlohi_a.
move=>[phi_bst_xszlohi_a0] [phi_bst_xszlohi_a1] [phi_bst_xszlohi_a2].
move=>[sigma_bst_xszlohi_a].
subst.
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_bst_xszlohi_a.
ex_elim sz1x sz2x vx2 hi2x hi1x.
ex_elim lo1x2 lo2x lx2 rx2.
ex_elim h_bst_lx2sz1xlo1x2hi1x_513x h_bst_rx2sz2xlo2xhi2x_514x.
move=>[phi_bst_xszlohi_a0] [phi_bst_xszlohi_a1] [phi_bst_xszlohi_a2] [phi_bst_xszlohi_a3] [phi_bst_xszlohi_a4] [phi_bst_xszlohi_a5] [phi_bst_xszlohi_a6] [phi_bst_xszlohi_a7] [phi_bst_xszlohi_a8].
move=>[sigma_bst_xszlohi_a].
subst.
move=>[H_bst_lx2sz1xlo1x2hi1x_513x H_bst_rx2sz2xlo2xhi2x_514x].
ssl_read x.
ssl_read (x .+ 1).
ssl_call_pre (retv :-> unused2 \+ h_bst_lx2sz1xlo1x2hi1x_513x).
ssl_call (lo1x2, sz1x, hi1x, unused2).
exists (h_bst_lx2sz1xlo1x2hi1x_513x);
sslauto.
move=>h_call1.
ex_elim h_bst_lx2sz1xlo1x2hi1x_c1.
move=>[sigma_call1].
subst.
move=>H_bst_lx2sz1xlo1x2hi1x_c1.
store_valid.
ssl_read retv.
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> lx2 \+ x .+ 2 :-> rx2 \+ h_bst_lx2sz1xlo1x2hi1x_c1 \+ h_bst_rx2sz2xlo2xhi2x_514x);
sslauto.
unfold_constructor 2;
exists (sz1x), (sz2x), (vx2), (hi2x), (hi1x), (lo1x2), (lo2x), (lx2), (rx2);
exists (h_bst_lx2sz1xlo1x2hi1x_c1);
exists (h_bst_rx2sz2xlo2xhi2x_514x);
sslauto.
Qed.
