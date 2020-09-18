From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| lseg2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_lseg_nxts1_513,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg_nxts1_513 /\ lseg nxt s1 h_lseg_nxts1_513.

Definition listfree_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_lseg_xs_514,
      h = h_lseg_xs_514 /\ lseg x s h_lseg_xs_514,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).
Program Definition listfree : listfree_type :=
  Fix (fun (listfree : listfree_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if x == 0
      then
        ret tt
      else
        nxtx2 <-- @read ptr (x .+ 1);
        listfree (nxtx2);;
        dealloc x;;
        dealloc (x .+ 1);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_lseg_xs_514.
move=>[sigma_self].
subst.
move=>H_lseg_xs_514.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_lseg_xs_514.
move=>[phi_lseg_xs_514].
move=>[sigma_lseg_xs_514].
subst.
ssl_emp;
sslauto.
ssl_open_post H_lseg_xs_514.
ex_elim vx2 s1x nxtx2.
ex_elim h_lseg_nxtx2s1x_513x.
move=>[phi_lseg_xs_514].
move=>[sigma_lseg_xs_514].
subst.
move=>H_lseg_nxtx2s1x_513x.
ssl_read.
ssl_call_pre (h_lseg_nxtx2s1x_513x).
ssl_call (s1x).
exists (h_lseg_nxtx2s1x_513x);
sslauto.
move=>h_call1.
move=>[sigma_call1].
subst.
store_valid.
ssl_dealloc (x).
ssl_dealloc (x .+ 1).
ssl_emp;
sslauto.

Qed.
