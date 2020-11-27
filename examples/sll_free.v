From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  perm_eq (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_535,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_535 /\ sll nxt s1 h_sll_nxts1_535.

Definition sll_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_536,
      h = h_sll_xs_536 /\ sll x s h_sll_xs_536,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).
Program Definition sll_free : sll_free_type :=
  Fix (fun (sll_free : sll_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if x == null
      then
        ret tt
      else
        nxtx2 <-- @read ptr (x .+ 1);
        sll_free (nxtx2);;
        dealloc x;;
        dealloc (x .+ 1);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_sll_xs_536.
move=>[sigma_self].
subst.
move=>H_sll_xs_536.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_xs_536.
move=>[phi_sll_xs_536].
move=>[sigma_sll_xs_536].
subst.
ssl_emp;
sslauto.
ssl_open_post H_sll_xs_536.
ex_elim vx2 s1x nxtx2.
ex_elim h_sll_nxtx2s1x_535x.
move=>[phi_sll_xs_536].
move=>[sigma_sll_xs_536].
subst.
move=>H_sll_nxtx2s1x_535x.
ssl_read (x .+ 1).
ssl_call_pre (h_sll_nxtx2s1x_535x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_535x);
sslauto.
move=>h_call10.
move=>[sigma_call10].
subst.
store_valid.
ssl_dealloc (x).
ssl_dealloc (x .+ 1).
ssl_emp;
sslauto.

Qed.
