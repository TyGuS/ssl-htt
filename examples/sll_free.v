From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| sll2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) nxt,
  exists h_sll_nxts1_529,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_529 /\ sll nxt s1 h_sll_nxts1_529.

Definition sll_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_530,
      h = h_sll_xs_530 /\ sll x s h_sll_xs_530,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).
Program Definition sll_free : sll_free_type :=
  Fix (fun (sll_free : sll_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if x == 0
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
ex_elim h_sll_xs_530.
move=>[sigma_self].
subst.
move=>H_sll_xs_530.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll_xs_530.
move=>[phi_sll_xs_530].
move=>[sigma_sll_xs_530].
subst.
ssl_emp;
sslauto.
ssl_open_post H_sll_xs_530.
ex_elim vx2 s1x nxtx2.
ex_elim h_sll_nxtx2s1x_529x.
move=>[phi_sll_xs_530].
move=>[sigma_sll_xs_530].
subst.
move=>H_sll_nxtx2s1x_529x.
ssl_read.
ssl_call_pre (h_sll_nxtx2s1x_529x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_529x);
sslauto.
move=>h_call8.
move=>[sigma_call8].
subst.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
sslauto.

Qed.
