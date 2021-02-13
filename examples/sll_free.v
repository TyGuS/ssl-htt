From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_540,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_540 /\ sll nxt s1 h_sll_nxts1_540.

Lemma sll_perm_eq_trans22 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans22: ssl_pred.

Definition sll_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_541,
      h = h_sll_xs_541 /\ sll x s h_sll_xs_541,
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
        vx2 <-- @read nat x;
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
ex_elim h_sll_xs_541.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_541.
ssl_ghostelim_post.
ssl_open (x == null) H_sll_xs_541.
move=>[phi_sll_xs_5410].
move=>[sigma_sll_xs_541].
subst h_sll_xs_541.
shelve.
ex_elim vx s1x nxtx.
ex_elim h_sll_nxtxs1x_540x.
move=>[phi_sll_xs_5410].
move=>[sigma_sll_xs_541].
subst h_sll_xs_541.
move=>H_sll_nxtxs1x_540x.
shelve.
Unshelve.
try rename h_sll_xs_541 into h_sll_x_541.
try rename H_sll_xs_541 into H_sll_x_541.
ssl_emp;
sslauto.
try rename h_sll_xs_541 into h_sll_xvxs1x_541.
try rename H_sll_xs_541 into H_sll_xvxs1x_541.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xvxs1x_541 into h_sll_xvx2s1x_541.
try rename H_sll_xvxs1x_541 into H_sll_xvx2s1x_541.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxs1x_540x into h_sll_nxtx2s1x_540x.
try rename H_sll_nxtxs1x_540x into H_sll_nxtx2s1x_540x.
ssl_call_pre (h_sll_nxtx2s1x_540x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_540x);
sslauto.
move=>h_call0.
move=>[sigma_call0].
subst h_call0.
store_valid.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_emp;
sslauto.
Qed.