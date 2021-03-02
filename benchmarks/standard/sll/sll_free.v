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

Definition sll_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_sll_xs_526,
      h = h_sll_xs_526 /\ sll x s h_sll_xs_526,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).

Program Definition sll_free : sll_free_type :=
  Fix (fun (sll_free : sll_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if (x) == (null)
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
ex_elim h_sll_xs_526.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_526.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xs_526.
move=>[phi_sll_xs_5260].
move=>[sigma_sll_xs_526].
subst h_sll_xs_526.
try rename h_sll_xs_526 into h_sll_x_526.
try rename H_sll_xs_526 into H_sll_x_526.
ssl_emp;
sslauto.
ex_elim vx s1x nxtx.
ex_elim h_sll_nxtxs1x_525x.
move=>[phi_sll_xs_5260].
move=>[sigma_sll_xs_526].
subst h_sll_xs_526.
move=>H_sll_nxtxs1x_525x.
try rename h_sll_xs_526 into h_sll_xvxs1x_526.
try rename H_sll_xs_526 into H_sll_xvxs1x_526.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xvxs1x_526 into h_sll_xvx2s1x_526.
try rename H_sll_xvxs1x_526 into H_sll_xvx2s1x_526.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxs1x_525x into h_sll_nxtx2s1x_525x.
try rename H_sll_nxtxs1x_525x into H_sll_nxtx2s1x_525x.
try rename h_sll_x1s1_5261 into h_sll_nxtx2s1x_525x.
try rename H_sll_x1s1_5261 into H_sll_nxtx2s1x_525x.
ssl_call_pre (h_sll_nxtx2s1x_525x).
ssl_call (s1x).
exists (h_sll_nxtx2s1x_525x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
move=>[sigma_call0].
subst h_call0.
store_valid.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_emp;
sslauto.
Qed.