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
Set Hammer ATPLimit 60.
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
      exists h_sll_xs_1,
      h = h_sll_xs_1 /\ sll x s h_sll_xs_1,
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
        vx1 <-- @read nat x;
        nxtx1 <-- @read ptr (x .+ 1);
        sll_free (nxtx1);;
        dealloc x;;
        dealloc (x .+ 1);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_sll_xs_1.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_1.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xs_1.
move=>[phi_sll_xs_10].
move=>[sigma_sll_xs_1].
subst h_sll_xs_1.
try rename h_sll_xs_1 into h_sll_x_1.
try rename H_sll_xs_1 into H_sll_x_1.
ssl_emp;
sslauto.
ex_elim vx s1x nxtx.
ex_elim h_sll_nxtxs1x_0x.
move=>[phi_sll_xs_10].
move=>[sigma_sll_xs_1].
subst h_sll_xs_1.
move=>H_sll_nxtxs1x_0x.
try rename h_sll_xs_1 into h_sll_xvxs1x_1.
try rename H_sll_xs_1 into H_sll_xvxs1x_1.
ssl_read x.
try rename vx into vx1.
try rename h_sll_xvxs1x_1 into h_sll_xvx1s1x_1.
try rename H_sll_xvxs1x_1 into H_sll_xvx1s1x_1.
ssl_read (x .+ 1).
try rename nxtx into nxtx1.
try rename h_sll_nxtxs1x_0x into h_sll_nxtx1s1x_0x.
try rename H_sll_nxtxs1x_0x into H_sll_nxtx1s1x_0x.
try rename h_sll_x1s1_11 into h_sll_nxtx1s1x_0x.
try rename H_sll_x1s1_11 into H_sll_nxtx1s1x_0x.
ssl_call_pre (h_sll_nxtx1s1x_0x).
ssl_call (s1x).
exists (h_sll_nxtx1s1x_0x);
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