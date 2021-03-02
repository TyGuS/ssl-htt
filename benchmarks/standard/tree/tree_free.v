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

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_564,
      h = h_tree_xs_564 /\ tree x s h_tree_xs_564,
    [vfun (_: unit) h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      h = empty
    ]).

Program Definition tree_free : tree_free_type :=
  Fix (fun (tree_free : tree_free_type) vprogs =>
    let: (x) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx2 <-- @read nat x;
        lx2 <-- @read ptr (x .+ 1);
        rx2 <-- @read ptr (x .+ 2);
        tree_free (lx2);;
        tree_free (rx2);;
        dealloc x;;
        dealloc (x .+ 1);;
        dealloc (x .+ 2);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_tree_xs_564.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_564.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_tree_xs_564.
move=>[phi_tree_xs_5640].
move=>[sigma_tree_xs_564].
subst h_tree_xs_564.
try rename h_tree_xs_564 into h_tree_x_564.
try rename H_tree_xs_564 into H_tree_x_564.
ssl_emp;
sslauto.
ex_elim vx s1x s2x lx rx.
ex_elim h_tree_lxs1x_559x h_tree_rxs2x_560x.
move=>[phi_tree_xs_5640].
move=>[sigma_tree_xs_564].
subst h_tree_xs_564.
move=>[H_tree_lxs1x_559x H_tree_rxs2x_560x].
try rename h_tree_xs_564 into h_tree_xvxs1xs2x_564.
try rename H_tree_xs_564 into H_tree_xvxs1xs2x_564.
ssl_read x.
try rename vx into vx2.
try rename h_tree_xvxs1xs2x_564 into h_tree_xvx2s1xs2x_564.
try rename H_tree_xvxs1xs2x_564 into H_tree_xvx2s1xs2x_564.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_tree_lxs1x_559x into h_tree_lx2s1x_559x.
try rename H_tree_lxs1x_559x into H_tree_lx2s1x_559x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_tree_rxs2x_560x into h_tree_rx2s2x_560x.
try rename H_tree_rxs2x_560x into H_tree_rx2s2x_560x.
try rename h_tree_x1s1_5641 into h_tree_lx2s1x_559x.
try rename H_tree_x1s1_5641 into H_tree_lx2s1x_559x.
ssl_call_pre (h_tree_lx2s1x_559x).
ssl_call (s1x).
exists (h_tree_lx2s1x_559x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
move=>[sigma_call0].
subst h_call0.
store_valid.
try rename h_tree_x2s2_5642 into h_tree_rx2s2x_560x.
try rename H_tree_x2s2_5642 into H_tree_rx2s2x_560x.
ssl_call_pre (h_tree_rx2s2x_560x).
ssl_call (s2x).
exists (h_tree_rx2s2x_560x);
sslauto.
ssl_frame_unfold.
move=>h_call1.
move=>[sigma_call1].
subst h_call1.
store_valid.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_dealloc (x .+ 2).
ssl_emp;
sslauto.
Qed.