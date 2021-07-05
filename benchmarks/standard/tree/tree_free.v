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

Definition tree_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_tree_xs_5,
      h = h_tree_xs_5 /\ tree x s h_tree_xs_5,
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
        vx1 <-- @read nat x;
        lx1 <-- @read ptr (x .+ 1);
        rx1 <-- @read ptr (x .+ 2);
        tree_free (lx1);;
        tree_free (rx1);;
        dealloc x;;
        dealloc (x .+ 1);;
        dealloc (x .+ 2);;
        ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
ex_elim h_tree_xs_5.
move=>[sigma_self].
subst h_self.
move=>H_tree_xs_5.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_tree_xs_5.
move=>[phi_tree_xs_50].
move=>[sigma_tree_xs_5].
subst h_tree_xs_5.
try rename h_tree_xs_5 into h_tree_x_5.
try rename H_tree_xs_5 into H_tree_x_5.
ssl_emp;
sslauto.
ex_elim vx s1x s2x lx rx.
ex_elim h_tree_lxs1x_0x h_tree_rxs2x_1x.
move=>[phi_tree_xs_50].
move=>[sigma_tree_xs_5].
subst h_tree_xs_5.
move=>[H_tree_lxs1x_0x H_tree_rxs2x_1x].
try rename h_tree_xs_5 into h_tree_xvxs1xs2x_5.
try rename H_tree_xs_5 into H_tree_xvxs1xs2x_5.
ssl_read x.
try rename vx into vx1.
try rename h_tree_xvxs1xs2x_5 into h_tree_xvx1s1xs2x_5.
try rename H_tree_xvxs1xs2x_5 into H_tree_xvx1s1xs2x_5.
ssl_read (x .+ 1).
try rename lx into lx1.
try rename h_tree_lxs1x_0x into h_tree_lx1s1x_0x.
try rename H_tree_lxs1x_0x into H_tree_lx1s1x_0x.
ssl_read (x .+ 2).
try rename rx into rx1.
try rename h_tree_rxs2x_1x into h_tree_rx1s2x_1x.
try rename H_tree_rxs2x_1x into H_tree_rx1s2x_1x.
try rename h_tree_x1s1_51 into h_tree_lx1s1x_0x.
try rename H_tree_x1s1_51 into H_tree_lx1s1x_0x.
ssl_call_pre (h_tree_lx1s1x_0x).
ssl_call (s1x).
exists (h_tree_lx1s1x_0x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
move=>[sigma_call0].
subst h_call0.
store_valid.
try rename h_tree_x2s2_52 into h_tree_rx1s2x_1x.
try rename H_tree_x2s2_52 into H_tree_rx1s2x_1x.
ssl_call_pre (h_tree_rx1s2x_1x).
ssl_call (s2x).
exists (h_tree_rx1s2x_1x);
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