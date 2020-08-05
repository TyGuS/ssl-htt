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
  s = nil /\ h = empty
| lseg2 of ~~ (x == 0) of
  exists v s1 nxt,
  exists h_lseg513,
  s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg513 /\ lseg nxt s1 h_lseg513.

Definition listfree_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
  STsep (
    fun h =>
      let: (x) := vprogs in
      let: (s) := vghosts in
      exists h_lseg514,
      h = h_lseg514 /\ lseg x s h_lseg514,
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
move=>[h_lseg514].
move=>[sigma_self].
rewrite->sigma_self in *.
move=>H_lseg514.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_lseg514.
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
ssl_emp;
ssl_emp_post.
ssl_open_post H_lseg514.
move=>[vx2] [s1x] [nxtx2].
move=>[h_lseg513x].
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
move=>H_lseg513x.
ssl_read.
ssl_call_pre (h_lseg513x).
ssl_call (s1x).
exists (h_lseg513x);
ssl_emp_post.
move=>h_call1.
move=>[sigma_call1].
rewrite->sigma_call1 in *.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.
