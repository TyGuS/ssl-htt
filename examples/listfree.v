From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (n : seq nat) (h : heap) : Prop :=
| lseg0 of x == 0 of
    n = nil /\ h = empty
| lseg1 of x != 0 of
  exists nxt n1 v,
  exists h_lseg513,
    n = [:: v] ++ n1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg513 /\ lseg nxt n1 h_lseg513
.
Definition listfree_type :=
  forall (x : ptr),
  {(args: seq nat)},
    STsep (
      fun h =>
        let: s := args in
        exists h_lseg514,
          h = h_lseg514 /\ lseg x s h_lseg514,
      [vfun (_: unit) h =>
        let: s := args in
          h = empty
      ]).
Program Definition listfree : listfree_type :=
  Fix (fun (listfree : listfree_type) x =>
    Do (
  if x == 0
  then
    ret tt
  else
    nxtx2 <-- @read ptr (x .+ 1);
    listfree nxtx2;;
    dealloc x;;
    dealloc (x .+ 1);;
    ret tt
    )).
Next Obligation.
ssl_ghostelim_pre.
move=>s.
move=>[h_lseg514].
move=>[sigma_root].
rewrite->sigma_root in *.
move=>H_lseg514.
ssl_ghostelim_post.
case: ifP=>H_cond.
case H_lseg514; rewrite H_cond=>//= _.
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
ssl_emp;
ssl_emp_post.
case H_lseg514; rewrite H_cond=>//= _.
move=>[nxtx] [n1x] [vx].
move=>[h_lseg513x].
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
move=>H_lseg513x.
ssl_read.
ssl_call_pre (h_lseg513x).
ssl_call (n1x).
exists (h_lseg513x);
ssl_emp_post.
move=>h_call785375194.
move=>[sigma_call785375194].
rewrite->sigma_call785375194 in *.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.

