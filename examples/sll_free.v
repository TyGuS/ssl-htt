From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll0 of x == 0 of
    s = nil /\ h = empty
| sll1 of x != 0 of
  exists nxt s1 v,
  exists h_sll522,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll522 /\ sll nxt s1 h_sll522
.
Definition sll_free_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
    STsep (
      fun h =>
        let: (x) := vprogs in
        let: (s) := vghosts in
        exists h_sll523,
          h = h_sll523 /\ sll x s h_sll523,
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
move=>[h_sll523].
move=>[sigma_root].
rewrite->sigma_root in *.
move=>H_sll523.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll523.
move=>[phi_sll523].
move=>[sigma_sll523].
rewrite->sigma_sll523 in *.
ssl_emp;
ssl_emp_post.
ssl_open_post H_sll523.
move=>[nxtx] [s1x] [vx].
move=>[h_sll522x].
move=>[phi_sll523].
move=>[sigma_sll523].
rewrite->sigma_sll523 in *.
move=>H_sll522x.
ssl_read.
ssl_call_pre (h_sll522x).
ssl_call (s1x).
exists (h_sll522x);
ssl_emp_post.
move=>h_call939137670.
move=>[sigma_call939137670].
rewrite->sigma_call939137670 in *.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.
