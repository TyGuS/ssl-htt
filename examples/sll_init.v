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
  exists h_sll513,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll513 /\ sll nxt s1 h_sll513.


Definition sll_init_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : seq nat)},
    STsep (
      fun h =>
        let: (x, v) := vprogs in
        let: (s) := vghosts in
        exists h_sll514,
          h = h_sll514 /\ sll x s h_sll514,
      [vfun (_: unit) h =>
        let: (x, v) := vprogs in
        let: (s) := vghosts in
        exists s1,
        exists h_sll515,
          {subset s1 <= [:: v]} /\ h = h_sll515 /\ sll x s1 h_sll515
      ]).

Program Definition sll_init : sll_init_type :=
  Fix (fun (sll_init : sll_init_type) vprogs =>
  let: (x, v) := vprogs in
    Do (
  if x == 0
  then
    ret tt
  else
    nxtx2 <-- @read ptr (x .+ 1);
    sll_init (nxtx2, v);;
    x ::= v;;
    ret tt
    )).

Obligation Tactic := intro; move=>[x v]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
move=>[h_sll514].
move=>[sigma_root].
rewrite->sigma_root in *.
move=>H_sll514.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_sll514.
move=>[phi_sll514].
move=>[sigma_sll514].
rewrite->sigma_sll514 in *.
ssl_emp;
exists (nil);
exists (empty);
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.
ssl_open_post H_sll514.
move=>[(*nxtx*) nxtx2] [s1x] [vx].
move=>[h_sll513x].
move=>[phi_sll514].
move=>[sigma_sll514].
rewrite->sigma_sll514 in *.
move=>H_sll513x.
ssl_read.
(*ssl_read.*)
ssl_call_pre (h_sll513x).
ssl_call (s1x).
exists (h_sll513x);
ssl_emp_post.
move=>h_call1550077777.
move=>[s11].
move=>[h_sll5151].
move=>[phi_call1550077777].
move=>[sigma_call1550077777].
rewrite->sigma_call1550077777 in *.
move=>H_sll5151.
store_valid.
ssl_write.
ssl_write_post x.
ssl_emp;
exists ([:: v] ++ s11);
exists (x :-> v \+ x .+ 1 :-> nxtx2 \+ h_sll5151);
ssl_emp_post.
unfold_constructor 2;
exists (nxtx2), (s11), (v);
exists (h_sll5151);
ssl_emp_post.

Qed.
