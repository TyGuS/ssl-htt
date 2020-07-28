From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree0 of x == 0 of
    s = nil /\ h = empty
| tree1 of x != 0 of
  exists l s1 r s2 v,
  exists h_tree519 h_tree520,
    s = [:: v] ++ s1 ++ s2 /\ h = x :-> v \+ x .+ 1 :-> l \+ x .+ 2 :-> r \+ h_tree519 \+ h_tree520 /\ tree l s1 h_tree519 /\ tree r s2 h_tree520
.
Definition treefree_type :=
  forall (vprogs : ptr),
  {(vghosts : seq nat)},
    STsep (
      fun h =>
        let: (x) := vprogs in
        let: (s) := vghosts in
        exists h_tree521,
          h = h_tree521 /\ tree x s h_tree521,
      [vfun (_: unit) h =>
        let: (x) := vprogs in
        let: (s) := vghosts in
          h = empty
      ]).
Program Definition treefree : treefree_type :=
  Fix (fun (treefree : treefree_type) vprogs =>
  let: (x) := vprogs in
    Do (
  if x == 0
  then
    ret tt
  else
    lx2 <-- @read ptr (x .+ 1);
    rx2 <-- @read ptr (x .+ 2);
    treefree (lx2);;
    treefree (rx2);;
    dealloc x;;
    dealloc (x .+ 1);;
    dealloc (x .+ 2);;
    ret tt
    )).
Obligation Tactic := intro; move=>x; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>s.
move=>[h_tree521].
move=>[sigma_root].
rewrite->sigma_root in *.
move=>H_tree521.
ssl_ghostelim_post.
ssl_open.
ssl_open_post H_tree521.
move=>[phi_tree521].
move=>[sigma_tree521].
rewrite->sigma_tree521 in *.
ssl_emp;
ssl_emp_post.
ssl_open_post H_tree521.
move=>[lx] [s1x] [rx] [s2x] [vx].
move=>[h_tree519x] [h_tree520x].
move=>[phi_tree521].
move=>[sigma_tree521].
rewrite->sigma_tree521 in *.
move=>[H_tree519x H_tree520x].
ssl_read.
ssl_read.
ssl_call_pre (h_tree519x).
ssl_call (s1x).
exists (h_tree519x);
ssl_emp_post.
move=>h_call1840789674.
move=>[sigma_call1840789674].
rewrite->sigma_call1840789674 in *.
store_valid.
ssl_call_pre (h_tree520x).
ssl_call (s2x).
exists (h_tree520x);
ssl_emp_post.
move=>h_call1234089735.
move=>[sigma_call1234089735].
rewrite->sigma_call1234089735 in *.
store_valid.
ssl_dealloc.
ssl_dealloc.
ssl_dealloc.
ssl_emp;
ssl_emp_post.

Qed.
