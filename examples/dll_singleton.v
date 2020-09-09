From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| dll2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) w,
  exists h_dll_wxs1_543,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_543 /\ dll w x s1 h_dll_wxs1_543.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == 0 of
  perm_eq (s) (nil) /\ h = empty
| sll2 of ~~ (x == 0) of
  exists (v : nat) (s1 : seq nat) nxt,
  exists h_sll_nxts1_544,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_544 /\ sll nxt s1 h_sll_nxts1_544.

Definition dll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      h = r :-> a,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      exists (elems : seq nat) y,
      exists h_dll_yelems_545,
      perm_eq (elems) ([:: x]) /\ h = r :-> y \+ h_dll_yelems_545 /\ dll y 0 elems h_dll_yelems_545
    ]).
Program Definition dll_singleton : dll_singleton_type :=
  Fix (fun (dll_singleton : dll_singleton_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      y2 <-- allocb null 3;
      r ::= y2;;
      (y2 .+ 1) ::= null;;
      (y2 .+ 2) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a2.
move=>[sigma_self].
subst.
ssl_ghostelim_post.
ssl_alloc y2.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write (y2 .+ 2).
ssl_write_post (y2 .+ 2).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null \+ y2 .+ 2 :-> null);
sslauto.
unfold_constructor 2;
exists (x), (nil), (0);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.

Qed.
