From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| dll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_549,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_549 /\ dll w x s1 h_dll_wxs1_549.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_550,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_550 /\ sll nxt s1 h_sll_nxts1_550.

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
      exists elems y,
      exists h_dll_yelems_551,
      @perm_eq nat_eqType (elems) ([:: x]) /\ h = r :-> y \+ h_dll_yelems_551 /\ dll y null elems h_dll_yelems_551
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
Hypothesis dll_perm_eq_trans35: forall x z h s_1 s_2, perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h.
Hint Resolve dll_perm_eq_trans35: ssl_pred.
Hypothesis sll_perm_eq_trans36: forall x h s_1 s_2, perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
Hint Resolve sll_perm_eq_trans36: ssl_pred.
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
Hypothesis pure37 : forall x, @perm_eq nat_eqType ([:: x]) ([:: x]).
Hint Resolve pure37: ssl_pure.
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null \+ y2 .+ 2 :-> null);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.
