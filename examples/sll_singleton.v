From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_547,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_547 /\ sll nxt s1 h_sll_nxts1_547.

Lemma sll_perm_eq_trans34 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans34: ssl_pred.
Lemma pure35 x : @perm_eq nat_eqType ([:: x]) ([:: x]). Admitted.
Hint Resolve pure35: ssl_pure.

Definition sll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      h = p :-> a,
    [vfun (_: unit) h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      exists elems y,
      exists h_sll_yelems_548,
      @perm_eq nat_eqType (elems) ([:: x]) /\ h = p :-> y \+ h_sll_yelems_548 /\ sll y elems h_sll_yelems_548
    ]).

Program Definition sll_singleton : sll_singleton_type :=
  Fix (fun (sll_singleton : sll_singleton_type) vprogs =>
    let: (x, p) := vprogs in
    Do (
      y2 <-- allocb null 2;
      p ::= y2;;
      (y2 .+ 1) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x p]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a2.
move=>[sigma_self].
subst.
ssl_ghostelim_post.
ssl_alloc y2.
ssl_write p.
ssl_write_post p.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.
