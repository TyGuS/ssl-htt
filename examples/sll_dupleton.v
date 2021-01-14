From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_532,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_532 /\ sll nxt s1 h_sll_nxts1_532.

Definition sll_dupleton_type :=
  forall (vprogs : nat * nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, y, r) := vprogs in
      let: (a) := vghosts in
      h = r :-> a,
    [vfun (_: unit) h =>
      let: (x, y, r) := vprogs in
      let: (a) := vghosts in
      exists elems z,
      exists h_sll_zelems_533,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> z \+ h_sll_zelems_533 /\ sll z elems h_sll_zelems_533
    ]).
Program Definition sll_dupleton : sll_dupleton_type :=
  Fix (fun (sll_dupleton : sll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      z2 <-- allocb null 2;
      nxtz2 <-- allocb null 2;
      r ::= z2;;
      (z2 .+ 1) ::= nxtz2;;
      (nxtz2 .+ 1) ::= null;;
      z2 ::= x;;
      nxtz2 ::= y;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[x y] r]; ssl_program_simpl.
Next Obligation.
Hypothesis sll_perm_eq_trans17: forall x h s_1 s_2, perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
Hint Resolve sll_perm_eq_trans17: ssl_pred.
ssl_ghostelim_pre.
move=>a2.
move=>[sigma_self].
subst.
ssl_ghostelim_post.
ssl_alloc z2.
ssl_alloc nxtz2.
ssl_write r.
ssl_write_post r.
ssl_write (z2 .+ 1).
ssl_write_post (z2 .+ 1).
ssl_write (nxtz2 .+ 1).
ssl_write_post (nxtz2 .+ 1).
Hypothesis pure18 : forall x y, @perm_eq nat_eqType ([:: x; y]) ([:: x] ++ [:: y]).
Hint Resolve pure18: ssl_pure.
ssl_write z2.
ssl_write_post z2.
ssl_write nxtz2.
ssl_write_post nxtz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> x \+ z2 .+ 1 :-> nxtz2 \+ nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
unfold_constructor 2;
exists (x), ([:: y] ++ nil), (nxtz2);
exists (nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
unfold_constructor 2;
exists (y), (nil), (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.
