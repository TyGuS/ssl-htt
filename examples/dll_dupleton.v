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
  exists h_dll_wxs1_546,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_546 /\ dll w x s1 h_dll_wxs1_546.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_547,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_547 /\ sll nxt s1 h_sll_nxts1_547.

Lemma dll_perm_eq_trans32 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans32: ssl_pred.
Lemma sll_perm_eq_trans33 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans33: ssl_pred.
Lemma pure34 x y : @perm_eq nat_eqType ([:: x; y]) ([:: y] ++ [:: x]). Admitted.
Hint Resolve pure34: ssl_pure.

Definition dll_dupleton_type :=
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
      exists h_dll_zelems_548,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> z \+ h_dll_zelems_548 /\ dll z null elems h_dll_zelems_548
    ]).

Program Definition dll_dupleton : dll_dupleton_type :=
  Fix (fun (dll_dupleton : dll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      z2 <-- allocb null 3;
      wz2 <-- allocb null 3;
      r ::= z2;;
      (z2 .+ 1) ::= wz2;;
      (z2 .+ 2) ::= null;;
      (wz2 .+ 1) ::= null;;
      (wz2 .+ 2) ::= z2;;
      z2 ::= y;;
      wz2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[x y] r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a2.
move=>[sigma_self].
subst.
ssl_ghostelim_post.
ssl_alloc z2.
ssl_alloc wz2.
ssl_write r.
ssl_write_post r.
ssl_write (z2 .+ 1).
ssl_write_post (z2 .+ 1).
ssl_write (z2 .+ 2).
ssl_write_post (z2 .+ 2).
ssl_write (wz2 .+ 1).
ssl_write_post (wz2 .+ 1).
ssl_write (wz2 .+ 2).
ssl_write_post (wz2 .+ 2).
ssl_write z2.
ssl_write_post z2.
ssl_write wz2.
ssl_write_post wz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> y \+ z2 .+ 1 :-> wz2 \+ z2 .+ 2 :-> null \+ wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
unfold_constructor 2;
exists (y), ([:: x] ++ nil), (wz2);
exists (wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.
