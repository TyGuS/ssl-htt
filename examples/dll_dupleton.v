From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| dll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_551,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_551 /\ dll w x s1 h_dll_wxs1_551.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_552,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_552 /\ sll nxt s1 h_sll_nxts1_552.

Lemma dll_perm_eq_trans30 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans30: ssl_pred.
Lemma sll_perm_eq_trans31 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans31: ssl_pred.
Lemma pure32 x y : @perm_eq nat_eqType ([:: x; y]) ([:: y] ++ [:: x]). Admitted.
Hint Resolve pure32: ssl_pure.

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
      exists h_dll_zelems_553,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> z \+ h_dll_zelems_553 /\ dll z null elems h_dll_zelems_553
    ]).

Program Definition dll_dupleton : dll_dupleton_type :=
  Fix (fun (dll_dupleton : dll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
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
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_dll_zelems_553 into h_dll_zxy_553.
try rename H_dll_zelems_553 into H_dll_zxy_553.
ssl_read r.
try rename a into a2.
try rename h_dll_wzzs1z_551z into h_dll_wzzvwzs1wz_551z.
try rename H_dll_wzzs1z_551z into H_dll_wzzvwzs1wz_551z.
try rename h_dll_wwzwzs1wz_551wz into h_dll_wwzwz_551wz.
try rename H_dll_wwzwzs1wz_551wz into H_dll_wwzwz_551wz.
try rename h_dll_wzzvwzs1wz_551z into h_dll_wzzvwz_551z.
try rename H_dll_wzzvwzs1wz_551z into H_dll_wzzvwz_551z.
try rename h_dll_wwzwz_551wz into h_dll_wz_551wz.
try rename H_dll_wwzwz_551wz into H_dll_wz_551wz.
ssl_alloc z2.
try rename z into z2.
try rename h_dll_wzzvwz_551z into h_dll_wzz2vwz_551z.
try rename H_dll_wzzvwz_551z into H_dll_wzz2vwz_551z.
try rename h_dll_zxy_553 into h_dll_z2xy_553.
try rename H_dll_zxy_553 into H_dll_z2xy_553.
ssl_alloc wz2.
try rename wz into wz2.
try rename h_dll_wzz2vwz_551z into h_dll_wz2z2vwz_551z.
try rename H_dll_wzz2vwz_551z into H_dll_wz2z2vwz_551z.
try rename h_dll_wz_551wz into h_dll_wz2_551wz.
try rename H_dll_wz_551wz into H_dll_wz2_551wz.
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
try rename h_dll_wz2z2vwz_551z into h_dll_wz2z2x_551z.
try rename H_dll_wz2z2vwz_551z into H_dll_wz2z2x_551z.
ssl_write z2.
ssl_write_post z2.
ssl_write wz2.
ssl_write_post wz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> y \+ z2 .+ 1 :-> wz2 \+ z2 .+ 2 :-> null \+ wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
unfold_constructor 2;
exists (y), ([:: x] ++ nil), (wz2), (wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.