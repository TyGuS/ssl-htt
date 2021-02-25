From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_559,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_559 /\ sll nxt s1 h_sll_nxts1_559.

Lemma sll_perm_eq_trans34 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans34: ssl_pred.
Lemma pure35 x y : @perm_eq nat_eqType ([:: x; y]) (([:: x]) ++ ([:: y])). Admitted.
Hint Resolve pure35: ssl_pure.

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
      exists h_sll_zelems_560,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> z \+ h_sll_zelems_560 /\ sll z elems h_sll_zelems_560
    ]).

Program Definition sll_dupleton : sll_dupleton_type :=
  Fix (fun (sll_dupleton : sll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
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
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_sll_zelems_560 into h_sll_zxy_560.
try rename H_sll_zelems_560 into H_sll_zxy_560.
ssl_read r.
try rename a into a2.
try rename h_sll_nxtzs1z_559z into h_sll_nxtzvnxtzs1nxtz_559z.
try rename H_sll_nxtzs1z_559z into H_sll_nxtzvnxtzs1nxtz_559z.
try rename h_sll_nxtnxtzs1nxtz_559nxtz into h_sll_s1nxtz_559nxtz.
try rename H_sll_nxtnxtzs1nxtz_559nxtz into H_sll_s1nxtz_559nxtz.
try rename h_sll_s1nxtz_559nxtz into h_sll__559nxtz.
try rename H_sll_s1nxtz_559nxtz into H_sll__559nxtz.
try rename h_sll_nxtzvnxtzs1nxtz_559z into h_sll_nxtzvnxtz_559z.
try rename H_sll_nxtzvnxtzs1nxtz_559z into H_sll_nxtzvnxtz_559z.
ssl_alloc z2.
try rename z into z2.
try rename h_sll_zxy_560 into h_sll_z2xy_560.
try rename H_sll_zxy_560 into H_sll_z2xy_560.
ssl_alloc nxtz2.
try rename nxtz into nxtz2.
try rename h_sll_nxtzvnxtz_559z into h_sll_nxtz2vnxtz_559z.
try rename H_sll_nxtzvnxtz_559z into H_sll_nxtz2vnxtz_559z.
ssl_write r.
ssl_write_post r.
ssl_write (z2 .+ 1).
ssl_write_post (z2 .+ 1).
ssl_write (nxtz2 .+ 1).
ssl_write_post (nxtz2 .+ 1).
try rename h_sll_nxtz2vnxtz_559z into h_sll_nxtz2y_559z.
try rename H_sll_nxtz2vnxtz_559z into H_sll_nxtz2y_559z.
ssl_write z2.
ssl_write_post z2.
ssl_write nxtz2.
ssl_write_post nxtz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> x \+ z2 .+ 1 :-> nxtz2 \+ nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
ssl_close 2;
exists (x), (([:: y]) ++ (nil)), (nxtz2), (nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
ssl_close 2;
exists (y), (nil), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.