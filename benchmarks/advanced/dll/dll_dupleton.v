From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.
From Hammer Require Import Hammer.
(* Configure Hammer *)
Unset Hammer Eprover.
Unset Hammer Vampire.
Add Search Blacklist "fcsl.".
Add Search Blacklist "HTT.".
Add Search Blacklist "Coq.ssr.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.bigop".
Add Search Blacklist "mathcomp.ssreflect.choice".
Add Search Blacklist "mathcomp.ssreflect.div".
Add Search Blacklist "mathcomp.ssreflect.finfun".
Add Search Blacklist "mathcomp.ssreflect.fintype".
Add Search Blacklist "mathcomp.ssreflect.path".
Add Search Blacklist "mathcomp.ssreflect.tuple".


Require Import common.

Lemma pure3 (x : nat) (y : nat) : @perm_eq nat_eqType ([:: x; y]) (([:: y]) ++ ([:: x])). solve_perm_eq. (* intros; hammer. *) Qed.
Hint Resolve pure3: ssl_pure.

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
      exists h_dll_zelems_515,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> z \+ h_dll_zelems_515 /\ dll z null elems h_dll_zelems_515
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
try rename h_dll_zelems_515 into h_dll_zxy_515.
try rename H_dll_zelems_515 into H_dll_zxy_515.
ssl_read r.
try rename a into a2.
try rename h_dll_wzzs1z_513z into h_dll_wzzvwzs1wz_513z.
try rename H_dll_wzzs1z_513z into H_dll_wzzvwzs1wz_513z.
try rename h_dll_wwzwzs1wz_513wz into h_dll_wwzwz_513wz.
try rename H_dll_wwzwzs1wz_513wz into H_dll_wwzwz_513wz.
try rename h_dll_wzzvwzs1wz_513z into h_dll_wzzvwz_513z.
try rename H_dll_wzzvwzs1wz_513z into H_dll_wzzvwz_513z.
try rename h_dll_wwzwz_513wz into h_dll_wz_513wz.
try rename H_dll_wwzwz_513wz into H_dll_wz_513wz.
ssl_alloc z2.
try rename z into z2.
try rename h_dll_zxy_515 into h_dll_z2xy_515.
try rename H_dll_zxy_515 into H_dll_z2xy_515.
try rename h_dll_wzzvwz_513z into h_dll_wzz2vwz_513z.
try rename H_dll_wzzvwz_513z into H_dll_wzz2vwz_513z.
ssl_alloc wz2.
try rename wz into wz2.
try rename h_dll_wzz2vwz_513z into h_dll_wz2z2vwz_513z.
try rename H_dll_wzz2vwz_513z into H_dll_wz2z2vwz_513z.
try rename h_dll_wz_513wz into h_dll_wz2_513wz.
try rename H_dll_wz_513wz into H_dll_wz2_513wz.
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
try rename h_dll_wz2z2vwz_513z into h_dll_wz2z2x_513z.
try rename H_dll_wz2z2vwz_513z into H_dll_wz2z2x_513z.
ssl_write z2.
ssl_write_post z2.
ssl_write wz2.
ssl_write_post wz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> y \+ z2 .+ 1 :-> wz2 \+ z2 .+ 2 :-> null \+ wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
ssl_close 2;
exists (y), (([:: x]) ++ (@nil nat)), (wz2), (wz2 :-> x \+ wz2 .+ 1 :-> null \+ wz2 .+ 2 :-> z2);
sslauto.
ssl_close 2;
exists (x), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.
