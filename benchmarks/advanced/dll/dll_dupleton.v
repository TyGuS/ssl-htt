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
Set Hammer ATPLimit 60.
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

Lemma dll_perm_eq_congr1 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h.
  (* intros; hammer. *)
  move=>Heq Hdll; sslauto.
  case: Hdll=>cond.
  move=>[Heq1 ->].
  constructor 1=>//=; sslauto.
  move=>[v][s1][w][h'].
  move=>[Heq1 [->Hdll]].
  constructor 2=>//=.
  exists v, s1, w, h'.
  sslauto.
  assumption.
Qed.
Hint Resolve dll_perm_eq_congr1: ssl_pred.
Lemma sll_perm_eq_congr2 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
  (* intros; hammer *)
  move=>Heq Hsll; sslauto.
  case: Hsll=>cond.
  move=>[Heq1 ->].
  constructor 1=>//=; sslauto.
  move=>[v] [s2] [nxt] [h'].
  move=>[Heq1 [-> Hssl]].
  constructor 2=>//=.
  exists v, s2, nxt, h'.
  sslauto.
  assumption.
Qed.
Hint Resolve sll_perm_eq_congr2: ssl_pred.
Lemma pure3 (x : nat) (y : nat) : @perm_eq nat_eqType ([:: x; y]) (([:: y]) ++ ([:: x])).
  (* intros; hammer. *)
  solve_perm_eq.
Qed.
Hint Resolve pure3: ssl_pure.

Definition dll_dupleton_type :=
  forall (vprogs : nat * nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, y, r) := vprogs in
      let: (a) := vghosts in
      h = r :-> (a),
    [vfun (_: unit) h =>
      let: (x, y, r) := vprogs in
      let: (a) := vghosts in
      exists elems z,
      exists h_dll_zelems_2,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> (z) \+ h_dll_zelems_2 /\ dll z null elems h_dll_zelems_2
    ]).

Program Definition dll_dupleton : dll_dupleton_type :=
  Fix (fun (dll_dupleton : dll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      a1 <-- @read ptr r;
      z1 <-- allocb null 3;
      wz1 <-- allocb null 3;
      r ::= z1;;
      (z1 .+ 1) ::= wz1;;
      (z1 .+ 2) ::= null;;
      (wz1 .+ 1) ::= null;;
      (wz1 .+ 2) ::= z1;;
      wz1 ::= x;;
      z1 ::= y;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[x y] r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_dll_zelems_2 into h_dll_zxy_2.
try rename H_dll_zelems_2 into H_dll_zxy_2.
ssl_read r.
try rename a into a1.
try rename h_dll_wzzs1z_0z into h_dll_wzzvwzs1wz_0z.
try rename H_dll_wzzs1z_0z into H_dll_wzzvwzs1wz_0z.
try rename h_dll_wwzwzs1wz_0wz into h_dll_wwzwz_0wz.
try rename H_dll_wwzwzs1wz_0wz into H_dll_wwzwz_0wz.
try rename h_dll_wzzvwzs1wz_0z into h_dll_wzzvwz_0z.
try rename H_dll_wzzvwzs1wz_0z into H_dll_wzzvwz_0z.
try rename h_dll_wwzwz_0wz into h_dll_wz_0wz.
try rename H_dll_wwzwz_0wz into H_dll_wz_0wz.
ssl_alloc z1.
try rename z into z1.
try rename h_dll_zxy_2 into h_dll_z1xy_2.
try rename H_dll_zxy_2 into H_dll_z1xy_2.
try rename h_dll_wzzvwz_0z into h_dll_wzz1vwz_0z.
try rename H_dll_wzzvwz_0z into H_dll_wzz1vwz_0z.
ssl_alloc wz1.
try rename wz into wz1.
try rename h_dll_wzz1vwz_0z into h_dll_wz1z1vwz_0z.
try rename H_dll_wzz1vwz_0z into H_dll_wz1z1vwz_0z.
try rename h_dll_wz_0wz into h_dll_wz1_0wz.
try rename H_dll_wz_0wz into H_dll_wz1_0wz.
ssl_write r.
ssl_write_post r.
ssl_write (z1 .+ 1).
ssl_write_post (z1 .+ 1).
ssl_write (z1 .+ 2).
ssl_write_post (z1 .+ 2).
ssl_write (wz1 .+ 1).
ssl_write_post (wz1 .+ 1).
ssl_write (wz1 .+ 2).
ssl_write_post (wz1 .+ 2).
try rename h_dll_wz1z1vwz_0z into h_dll_wz1z1x_0z.
try rename H_dll_wz1z1vwz_0z into H_dll_wz1z1x_0z.
ssl_write wz1.
ssl_write_post wz1.
ssl_write z1.
ssl_write_post z1.
ssl_emp;
exists ([:: x; y]), (z1);
exists (z1 :-> (y) \+ z1 .+ 1 :-> (wz1) \+ z1 .+ 2 :-> (null) \+ wz1 :-> (x) \+ wz1 .+ 1 :-> (null) \+ wz1 .+ 2 :-> (z1));
sslauto.
ssl_close 2;
exists (y), (([:: x]) ++ (@nil nat)), (wz1), (wz1 :-> (x) \+ wz1 .+ 1 :-> (null) \+ wz1 .+ 2 :-> (z1));
sslauto.
ssl_close 2;
exists (x), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.
