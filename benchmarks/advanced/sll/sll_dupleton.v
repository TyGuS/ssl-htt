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
Lemma pure2 (x : nat) (y : nat) : @perm_eq nat_eqType ([:: x; y]) (([:: y]) ++ ([:: x])).
  (* intros; hammer. *)
  solve_perm_eq.
Qed.
Hint Resolve pure2: ssl_pure.

Definition sll_dupleton_type :=
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
      exists h_sll_zelems_1,
      @perm_eq nat_eqType (elems) ([:: x; y]) /\ h = r :-> (z) \+ h_sll_zelems_1 /\ sll z elems h_sll_zelems_1
    ]).

Program Definition sll_dupleton : sll_dupleton_type :=
  Fix (fun (sll_dupleton : sll_dupleton_type) vprogs =>
    let: (x, y, r) := vprogs in
    Do (
      a1 <-- @read ptr r;
      z1 <-- allocb null 2;
      nxtz1 <-- allocb null 2;
      r ::= z1;;
      (z1 .+ 1) ::= nxtz1;;
      (nxtz1 .+ 1) ::= null;;
      nxtz1 ::= x;;
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
try rename h_sll_zelems_1 into h_sll_zxy_1.
try rename H_sll_zelems_1 into H_sll_zxy_1.
ssl_read r.
try rename a into a1.
try rename h_sll_nxtzs1z_0z into h_sll_nxtzvnxtzs1nxtz_0z.
try rename H_sll_nxtzs1z_0z into H_sll_nxtzvnxtzs1nxtz_0z.
try rename h_sll_nxtnxtzs1nxtz_0nxtz into h_sll_s1nxtz_0nxtz.
try rename H_sll_nxtnxtzs1nxtz_0nxtz into H_sll_s1nxtz_0nxtz.
try rename h_sll_s1nxtz_0nxtz into h_sll__0nxtz.
try rename H_sll_s1nxtz_0nxtz into H_sll__0nxtz.
try rename h_sll_nxtzvnxtzs1nxtz_0z into h_sll_nxtzvnxtz_0z.
try rename H_sll_nxtzvnxtzs1nxtz_0z into H_sll_nxtzvnxtz_0z.
ssl_alloc z1.
try rename z into z1.
try rename h_sll_zxy_1 into h_sll_z1xy_1.
try rename H_sll_zxy_1 into H_sll_z1xy_1.
ssl_alloc nxtz1.
try rename nxtz into nxtz1.
try rename h_sll_nxtzvnxtz_0z into h_sll_nxtz1vnxtz_0z.
try rename H_sll_nxtzvnxtz_0z into H_sll_nxtz1vnxtz_0z.
ssl_write r.
ssl_write_post r.
ssl_write (z1 .+ 1).
ssl_write_post (z1 .+ 1).
ssl_write (nxtz1 .+ 1).
ssl_write_post (nxtz1 .+ 1).
try rename h_sll_nxtz1vnxtz_0z into h_sll_nxtz1x_0z.
try rename H_sll_nxtz1vnxtz_0z into H_sll_nxtz1x_0z.
ssl_write nxtz1.
ssl_write_post nxtz1.
ssl_write z1.
ssl_write_post z1.
ssl_emp;
exists ([:: x; y]), (z1);
exists (z1 :-> (y) \+ z1 .+ 1 :-> (nxtz1) \+ nxtz1 :-> (x) \+ nxtz1 .+ 1 :-> (null));
sslauto.
ssl_close 2;
exists (y), (([:: x]) ++ (@nil nat)), (nxtz1), (nxtz1 :-> (x) \+ nxtz1 .+ 1 :-> (null));
sslauto.
ssl_close 2;
exists (x), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.
