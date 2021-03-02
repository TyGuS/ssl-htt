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

Lemma pure22 (x : nat) (y : nat) : ([:: x; y]) = (([:: x]) ++ ([:: y])). intros; hammer. Qed.
Hint Resolve pure22: ssl_pure.

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
      exists h_sll_zelems_523,
      (elems) == ([:: x; y]) /\ h = r :-> z \+ h_sll_zelems_523 /\ sll z elems h_sll_zelems_523
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
try rename h_sll_zelems_523 into h_sll_zxy_523.
try rename H_sll_zelems_523 into H_sll_zxy_523.
ssl_read r.
try rename a into a2.
try rename h_sll_nxtzs1z_522z into h_sll_nxtzvnxtzs1nxtz_522z.
try rename H_sll_nxtzs1z_522z into H_sll_nxtzvnxtzs1nxtz_522z.
try rename h_sll_nxtnxtzs1nxtz_522nxtz into h_sll_s1nxtz_522nxtz.
try rename H_sll_nxtnxtzs1nxtz_522nxtz into H_sll_s1nxtz_522nxtz.
try rename h_sll_nxtzvnxtzs1nxtz_522z into h_sll_nxtzvnxtz_522z.
try rename H_sll_nxtzvnxtzs1nxtz_522z into H_sll_nxtzvnxtz_522z.
try rename h_sll_s1nxtz_522nxtz into h_sll__522nxtz.
try rename H_sll_s1nxtz_522nxtz into H_sll__522nxtz.
ssl_alloc z2.
try rename z into z2.
try rename h_sll_zxy_523 into h_sll_z2xy_523.
try rename H_sll_zxy_523 into H_sll_z2xy_523.
ssl_alloc nxtz2.
try rename nxtz into nxtz2.
try rename h_sll_nxtzvnxtz_522z into h_sll_nxtz2vnxtz_522z.
try rename H_sll_nxtzvnxtz_522z into H_sll_nxtz2vnxtz_522z.
ssl_write r.
ssl_write_post r.
ssl_write (z2 .+ 1).
ssl_write_post (z2 .+ 1).
ssl_write (nxtz2 .+ 1).
ssl_write_post (nxtz2 .+ 1).
try rename h_sll_nxtz2vnxtz_522z into h_sll_nxtz2y_522z.
try rename H_sll_nxtz2vnxtz_522z into H_sll_nxtz2y_522z.
ssl_write z2.
ssl_write_post z2.
ssl_write nxtz2.
ssl_write_post nxtz2.
ssl_emp;
exists ([:: x; y]), (z2);
exists (z2 :-> x \+ z2 .+ 1 :-> nxtz2 \+ nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
ssl_close 2;
exists (x), (([:: y]) ++ (@nil nat)), (nxtz2), (nxtz2 :-> y \+ nxtz2 .+ 1 :-> null);
sslauto.
ssl_close 2;
exists (y), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.