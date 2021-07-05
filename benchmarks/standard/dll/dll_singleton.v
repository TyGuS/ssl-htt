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

Lemma pure1 (x : nat) : ([:: x]) = ([:: x]). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.

Definition dll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      h = r :-> (a),
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      exists elems y,
      exists h_dll_yelems_1,
      (elems) == ([:: x]) /\ h = r :-> (y) \+ h_dll_yelems_1 /\ dll y null elems h_dll_yelems_1
    ]).

Program Definition dll_singleton : dll_singleton_type :=
  Fix (fun (dll_singleton : dll_singleton_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a1 <-- @read ptr r;
      y1 <-- allocb null 3;
      r ::= y1;;
      (y1 .+ 1) ::= null;;
      (y1 .+ 2) ::= null;;
      y1 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_dll_yelems_1 into h_dll_yx_1.
try rename H_dll_yelems_1 into H_dll_yx_1.
ssl_read r.
try rename a into a1.
try rename h_dll_wyys1y_0y into h_dll_wyy_0y.
try rename H_dll_wyys1y_0y into H_dll_wyy_0y.
try rename h_dll_wyy_0y into h_dll_y_0y.
try rename H_dll_wyy_0y into H_dll_y_0y.
ssl_alloc y1.
try rename y into y1.
try rename h_dll_yx_1 into h_dll_y1x_1.
try rename H_dll_yx_1 into H_dll_y1x_1.
try rename h_dll_y_0y into h_dll_y1_0y.
try rename H_dll_y_0y into H_dll_y1_0y.
ssl_write r.
ssl_write_post r.
ssl_write (y1 .+ 1).
ssl_write_post (y1 .+ 1).
ssl_write (y1 .+ 2).
ssl_write_post (y1 .+ 2).
ssl_write y1.
ssl_write_post y1.
ssl_emp;
exists ([:: x]), (y1);
exists (y1 :-> (x) \+ y1 .+ 1 :-> (null) \+ y1 .+ 2 :-> (null));
sslauto.
ssl_close 2;
exists (x), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
Qed.