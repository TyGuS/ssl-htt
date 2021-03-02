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


Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (@nil nat) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_514,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_514 /\ sll nxt s1 h_sll_nxts1_514.


Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (@nil nat) /\ h = empty
| dll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_513,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_513 /\ dll w x s1 h_dll_wxs1_513.


Lemma sll_perm_eq_trans16 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
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
Hint Resolve sll_perm_eq_trans16: ssl_pred.

Lemma dll_perm_eq_trans17 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h.
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
Hint Resolve dll_perm_eq_trans17: ssl_pred.
