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


Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  (s) == (@nil nat) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_4,
  (s) == (([:: v]) ++ (s1)) /\ h = x :-> (v) \+ x .+ 1 :-> (nxt) \+ h_sll_nxts1_4 /\ sll nxt s1 h_sll_nxts1_4.


Inductive treeN (x : ptr) (n : nat) (h : heap) : Prop :=
| treeN_1 of (x) == (null) of
  (n) == (0) /\ h = empty
| treeN_2 of ~~ ((x) == (null)) of
  exists (n1 : nat) (n2 : nat) (l : ptr) (r : ptr) (v : ptr),
  exists h_treeN_ln1_2 h_treeN_rn2_3,
  (0) <= (n1) /\ (0) <= (n2) /\ (n) == (((1) + (n1)) + (n2)) /\ h = x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_treeN_ln1_2 \+ h_treeN_rn2_3 /\ treeN l n1 h_treeN_ln1_2 /\ treeN r n2 h_treeN_rn2_3.


Inductive tree (x : ptr) (s : seq nat) (h : heap) : Prop :=
| tree_1 of (x) == (null) of
  (s) == (@nil nat) /\ h = empty
| tree_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (s2 : seq nat) (l : ptr) (r : ptr),
  exists h_tree_ls1_0 h_tree_rs2_1,
  (s) == ((([:: v]) ++ (s1)) ++ (s2)) /\ h = x :-> (v) \+ x .+ 1 :-> (l) \+ x .+ 2 :-> (r) \+ h_tree_ls1_0 \+ h_tree_rs2_1 /\ tree l s1 h_tree_ls1_0 /\ tree r s2 h_tree_rs2_1.
