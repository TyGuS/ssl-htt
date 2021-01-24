From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From Hammer Require Import Hammer.

(* The empty heap *)
Notation empty := Unit.

(* No-op at the end of a program branch *)
Definition skip := ret tt.

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

(* Utilities to move a heaplet around within a heap *)
Ltac put_to_tail_ptr p :=
  try rewrite ptrA; rewrite -?joinA; rewrite ?(joinC (p :-> _) _); rewrite ?joinA.

Ltac put_to_tail h :=
  try rewrite ptrA; rewrite -?joinA; rewrite ?(joinC h _); rewrite ?joinA.

Ltac put_to_head_ptr p :=
  put_to_tail p;
  try rewrite (joinC _ (p :-> _)).

Ltac put_to_head h :=
  put_to_tail h;
  try rewrite (joinC _ h).

(* Utilities for nat and seq nat *)

Ltac put_to_tail_nat n :=
  rewrite -?addnA; rewrite ?(addnC n _); rewrite ?addnA.

Ltac nat_add_eq' ns :=
  match ns with
  | ?A + ?B => put_to_tail_nat B; nat_add_eq' A
  | ?A => put_to_tail A
  end.

Ltac nat_add_eq :=
  by rewrite ?addnA;
  match goal with
  | [|- ?LHS = _] => nat_add_eq' LHS
  end.

(* Store heap validity assertions *)
Ltac store_valid :=
  rewrite ?unitL ?unitR;
  try match goal with
  | [|- is_true (valid _) -> _] =>
    let hyp := fresh "H_valid" in move=>hyp;
    store_valid
  end
.

(* If goal is to prove a pointer is not null, derive that fact from one of the heap validity assertions *)
Ltac assert_not_null :=
  let derive H x := (
    rewrite ?joinA in H;
    rewrite -?(joinC (x :-> _)) in H;
    rewrite ?joinA in H;
    move:(H);
    rewrite defPtUnO;
    case/andP;
    let not_null := fresh "not_null" in move=>not_null _;
    assumption) in
  match goal with
  | [H: is_true (valid ?h) |- is_true (?x != null)] =>
    derive H x
  end.

(* Unfold a constructor  *)
Ltac unfold_constructor n :=
  match goal with
  (* There was nothing to solve; this happens if a preceding step *)
  (* unwittingly solved the intended goal without needing to unfold. *)
  | [|- verify _ _ _] =>
    idtac
  (* Unfold and discharge selector goal if needed *)
  | _ => match n with
         | 1 => constructor 1=>//
         | 2 => constructor 2=>//
         | 3 => constructor 3=>//
         | _ => constructor=>//
         end;
         match goal with
         | [|- is_true (_ != null)] => assert_not_null
         | [|- (_ == null) = false] => apply negbTE; assert_not_null
         | _ => idtac
         end
  end.

(* Theory about seq nats *)

Create HintDb ssl_seqnat.

Lemma subset_singleton (A : eqType) (s1: seq A) (x: A):
  {subset s1 <= [::x]} -> {subset x :: s1 <= [::x]}.
Proof.
move=>H n.
rewrite inE; move/orP. case.
move/eqP=>->. by rewrite inE eqxx.
move/H=>//.
Qed.

Lemma perm_eq_trans_el (A: eqType) (s1 s2 s3: seq A) (a b : A):
  perm_eq s1 (a :: s2) ->
  perm_eq s2 (b :: s3)->
  perm_eq s1 [:: a, b & s3].
Proof.
move=> /permP H1 /permP H2; apply/permP=>n; move: (H1 n)  (H2 n) => //= -> -> //=.
Qed.

Lemma perm_eq_nil_r (A: eqType) (s: seq A): perm_eq s nil -> s = nil.
Proof. by move/perm_nilP. Qed.

Lemma perm_eq_nil_l (A: eqType) (s: seq A): perm_eq nil s -> s = nil.
Proof. by rewrite perm_sym; move/perm_nilP. Qed.

Hint Resolve subset_singleton : ssl_seqnat.
Hint Resolve perm_eq_trans_el : ssl_seqnat.
Hint Extern 1 (is_true (perm_eq _ _)) =>
  match goal with
  | [H: is_true (perm_eq _ nil) |- _] => apply perm_eq_nil_r in H; subst
  | [H: is_true (perm_eq nil _) |- _] => apply perm_eq_nil_l in H; subst
  end : ssl_seqnat.
Hint Extern 1 (is_true (perm_eq _ _)) => apply/permP=>//=?; nat_add_eq : ssl_seqnat.

Hint Rewrite <- cat_cons : ssl_seqnat.
Hint Rewrite cat_cons : ssl_seqnat.
Hint Rewrite perm_cat2r : ssl_seqnat.
Lemma ssl_perm_sym (A: eqType) (x y: seq A): perm_eq x y -> perm_eq y x = perm_eq x y.
Proof. by rewrite perm_sym. Qed.
Hint Rewrite ssl_perm_sym using assumption: ssl_seqnat.

(* Theory about nats *)

Create HintDb ssl_nat.

Lemma leq_neg (x y : nat) : (x <= y) = false -> y <= x.
Proof. by case: ltngtP=>//. Qed.

Hint Resolve leq_neg : ssl_nat.

(* Theory about heaps *)

Create HintDb ssl_heap.

Ltac hhauto' h :=
  match type of h with
  | PCM.sort heapPCM => hhauto
  | PCM.sort (union_map_classPCM heapUMC) => hhauto
  end.

Hint Extern 1 (?h = _) => hhauto' h : ssl_heap.

(* Theory about predicates (to be filled by each certificate) *)

Create HintDb ssl_pred.

(* Theory about pure constraints (to be filled by each certificate) *)

Create HintDb ssl_pure.

(* Extend auto with additional strategies *)

Ltac eq_bool_to_prop :=
  repeat match goal with
         | [H: is_true (_ == _) |- _] => move/eqP in H
         end.

Ltac sslauto :=
  let sslauto_seqnat := (eauto with ssl_heap ssl_nat ssl_seqnat; autorewrite with ssl_seqnat=>//=) in
  eq_bool_to_prop;
  subst;
  match goal with
  | [|- verify _ _ _] => idtac
  | _ =>
    rewrite ?unitL ?unitR ?addnA;
    repeat split=>//=;
    match goal with
    | [|- context [perm_eq]] => sslauto_seqnat
    | [|- context [{subset _ <= _}]] => sslauto_seqnat
    | _ => auto with ssl_heap ssl_nat
    end;
    eauto with ssl_pred;
    match goal with
    | [|- is_true (_ <= _)] => unshelve (progress eauto 2 with ssl_pure + hammer)
    | [|- is_true (_ < _)] => unshelve (progress eauto 2 with ssl_pure + hammer)
    | [|- is_true (_ == _)] => unshelve (progress eauto 2 with ssl_pure + hammer)
    | _ => idtac
    end;
    try exact 0
  end.

Ltac ex_elim1 A := try clear dependent A; move=>[A].
Ltac ex_elim2 A B := try clear dependent A; try clear dependent B; move=>[A][B].
Ltac ex_elim3 A B C := try clear dependent A; try clear dependent B; try clear dependent C; move=>[A][B][C].

Tactic Notation "ex_elim" ident(A) := ex_elim1 A.
Tactic Notation "ex_elim" ident(A) ident(B) := ex_elim2 A B.
Tactic Notation "ex_elim" ident(A) ident(B) ident(C) := ex_elim3 A B C.
Tactic Notation "ex_elim" ident(A) ident(B) ident(C) ident(D) := ex_elim2 A B; ex_elim2 C D.
Tactic Notation "ex_elim" ident(A) ident(B) ident(C) ident(D) ident(E) := ex_elim2 A B; ex_elim3 C D E.
Tactic Notation "ex_elim" ident(A) ident(B) ident(C) ident(D) ident(E) ident(F) := ex_elim3 A B C; ex_elim3 D E F.

(***********)
(* Tactics *)
(***********)

(* After binding program variables to their correct labels, we use the Coq's default simplification algorithm *)
Ltac ssl_program_simpl := Tactics.program_simpl.


(* Ghost Variable Elim *)
Ltac ssl_ghostelim_pre := try apply: ghR; move=>h_self//=.

Ltac ssl_ghostelim_post := store_valid.

(* Read Rule *)
Ltac ssl_read from :=
  put_to_head_ptr from;
  apply: bnd_readR=>/=.

(* Write Rule *)
Ltac ssl_write x :=
  put_to_head_ptr x; (* this significantly speeds up bnd_writeR *)
  apply: bnd_writeR=>/=.

Ltac ssl_write_post x :=
  (put_to_tail_ptr x + rewrite -(unitL (x :-> _))); apply frame.

(* Alloc Rule *)
Ltac ssl_alloc x :=
  apply: bnd_allocbR=>x//=.

(* Free Rule *)
Ltac ssl_dealloc x :=
  apply: bnd_seq;
  put_to_head_ptr x;
  match goal with
  | [|- context[_ :-> _ \+ _]] =>
    apply: val_dealloc=>//=_
  | [|- context[_ :-> _]] =>
    apply: val_deallocR=>//=_
  end;
  try match goal with
  | [|- context[_ \+ empty]] =>
    rewrite unitR
  end
.

(* Call Rule *)
Ltac ssl_call_pre_aux h :=
  match h with
  | ?h1 \+ ?h2 => put_to_head h2; ssl_call_pre_aux h1
  | _ => put_to_head h
  end.

Ltac ssl_call_pre h :=
  ssl_call_pre_aux h;
  rewrite ?joinA;
  rewrite -?(joinA h).

Ltac ssl_call' ex :=
  apply: bnd_seq;
  match ex with
  | ltac_No_arg => idtac
  | _ => apply: (gh_ex ex)
  end;
  apply: val_do=>//=;
  move=>_.

Tactic Notation "ssl_call" := ssl_call' ltac_No_arg.
Tactic Notation "ssl_call" constr(ex) := ssl_call' ex.

(* Emp Rule *)
Ltac ssl_emp := apply: val_ret; rewrite ?unitL; store_valid; move=>//.

(* Open Rule *)
Ltac ssl_open sel := let H := fresh "H_cond" in try case: (ifP sel)=>H.
Ltac ssl_open_post H :=
  case H;
  match goal with
  | [H_cond: is_true (_ == _) |- _] => move/eqP in H_cond; rewrite->H_cond in *=>//=
  | [H_cond: (_ == _) = false |- _] => rewrite->H_cond=>//=
  end;
  move=>_.

(* Abduce Branch Rule *)
Ltac ssl_abduce_branch sel := let H := fresh "H_cond" in try case: (ifP sel)=>H.
