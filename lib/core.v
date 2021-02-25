From Coq Require Import Zify.
From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun zify.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From Hammer Require Import Tactics.
Require Import ZArith.

(* The empty heap *)
Definition empty := @PCM.unit heapPCM.

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

(* Store heap validity assertions *)
Ltac store_valid :=
  rewrite ?unitL ?unitR;
  try match goal with
  | [|- is_true (valid _) -> _] =>
    let hyp := fresh "H_valid" in move=>hyp;
    store_valid
  end.

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

(* Theory about predicates (to be filled by each certificate) *)

Create HintDb ssl_pred.

(* Theory about pure constraints (to be filled by each certificate) *)

Create HintDb ssl_pure.

(* Extend auto with additional strategies *)

Ltac eq_bool_to_prop :=
  repeat match goal with
         | [H: is_true (_ == _) |- _] => move/eqP in H
         end.

Ltac solve_perm_eq :=
  let n := fresh "n" in
  apply/permP=>n;
  repeat match goal with
         | [H: is_true (perm_eq _ _) |- _] => move/permP in H; move:(H n)
         end;
  move=>//=;
  rewrite ?count_cat;
  zify; lia.

Ltac solve_pure := (timeout 2 progress eauto 2 with ssl_pure) + (sauto depth: 3).

Ltac sslauto :=
  let simplify := eq_bool_to_prop; subst in
  repeat apply conj;
  match goal with
  | [|- {subset _ <= _}] => simplify; unshelve solve_pure; done
  | [|- is_true (perm_eq _ _)] => solve_perm_eq
  | [|- _ = _] => simplify; rewrite ?unitL ?unitR; hhauto
  | [|- is_true (_ == _)] => simplify; apply/eqP; unshelve solve_pure; done
  | [|- is_true (_ < _)] => simplify; unshelve solve_pure; done
  | [|- is_true (_ <= _)] => simplify; unshelve solve_pure; done
  | _ => idtac
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
  apply: val_deallocR=>//=_;
  rewrite ?unitR.

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

Ltac conjuncts_to_ctx :=
  match goal with
  | [|- is_true (_ && _) -> _ ] => case/andP; conjuncts_to_ctx; let H := fresh "H_cond" in move=>H
  | _ => let H := fresh "H_cond" in move=>H
  end.

Ltac demorgan' :=
  match goal with
  | [|- context [~~ (_ && _)]] => rewrite Bool.negb_andb; demorgan'
  | [|- context [~~ (_ || _)]] => rewrite Bool.negb_orb; demorgan'
  | _ => idtac
  end.

Ltac demorgan :=
  demorgan';
  conjuncts_to_ctx.

Ltac ssl_open sel hyp :=
  let H := fresh "H_cond" in
  case: hyp;
  (case: (ifP sel); try move/negbT; demorgan; move=>_//) + demorgan .

(* Branch Rule *)

Ltac ssl_branch sel :=
  let H := fresh "H_cond" in
  try case: (ifP sel);
  try move/negbT;
  try demorgan.

(* Inconsistency Rule *)

Ltac ssl_inconsistency :=
  match goal with
  | [H_true: is_true ?sel, H_false: is_true (~~ ?sel) |- _] => rewrite H_true in H_false=>//=
  end.

(* Close Rule *)

Ltac ssl_close n :=
  match n with
  | 1 => constructor 1=>//
  | 2 => constructor 2=>//
  | 3 => constructor 3=>//
  | _ => constructor=>//
  end;
  match goal with
  | [|- is_true (_ != null)] => assert_not_null
  | [|- (_ == null) = false] => apply negbTE; assert_not_null
  | _ => idtac
  end.

(* Frame Unfold Rule *)

Ltac ssl_frame_unfold :=
  (eq_bool_to_prop; subst; assumption) + (timeout 3 eauto 2 with ssl_pred).
