From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.

(* The empty heap *)
Notation empty := Unit.

(* Register the value 0 as null *)
Coercion ptr_nat : nat >-> ptr.

(* No-op at the end of a program branch *)
Definition skip := ret tt.

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

(* Utilities to move a heaplet around within a heap *)
Ltac put_to_tail_ptr p :=
  rewrite -?joinA; rewrite ?(joinC (p :-> _) _); rewrite ?joinA.

Ltac put_to_tail h :=
  rewrite -?joinA; rewrite ?(joinC h _); rewrite ?joinA.

Ltac put_to_head h :=
  put_to_tail h;
  rewrite (joinC _ h).

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
  match goal with
  | [H: is_true (valid ?h) |- is_true (?x != ptr_nat 0)] =>
    rewrite ?joinA in H;
    rewrite -?(joinC (x :-> _)) in H;
    rewrite ?joinA in H;
    move:(H);
    rewrite defPtUnO;
    case/andP;
    let not_null := fresh "not_null" in move=>not_null _;
    assumption
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
         | [|- is_true (_ != ptr_nat 0)] => assert_not_null
         | _ => idtac
         end
  end.

(* Reasoning about singleton subsets *)
Lemma subset_singleton :
    forall (s1: seq nat) (x: nat),
      {subset s1 <= [::x]} -> {subset x :: s1 <= [::x]}.
intros.
move=>n.
rewrite inE; move/orP. case.
move/eqP=>->. by rewrite inE eqxx.
move/H=>//.
Qed.

Ltac sslauto :=
  (* Various strategies to solve all parts of the current goal except the predicate applications  *)
  match goal with
  | [|- verify _ _ _] => idtac
  | _ => rewrite ?unitL ?unitR;
         repeat split=>//=;
         repeat match goal with
                | [|- _ /\ _] => split=>//
                | [|- ?h = _] => match type of h with
                                 | (PCM.sort heapPCM) => hhauto
                                 | (PCM.sort (union_map_classPCM heapUMC)) => hhauto
                                 | _ => auto
                                 end
                | [H: is_true (_ <= _) |- _] => case: ltngtP H=>//
                | [H: (_ <= _) = false |- _] => case: ltngtP H=>//
                | [H: {subset ?s1 <= ?s2} |- {subset _ :: ?s1 <= ?s2}] => apply: subset_singleton=>//
                end
  end.

(***********)
(* Tactics *)
(***********)

(* After binding program variables to their correct labels, we use the Coq's default simplification algorithm *)
Ltac ssl_program_simpl := Tactics.program_simpl.


(* Ghost Variable Elim *)
Ltac ssl_ghostelim_pre := try apply: ghR; move=>h.

Ltac ssl_ghostelim_post := store_valid.

(* Read Rule *)
Ltac ssl_read := apply: bnd_readR=>/=.

(* Write Rule *)
Ltac ssl_write := apply: bnd_writeR=>/=.

Ltac ssl_write_post x :=
  (put_to_tail_ptr x + rewrite -(unitL (x :-> _))); apply frame.

(* Alloc Rule *)
Ltac ssl_alloc x :=
  apply: bnd_allocbR=>x//=.

(* Free Rule *)
Ltac ssl_dealloc :=
  apply: bnd_seq;
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
  | ?h1 \+ ?h2 => ssl_call_pre_aux h2; put_to_head h1
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
Ltac ssl_open := case: ifP=> H_cond.
Ltac ssl_open_post H :=
  case H;
  match goal with
  | [H_cond: is_true (_ == _) |- _] => move/eqP in H_cond; rewrite->H_cond in *=>//=
  | [H_cond: (_ == _) = false |- _] => rewrite->H_cond=>//=
  end;
  move=>_.

(* Abduce Branch Rule *)
Ltac ssl_abduce_branch := case: ifP=>H_cond.
