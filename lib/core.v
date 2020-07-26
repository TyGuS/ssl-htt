From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.

(* SuSLik bindings *)
Notation empty := Unit.
Coercion ptr_nat : nat >-> ptr.
Definition skip := ret tt.

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

Ltac put_to_tail_ptr p :=
  rewrite -?joinA; rewrite ?(joinC (p :-> _) _); rewrite ?joinA.

Ltac put_to_tail h :=
  rewrite -?joinA; rewrite ?(joinC h _); rewrite ?joinA.

Ltac put_to_head h :=
  put_to_tail h;
  rewrite (joinC _ h).

Ltac ssl_read := apply: bnd_readR=>/=.

Ltac ssl_write := apply: bnd_writeR=>/=.

Ltac ssl_write_post x :=
  (put_to_tail_ptr x + rewrite -(unitL (x :-> _))); apply frame.

Ltac ssl_alloc x :=
  apply: bnd_allocbR=>x//=.

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

Ltac store_valid :=
  rewrite ?unitL ?unitR;
  try match goal with
  | [|- is_true (valid _) -> _] =>
    let hyp := fresh "H_valid" in move=>hyp;
    store_valid
  end
.

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

Ltac ssl_emp := apply: val_ret; rewrite ?unitL; store_valid; move=>//.

Lemma subset_singleton :
    forall (s1: seq nat) (x: nat),
      {subset s1 <= [::x]} -> {subset x :: s1 <= [::x]}.
intros.
move=>n.
rewrite inE; move/orP. case.
move/eqP=>->. by rewrite inE eqxx.
move/H=>//.
Qed.

Ltac ssl_emp_post :=
  rewrite ?unitL ?unitR;
  repeat match goal with
  | [|- _ /\ _] => split=>//
  | [|- ?h = _] =>
    match type of h with
    | (PCM.sort heapPCM) => rewrite ?unitL; rewrite ?unitR; hhauto
    | (PCM.sort (union_map_classPCM heapUMC)) => rewrite ?unitL; rewrite ?unitR; hhauto
    | _ => auto
    end
  | [H: is_true (_ <= _) |- _] => case: ltngtP H=>//
  | [H: (_ <= _) = false |- _] => case: ltngtP H=>//
  | [H: {subset ?s1 <= ?s2} |- {subset _ :: ?s1 <= ?s2}] => apply: subset_singleton=>//
   end.

Ltac unfold_constructor n :=
  match n with
  | 1 => constructor 1=>//
  | 2 => constructor 2=>//
  | 3 => constructor 3=>//
  | _ => constructor=>//
  end;
  match goal with
  | [|- is_true (_ != ptr_nat 0)] => assert_not_null
  | _ => idtac
  end.

Ltac ssl_ghostelim_pre := try apply: ghR; move=>h.

Ltac ssl_ghostelim_post := store_valid.

