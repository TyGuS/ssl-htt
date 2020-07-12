From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg0 of x == 0 of
    s = nil /\ h = empty
| lseg1 of x != 0 of
  exists nxt s1 v,
  exists heap_lseg_alpha_513,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ heap_lseg_alpha_513 /\ lseg nxt s1 heap_lseg_alpha_513
.

Lemma lseg_heap_unify :
  forall h h' x s,
    lseg x s h -> lseg x s h' -> h = h'.
Proof.
  intros h h' x s Hh Hh'.
  case: Hh=>cond; case: Hh'=>cond'=>//=.
  - by move=>[_ ->] [_ ->].
  - move/eqP in cond; move/eqP in cond'; intuition.
  - move/eqP in cond; move/eqP in cond'; intuition.
  - move=>[nxt] [s1] [v] [h''] Hh.
    move=>[nxt'] [s1'] [v'] [h'''] Hh'.
Admitted.



(*
void listcopy(loc r) []
{true ; r :-> x ** lseg(x, S)<_alpha_519>}
{true ; r :-> y ** lseg(x, S)<_alpha_520> ** lseg(y, S)<_alpha_521>}

void listcopy (loc r) {
  let x = *r;
  if (x == 0) {
  } else {
    let v = *x;
    let n = *(x + 1);
    *x = n;
    listcopy(x);
    let yx = *x;
    let y = malloc(2);
    *r = y;
    *(y + 1) = yx;
    *x = v;
    *y = v;
  }
}
*)


Definition listcopy_type :=
  forall (r : ptr),
  {(arg: ptr * seq nat)},
    STsep (
        fun h =>
          let: (x, s) := arg in
        exists heap_lseg_alpha_519,
          h = r :-> x \+ heap_lseg_alpha_519 /\ lseg x s heap_lseg_alpha_519,
      [vfun (_: unit) h =>
        exists y,
        exists heap_lseg_alpha_520 heap_lseg_alpha_521,
          let: (x, s) := arg in
          h = r :-> y \+ heap_lseg_alpha_520 \+ heap_lseg_alpha_521 /\ lseg x s heap_lseg_alpha_520 /\ lseg y s heap_lseg_alpha_521      ]).


Program Definition listcopy : listcopy_type :=
  Fix (fun (listcopy: listcopy_type) r =>
    Do (
  x <-- @read ptr r;
  if x == 0
  then
    ret tt
  else
    v <-- @read nat x;
    n <-- @read ptr (x .+ 1);
    x ::= n;;
    listcopy x;;
    yx <-- @read ptr x;
    y <-- allocb null 2;
    r ::= y;;
    (y .+ 1) ::= yx;;
    x ::= v;;
    y ::= v;;
    ret tt
      )).

Next Obligation.
  ssl_ghostelim_pre.
  move=>[x2 S].
  move=>[heap_lseg_alpha_519].
  move=>[->]=>/=.
  move=>H_lseg_alpha_519.
  ssl_ghostelim_post.

  ssl_read.

  case: ifP=>H_cond.  

  case: (H_lseg_alpha_519); rewrite H_cond=>//= _.
  move=>[phi_lseg_alpha_519].
  move=>[sigma_lseg_alpha_519].
  ssl_emp.
  rewrite sigma_lseg_alpha_519 in H_lseg_alpha_519.
  exists x2, empty, empty.
  ssl_emp_post.

  case: (H_lseg_alpha_519); rewrite H_cond=>//= _.
  move=>[nxtx22] [s1x2] [vx22] [heap_lseg_alpha_513x2].
  move=>[phi_lseg_alpha_519].
  move=>[sigma_lseg_alpha_519].
  rewrite sigma_lseg_alpha_519.
  move=>H_lseg_alpha_513x2.
  
  ssl_read.
  ssl_read.

  ssl_write.
  put_to_head heap_lseg_alpha_513x2.
  put_to_head (x2 :-> nxtx22).
  rewrite -?joinA.
  rewrite (joinA _ heap_lseg_alpha_513x2).
  apply: bnd_seq.
  apply: (gh_ex (nxtx22, s1x2)).
  apply: val_do=>//=.
  store_valid_hyps.    
  exists heap_lseg_alpha_513x2. hhauto.

  move=>_ h'.  
  move=>[yx22] [heap_lseg_alpha_520x2] [heap_lseg_alpha_521x2].
  move=>[sigma_lseg_alpha_513x2 [H_lseg_alpha_520x2 H_lseg_alpha_521x2]]=>//=.
  rewrite ?joinA.
  store_valid_hyps.

  rewrite sigma_lseg_alpha_513x2.
  ssl_read.
  ssl_alloc y2.
  ssl_write. ssl_write_post r.
  ssl_write. ssl_write_post (y2 .+ 1).
  ssl_write. ssl_write_post x2.
  ssl_write. ssl_write_post y2.

  rewrite unitL.
  apply: val_ret.
  rewrite ?unitL.
  move=>H_valid1 H_valid2 H_valid3 H_valid4.

  exists y2.
  exists heap_lseg_alpha_519.
  exists ( y2 :-> vx22 \+ y2 .+ 1 :-> yx22 \+ heap_lseg_alpha_521x2).
  split.
  rewrite sigma_lseg_alpha_519.
  rewrite ?joinA.
  rewrite (lseg_heap_unify heap_lseg_alpha_513x2 heap_lseg_alpha_520x2 nxtx22 s1x2 H_lseg_alpha_513x2 H_lseg_alpha_520x2).
  hhauto.
  split; auto.
  constructor 2.
  - move:(H_valid4).
    put_to_head (y2 :-> vx22).
    rewrite defPtUnO; case/andP. auto.
  - exists yx22, s1x2, vx22.
    exists heap_lseg_alpha_521x2.
    split; auto.
Qed.
