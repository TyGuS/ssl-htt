From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_568,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_568 /\ sll nxt s1 h_sll_nxts1_568.

Lemma sll_perm_eq_trans44 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans44: ssl_pred.
Lemma pure45 x : @perm_eq nat_eqType ([:: x]) ([:: x]). Admitted.
Hint Resolve pure45: ssl_pure.

Definition sll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      h = p :-> a,
    [vfun (_: unit) h =>
      let: (x, p) := vprogs in
      let: (a) := vghosts in
      exists elems y,
      exists h_sll_yelems_569,
      @perm_eq nat_eqType (elems) ([:: x]) /\ h = p :-> y \+ h_sll_yelems_569 /\ sll y elems h_sll_yelems_569
    ]).

Program Definition sll_singleton : sll_singleton_type :=
  Fix (fun (sll_singleton : sll_singleton_type) vprogs =>
    let: (x, p) := vprogs in
    Do (
      a2 <-- @read ptr p;
      y2 <-- allocb null 2;
      p ::= y2;;
      (y2 .+ 1) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x p]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_sll_yelems_569 into h_sll_yx_569.
try rename H_sll_yelems_569 into H_sll_yx_569.
ssl_read p.
try rename a into a2.
try rename h_sll_nxtys1y_568y into h_sll_s1y_568y.
try rename H_sll_nxtys1y_568y into H_sll_s1y_568y.
try rename h_sll_s1y_568y into h_sll__568y.
try rename H_sll_s1y_568y into H_sll__568y.
ssl_alloc y2.
try rename y into y2.
try rename h_sll_yx_569 into h_sll_y2x_569.
try rename H_sll_yx_569 into H_sll_y2x_569.
ssl_write p.
ssl_write_post p.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.