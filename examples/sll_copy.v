From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_540,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_540 /\ sll nxt s1 h_sll_nxts1_540.

Lemma sll_perm_eq_trans26 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans26: ssl_pred.
Lemma pure27 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure27: ssl_pure.
Lemma pure28 b1 : b1 < b1 + 1. Admitted.
Hint Resolve pure28: ssl_pure.
Lemma pure29 vx22 s1x2 : @perm_eq nat_eqType ([:: vx22] ++ s1x2) ([:: vx22] ++ s1x2). Admitted.
Hint Resolve pure29: ssl_pure.
Lemma pure30 vx22 s1x2 : @perm_eq nat_eqType ([:: vx22] ++ s1x2) ([:: vx22] ++ s1x2). Admitted.
Hint Resolve pure30: ssl_pure.

Definition sll_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_a,
      h = r :-> x \+ h_sll_xs_a /\ sll x s h_sll_xs_a,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_sll_xs_a h_sll_ys_b,
      h = r :-> y \+ h_sll_xs_a \+ h_sll_ys_b /\ sll x s h_sll_xs_a /\ sll y s h_sll_ys_b
    ]).

Program Definition sll_copy : sll_copy_type :=
  Fix (fun (sll_copy : sll_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        r ::= nxtx22;;
        sll_copy (r);;
        y12 <-- @read ptr r;
        y2 <-- allocb null 2;
        r ::= y2;;
        (y2 .+ 1) ::= y12;;
        y2 ::= vx22;;
        ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
ex_elim h_sll_x2s_a.
move=>[sigma_self].
subst h_self.
move=>H_sll_x2s_a.
ssl_ghostelim_post.
ssl_read r.
ssl_open (x2 == null);
ssl_open_post H_sll_x2s_a.
move=>[phi_sll_x2s_a0].
move=>[sigma_sll_x2s_a].
subst h_sll_x2s_a.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto |
unfold_constructor 1;
sslauto ].
ex_elim vx22 s1x2 nxtx22.
ex_elim h_sll_nxtx22s1x2_540x2.
move=>[phi_sll_x2s_a0].
move=>[sigma_sll_x2s_a].
subst h_sll_x2s_a.
move=>H_sll_nxtx22s1x2_540x2.
ssl_read x2.
ssl_read (x2 .+ 1).
ssl_write r.
ssl_call_pre (r :-> nxtx22 \+ h_sll_nxtx22s1x2_540x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_540x2);
sslauto.
move=>h_call1.
ex_elim y12.
ex_elim h_sll_nxtx22s1x2_540x2 h_sll_y12s1x2_b1.
move=>[sigma_call1].
subst h_call1.
move=>[H_sll_nxtx22s1x2_540x2 H_sll_y12s1x2_b1].
store_valid.
ssl_read r.
ssl_alloc y2.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists (y2);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> nxtx22 \+ h_sll_nxtx22s1x2_540x2);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> y12 \+ h_sll_y12s1x2_b1);
sslauto;
solve [
unfold_constructor 2;
exists (vx22), (s1x2), (nxtx22);
exists (h_sll_nxtx22s1x2_540x2);
sslauto |
unfold_constructor 2;
exists (vx22), (s1x2), (y12);
exists (h_sll_y12s1x2_b1);
sslauto ].
Qed.
