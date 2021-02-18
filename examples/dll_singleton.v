From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| dll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_585,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_585 /\ dll w x s1 h_dll_wxs1_585.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_586,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_586 /\ sll nxt s1 h_sll_nxts1_586.

Lemma dll_perm_eq_trans67 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans67: ssl_pred.
Lemma sll_perm_eq_trans68 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans68: ssl_pred.
Lemma pure69 x : @perm_eq nat_eqType ([:: x]) ([:: x]). Admitted.
Hint Resolve pure69: ssl_pure.

Definition dll_singleton_type :=
  forall (vprogs : nat * ptr),
  {(vghosts : ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      h = r :-> a,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (a) := vghosts in
      exists elems y,
      exists h_dll_yelems_587,
      @perm_eq nat_eqType (elems) ([:: x]) /\ h = r :-> y \+ h_dll_yelems_587 /\ dll y null elems h_dll_yelems_587
    ]).

Program Definition dll_singleton : dll_singleton_type :=
  Fix (fun (dll_singleton : dll_singleton_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      y2 <-- allocb null 3;
      r ::= y2;;
      (y2 .+ 1) ::= null;;
      (y2 .+ 2) ::= null;;
      y2 ::= x;;
      ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>a.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
try rename h_dll_yelems_587 into h_dll_yx_587.
try rename H_dll_yelems_587 into H_dll_yx_587.
ssl_read r.
try rename a into a2.
try rename h_dll_wyys1y_585y into h_dll_wyy_585y.
try rename H_dll_wyys1y_585y into H_dll_wyy_585y.
try rename h_dll_wyy_585y into h_dll_y_585y.
try rename H_dll_wyy_585y into H_dll_y_585y.
ssl_alloc y2.
try rename y into y2.
try rename h_dll_yx_587 into h_dll_y2x_587.
try rename H_dll_yx_587 into H_dll_y2x_587.
try rename h_dll_y_585y into h_dll_y2_585y.
try rename H_dll_y_585y into H_dll_y2_585y.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write (y2 .+ 2).
ssl_write_post (y2 .+ 2).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ([:: x]), (y2);
exists (y2 :-> x \+ y2 .+ 1 :-> null \+ y2 .+ 2 :-> null);
sslauto.
unfold_constructor 2;
exists (x), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
Qed.