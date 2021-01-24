From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| dll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_558,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_558 /\ dll w x s1 h_dll_wxs1_558.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_559,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_559 /\ sll nxt s1 h_sll_nxts1_559.

Lemma dll_perm_eq_trans45 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans45: ssl_pred.
Lemma sll_perm_eq_trans46 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans46: ssl_pred.
Lemma pure47 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure47: ssl_pure.
Lemma pure48 vx22 : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). Admitted.
Hint Resolve pure48: ssl_pure.
Lemma pure49 vx22 vi122 s1i12 : @perm_eq nat_eqType ([:: vx22] ++ [:: vi122] ++ s1i12) ([:: vx22] ++ [:: vi122] ++ s1i12). Admitted.
Hint Resolve pure49: ssl_pure.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_560,
      h = f :-> x \+ h_sll_xs_560 /\ sll x s h_sll_xs_560,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_561,
      h = f :-> i \+ h_dll_is_561 /\ dll i null s h_dll_is_561
    ]).

Program Definition sll_to_dll : sll_to_dll_type :=
  Fix (fun (sll_to_dll : sll_to_dll_type) vprogs =>
    let: (f) := vprogs in
    Do (
      x2 <-- @read ptr f;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        f ::= nxtx22;;
        sll_to_dll (f);;
        i12 <-- @read ptr f;
        if i12 == null
        then
          i2 <-- allocb null 3;
          dealloc x2;;
          dealloc (x2 .+ 1);;
          f ::= i2;;
          (i2 .+ 1) ::= null;;
          (i2 .+ 2) ::= null;;
          i2 ::= vx22;;
          ret tt
        else
          i2 <-- allocb null 3;
          dealloc x2;;
          dealloc (x2 .+ 1);;
          (i12 .+ 2) ::= i2;;
          f ::= i2;;
          (i2 .+ 1) ::= i12;;
          (i2 .+ 2) ::= null;;
          i2 ::= vx22;;
          ret tt
    )).
Obligation Tactic := intro; move=>f; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
ex_elim h_sll_x2s_560.
move=>[sigma_self].
subst h_self.
move=>H_sll_x2s_560.
ssl_ghostelim_post.
ssl_read f.
ssl_open (x2 == null);
ssl_open_post H_sll_x2s_560.
move=>[phi_sll_x2s_5600].
move=>[sigma_sll_x2s_560].
subst h_sll_x2s_560.
ssl_emp;
exists (null);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto ].
ex_elim vx22 s1x2 nxtx22.
ex_elim h_sll_nxtx22s1x2_559x2.
move=>[phi_sll_x2s_5600].
move=>[sigma_sll_x2s_560].
subst h_sll_x2s_560.
move=>H_sll_nxtx22s1x2_559x2.
ssl_read x2.
ssl_read (x2 .+ 1).
ssl_write f.
ssl_call_pre (f :-> nxtx22 \+ h_sll_nxtx22s1x2_559x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_559x2);
sslauto.
move=>h_call1.
ex_elim i12.
ex_elim h_dll_i12s1x2_5611.
move=>[sigma_call1].
subst h_call1.
move=>H_dll_i12s1x2_5611.
store_valid.
ssl_read f.
ssl_open (i12 == null);
ssl_open_post H_dll_i12s1x2_5611.
move=>[phi_dll_i12s1x2_56110].
move=>[sigma_dll_i12s1x2_5611].
subst h_dll_i12s1x2_5611.
ssl_alloc i2.
ssl_dealloc x2.
ssl_dealloc (x2 .+ 1).
ssl_write f.
ssl_write_post f.
ssl_write (i2 .+ 1).
ssl_write_post (i2 .+ 1).
ssl_write (i2 .+ 2).
ssl_write_post (i2 .+ 2).
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> null \+ i2 .+ 2 :-> null);
sslauto;
solve [
unfold_constructor 2;
exists (vx22), (nil), (null);
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto ] ].
ex_elim vi122 s1i12 wi122.
ex_elim h_dll_wi122i12s1i12_558i12.
move=>[phi_dll_i12s1x2_56110].
move=>[sigma_dll_i12s1x2_5611].
subst h_dll_i12s1x2_5611.
move=>H_dll_wi122i12s1i12_558i12.
ssl_alloc i2.
ssl_dealloc x2.
ssl_dealloc (x2 .+ 1).
ssl_write (i12 .+ 2).
ssl_write_post (i12 .+ 2).
ssl_write f.
ssl_write_post f.
ssl_write (i2 .+ 1).
ssl_write_post (i2 .+ 1).
ssl_write (i2 .+ 2).
ssl_write_post (i2 .+ 2).
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> i12 \+ i2 .+ 2 :-> null \+ i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_558i12);
sslauto;
solve [
unfold_constructor 2;
exists (vx22), ([:: vi122] ++ s1i12), (i12);
exists (i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_558i12);
sslauto;
solve [
unfold_constructor 2;
exists (vi122), (s1i12), (wi122);
exists (h_dll_wi122i12s1i12_558i12);
sslauto ] ].
Qed.
