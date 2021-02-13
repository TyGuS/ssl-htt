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
  exists h_dll_wxs1_557,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_557 /\ dll w x s1 h_dll_wxs1_557.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_558,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_558 /\ sll nxt s1 h_sll_nxts1_558.

Lemma dll_perm_eq_trans36 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans36: ssl_pred.
Lemma sll_perm_eq_trans37 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans37: ssl_pred.
Lemma pure38 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure38: ssl_pure.
Lemma pure39 vx22 : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). Admitted.
Hint Resolve pure39: ssl_pure.
Lemma pure40 vx22 vi122 s1i12 : @perm_eq nat_eqType ([:: vx22] ++ [:: vi122] ++ s1i12) ([:: vx22] ++ [:: vi122] ++ s1i12). Admitted.
Hint Resolve pure40: ssl_pure.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_559,
      h = f :-> x \+ h_sll_xs_559 /\ sll x s h_sll_xs_559,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_560,
      h = f :-> i \+ h_dll_is_560 /\ dll i null s h_dll_is_560
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
          vi122 <-- @read nat i12;
          wi122 <-- @read ptr (i12 .+ 1);
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
move=>[x s].
ex_elim h_sll_xs_559.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_559.
ssl_ghostelim_post.
ssl_read f.
try rename x into x2.
try rename h_sll_xs_559 into h_sll_x2s_559.
try rename H_sll_xs_559 into H_sll_x2s_559.
ssl_open (x2 == null) H_sll_x2s_559.
move=>[phi_sll_x2s_5590].
move=>[sigma_sll_x2s_559].
subst h_sll_x2s_559.
shelve.
ex_elim vx2 s1x2 nxtx2.
ex_elim h_sll_nxtx2s1x2_558x2.
move=>[phi_sll_x2s_5590].
move=>[sigma_sll_x2s_559].
subst h_sll_x2s_559.
move=>H_sll_nxtx2s1x2_558x2.
shelve.
Unshelve.
try rename h_dll_is_560 into h_dll_i_560.
try rename H_dll_is_560 into H_dll_i_560.
try rename h_sll_x2s_559 into h_sll_x2_559.
try rename H_sll_x2s_559 into H_sll_x2_559.
try rename h_dll_i_560 into h_dll__560.
try rename H_dll_i_560 into H_dll__560.
ssl_emp;
exists (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_dll_is_560 into h_dll_ivx2s1x2_560.
try rename H_dll_is_560 into H_dll_ivx2s1x2_560.
try rename h_sll_x2s_559 into h_sll_x2vx2s1x2_559.
try rename H_sll_x2s_559 into H_sll_x2vx2s1x2_559.
ssl_read x2.
try rename vx2 into vx22.
try rename h_dll_ivx2s1x2_560 into h_dll_ivx22s1x2_560.
try rename H_dll_ivx2s1x2_560 into H_dll_ivx22s1x2_560.
try rename h_sll_x2vx2s1x2_559 into h_sll_x2vx22s1x2_559.
try rename H_sll_x2vx2s1x2_559 into H_sll_x2vx22s1x2_559.
ssl_read (x2 .+ 1).
try rename nxtx2 into nxtx22.
try rename h_sll_nxtx2s1x2_558x2 into h_sll_nxtx22s1x2_558x2.
try rename H_sll_nxtx2s1x2_558x2 into H_sll_nxtx22s1x2_558x2.
ssl_write f.
ssl_call_pre (f :-> nxtx22 \+ h_sll_nxtx22s1x2_558x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_558x2);
sslauto.
move=>h_call0.
ex_elim i1.
ex_elim h_dll_i1s1x2_5601.
move=>[sigma_call0].
subst h_call0.
move=>H_dll_i1s1x2_5601.
store_valid.
ssl_read f.
try rename i1 into i12.
try rename h_dll_i1s1x2_5601 into h_dll_i12s1x2_5601.
try rename H_dll_i1s1x2_5601 into H_dll_i12s1x2_5601.
ssl_open (i12 == null) H_dll_i12s1x2_5601.
move=>[phi_dll_i12s1x2_56010].
move=>[sigma_dll_i12s1x2_5601].
subst h_dll_i12s1x2_5601.
shelve.
ex_elim vi12 s1i12 wi12.
ex_elim h_dll_wi12i12s1i12_557i12.
move=>[phi_dll_i12s1x2_56010].
move=>[sigma_dll_i12s1x2_5601].
subst h_dll_i12s1x2_5601.
move=>H_dll_wi12i12s1i12_557i12.
shelve.
Unshelve.
try rename h_dll_ivx22s1x2_560 into h_dll_ivx22_560.
try rename H_dll_ivx22s1x2_560 into H_dll_ivx22_560.
try rename h_dll_i12s1x2_5601 into h_dll_i12_5601.
try rename H_dll_i12s1x2_5601 into H_dll_i12_5601.
try rename h_sll_x2vx22s1x2_559 into h_sll_x2vx22_559.
try rename H_sll_x2vx22s1x2_559 into H_sll_x2vx22_559.
try rename h_sll_nxtx22s1x2_558x2 into h_sll_nxtx22_558x2.
try rename H_sll_nxtx22s1x2_558x2 into H_sll_nxtx22_558x2.
try rename h_dll_wiis11i_557i into h_dll_wii_557i.
try rename H_dll_wiis11i_557i into H_dll_wii_557i.
try rename h_dll_wii_557i into h_dll_i_557i.
try rename H_dll_wii_557i into H_dll_i_557i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx22_560 into h_dll_i2vx22_560.
try rename H_dll_ivx22_560 into H_dll_i2vx22_560.
try rename h_dll_i_557i into h_dll_i2_557i.
try rename H_dll_i_557i into H_dll_i2_557i.
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
sslauto.
unfold_constructor 2;
exists (vx22), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_dll_ivx22s1x2_560 into h_dll_ivx22vi12s1i12_560.
try rename H_dll_ivx22s1x2_560 into H_dll_ivx22vi12s1i12_560.
try rename h_dll_i12s1x2_5601 into h_dll_i12vi12s1i12_5601.
try rename H_dll_i12s1x2_5601 into H_dll_i12vi12s1i12_5601.
try rename h_sll_x2vx22s1x2_559 into h_sll_x2vx22vi12s1i12_559.
try rename H_sll_x2vx22s1x2_559 into H_sll_x2vx22vi12s1i12_559.
try rename h_sll_nxtx22s1x2_558x2 into h_sll_nxtx22vi12s1i12_558x2.
try rename H_sll_nxtx22s1x2_558x2 into H_sll_nxtx22vi12s1i12_558x2.
ssl_read i12.
try rename vi12 into vi122.
try rename h_sll_x2vx22vi12s1i12_559 into h_sll_x2vx22vi122s1i12_559.
try rename H_sll_x2vx22vi12s1i12_559 into H_sll_x2vx22vi122s1i12_559.
try rename h_sll_nxtx22vi12s1i12_558x2 into h_sll_nxtx22vi122s1i12_558x2.
try rename H_sll_nxtx22vi12s1i12_558x2 into H_sll_nxtx22vi122s1i12_558x2.
try rename h_dll_i12vi12s1i12_5601 into h_dll_i12vi122s1i12_5601.
try rename H_dll_i12vi12s1i12_5601 into H_dll_i12vi122s1i12_5601.
try rename h_dll_ivx22vi12s1i12_560 into h_dll_ivx22vi122s1i12_560.
try rename H_dll_ivx22vi12s1i12_560 into H_dll_ivx22vi122s1i12_560.
ssl_read (i12 .+ 1).
try rename wi12 into wi122.
try rename h_dll_wi12i12s1i12_557i12 into h_dll_wi122i12s1i12_557i12.
try rename H_dll_wi12i12s1i12_557i12 into H_dll_wi122i12s1i12_557i12.
try rename h_dll_wiis11i_557i into h_dll_wiivwis11wi_557i.
try rename H_dll_wiis11i_557i into H_dll_wiivwis11wi_557i.
try rename h_dll_wwiwis11wi_557wi into h_dll_wwiwis11wi_557i12.
try rename H_dll_wwiwis11wi_557wi into H_dll_wwiwis11wi_557i12.
try rename h_dll_wiivwis11wi_557i into h_dll_i12ivwis11wi_557i.
try rename H_dll_wiivwis11wi_557i into H_dll_i12ivwis11wi_557i.
try rename h_dll_wwiwis11wi_557i12 into h_dll_wwii12s11wi_557i12.
try rename H_dll_wwiwis11wi_557i12 into H_dll_wwii12s11wi_557i12.
try rename h_dll_wwii12s11wi_557i12 into h_dll_wwii12s1i12_557i12.
try rename H_dll_wwii12s11wi_557i12 into H_dll_wwii12s1i12_557i12.
try rename h_dll_i12ivwis11wi_557i into h_dll_i12ivwis1i12_557i.
try rename H_dll_i12ivwis11wi_557i into H_dll_i12ivwis1i12_557i.
try rename h_dll_wwii12s1i12_557i12 into h_dll_wi122i12s1i12_557i12.
try rename H_dll_wwii12s1i12_557i12 into H_dll_wi122i12s1i12_557i12.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_i12ivwis1i12_557i into h_dll_i12i2vwis1i12_557i.
try rename H_dll_i12ivwis1i12_557i into H_dll_i12i2vwis1i12_557i.
try rename h_dll_ivx22vi122s1i12_560 into h_dll_i2vx22vi122s1i12_560.
try rename H_dll_ivx22vi122s1i12_560 into H_dll_i2vx22vi122s1i12_560.
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
try rename h_dll_i12i2vwis1i12_557i into h_dll_i12i2vi122s1i12_557i.
try rename H_dll_i12i2vwis1i12_557i into H_dll_i12i2vi122s1i12_557i.
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> i12 \+ i2 .+ 2 :-> null \+ i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_557i12);
sslauto.
unfold_constructor 2;
exists (vx22), ([:: vi122] ++ s1i12), (i12), (i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_557i12);
sslauto.
unfold_constructor 2;
exists (vi122), (s1i12), (wi122), (h_dll_wi122i12s1i12_557i12);
sslauto.
Qed.