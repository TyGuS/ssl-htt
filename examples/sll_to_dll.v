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
  exists h_dll_wxs1_588,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_588 /\ dll w x s1 h_dll_wxs1_588.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_589,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_589 /\ sll nxt s1 h_sll_nxts1_589.

Lemma dll_perm_eq_trans70 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans70: ssl_pred.
Lemma sll_perm_eq_trans71 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans71: ssl_pred.
Lemma pure72 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure72: ssl_pure.
Lemma pure73 vx22 : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). Admitted.
Hint Resolve pure73: ssl_pure.
Lemma pure74 vx22 vi122 s1i12 : @perm_eq nat_eqType (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))) (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))). Admitted.
Hint Resolve pure74: ssl_pure.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_590,
      h = f :-> x \+ h_sll_xs_590 /\ sll x s h_sll_xs_590,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_591,
      h = f :-> i \+ h_dll_is_591 /\ dll i null s h_dll_is_591
    ]).

Program Definition sll_to_dll : sll_to_dll_type :=
  Fix (fun (sll_to_dll : sll_to_dll_type) vprogs =>
    let: (f) := vprogs in
    Do (
      x2 <-- @read ptr f;
      if (x2) == (null)
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        f ::= nxtx22;;
        sll_to_dll (f);;
        i12 <-- @read ptr f;
        if (i12) == (null)
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
ex_elim h_sll_xs_590.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_590.
ssl_ghostelim_post.
ssl_read f.
try rename x into x2.
try rename h_sll_xs_590 into h_sll_x2s_590.
try rename H_sll_xs_590 into H_sll_x2s_590.
ssl_open ((x2) == (null)) H_sll_x2s_590.
move=>[phi_sll_x2s_5900].
move=>[sigma_sll_x2s_590].
subst h_sll_x2s_590.
try rename h_dll_is_591 into h_dll_i_591.
try rename H_dll_is_591 into H_dll_i_591.
try rename h_sll_x2s_590 into h_sll_x2_590.
try rename H_sll_x2s_590 into H_sll_x2_590.
try rename h_dll_i_591 into h_dll__591.
try rename H_dll_i_591 into H_dll__591.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx2 s1x2 nxtx2.
ex_elim h_sll_nxtx2s1x2_589x2.
move=>[phi_sll_x2s_5900].
move=>[sigma_sll_x2s_590].
subst h_sll_x2s_590.
move=>H_sll_nxtx2s1x2_589x2.
try rename h_dll_is_591 into h_dll_ivx2s1x2_591.
try rename H_dll_is_591 into H_dll_ivx2s1x2_591.
try rename h_sll_x2s_590 into h_sll_x2vx2s1x2_590.
try rename H_sll_x2s_590 into H_sll_x2vx2s1x2_590.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_x2vx2s1x2_590 into h_sll_x2vx22s1x2_590.
try rename H_sll_x2vx2s1x2_590 into H_sll_x2vx22s1x2_590.
try rename h_dll_ivx2s1x2_591 into h_dll_ivx22s1x2_591.
try rename H_dll_ivx2s1x2_591 into H_dll_ivx22s1x2_591.
ssl_read (x2 .+ 1).
try rename nxtx2 into nxtx22.
try rename h_sll_nxtx2s1x2_589x2 into h_sll_nxtx22s1x2_589x2.
try rename H_sll_nxtx2s1x2_589x2 into H_sll_nxtx22s1x2_589x2.
try rename h_sll_x1s1_5901 into h_sll_nxtx22s1x2_589x2.
try rename H_sll_x1s1_5901 into H_sll_nxtx22s1x2_589x2.
ssl_write f.
ssl_call_pre (f :-> nxtx22 \+ h_sll_nxtx22s1x2_589x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_589x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim i1.
ex_elim h_dll_i1s1x2_5911.
move=>[sigma_call0].
subst h_call0.
move=>H_dll_i1s1x2_5911.
store_valid.
ssl_read f.
try rename i1 into i12.
try rename h_dll_i1s1x2_5911 into h_dll_i12s1x2_5911.
try rename H_dll_i1s1x2_5911 into H_dll_i12s1x2_5911.
ssl_open ((i12) == (null)) H_dll_i12s1x2_5911.
move=>[phi_dll_i12s1x2_59110].
move=>[sigma_dll_i12s1x2_5911].
subst h_dll_i12s1x2_5911.
try rename h_sll_nxtx22s1x2_589x2 into h_sll_nxtx22_589x2.
try rename H_sll_nxtx22s1x2_589x2 into H_sll_nxtx22_589x2.
try rename h_dll_ivx22s1x2_591 into h_dll_ivx22_591.
try rename H_dll_ivx22s1x2_591 into H_dll_ivx22_591.
try rename h_sll_x2vx22s1x2_590 into h_sll_x2vx22_590.
try rename H_sll_x2vx22s1x2_590 into H_sll_x2vx22_590.
try rename h_dll_i12s1x2_5911 into h_dll_i12_5911.
try rename H_dll_i12s1x2_5911 into H_dll_i12_5911.
try rename h_dll_wiis11i_588i into h_dll_wii_588i.
try rename H_dll_wiis11i_588i into H_dll_wii_588i.
try rename h_dll_wii_588i into h_dll_i_588i.
try rename H_dll_wii_588i into H_dll_i_588i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx22_591 into h_dll_i2vx22_591.
try rename H_dll_ivx22_591 into H_dll_i2vx22_591.
try rename h_dll_i_588i into h_dll_i2_588i.
try rename H_dll_i_588i into H_dll_i2_588i.
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
ssl_close 2;
exists (vx22), (nil), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vi12 s1i12 wi12.
ex_elim h_dll_wi12i12s1i12_588i12.
move=>[phi_dll_i12s1x2_59110].
move=>[sigma_dll_i12s1x2_5911].
subst h_dll_i12s1x2_5911.
move=>H_dll_wi12i12s1i12_588i12.
try rename h_sll_nxtx22s1x2_589x2 into h_sll_nxtx22vi12s1i12_589x2.
try rename H_sll_nxtx22s1x2_589x2 into H_sll_nxtx22vi12s1i12_589x2.
try rename h_dll_ivx22s1x2_591 into h_dll_ivx22vi12s1i12_591.
try rename H_dll_ivx22s1x2_591 into H_dll_ivx22vi12s1i12_591.
try rename h_sll_x2vx22s1x2_590 into h_sll_x2vx22vi12s1i12_590.
try rename H_sll_x2vx22s1x2_590 into H_sll_x2vx22vi12s1i12_590.
try rename h_dll_i12s1x2_5911 into h_dll_i12vi12s1i12_5911.
try rename H_dll_i12s1x2_5911 into H_dll_i12vi12s1i12_5911.
ssl_read i12.
try rename vi12 into vi122.
try rename h_sll_x2vx22vi12s1i12_590 into h_sll_x2vx22vi122s1i12_590.
try rename H_sll_x2vx22vi12s1i12_590 into H_sll_x2vx22vi122s1i12_590.
try rename h_dll_ivx22vi12s1i12_591 into h_dll_ivx22vi122s1i12_591.
try rename H_dll_ivx22vi12s1i12_591 into H_dll_ivx22vi122s1i12_591.
try rename h_dll_i12vi12s1i12_5911 into h_dll_i12vi122s1i12_5911.
try rename H_dll_i12vi12s1i12_5911 into H_dll_i12vi122s1i12_5911.
try rename h_sll_nxtx22vi12s1i12_589x2 into h_sll_nxtx22vi122s1i12_589x2.
try rename H_sll_nxtx22vi12s1i12_589x2 into H_sll_nxtx22vi122s1i12_589x2.
ssl_read (i12 .+ 1).
try rename wi12 into wi122.
try rename h_dll_wi12i12s1i12_588i12 into h_dll_wi122i12s1i12_588i12.
try rename H_dll_wi12i12s1i12_588i12 into H_dll_wi122i12s1i12_588i12.
try rename h_dll_wiis11i_588i into h_dll_wiivwis11wi_588i.
try rename H_dll_wiis11i_588i into H_dll_wiivwis11wi_588i.
try rename h_dll_wwiwis11wi_588wi into h_dll_wi122i12s1i12_588i12.
try rename H_dll_wwiwis11wi_588wi into H_dll_wi122i12s1i12_588i12.
try rename h_dll_wiivwis11wi_588i into h_dll_i12ivwis11wi_588i.
try rename H_dll_wiivwis11wi_588i into H_dll_i12ivwis11wi_588i.
try rename h_dll_i12ivwis11wi_588i into h_dll_i12ivwis1i12_588i.
try rename H_dll_i12ivwis11wi_588i into H_dll_i12ivwis1i12_588i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_i12ivwis1i12_588i into h_dll_i12i2vwis1i12_588i.
try rename H_dll_i12ivwis1i12_588i into H_dll_i12i2vwis1i12_588i.
try rename h_dll_ivx22vi122s1i12_591 into h_dll_i2vx22vi122s1i12_591.
try rename H_dll_ivx22vi122s1i12_591 into H_dll_i2vx22vi122s1i12_591.
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
try rename h_dll_i12i2vwis1i12_588i into h_dll_i12i2vi122s1i12_588i.
try rename H_dll_i12i2vwis1i12_588i into H_dll_i12i2vi122s1i12_588i.
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> i12 \+ i2 .+ 2 :-> null \+ i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_588i12);
sslauto.
ssl_close 2;
exists (vx22), (([:: vi122]) ++ (s1i12)), (i12), (i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_588i12);
sslauto.
ssl_close 2;
exists (vi122), (s1i12), (wi122), (h_dll_wi122i12s1i12_588i12);
sslauto.
ssl_frame_unfold.
Qed.