From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.
From Hammer Require Import Hammer.
(* Configure Hammer *)
Set Hammer ATPLimit 60.
Unset Hammer Eprover.
Unset Hammer Vampire.
Add Search Blacklist "fcsl.".
Add Search Blacklist "HTT.".
Add Search Blacklist "Coq.ssr.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.ssrfun".
Add Search Blacklist "mathcomp.ssreflect.bigop".
Add Search Blacklist "mathcomp.ssreflect.choice".
Add Search Blacklist "mathcomp.ssreflect.div".
Add Search Blacklist "mathcomp.ssreflect.finfun".
Add Search Blacklist "mathcomp.ssreflect.fintype".
Add Search Blacklist "mathcomp.ssreflect.path".
Add Search Blacklist "mathcomp.ssreflect.tuple".


Require Import common.

Lemma dll_perm_eq_congr1 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h.
  (* intros; hammer. *)
  move=>Heq Hdll; sslauto.
  case: Hdll=>cond.
  move=>[Heq1 ->].
  constructor 1=>//=; sslauto.
  move=>[v][s1][w][h'].
  move=>[Heq1 [->Hdll]].
  constructor 2=>//=.
  exists v, s1, w, h'.
  sslauto.
  assumption.
Qed.
Hint Resolve dll_perm_eq_congr1: ssl_pred.
Lemma sll_perm_eq_congr2 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h.
  (* intros; hammer *)
  move=>Heq Hsll; sslauto.
  case: Hsll=>cond.
  move=>[Heq1 ->].
  constructor 1=>//=; sslauto.
  move=>[v] [s2] [nxt] [h'].
  move=>[Heq1 [-> Hssl]].
  constructor 2=>//=.
  exists v, s2, nxt, h'.
  sslauto.
  assumption.
Qed.
Hint Resolve sll_perm_eq_congr2: ssl_pred.
Lemma pure3 : @perm_eq nat_eqType (@nil nat) (@nil nat). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (vx22 : nat) : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (vx22 : nat) (vi122 : nat) (s1i12 : seq nat) : @perm_eq nat_eqType (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))) (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_2,
      h = f :-> (x) \+ h_sll_xs_2 /\ sll x s h_sll_xs_2,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_3,
      h = f :-> (i) \+ h_dll_is_3 /\ dll i null s h_dll_is_3
    ]).

Program Definition sll_to_dll : sll_to_dll_type :=
  Fix (fun (sll_to_dll : sll_to_dll_type) vprogs =>
    let: (f) := vprogs in
    Do (
      x1 <-- @read ptr f;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        nxtx11 <-- @read ptr (x1 .+ 1);
        f ::= nxtx11;;
        sll_to_dll (f);;
        i11 <-- @read ptr f;
        if (i11) == (null)
        then
          i2 <-- allocb null 3;
          dealloc x1;;
          dealloc (x1 .+ 1);;
          f ::= i2;;
          (i2 .+ 1) ::= null;;
          (i2 .+ 2) ::= null;;
          i2 ::= vx11;;
          ret tt
        else
          vi111 <-- @read nat i11;
          wi111 <-- @read ptr (i11 .+ 1);
          i2 <-- allocb null 3;
          dealloc x1;;
          dealloc (x1 .+ 1);;
          (i11 .+ 2) ::= i2;;
          f ::= i2;;
          (i2 .+ 1) ::= i11;;
          (i2 .+ 2) ::= null;;
          i2 ::= vi111;;
          i11 ::= vx11;;
          ret tt
    )).
Obligation Tactic := intro; move=>f; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x s].
ex_elim h_sll_xs_2.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_2.
ssl_ghostelim_post.
ssl_read f.
try rename x into x1.
try rename h_sll_xs_2 into h_sll_x1s_2.
try rename H_sll_xs_2 into H_sll_x1s_2.
ssl_open ((x1) == (null)) H_sll_x1s_2.
move=>[phi_sll_x1s_20].
move=>[sigma_sll_x1s_2].
subst h_sll_x1s_2.
try rename h_dll_is_3 into h_dll_i_3.
try rename H_dll_is_3 into H_dll_i_3.
try rename h_sll_x1s_2 into h_sll_x1_2.
try rename H_sll_x1s_2 into H_sll_x1_2.
try rename h_dll_i_3 into h_dll__3.
try rename H_dll_i_3 into H_dll__3.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx1 s1x1 nxtx1.
ex_elim h_sll_nxtx1s1x1_1x1.
move=>[phi_sll_x1s_20].
move=>[sigma_sll_x1s_2].
subst h_sll_x1s_2.
move=>H_sll_nxtx1s1x1_1x1.
try rename h_dll_is_3 into h_dll_ivx1s1x1_3.
try rename H_dll_is_3 into H_dll_ivx1s1x1_3.
try rename h_sll_x1s_2 into h_sll_x1vx1s1x1_2.
try rename H_sll_x1s_2 into H_sll_x1vx1s1x1_2.
ssl_read x1.
try rename vx1 into vx11.
try rename h_dll_ivx1s1x1_3 into h_dll_ivx11s1x1_3.
try rename H_dll_ivx1s1x1_3 into H_dll_ivx11s1x1_3.
try rename h_sll_x1vx1s1x1_2 into h_sll_x1vx11s1x1_2.
try rename H_sll_x1vx1s1x1_2 into H_sll_x1vx11s1x1_2.
ssl_read (x1 .+ 1).
try rename nxtx1 into nxtx11.
try rename h_sll_nxtx1s1x1_1x1 into h_sll_nxtx11s1x1_1x1.
try rename H_sll_nxtx1s1x1_1x1 into H_sll_nxtx11s1x1_1x1.
try rename h_sll_x2s1_21 into h_sll_nxtx11s1x1_1x1.
try rename H_sll_x2s1_21 into H_sll_nxtx11s1x1_1x1.
ssl_write f.
ssl_call_pre (f :-> (nxtx11) \+ h_sll_nxtx11s1x1_1x1).
ssl_call (nxtx11, s1x1).
exists (h_sll_nxtx11s1x1_1x1);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim i1.
ex_elim h_dll_i1s1x1_31.
move=>[sigma_call0].
subst h_call0.
move=>H_dll_i1s1x1_31.
store_valid.
ssl_read f.
try rename i1 into i11.
try rename h_dll_i1s1x1_31 into h_dll_i11s1x1_31.
try rename H_dll_i1s1x1_31 into H_dll_i11s1x1_31.
ssl_open ((i11) == (null)) H_dll_i11s1x1_31.
move=>[phi_dll_i11s1x1_310].
move=>[sigma_dll_i11s1x1_31].
subst h_dll_i11s1x1_31.
try rename h_sll_nxtx11s1x1_1x1 into h_sll_nxtx11_1x1.
try rename H_sll_nxtx11s1x1_1x1 into H_sll_nxtx11_1x1.
try rename h_dll_i11s1x1_31 into h_dll_i11_31.
try rename H_dll_i11s1x1_31 into H_dll_i11_31.
try rename h_dll_ivx11s1x1_3 into h_dll_ivx11_3.
try rename H_dll_ivx11s1x1_3 into H_dll_ivx11_3.
try rename h_sll_x1vx11s1x1_2 into h_sll_x1vx11_2.
try rename H_sll_x1vx11s1x1_2 into H_sll_x1vx11_2.
try rename h_dll_wiis11i_0i into h_dll_wii_0i.
try rename H_dll_wiis11i_0i into H_dll_wii_0i.
try rename h_dll_wii_0i into h_dll_i_0i.
try rename H_dll_wii_0i into H_dll_i_0i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx11_3 into h_dll_i2vx11_3.
try rename H_dll_ivx11_3 into H_dll_i2vx11_3.
try rename h_dll_i_0i into h_dll_i2_0i.
try rename H_dll_i_0i into H_dll_i2_0i.
ssl_dealloc x1.
ssl_dealloc (x1 .+ 1).
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
exists (i2 :-> (vx11) \+ i2 .+ 1 :-> (null) \+ i2 .+ 2 :-> (null));
sslauto.
ssl_close 2;
exists (vx11), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vi11 s1i11 wi11.
ex_elim h_dll_wi11i11s1i11_0i11.
move=>[phi_dll_i11s1x1_310].
move=>[sigma_dll_i11s1x1_31].
subst h_dll_i11s1x1_31.
move=>H_dll_wi11i11s1i11_0i11.
try rename h_sll_nxtx11s1x1_1x1 into h_sll_nxtx11vi11s1i11_1x1.
try rename H_sll_nxtx11s1x1_1x1 into H_sll_nxtx11vi11s1i11_1x1.
try rename h_dll_i11s1x1_31 into h_dll_i11vi11s1i11_31.
try rename H_dll_i11s1x1_31 into H_dll_i11vi11s1i11_31.
try rename h_dll_ivx11s1x1_3 into h_dll_ivx11vi11s1i11_3.
try rename H_dll_ivx11s1x1_3 into H_dll_ivx11vi11s1i11_3.
try rename h_sll_x1vx11s1x1_2 into h_sll_x1vx11vi11s1i11_2.
try rename H_sll_x1vx11s1x1_2 into H_sll_x1vx11vi11s1i11_2.
ssl_read i11.
try rename vi11 into vi111.
try rename h_dll_i11vi11s1i11_31 into h_dll_i11vi111s1i11_31.
try rename H_dll_i11vi11s1i11_31 into H_dll_i11vi111s1i11_31.
try rename h_dll_ivx11vi11s1i11_3 into h_dll_ivx11vi111s1i11_3.
try rename H_dll_ivx11vi11s1i11_3 into H_dll_ivx11vi111s1i11_3.
try rename h_sll_nxtx11vi11s1i11_1x1 into h_sll_nxtx11vi111s1i11_1x1.
try rename H_sll_nxtx11vi11s1i11_1x1 into H_sll_nxtx11vi111s1i11_1x1.
try rename h_sll_x1vx11vi11s1i11_2 into h_sll_x1vx11vi111s1i11_2.
try rename H_sll_x1vx11vi11s1i11_2 into H_sll_x1vx11vi111s1i11_2.
ssl_read (i11 .+ 1).
try rename wi11 into wi111.
try rename h_dll_wi11i11s1i11_0i11 into h_dll_wi111i11s1i11_0i11.
try rename H_dll_wi11i11s1i11_0i11 into H_dll_wi111i11s1i11_0i11.
try rename h_dll_wiis11i_0i into h_dll_wiivwis11wi_0i.
try rename H_dll_wiis11i_0i into H_dll_wiivwis11wi_0i.
try rename h_dll_wwiwis11wi_0wi into h_dll_wi111i11s1i11_0i11.
try rename H_dll_wwiwis11wi_0wi into H_dll_wi111i11s1i11_0i11.
try rename h_dll_wiivwis11wi_0i into h_dll_i11ivwis11wi_0i.
try rename H_dll_wiivwis11wi_0i into H_dll_i11ivwis11wi_0i.
try rename h_dll_i11ivwis11wi_0i into h_dll_i11ivwis1i11_0i.
try rename H_dll_i11ivwis11wi_0i into H_dll_i11ivwis1i11_0i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx11vi111s1i11_3 into h_dll_i2vx11vi111s1i11_3.
try rename H_dll_ivx11vi111s1i11_3 into H_dll_i2vx11vi111s1i11_3.
try rename h_dll_i11ivwis1i11_0i into h_dll_i11i2vwis1i11_0i.
try rename H_dll_i11ivwis1i11_0i into H_dll_i11i2vwis1i11_0i.
ssl_dealloc x1.
ssl_dealloc (x1 .+ 1).
ssl_write (i11 .+ 2).
ssl_write_post (i11 .+ 2).
ssl_write f.
ssl_write_post f.
ssl_write (i2 .+ 1).
ssl_write_post (i2 .+ 1).
ssl_write (i2 .+ 2).
ssl_write_post (i2 .+ 2).
ssl_write i2.
ssl_write_post i2.
try rename h_dll_i11i2vwis1i11_0i into h_dll_i11i2vx11s1i11_0i.
try rename H_dll_i11i2vwis1i11_0i into H_dll_i11i2vx11s1i11_0i.
ssl_write i11.
ssl_write_post i11.
ssl_emp;
exists (i2);
exists (i2 :-> (vi111) \+ i2 .+ 1 :-> (i11) \+ i2 .+ 2 :-> (null) \+ i11 :-> (vx11) \+ i11 .+ 1 :-> (wi111) \+ i11 .+ 2 :-> (i2) \+ h_dll_wi111i11s1i11_0i11);
sslauto.
ssl_close 2;
exists (vi111), (([:: vx11]) ++ (s1i11)), (i11), (i11 :-> (vx11) \+ i11 .+ 1 :-> (wi111) \+ i11 .+ 2 :-> (i2) \+ h_dll_wi111i11s1i11_0i11);
sslauto.
ssl_close 2;
exists (vx11), (s1i11), (wi111), (h_dll_wi111i11s1i11_0i11);
sslauto.
ssl_frame_unfold.
Qed.
