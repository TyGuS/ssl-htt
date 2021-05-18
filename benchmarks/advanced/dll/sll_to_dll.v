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
      exists h_sll_xs_536,
      h = f :-> (x) \+ h_sll_xs_536 /\ sll x s h_sll_xs_536,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_537,
      h = f :-> (i) \+ h_dll_is_537 /\ dll i null s h_dll_is_537
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
ex_elim h_sll_xs_536.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_536.
ssl_ghostelim_post.
ssl_read f.
try rename x into x2.
try rename h_sll_xs_536 into h_sll_x2s_536.
try rename H_sll_xs_536 into H_sll_x2s_536.
ssl_open ((x2) == (null)) H_sll_x2s_536.
move=>[phi_sll_x2s_5360].
move=>[sigma_sll_x2s_536].
subst h_sll_x2s_536.
try rename h_dll_is_537 into h_dll_i_537.
try rename H_dll_is_537 into H_dll_i_537.
try rename h_sll_x2s_536 into h_sll_x2_536.
try rename H_sll_x2s_536 into H_sll_x2_536.
try rename h_dll_i_537 into h_dll__537.
try rename H_dll_i_537 into H_dll__537.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx2 s1x2 nxtx2.
ex_elim h_sll_nxtx2s1x2_535x2.
move=>[phi_sll_x2s_5360].
move=>[sigma_sll_x2s_536].
subst h_sll_x2s_536.
move=>H_sll_nxtx2s1x2_535x2.
try rename h_dll_is_537 into h_dll_ivx2s1x2_537.
try rename H_dll_is_537 into H_dll_ivx2s1x2_537.
try rename h_sll_x2s_536 into h_sll_x2vx2s1x2_536.
try rename H_sll_x2s_536 into H_sll_x2vx2s1x2_536.
ssl_read x2.
try rename vx2 into vx22.
try rename h_sll_x2vx2s1x2_536 into h_sll_x2vx22s1x2_536.
try rename H_sll_x2vx2s1x2_536 into H_sll_x2vx22s1x2_536.
try rename h_dll_ivx2s1x2_537 into h_dll_ivx22s1x2_537.
try rename H_dll_ivx2s1x2_537 into H_dll_ivx22s1x2_537.
ssl_read (x2 .+ 1).
try rename nxtx2 into nxtx22.
try rename h_sll_nxtx2s1x2_535x2 into h_sll_nxtx22s1x2_535x2.
try rename H_sll_nxtx2s1x2_535x2 into H_sll_nxtx22s1x2_535x2.
try rename h_sll_x1s1_5361 into h_sll_nxtx22s1x2_535x2.
try rename H_sll_x1s1_5361 into H_sll_nxtx22s1x2_535x2.
ssl_write f.
ssl_call_pre (f :-> (nxtx22) \+ h_sll_nxtx22s1x2_535x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_535x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim i1.
ex_elim h_dll_i1s1x2_5371.
move=>[sigma_call0].
subst h_call0.
move=>H_dll_i1s1x2_5371.
store_valid.
ssl_read f.
try rename i1 into i12.
try rename h_dll_i1s1x2_5371 into h_dll_i12s1x2_5371.
try rename H_dll_i1s1x2_5371 into H_dll_i12s1x2_5371.
ssl_open ((i12) == (null)) H_dll_i12s1x2_5371.
move=>[phi_dll_i12s1x2_53710].
move=>[sigma_dll_i12s1x2_5371].
subst h_dll_i12s1x2_5371.
try rename h_sll_nxtx22s1x2_535x2 into h_sll_nxtx22_535x2.
try rename H_sll_nxtx22s1x2_535x2 into H_sll_nxtx22_535x2.
try rename h_dll_ivx22s1x2_537 into h_dll_ivx22_537.
try rename H_dll_ivx22s1x2_537 into H_dll_ivx22_537.
try rename h_dll_i12s1x2_5371 into h_dll_i12_5371.
try rename H_dll_i12s1x2_5371 into H_dll_i12_5371.
try rename h_sll_x2vx22s1x2_536 into h_sll_x2vx22_536.
try rename H_sll_x2vx22s1x2_536 into H_sll_x2vx22_536.
try rename h_dll_wiis11i_534i into h_dll_wii_534i.
try rename H_dll_wiis11i_534i into H_dll_wii_534i.
try rename h_dll_wii_534i into h_dll_i_534i.
try rename H_dll_wii_534i into H_dll_i_534i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx22_537 into h_dll_i2vx22_537.
try rename H_dll_ivx22_537 into H_dll_i2vx22_537.
try rename h_dll_i_534i into h_dll_i2_534i.
try rename H_dll_i_534i into H_dll_i2_534i.
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
exists (i2 :-> (vx22) \+ i2 .+ 1 :-> (null) \+ i2 .+ 2 :-> (null));
sslauto.
ssl_close 2;
exists (vx22), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vi12 s1i12 wi12.
ex_elim h_dll_wi12i12s1i12_534i12.
move=>[phi_dll_i12s1x2_53710].
move=>[sigma_dll_i12s1x2_5371].
subst h_dll_i12s1x2_5371.
move=>H_dll_wi12i12s1i12_534i12.
try rename h_sll_nxtx22s1x2_535x2 into h_sll_nxtx22vi12s1i12_535x2.
try rename H_sll_nxtx22s1x2_535x2 into H_sll_nxtx22vi12s1i12_535x2.
try rename h_dll_ivx22s1x2_537 into h_dll_ivx22vi12s1i12_537.
try rename H_dll_ivx22s1x2_537 into H_dll_ivx22vi12s1i12_537.
try rename h_dll_i12s1x2_5371 into h_dll_i12vi12s1i12_5371.
try rename H_dll_i12s1x2_5371 into H_dll_i12vi12s1i12_5371.
try rename h_sll_x2vx22s1x2_536 into h_sll_x2vx22vi12s1i12_536.
try rename H_sll_x2vx22s1x2_536 into H_sll_x2vx22vi12s1i12_536.
ssl_read i12.
try rename vi12 into vi122.
try rename h_sll_x2vx22vi12s1i12_536 into h_sll_x2vx22vi122s1i12_536.
try rename H_sll_x2vx22vi12s1i12_536 into H_sll_x2vx22vi122s1i12_536.
try rename h_dll_ivx22vi12s1i12_537 into h_dll_ivx22vi122s1i12_537.
try rename H_dll_ivx22vi12s1i12_537 into H_dll_ivx22vi122s1i12_537.
try rename h_dll_i12vi12s1i12_5371 into h_dll_i12vi122s1i12_5371.
try rename H_dll_i12vi12s1i12_5371 into H_dll_i12vi122s1i12_5371.
try rename h_sll_nxtx22vi12s1i12_535x2 into h_sll_nxtx22vi122s1i12_535x2.
try rename H_sll_nxtx22vi12s1i12_535x2 into H_sll_nxtx22vi122s1i12_535x2.
ssl_read (i12 .+ 1).
try rename wi12 into wi122.
try rename h_dll_wi12i12s1i12_534i12 into h_dll_wi122i12s1i12_534i12.
try rename H_dll_wi12i12s1i12_534i12 into H_dll_wi122i12s1i12_534i12.
try rename h_dll_wiis11i_534i into h_dll_wiivwis11wi_534i.
try rename H_dll_wiis11i_534i into H_dll_wiivwis11wi_534i.
try rename h_dll_wwiwis11wi_534wi into h_dll_wi122i12s1i12_534i12.
try rename H_dll_wwiwis11wi_534wi into H_dll_wi122i12s1i12_534i12.
try rename h_dll_wiivwis11wi_534i into h_dll_i12ivwis11wi_534i.
try rename H_dll_wiivwis11wi_534i into H_dll_i12ivwis11wi_534i.
try rename h_dll_i12ivwis11wi_534i into h_dll_i12ivwis1i12_534i.
try rename H_dll_i12ivwis11wi_534i into H_dll_i12ivwis1i12_534i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_i12ivwis1i12_534i into h_dll_i12i2vwis1i12_534i.
try rename H_dll_i12ivwis1i12_534i into H_dll_i12i2vwis1i12_534i.
try rename h_dll_ivx22vi122s1i12_537 into h_dll_i2vx22vi122s1i12_537.
try rename H_dll_ivx22vi122s1i12_537 into H_dll_i2vx22vi122s1i12_537.
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
try rename h_dll_i12i2vwis1i12_534i into h_dll_i12i2vi122s1i12_534i.
try rename H_dll_i12i2vwis1i12_534i into H_dll_i12i2vi122s1i12_534i.
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> (vx22) \+ i2 .+ 1 :-> (i12) \+ i2 .+ 2 :-> (null) \+ i12 :-> (vi122) \+ i12 .+ 1 :-> (wi122) \+ i12 .+ 2 :-> (i2) \+ h_dll_wi122i12s1i12_534i12);
sslauto.
ssl_close 2;
exists (vx22), (([:: vi122]) ++ (s1i12)), (i12), (i12 :-> (vi122) \+ i12 .+ 1 :-> (wi122) \+ i12 .+ 2 :-> (i2) \+ h_dll_wi122i12s1i12_534i12);
sslauto.
ssl_close 2;
exists (vi122), (s1i12), (wi122), (h_dll_wi122i12s1i12_534i12);
sslauto.
ssl_frame_unfold.
Qed.