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

Lemma pure6 : @perm_eq nat_eqType (@nil nat) (@nil nat). intros; hammer. Qed.
Hint Resolve pure6: ssl_pure.
Lemma pure7 (vx22 : nat) : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). intros; hammer. Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 (vx22 : nat) (vi122 : nat) (s1i12 : seq nat) : @perm_eq nat_eqType (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))) (([:: vx22]) ++ (([:: vi122]) ++ (s1i12))). intros; hammer. Qed.
Hint Resolve pure8: ssl_pure.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_518,
      h = f :-> x \+ h_sll_xs_518 /\ sll x s h_sll_xs_518,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_519,
      h = f :-> i \+ h_dll_is_519 /\ dll i null s h_dll_is_519
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
ex_elim h_sll_xs_518.
move=>[sigma_self].
subst h_self.
move=>H_sll_xs_518.
ssl_ghostelim_post.
ssl_read f.
try rename x into x2.
try rename h_sll_xs_518 into h_sll_x2s_518.
try rename H_sll_xs_518 into H_sll_x2s_518.
ssl_open ((x2) == (null)) H_sll_x2s_518.
move=>[phi_sll_x2s_5180].
move=>[sigma_sll_x2s_518].
subst h_sll_x2s_518.
try rename h_dll_is_519 into h_dll_i_519.
try rename H_dll_is_519 into H_dll_i_519.
try rename h_sll_x2s_518 into h_sll_x2_518.
try rename H_sll_x2s_518 into H_sll_x2_518.
try rename h_dll_i_519 into h_dll__519.
try rename H_dll_i_519 into H_dll__519.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vx2 s1x2 nxtx2.
ex_elim h_sll_nxtx2s1x2_517x2.
move=>[phi_sll_x2s_5180].
move=>[sigma_sll_x2s_518].
subst h_sll_x2s_518.
move=>H_sll_nxtx2s1x2_517x2.
try rename h_dll_is_519 into h_dll_ivx2s1x2_519.
try rename H_dll_is_519 into H_dll_ivx2s1x2_519.
try rename h_sll_x2s_518 into h_sll_x2vx2s1x2_518.
try rename H_sll_x2s_518 into H_sll_x2vx2s1x2_518.
ssl_read x2.
try rename vx2 into vx22.
try rename h_dll_ivx2s1x2_519 into h_dll_ivx22s1x2_519.
try rename H_dll_ivx2s1x2_519 into H_dll_ivx22s1x2_519.
try rename h_sll_x2vx2s1x2_518 into h_sll_x2vx22s1x2_518.
try rename H_sll_x2vx2s1x2_518 into H_sll_x2vx22s1x2_518.
ssl_read (x2 .+ 1).
try rename nxtx2 into nxtx22.
try rename h_sll_nxtx2s1x2_517x2 into h_sll_nxtx22s1x2_517x2.
try rename H_sll_nxtx2s1x2_517x2 into H_sll_nxtx22s1x2_517x2.
try rename h_sll_x1s1_5181 into h_sll_nxtx22s1x2_517x2.
try rename H_sll_x1s1_5181 into H_sll_nxtx22s1x2_517x2.
ssl_write f.
ssl_call_pre (f :-> nxtx22 \+ h_sll_nxtx22s1x2_517x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_517x2);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim i1.
ex_elim h_dll_i1s1x2_5191.
move=>[sigma_call0].
subst h_call0.
move=>H_dll_i1s1x2_5191.
store_valid.
ssl_read f.
try rename i1 into i12.
try rename h_dll_i1s1x2_5191 into h_dll_i12s1x2_5191.
try rename H_dll_i1s1x2_5191 into H_dll_i12s1x2_5191.
ssl_open ((i12) == (null)) H_dll_i12s1x2_5191.
move=>[phi_dll_i12s1x2_51910].
move=>[sigma_dll_i12s1x2_5191].
subst h_dll_i12s1x2_5191.
try rename h_sll_x2vx22s1x2_518 into h_sll_x2vx22_518.
try rename H_sll_x2vx22s1x2_518 into H_sll_x2vx22_518.
try rename h_dll_i12s1x2_5191 into h_dll_i12_5191.
try rename H_dll_i12s1x2_5191 into H_dll_i12_5191.
try rename h_sll_nxtx22s1x2_517x2 into h_sll_nxtx22_517x2.
try rename H_sll_nxtx22s1x2_517x2 into H_sll_nxtx22_517x2.
try rename h_dll_ivx22s1x2_519 into h_dll_ivx22_519.
try rename H_dll_ivx22s1x2_519 into H_dll_ivx22_519.
try rename h_dll_wiis11i_516i into h_dll_wii_516i.
try rename H_dll_wiis11i_516i into H_dll_wii_516i.
try rename h_dll_wii_516i into h_dll_i_516i.
try rename H_dll_wii_516i into H_dll_i_516i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_ivx22_519 into h_dll_i2vx22_519.
try rename H_dll_ivx22_519 into H_dll_i2vx22_519.
try rename h_dll_i_516i into h_dll_i2_516i.
try rename H_dll_i_516i into H_dll_i2_516i.
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
exists (vx22), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vi12 s1i12 wi12.
ex_elim h_dll_wi12i12s1i12_516i12.
move=>[phi_dll_i12s1x2_51910].
move=>[sigma_dll_i12s1x2_5191].
subst h_dll_i12s1x2_5191.
move=>H_dll_wi12i12s1i12_516i12.
try rename h_sll_x2vx22s1x2_518 into h_sll_x2vx22vi12s1i12_518.
try rename H_sll_x2vx22s1x2_518 into H_sll_x2vx22vi12s1i12_518.
try rename h_dll_i12s1x2_5191 into h_dll_i12vi12s1i12_5191.
try rename H_dll_i12s1x2_5191 into H_dll_i12vi12s1i12_5191.
try rename h_sll_nxtx22s1x2_517x2 into h_sll_nxtx22vi12s1i12_517x2.
try rename H_sll_nxtx22s1x2_517x2 into H_sll_nxtx22vi12s1i12_517x2.
try rename h_dll_ivx22s1x2_519 into h_dll_ivx22vi12s1i12_519.
try rename H_dll_ivx22s1x2_519 into H_dll_ivx22vi12s1i12_519.
ssl_read i12.
try rename vi12 into vi122.
try rename h_dll_ivx22vi12s1i12_519 into h_dll_ivx22vi122s1i12_519.
try rename H_dll_ivx22vi12s1i12_519 into H_dll_ivx22vi122s1i12_519.
try rename h_sll_x2vx22vi12s1i12_518 into h_sll_x2vx22vi122s1i12_518.
try rename H_sll_x2vx22vi12s1i12_518 into H_sll_x2vx22vi122s1i12_518.
try rename h_sll_nxtx22vi12s1i12_517x2 into h_sll_nxtx22vi122s1i12_517x2.
try rename H_sll_nxtx22vi12s1i12_517x2 into H_sll_nxtx22vi122s1i12_517x2.
try rename h_dll_i12vi12s1i12_5191 into h_dll_i12vi122s1i12_5191.
try rename H_dll_i12vi12s1i12_5191 into H_dll_i12vi122s1i12_5191.
ssl_read (i12 .+ 1).
try rename wi12 into wi122.
try rename h_dll_wi12i12s1i12_516i12 into h_dll_wi122i12s1i12_516i12.
try rename H_dll_wi12i12s1i12_516i12 into H_dll_wi122i12s1i12_516i12.
try rename h_dll_wiis11i_516i into h_dll_wiivwis11wi_516i.
try rename H_dll_wiis11i_516i into H_dll_wiivwis11wi_516i.
try rename h_dll_wwiwis11wi_516wi into h_dll_wi122i12s1i12_516i12.
try rename H_dll_wwiwis11wi_516wi into H_dll_wi122i12s1i12_516i12.
try rename h_dll_wiivwis11wi_516i into h_dll_i12ivwis11wi_516i.
try rename H_dll_wiivwis11wi_516i into H_dll_i12ivwis11wi_516i.
try rename h_dll_i12ivwis11wi_516i into h_dll_i12ivwis1i12_516i.
try rename H_dll_i12ivwis11wi_516i into H_dll_i12ivwis1i12_516i.
ssl_alloc i2.
try rename i into i2.
try rename h_dll_i12ivwis1i12_516i into h_dll_i12i2vwis1i12_516i.
try rename H_dll_i12ivwis1i12_516i into H_dll_i12i2vwis1i12_516i.
try rename h_dll_ivx22vi122s1i12_519 into h_dll_i2vx22vi122s1i12_519.
try rename H_dll_ivx22vi122s1i12_519 into H_dll_i2vx22vi122s1i12_519.
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
try rename h_dll_i12i2vwis1i12_516i into h_dll_i12i2vi122s1i12_516i.
try rename H_dll_i12i2vwis1i12_516i into H_dll_i12i2vi122s1i12_516i.
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> i12 \+ i2 .+ 2 :-> null \+ i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_516i12);
sslauto.
ssl_close 2;
exists (vx22), (([:: vi122]) ++ (s1i12)), (i12), (i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_516i12);
sslauto.
ssl_close 2;
exists (vi122), (s1i12), (wi122), (h_dll_wi122i12s1i12_516i12);
sslauto.
ssl_frame_unfold.
Qed.