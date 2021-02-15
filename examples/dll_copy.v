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
  exists h_dll_wxs1_513,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_513 /\ dll w x s1 h_dll_wxs1_513.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_514,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_514 /\ sll nxt s1 h_sll_nxts1_514.

Lemma dll_perm_eq_trans1 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans1: ssl_pred.
Lemma sll_perm_eq_trans2 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans2: ssl_pred.
Lemma pure3 : @perm_eq nat_eqType (nil) (nil). Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 vx22 : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). Admitted.
Hint Resolve pure4: ssl_pure.
Lemma pure5 vx22 : @perm_eq nat_eqType ([:: vx22]) ([:: vx22]). Admitted.
Hint Resolve pure5: ssl_pure.
Lemma pure6 vx22 vy122 s1y12 : @perm_eq nat_eqType ([:: vx22] ++ [:: vy122] ++ s1y12) ([:: vx22] ++ [:: vy122] ++ s1y12). Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 vx22 vy122 s1y12 : @perm_eq nat_eqType ([:: vx22] ++ [:: vy122] ++ s1y12) ([:: vy122] ++ [:: vx22] ++ s1y12). Admitted.
Hint Resolve pure7: ssl_pure.

Definition dll_copy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, a, s) := vghosts in
      exists h_dll_xas_515,
      h = r :-> x \+ h_dll_xas_515 /\ dll x a s h_dll_xas_515,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, a, s) := vghosts in
      exists y b,
      exists h_dll_xas_516 h_dll_ybs_517,
      h = r :-> y \+ h_dll_xas_516 \+ h_dll_ybs_517 /\ dll x a s h_dll_xas_516 /\ dll y b s h_dll_ybs_517
    ]).

Program Definition dll_copy : dll_copy_type :=
  Fix (fun (dll_copy : dll_copy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        wx22 <-- @read ptr (x2 .+ 1);
        a2 <-- @read ptr (x2 .+ 2);
        r ::= wx22;;
        dll_copy (r);;
        y12 <-- @read ptr r;
        if y12 == null
        then
          y2 <-- allocb null 3;
          r ::= y2;;
          (y2 .+ 1) ::= null;;
          y2 ::= vx22;;
          (y2 .+ 2) ::= null;;
          ret tt
        else
          vy122 <-- @read nat y12;
          wy122 <-- @read ptr (y12 .+ 1);
          b12 <-- @read ptr (y12 .+ 2);
          y2 <-- allocb null 3;
          (y12 .+ 2) ::= y2;;
          r ::= y2;;
          (y2 .+ 1) ::= y12;;
          y12 ::= vx22;;
          y2 ::= vy122;;
          (y2 .+ 2) ::= null;;
          ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[x a] s].
ex_elim h_dll_xas_515.
move=>[sigma_self].
subst h_self.
move=>H_dll_xas_515.
ssl_ghostelim_post.
ssl_read r.
try rename x into x2.
try rename h_dll_xas_515 into h_dll_x2as_515.
try rename H_dll_xas_515 into H_dll_x2as_515.
try rename h_dll_xas_516 into h_dll_x2as_516.
try rename H_dll_xas_516 into H_dll_x2as_516.
ssl_open (x2 == null) H_dll_x2as_515.
move=>[phi_dll_x2as_5150].
move=>[sigma_dll_x2as_515].
subst h_dll_x2as_515.
shelve.
ex_elim vx2 s1x2 wx2.
ex_elim h_dll_wx2x2s1x2_513x2.
move=>[phi_dll_x2as_5150].
move=>[sigma_dll_x2as_515].
subst h_dll_x2as_515.
move=>H_dll_wx2x2s1x2_513x2.
shelve.
Unshelve.
try rename h_dll_x2as_515 into h_dll_x2a_515.
try rename H_dll_x2as_515 into H_dll_x2a_515.
try rename h_dll_ybs_517 into h_dll_yb_517.
try rename H_dll_ybs_517 into H_dll_yb_517.
try rename h_dll_x2as_516 into h_dll_x2a_516.
try rename H_dll_x2as_516 into H_dll_x2a_516.
try rename h_dll_yb_517 into h_dll_b_517.
try rename H_dll_yb_517 into H_dll_b_517.
ssl_emp;
exists (null), (null);
exists (empty);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
unfold_constructor 1;
sslauto.
try rename h_dll_x2as_515 into h_dll_x2avx2s1x2_515.
try rename H_dll_x2as_515 into H_dll_x2avx2s1x2_515.
try rename h_dll_ybs_517 into h_dll_ybvx2s1x2_517.
try rename H_dll_ybs_517 into H_dll_ybvx2s1x2_517.
try rename h_dll_x2as_516 into h_dll_x2avx2s1x2_516.
try rename H_dll_x2as_516 into H_dll_x2avx2s1x2_516.
ssl_read x2.
try rename vx2 into vx22.
try rename h_dll_x2avx2s1x2_516 into h_dll_x2avx22s1x2_516.
try rename H_dll_x2avx2s1x2_516 into H_dll_x2avx22s1x2_516.
try rename h_dll_x2avx2s1x2_515 into h_dll_x2avx22s1x2_515.
try rename H_dll_x2avx2s1x2_515 into H_dll_x2avx22s1x2_515.
try rename h_dll_ybvx2s1x2_517 into h_dll_ybvx22s1x2_517.
try rename H_dll_ybvx2s1x2_517 into H_dll_ybvx22s1x2_517.
ssl_read (x2 .+ 1).
try rename wx2 into wx22.
try rename h_dll_wx2x2s1x2_513x2 into h_dll_wx22x2s1x2_513x2.
try rename H_dll_wx2x2s1x2_513x2 into H_dll_wx22x2s1x2_513x2.
ssl_read (x2 .+ 2).
try rename a into a2.
try rename h_dll_x2avx22s1x2_515 into h_dll_x2a2vx22s1x2_515.
try rename H_dll_x2avx22s1x2_515 into H_dll_x2a2vx22s1x2_515.
try rename h_dll_x2avx22s1x2_516 into h_dll_x2a2vx22s1x2_516.
try rename H_dll_x2avx22s1x2_516 into H_dll_x2a2vx22s1x2_516.
ssl_write r.
ssl_call_pre (r :-> wx22 \+ h_dll_wx22x2s1x2_513x2).
ssl_call (wx22, x2, s1x2).
exists (h_dll_wx22x2s1x2_513x2);
sslauto.
move=>h_call0.
ex_elim y1 b1.
ex_elim h_dll_wx22x2s1x2_5161 h_dll_y1b1s1x2_5171.
move=>[sigma_call0].
subst h_call0.
move=>[H_dll_wx22x2s1x2_5161 H_dll_y1b1s1x2_5171].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_dll_y1b1s1x2_5171 into h_dll_y12b1s1x2_5171.
try rename H_dll_y1b1s1x2_5171 into H_dll_y12b1s1x2_5171.
ssl_open (y12 == null) H_dll_y12b1s1x2_5171.
move=>[phi_dll_y12b1s1x2_51710].
move=>[sigma_dll_y12b1s1x2_5171].
subst h_dll_y12b1s1x2_5171.
shelve.
ex_elim vy12 s1y12 wy12.
ex_elim h_dll_wy12y12s1y12_513y12.
move=>[phi_dll_y12b1s1x2_51710].
move=>[sigma_dll_y12b1s1x2_5171].
subst h_dll_y12b1s1x2_5171.
move=>H_dll_wy12y12s1y12_513y12.
shelve.
Unshelve.
try rename h_dll_y12b1s1x2_5171 into h_dll_y12b1_5171.
try rename H_dll_y12b1s1x2_5171 into H_dll_y12b1_5171.
try rename h_dll_x2a2vx22s1x2_515 into h_dll_x2a2vx22_515.
try rename H_dll_x2a2vx22s1x2_515 into H_dll_x2a2vx22_515.
try rename h_dll_wx22x2s1x2_513x2 into h_dll_wx22x2_513x2.
try rename H_dll_wx22x2s1x2_513x2 into H_dll_wx22x2_513x2.
try rename h_dll_ybvx22s1x2_517 into h_dll_ybvx22_517.
try rename H_dll_ybvx22s1x2_517 into H_dll_ybvx22_517.
try rename h_dll_x2a2vx22s1x2_516 into h_dll_x2a2vx22_516.
try rename H_dll_x2a2vx22s1x2_516 into H_dll_x2a2vx22_516.
try rename h_dll_wx22x2s1x2_5161 into h_dll_wx22x2_5161.
try rename H_dll_wx22x2s1x2_5161 into H_dll_wx22x2_5161.
try rename h_dll_wyys11y_513y into h_dll_wyy_513y.
try rename H_dll_wyys11y_513y into H_dll_wyy_513y.
try rename h_dll_wyy_513y into h_dll_y_513y.
try rename H_dll_wyy_513y into H_dll_y_513y.
try rename h_dll_wx21x2s11x2_513x21 into h_dll_wx21x2s11x2_5161.
try rename H_dll_wx21x2s11x2_513x21 into H_dll_wx21x2s11x2_5161.
try rename h_dll_wx21x2s11x2_5161 into h_dll_wx21x2_5161.
try rename H_dll_wx21x2s11x2_5161 into H_dll_wx21x2_5161.
try rename h_dll_wx21x2_5161 into h_dll_wx22x2_5161.
try rename H_dll_wx21x2_5161 into H_dll_wx22x2_5161.
ssl_alloc y2.
try rename y into y2.
try rename h_dll_y_513y into h_dll_y2_513y.
try rename H_dll_y_513y into H_dll_y2_513y.
try rename h_dll_ybvx22_517 into h_dll_y2bvx22_517.
try rename H_dll_ybvx22_517 into H_dll_y2bvx22_517.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
try rename h_dll_y2bvx22_517 into h_dll_y2vx22_517.
try rename H_dll_y2bvx22_517 into H_dll_y2vx22_517.
ssl_write y2.
ssl_write_post y2.
ssl_write (y2 .+ 2).
ssl_write_post (y2 .+ 2).
ssl_emp;
exists (y2), (null);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> wx22 \+ x2 .+ 2 :-> a2 \+ h_dll_wx22x2_5161);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> null \+ y2 .+ 2 :-> null);
sslauto.
unfold_constructor 2;
exists (vx22), (nil), (wx22), (h_dll_wx22x2_5161);
sslauto.
unfold_constructor 2;
exists (vx22), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_dll_y12b1s1x2_5171 into h_dll_y12b1vy12s1y12_5171.
try rename H_dll_y12b1s1x2_5171 into H_dll_y12b1vy12s1y12_5171.
try rename h_dll_x2a2vx22s1x2_515 into h_dll_x2a2vx22vy12s1y12_515.
try rename H_dll_x2a2vx22s1x2_515 into H_dll_x2a2vx22vy12s1y12_515.
try rename h_dll_wx22x2s1x2_513x2 into h_dll_wx22x2vy12s1y12_513x2.
try rename H_dll_wx22x2s1x2_513x2 into H_dll_wx22x2vy12s1y12_513x2.
try rename h_dll_ybvx22s1x2_517 into h_dll_ybvx22vy12s1y12_517.
try rename H_dll_ybvx22s1x2_517 into H_dll_ybvx22vy12s1y12_517.
try rename h_dll_x2a2vx22s1x2_516 into h_dll_x2a2vx22vy12s1y12_516.
try rename H_dll_x2a2vx22s1x2_516 into H_dll_x2a2vx22vy12s1y12_516.
try rename h_dll_wx22x2s1x2_5161 into h_dll_wx22x2vy12s1y12_5161.
try rename H_dll_wx22x2s1x2_5161 into H_dll_wx22x2vy12s1y12_5161.
ssl_read y12.
try rename vy12 into vy122.
try rename h_dll_x2a2vx22vy12s1y12_515 into h_dll_x2a2vx22vy122s1y12_515.
try rename H_dll_x2a2vx22vy12s1y12_515 into H_dll_x2a2vx22vy122s1y12_515.
try rename h_dll_x2a2vx22vy12s1y12_516 into h_dll_x2a2vx22vy122s1y12_516.
try rename H_dll_x2a2vx22vy12s1y12_516 into H_dll_x2a2vx22vy122s1y12_516.
try rename h_dll_wx22x2vy12s1y12_513x2 into h_dll_wx22x2vy122s1y12_513x2.
try rename H_dll_wx22x2vy12s1y12_513x2 into H_dll_wx22x2vy122s1y12_513x2.
try rename h_dll_ybvx22vy12s1y12_517 into h_dll_ybvx22vy122s1y12_517.
try rename H_dll_ybvx22vy12s1y12_517 into H_dll_ybvx22vy122s1y12_517.
try rename h_dll_y12b1vy12s1y12_5171 into h_dll_y12b1vy122s1y12_5171.
try rename H_dll_y12b1vy12s1y12_5171 into H_dll_y12b1vy122s1y12_5171.
try rename h_dll_wx22x2vy12s1y12_5161 into h_dll_wx22x2vy122s1y12_5161.
try rename H_dll_wx22x2vy12s1y12_5161 into H_dll_wx22x2vy122s1y12_5161.
ssl_read (y12 .+ 1).
try rename wy12 into wy122.
try rename h_dll_wy12y12s1y12_513y12 into h_dll_wy122y12s1y12_513y12.
try rename H_dll_wy12y12s1y12_513y12 into H_dll_wy122y12s1y12_513y12.
ssl_read (y12 .+ 2).
try rename b1 into b12.
try rename h_dll_y12b1vy122s1y12_5171 into h_dll_y12b12vy122s1y12_5171.
try rename H_dll_y12b1vy122s1y12_5171 into H_dll_y12b12vy122s1y12_5171.
try rename h_dll_wyys11y_513y into h_dll_wyyvwys11wy_513y.
try rename H_dll_wyys11y_513y into H_dll_wyyvwys11wy_513y.
try rename h_dll_wx21x2s11x2_513x21 into h_dll_wx21x2s11x2_5161.
try rename H_dll_wx21x2s11x2_513x21 into H_dll_wx21x2s11x2_5161.
try rename h_dll_wx21x2s11x2_5161 into h_dll_wx21x2vy122s1y12_5161.
try rename H_dll_wx21x2s11x2_5161 into H_dll_wx21x2vy122s1y12_5161.
try rename h_dll_wx21x2vy122s1y12_5161 into h_dll_wx22x2vy122s1y12_5161.
try rename H_dll_wx21x2vy122s1y12_5161 into H_dll_wx22x2vy122s1y12_5161.
try rename h_dll_wwywys11wy_513wy into h_dll_wwywys11wy_513y12.
try rename H_dll_wwywys11wy_513wy into H_dll_wwywys11wy_513y12.
try rename h_dll_wwywys11wy_513y12 into h_dll_wwywys1y12_513y12.
try rename H_dll_wwywys11wy_513y12 into H_dll_wwywys1y12_513y12.
try rename h_dll_wyyvwys11wy_513y into h_dll_wyyvwys1y12_513y.
try rename H_dll_wyyvwys11wy_513y into H_dll_wyyvwys1y12_513y.
try rename h_dll_wwywys1y12_513y12 into h_dll_wy122wys1y12_513y12.
try rename H_dll_wwywys1y12_513y12 into H_dll_wy122wys1y12_513y12.
try rename h_dll_wy122wys1y12_513y12 into h_dll_wy122y12s1y12_513y12.
try rename H_dll_wy122wys1y12_513y12 into H_dll_wy122y12s1y12_513y12.
try rename h_dll_wyyvwys1y12_513y into h_dll_y12yvwys1y12_513y.
try rename H_dll_wyyvwys1y12_513y into H_dll_y12yvwys1y12_513y.
ssl_alloc y2.
try rename y into y2.
try rename h_dll_y12yvwys1y12_513y into h_dll_y12y2vwys1y12_513y.
try rename H_dll_y12yvwys1y12_513y into H_dll_y12y2vwys1y12_513y.
try rename h_dll_ybvx22vy122s1y12_517 into h_dll_y2bvx22vy122s1y12_517.
try rename H_dll_ybvx22vy122s1y12_517 into H_dll_y2bvx22vy122s1y12_517.
ssl_write (y12 .+ 2).
ssl_write_post (y12 .+ 2).
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
try rename h_dll_y2bvx22vy122s1y12_517 into h_dll_y2vx22vy122s1y12_517.
try rename H_dll_y2bvx22vy122s1y12_517 into H_dll_y2vx22vy122s1y12_517.
try rename h_dll_y12y2vwys1y12_513y into h_dll_y12y2vx22s1y12_513y.
try rename H_dll_y12y2vwys1y12_513y into H_dll_y12y2vx22s1y12_513y.
ssl_write y12.
ssl_write_post y12.
ssl_write y2.
ssl_write_post y2.
ssl_write (y2 .+ 2).
ssl_write_post (y2 .+ 2).
ssl_emp;
exists (y2), (null);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> wx22 \+ x2 .+ 2 :-> a2 \+ h_dll_wx22x2vy122s1y12_5161);
exists (y2 :-> vy122 \+ y2 .+ 1 :-> y12 \+ y2 .+ 2 :-> null \+ y12 :-> vx22 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> y2 \+ h_dll_wy122y12s1y12_513y12);
sslauto.
unfold_constructor 2;
exists (vx22), ([:: vy122] ++ s1y12), (wx22), (h_dll_wx22x2vy122s1y12_5161);
sslauto.
unfold_constructor 2;
exists (vy122), ([:: vx22] ++ s1y12), (y12), (y12 :-> vx22 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> y2 \+ h_dll_wy122y12s1y12_513y12);
sslauto.
unfold_constructor 2;
exists (vx22), (s1y12), (wy122), (h_dll_wy122y12s1y12_513y12);
sslauto.
Qed.
