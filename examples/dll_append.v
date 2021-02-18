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
  exists h_dll_wxs1_597,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_597 /\ dll w x s1 h_dll_wxs1_597.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_598,
  @perm_eq nat_eqType (s) (([:: v]) ++ (s1)) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_598 /\ sll nxt s1 h_sll_nxts1_598.

Lemma dll_perm_eq_trans82 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans82: ssl_pred.
Lemma sll_perm_eq_trans83 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans83: ssl_pred.
Lemma pure84 vx12 s1x1 s2 : @perm_eq nat_eqType ((s1x1) ++ (s2)) (nil) -> @perm_eq nat_eqType ((([:: vx12]) ++ (s1x1)) ++ (s2)) ([:: vx12]). Admitted.
Hint Resolve pure84: ssl_pure.
Lemma pure85 s2 s1x1 s1y12 vy122 vx12 : @perm_eq nat_eqType ((s1x1) ++ (s2)) (([:: vy122]) ++ (s1y12)) -> @perm_eq nat_eqType ((([:: vx12]) ++ (s1x1)) ++ (s2)) (([:: vx12]) ++ (([:: vy122]) ++ (s1y12))). Admitted.
Hint Resolve pure85: ssl_pure.

Definition dll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : ptr * seq nat * ptr * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists h_dll_x1as1_599 h_dll_x2bs2_600,
      h = r :-> x2 \+ h_dll_x1as1_599 \+ h_dll_x2bs2_600 /\ dll x1 a s1 h_dll_x1as1_599 /\ dll x2 b s2 h_dll_x2bs2_600,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists s y c,
      exists h_dll_ycs_601,
      @perm_eq nat_eqType (s) ((s1) ++ (s2)) /\ h = r :-> y \+ h_dll_ycs_601 /\ dll y c s h_dll_ycs_601
    ]).

Program Definition dll_append : dll_append_type :=
  Fix (fun (dll_append : dll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x22 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx12 <-- @read nat x1;
        wx12 <-- @read ptr (x1 .+ 1);
        a2 <-- @read ptr (x1 .+ 2);
        dll_append (wx12, r);;
        y12 <-- @read ptr r;
        if (y12) == (null)
        then
          (x1 .+ 1) ::= null;;
          r ::= x1;;
          ret tt
        else
          vy122 <-- @read nat y12;
          wy122 <-- @read ptr (y12 .+ 1);
          c12 <-- @read ptr (y12 .+ 2);
          (y12 .+ 2) ::= x1;;
          (x1 .+ 1) ::= y12;;
          r ::= x1;;
          ret tt
    )).
Obligation Tactic := intro; move=>[x1 r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[a s1] x2] b] s2].
ex_elim h_dll_x1as1_599 h_dll_x2bs2_600.
move=>[sigma_self].
subst h_self.
move=>[H_dll_x1as1_599 H_dll_x2bs2_600].
ssl_ghostelim_post.
try rename h_dll_ycs_601 into h_dll_ycs1s2_601.
try rename H_dll_ycs_601 into H_dll_ycs1s2_601.
ssl_read r.
try rename x2 into x22.
try rename h_dll_x2bs2_600 into h_dll_x22bs2_600.
try rename H_dll_x2bs2_600 into H_dll_x22bs2_600.
ssl_open ((x1) == (null)) H_dll_x1as1_599.
move=>[phi_dll_x1as1_5990].
move=>[sigma_dll_x1as1_599].
subst h_dll_x1as1_599.
try rename h_dll_ycs1s2_601 into h_dll_ycs2_601.
try rename H_dll_ycs1s2_601 into H_dll_ycs2_601.
try rename h_dll_x1as1_599 into h_dll_x1a_599.
try rename H_dll_x1as1_599 into H_dll_x1a_599.
try rename h_dll_ycs2_601 into h_dll_x22bs2_600.
try rename H_dll_ycs2_601 into H_dll_x22bs2_600.
ssl_emp;
exists (s2), (x22), (b);
exists (h_dll_x22bs2_600);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 wx1.
ex_elim h_dll_wx1x1s1x1_597x1.
move=>[phi_dll_x1as1_5990].
move=>[sigma_dll_x1as1_599].
subst h_dll_x1as1_599.
move=>H_dll_wx1x1s1x1_597x1.
try rename h_dll_ycs1s2_601 into h_dll_ycvx1s1x1s2_601.
try rename H_dll_ycs1s2_601 into H_dll_ycvx1s1x1s2_601.
try rename h_dll_x1as1_599 into h_dll_x1avx1s1x1_599.
try rename H_dll_x1as1_599 into H_dll_x1avx1s1x1_599.
ssl_read x1.
try rename vx1 into vx12.
try rename h_dll_ycvx1s1x1s2_601 into h_dll_ycvx12s1x1s2_601.
try rename H_dll_ycvx1s1x1s2_601 into H_dll_ycvx12s1x1s2_601.
try rename h_dll_x1avx1s1x1_599 into h_dll_x1avx12s1x1_599.
try rename H_dll_x1avx1s1x1_599 into H_dll_x1avx12s1x1_599.
ssl_read (x1 .+ 1).
try rename wx1 into wx12.
try rename h_dll_wx1x1s1x1_597x1 into h_dll_wx12x1s1x1_597x1.
try rename H_dll_wx1x1s1x1_597x1 into H_dll_wx12x1s1x1_597x1.
ssl_read (x1 .+ 2).
try rename a into a2.
try rename h_dll_x1avx12s1x1_599 into h_dll_x1a2vx12s1x1_599.
try rename H_dll_x1avx12s1x1_599 into H_dll_x1a2vx12s1x1_599.
try rename h_dll_x11a1s11_5991 into h_dll_wx12x1s1x1_597x1.
try rename H_dll_x11a1s11_5991 into H_dll_wx12x1s1x1_597x1.
try rename h_dll_x21b1s21_6001 into h_dll_x22bs2_600.
try rename H_dll_x21b1s21_6001 into H_dll_x22bs2_600.
ssl_call_pre (r :-> x22 \+ h_dll_wx12x1s1x1_597x1 \+ h_dll_x22bs2_600).
ssl_call (x1, s1x1, x22, b, s2).
exists (h_dll_wx12x1s1x1_597x1), (h_dll_x22bs2_600);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1 c1.
ex_elim h_dll_y1c1s3_6011.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_dll_y1c1s3_6011.
store_valid.
try rename h_dll_y1c1s3_6011 into h_dll_y1c1s1x1s2_6011.
try rename H_dll_y1c1s3_6011 into H_dll_y1c1s1x1s2_6011.
ssl_read r.
try rename y1 into y12.
try rename h_dll_y1c1s1x1s2_6011 into h_dll_y12c1s1x1s2_6011.
try rename H_dll_y1c1s1x1s2_6011 into H_dll_y12c1s1x1s2_6011.
ssl_open ((y12) == (null)) H_dll_y12c1s1x1s2_6011.
move=>[phi_dll_y12c1s1x1s2_60110].
move=>[sigma_dll_y12c1s1x1s2_6011].
subst h_dll_y12c1s1x1s2_6011.
try rename h_dll_wyys12y_597y into h_dll_wyy_597y.
try rename H_dll_wyys12y_597y into H_dll_wyy_597y.
try rename h_dll_wyy_597y into h_dll_y_597y.
try rename H_dll_wyy_597y into H_dll_y_597y.
try rename h_dll_y_597y into h_dll_x1_597y.
try rename H_dll_y_597y into H_dll_x1_597y.
try rename h_dll_ycvx12s1x1s2_601 into h_dll_x1cvx12s1x1s2_601.
try rename H_dll_ycvx12s1x1s2_601 into H_dll_x1cvx12s1x1s2_601.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_601 into h_dll_x1a2vx12s1x1s2_601.
try rename H_dll_x1cvx12s1x1s2_601 into H_dll_x1a2vx12s1x1s2_601.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> null \+ x1 .+ 2 :-> a2);
sslauto.
unfold_constructor 2;
exists (vx12), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
ex_elim vy12 s1y12 wy12.
ex_elim h_dll_wy12y12s1y12_597y12.
move=>[phi_dll_y12c1s1x1s2_60110].
move=>[sigma_dll_y12c1s1x1s2_6011].
subst h_dll_y12c1s1x1s2_6011.
move=>H_dll_wy12y12s1y12_597y12.
ssl_read y12.
try rename vy12 into vy122.
ssl_read (y12 .+ 1).
try rename wy12 into wy122.
try rename h_dll_wy12y12s1y12_597y12 into h_dll_wy122y12s1y12_597y12.
try rename H_dll_wy12y12s1y12_597y12 into H_dll_wy122y12s1y12_597y12.
ssl_read (y12 .+ 2).
try rename c1 into c12.
try rename h_dll_y12c1s1x1s2_6011 into h_dll_y12c12s1x1s2_6011.
try rename H_dll_y12c1s1x1s2_6011 into H_dll_y12c12s1x1s2_6011.
try rename h_dll_wyys12y_597y into h_dll_wyyvwys12wy_597y.
try rename H_dll_wyys12y_597y into H_dll_wyyvwys12wy_597y.
try rename h_dll_wwywys12wy_597wy into h_dll_wy122y12s1y12_597y12.
try rename H_dll_wwywys12wy_597wy into H_dll_wy122y12s1y12_597y12.
try rename h_dll_wyyvwys12wy_597y into h_dll_wyyvwys1y12_597y.
try rename H_dll_wyyvwys12wy_597y into H_dll_wyyvwys1y12_597y.
try rename h_dll_wyyvwys1y12_597y into h_dll_y12yvwys1y12_597y.
try rename H_dll_wyyvwys1y12_597y into H_dll_y12yvwys1y12_597y.
try rename h_dll_ycvx12s1x1s2_601 into h_dll_x1cvx12s1x1s2_601.
try rename H_dll_ycvx12s1x1s2_601 into H_dll_x1cvx12s1x1s2_601.
try rename h_dll_y12yvwys1y12_597y into h_dll_y12x1vwys1y12_597y.
try rename H_dll_y12yvwys1y12_597y into H_dll_y12x1vwys1y12_597y.
ssl_write (y12 .+ 2).
ssl_write_post (y12 .+ 2).
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_601 into h_dll_x1a2vx12s1x1s2_601.
try rename H_dll_x1cvx12s1x1s2_601 into H_dll_x1a2vx12s1x1s2_601.
try rename h_dll_y12x1vwys1y12_597y into h_dll_y12x1vy122s1y12_597y.
try rename H_dll_y12x1vwys1y12_597y into H_dll_y12x1vy122s1y12_597y.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ x1 .+ 2 :-> a2 \+ y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_597y12);
sslauto.
unfold_constructor 2;
exists (vx12), (([:: vy122]) ++ (s1y12)), (y12), (y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_597y12);
sslauto.
unfold_constructor 2;
exists (vy122), (s1y12), (wy122), (h_dll_wy122y12s1y12_597y12);
sslauto.
ssl_frame_unfold.
Qed.