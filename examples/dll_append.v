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
  exists h_dll_wxs1_528,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_528 /\ dll w x s1 h_dll_wxs1_528.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll_1 of x == null of
  @perm_eq nat_eqType (s) (nil) /\ h = empty
| sll_2 of (x == null) = false of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_529,
  @perm_eq nat_eqType (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_529 /\ sll nxt s1 h_sll_nxts1_529.

Lemma dll_perm_eq_trans19 x z h s_1 s_2 : perm_eq s_1 s_2 -> dll x z s_1 h -> dll x z s_2 h. Admitted.
Hint Resolve dll_perm_eq_trans19: ssl_pred.
Lemma sll_perm_eq_trans20 x h s_1 s_2 : perm_eq s_1 s_2 -> sll x s_1 h -> sll x s_2 h. Admitted.
Hint Resolve sll_perm_eq_trans20: ssl_pred.
Lemma pure21 vx12 s1x1 s2 : @perm_eq nat_eqType (s1x1 ++ s2) (nil) -> @perm_eq nat_eqType ([:: vx12] ++ s1x1 ++ s2) ([:: vx12]). Admitted.
Hint Resolve pure21: ssl_pure.
Lemma pure22 s2 s1x1 s1y12 vy122 vx12 : @perm_eq nat_eqType (s1x1 ++ s2) ([:: vy122] ++ s1y12) -> @perm_eq nat_eqType ([:: vx12] ++ s1x1 ++ s2) ([:: vx12] ++ [:: vy122] ++ s1y12). Admitted.
Hint Resolve pure22: ssl_pure.

Definition dll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : ptr * seq nat * ptr * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists h_dll_x1as1_530 h_dll_x2bs2_531,
      h = r :-> x2 \+ h_dll_x1as1_530 \+ h_dll_x2bs2_531 /\ dll x1 a s1 h_dll_x1as1_530 /\ dll x2 b s2 h_dll_x2bs2_531,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists s y c,
      exists h_dll_ycs_532,
      @perm_eq nat_eqType (s) (s1 ++ s2) /\ h = r :-> y \+ h_dll_ycs_532 /\ dll y c s h_dll_ycs_532
    ]).

Program Definition dll_append : dll_append_type :=
  Fix (fun (dll_append : dll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x22 <-- @read ptr r;
      if x1 == null
      then
        ret tt
      else
        vx12 <-- @read nat x1;
        wx12 <-- @read ptr (x1 .+ 1);
        a2 <-- @read ptr (x1 .+ 2);
        dll_append (wx12, r);;
        y12 <-- @read ptr r;
        if y12 == null
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
ex_elim h_dll_x1as1_530 h_dll_x2bs2_531.
move=>[sigma_self].
subst h_self.
move=>[H_dll_x1as1_530 H_dll_x2bs2_531].
ssl_ghostelim_post.
try rename h_dll_ycs_532 into h_dll_ycs1s2_532.
try rename H_dll_ycs_532 into H_dll_ycs1s2_532.
ssl_read r.
try rename x2 into x22.
try rename h_dll_x2bs2_531 into h_dll_x22bs2_531.
try rename H_dll_x2bs2_531 into H_dll_x22bs2_531.
ssl_open (x1 == null) H_dll_x1as1_530.
move=>[phi_dll_x1as1_5300].
move=>[sigma_dll_x1as1_530].
subst h_dll_x1as1_530.
shelve.
ex_elim vx1 s1x1 wx1.
ex_elim h_dll_wx1x1s1x1_528x1.
move=>[phi_dll_x1as1_5300].
move=>[sigma_dll_x1as1_530].
subst h_dll_x1as1_530.
move=>H_dll_wx1x1s1x1_528x1.
shelve.
Unshelve.
try rename h_dll_x1as1_530 into h_dll_x1a_530.
try rename H_dll_x1as1_530 into H_dll_x1a_530.
try rename h_dll_ycs1s2_532 into h_dll_ycs2_532.
try rename H_dll_ycs1s2_532 into H_dll_ycs2_532.
try rename h_dll_ycs2_532 into h_dll_ycs2_531.
try rename H_dll_ycs2_532 into H_dll_ycs2_531.
try rename h_dll_ycs2_531 into h_dll_ybs2_531.
try rename H_dll_ycs2_531 into H_dll_ybs2_531.
try rename h_dll_ybs2_531 into h_dll_x22bs2_531.
try rename H_dll_ybs2_531 into H_dll_x22bs2_531.
ssl_emp;
exists (nil ++ s2), (x22), (b);
exists (h_dll_x22bs2_531);
sslauto.
try rename h_dll_x1as1_530 into h_dll_x1avx1s1x1_530.
try rename H_dll_x1as1_530 into H_dll_x1avx1s1x1_530.
try rename h_dll_ycs1s2_532 into h_dll_ycvx1s1x1s2_532.
try rename H_dll_ycs1s2_532 into H_dll_ycvx1s1x1s2_532.
ssl_read x1.
try rename vx1 into vx12.
try rename h_dll_ycvx1s1x1s2_532 into h_dll_ycvx12s1x1s2_532.
try rename H_dll_ycvx1s1x1s2_532 into H_dll_ycvx12s1x1s2_532.
try rename h_dll_x1avx1s1x1_530 into h_dll_x1avx12s1x1_530.
try rename H_dll_x1avx1s1x1_530 into H_dll_x1avx12s1x1_530.
ssl_read (x1 .+ 1).
try rename wx1 into wx12.
try rename h_dll_wx1x1s1x1_528x1 into h_dll_wx12x1s1x1_528x1.
try rename H_dll_wx1x1s1x1_528x1 into H_dll_wx12x1s1x1_528x1.
ssl_read (x1 .+ 2).
try rename a into a2.
try rename h_dll_x1avx12s1x1_530 into h_dll_x1a2vx12s1x1_530.
try rename H_dll_x1avx12s1x1_530 into H_dll_x1a2vx12s1x1_530.
ssl_call_pre (r :-> x22 \+ h_dll_wx12x1s1x1_528x1 \+ h_dll_x22bs2_531).
ssl_call (x1, s1x1, x22, b, s2).
exists (h_dll_wx12x1s1x1_528x1), (h_dll_x22bs2_531);
sslauto.
move=>h_call0.
ex_elim s3 y1 c1.
ex_elim h_dll_y1c1s3_5321.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_dll_y1c1s3_5321.
store_valid.
try rename h_dll_y1c1s3_5321 into h_dll_y1c1s1x1s2_5321.
try rename H_dll_y1c1s3_5321 into H_dll_y1c1s1x1s2_5321.
ssl_read r.
try rename y1 into y12.
try rename h_dll_y1c1s1x1s2_5321 into h_dll_y12c1s1x1s2_5321.
try rename H_dll_y1c1s1x1s2_5321 into H_dll_y12c1s1x1s2_5321.
ssl_open (y12 == null) H_dll_y12c1s1x1s2_5321.
move=>[phi_dll_y12c1s1x1s2_53210].
move=>[sigma_dll_y12c1s1x1s2_5321].
subst h_dll_y12c1s1x1s2_5321.
shelve.
ex_elim vy12 s1y12 wy12.
ex_elim h_dll_wy12y12s1y12_528y12.
move=>[phi_dll_y12c1s1x1s2_53210].
move=>[sigma_dll_y12c1s1x1s2_5321].
subst h_dll_y12c1s1x1s2_5321.
move=>H_dll_wy12y12s1y12_528y12.
shelve.
Unshelve.
try rename h_dll_wyys12y_528y into h_dll_wyy_528y.
try rename H_dll_wyys12y_528y into H_dll_wyy_528y.
try rename h_dll_wyy_528y into h_dll_y_528y.
try rename H_dll_wyy_528y into H_dll_y_528y.
try rename h_dll_ycvx12s1x1s2_532 into h_dll_x1cvx12s1x1s2_532.
try rename H_dll_ycvx12s1x1s2_532 into H_dll_x1cvx12s1x1s2_532.
try rename h_dll_y_528y into h_dll_x1_528y.
try rename H_dll_y_528y into H_dll_x1_528y.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_532 into h_dll_x1a2vx12s1x1s2_532.
try rename H_dll_x1cvx12s1x1s2_532 into H_dll_x1a2vx12s1x1s2_532.
ssl_emp;
exists ([:: vx12] ++ s1x1 ++ s2), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> null \+ x1 .+ 2 :-> a2);
sslauto.
unfold_constructor 2;
exists (vx12), (nil), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_read y12.
try rename vy12 into vy122.
ssl_read (y12 .+ 1).
try rename wy12 into wy122.
try rename h_dll_wy12y12s1y12_528y12 into h_dll_wy122y12s1y12_528y12.
try rename H_dll_wy12y12s1y12_528y12 into H_dll_wy122y12s1y12_528y12.
ssl_read (y12 .+ 2).
try rename c1 into c12.
try rename h_dll_y12c1s1x1s2_5321 into h_dll_y12c12s1x1s2_5321.
try rename H_dll_y12c1s1x1s2_5321 into H_dll_y12c12s1x1s2_5321.
try rename h_dll_wyys12y_528y into h_dll_wyyvwys12wy_528y.
try rename H_dll_wyys12y_528y into H_dll_wyyvwys12wy_528y.
try rename h_dll_wwywys12wy_528wy into h_dll_wwywys12wy_528y12.
try rename H_dll_wwywys12wy_528wy into H_dll_wwywys12wy_528y12.
try rename h_dll_wwywys12wy_528y12 into h_dll_wwywys1y12_528y12.
try rename H_dll_wwywys12wy_528y12 into H_dll_wwywys1y12_528y12.
try rename h_dll_wyyvwys12wy_528y into h_dll_wyyvwys1y12_528y.
try rename H_dll_wyyvwys12wy_528y into H_dll_wyyvwys1y12_528y.
try rename h_dll_wwywys1y12_528y12 into h_dll_wy122wys1y12_528y12.
try rename H_dll_wwywys1y12_528y12 into H_dll_wy122wys1y12_528y12.
try rename h_dll_wy122wys1y12_528y12 into h_dll_wy122y12s1y12_528y12.
try rename H_dll_wy122wys1y12_528y12 into H_dll_wy122y12s1y12_528y12.
try rename h_dll_wyyvwys1y12_528y into h_dll_y12yvwys1y12_528y.
try rename H_dll_wyyvwys1y12_528y into H_dll_y12yvwys1y12_528y.
try rename h_dll_ycvx12s1x1s2_532 into h_dll_x1cvx12s1x1s2_532.
try rename H_dll_ycvx12s1x1s2_532 into H_dll_x1cvx12s1x1s2_532.
try rename h_dll_y12yvwys1y12_528y into h_dll_y12x1vwys1y12_528y.
try rename H_dll_y12yvwys1y12_528y into H_dll_y12x1vwys1y12_528y.
ssl_write (y12 .+ 2).
ssl_write_post (y12 .+ 2).
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_532 into h_dll_x1a2vx12s1x1s2_532.
try rename H_dll_x1cvx12s1x1s2_532 into H_dll_x1a2vx12s1x1s2_532.
try rename h_dll_y12x1vwys1y12_528y into h_dll_y12x1vy122s1y12_528y.
try rename H_dll_y12x1vwys1y12_528y into H_dll_y12x1vy122s1y12_528y.
ssl_emp;
exists ([:: vx12] ++ s1x1 ++ s2), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ x1 .+ 2 :-> a2 \+ y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_528y12);
sslauto.
unfold_constructor 2;
exists (vx12), ([:: vy122] ++ s1y12), (y12), (y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_528y12);
sslauto.
unfold_constructor 2;
exists (vy122), (s1y12), (wy122), (h_dll_wy122y12s1y12_528y12);
sslauto.
Qed.