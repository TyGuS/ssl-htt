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

Lemma pure1 (vx11 : nat) (s1x1 : seq nat) (s2 : seq nat) : ((s1x1) ++ (s2)) = (@nil nat) -> ((([:: vx11]) ++ (s1x1)) ++ (s2)) = ([:: vx11]). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (s1y11 : seq nat) (s1x1 : seq nat) (s2 : seq nat) (vy111 : nat) (vx11 : nat) : ((s1x1) ++ (s2)) = (([:: vy111]) ++ (s1y11)) -> ((([:: vx11]) ++ (s1x1)) ++ (s2)) = (([:: vx11]) ++ (([:: vy111]) ++ (s1y11))). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.

Definition dll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : ptr * seq nat * ptr * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists h_dll_x1as1_1 h_dll_x2bs2_2,
      h = r :-> (x2) \+ h_dll_x1as1_1 \+ h_dll_x2bs2_2 /\ dll x1 a s1 h_dll_x1as1_1 /\ dll x2 b s2 h_dll_x2bs2_2,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists s y c,
      exists h_dll_ycs_3,
      (s) == ((s1) ++ (s2)) /\ h = r :-> (y) \+ h_dll_ycs_3 /\ dll y c s h_dll_ycs_3
    ]).

Program Definition dll_append : dll_append_type :=
  Fix (fun (dll_append : dll_append_type) vprogs =>
    let: (x1, r) := vprogs in
    Do (
      x21 <-- @read ptr r;
      if (x1) == (null)
      then
        ret tt
      else
        vx11 <-- @read nat x1;
        wx11 <-- @read ptr (x1 .+ 1);
        a1 <-- @read ptr (x1 .+ 2);
        dll_append (wx11, r);;
        y11 <-- @read ptr r;
        if (y11) == (null)
        then
          r ::= x1;;
          (x1 .+ 1) ::= null;;
          ret tt
        else
          vy111 <-- @read nat y11;
          wy111 <-- @read ptr (y11 .+ 1);
          c11 <-- @read ptr (y11 .+ 2);
          (y11 .+ 2) ::= x1;;
          r ::= x1;;
          (x1 .+ 1) ::= y11;;
          ret tt
    )).
Obligation Tactic := intro; move=>[x1 r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[[a s1] x2] b] s2].
ex_elim h_dll_x1as1_1 h_dll_x2bs2_2.
move=>[sigma_self].
subst h_self.
move=>[H_dll_x1as1_1 H_dll_x2bs2_2].
ssl_ghostelim_post.
try rename h_dll_ycs_3 into h_dll_ycs1s2_3.
try rename H_dll_ycs_3 into H_dll_ycs1s2_3.
ssl_read r.
try rename x2 into x21.
try rename h_dll_x2bs2_2 into h_dll_x21bs2_2.
try rename H_dll_x2bs2_2 into H_dll_x21bs2_2.
ssl_open ((x1) == (null)) H_dll_x1as1_1.
move=>[phi_dll_x1as1_10].
move=>[sigma_dll_x1as1_1].
subst h_dll_x1as1_1.
try rename h_dll_x1as1_1 into h_dll_x1a_1.
try rename H_dll_x1as1_1 into H_dll_x1a_1.
try rename h_dll_ycs1s2_3 into h_dll_ycs2_3.
try rename H_dll_ycs1s2_3 into H_dll_ycs2_3.
try rename h_dll_ycs2_3 into h_dll_x21bs2_2.
try rename H_dll_ycs2_3 into H_dll_x21bs2_2.
ssl_emp;
exists (s2), (x21), (b);
exists (h_dll_x21bs2_2);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 wx1.
ex_elim h_dll_wx1x1s1x1_0x1.
move=>[phi_dll_x1as1_10].
move=>[sigma_dll_x1as1_1].
subst h_dll_x1as1_1.
move=>H_dll_wx1x1s1x1_0x1.
try rename h_dll_x1as1_1 into h_dll_x1avx1s1x1_1.
try rename H_dll_x1as1_1 into H_dll_x1avx1s1x1_1.
try rename h_dll_ycs1s2_3 into h_dll_ycvx1s1x1s2_3.
try rename H_dll_ycs1s2_3 into H_dll_ycvx1s1x1s2_3.
ssl_read x1.
try rename vx1 into vx11.
try rename h_dll_ycvx1s1x1s2_3 into h_dll_ycvx11s1x1s2_3.
try rename H_dll_ycvx1s1x1s2_3 into H_dll_ycvx11s1x1s2_3.
try rename h_dll_x1avx1s1x1_1 into h_dll_x1avx11s1x1_1.
try rename H_dll_x1avx1s1x1_1 into H_dll_x1avx11s1x1_1.
ssl_read (x1 .+ 1).
try rename wx1 into wx11.
try rename h_dll_wx1x1s1x1_0x1 into h_dll_wx11x1s1x1_0x1.
try rename H_dll_wx1x1s1x1_0x1 into H_dll_wx11x1s1x1_0x1.
ssl_read (x1 .+ 2).
try rename a into a1.
try rename h_dll_x1avx11s1x1_1 into h_dll_x1a1vx11s1x1_1.
try rename H_dll_x1avx11s1x1_1 into H_dll_x1a1vx11s1x1_1.
try rename h_dll_x11a2s11_11 into h_dll_wx11x1s1x1_0x1.
try rename H_dll_x11a2s11_11 into H_dll_wx11x1s1x1_0x1.
try rename h_dll_x22b1s21_21 into h_dll_x21bs2_2.
try rename H_dll_x22b1s21_21 into H_dll_x21bs2_2.
ssl_call_pre (r :-> (x21) \+ h_dll_wx11x1s1x1_0x1 \+ h_dll_x21bs2_2).
ssl_call (x1, s1x1, x21, b, s2).
exists (h_dll_wx11x1s1x1_0x1), (h_dll_x21bs2_2);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1 c1.
ex_elim h_dll_y1c1s3_31.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_dll_y1c1s3_31.
store_valid.
try rename h_dll_y1c1s3_31 into h_dll_y1c1s1x1s2_31.
try rename H_dll_y1c1s3_31 into H_dll_y1c1s1x1s2_31.
ssl_read r.
try rename y1 into y11.
try rename h_dll_y1c1s1x1s2_31 into h_dll_y11c1s1x1s2_31.
try rename H_dll_y1c1s1x1s2_31 into H_dll_y11c1s1x1s2_31.
ssl_open ((y11) == (null)) H_dll_y11c1s1x1s2_31.
move=>[phi_dll_y11c1s1x1s2_310].
move=>[sigma_dll_y11c1s1x1s2_31].
subst h_dll_y11c1s1x1s2_31.
try rename h_dll_wyys12y_0y into h_dll_wyy_0y.
try rename H_dll_wyys12y_0y into H_dll_wyy_0y.
try rename h_dll_wyy_0y into h_dll_y_0y.
try rename H_dll_wyy_0y into H_dll_y_0y.
try rename h_dll_ycvx11s1x1s2_3 into h_dll_x1cvx11s1x1s2_3.
try rename H_dll_ycvx11s1x1s2_3 into H_dll_x1cvx11s1x1s2_3.
try rename h_dll_y_0y into h_dll_x1_0y.
try rename H_dll_y_0y into H_dll_x1_0y.
ssl_write r.
ssl_write_post r.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
try rename h_dll_x1cvx11s1x1s2_3 into h_dll_x1a1vx11s1x1s2_3.
try rename H_dll_x1cvx11s1x1s2_3 into H_dll_x1a1vx11s1x1s2_3.
ssl_emp;
exists ((([:: vx11]) ++ (s1x1)) ++ (s2)), (x1), (a1);
exists (x1 :-> (vx11) \+ x1 .+ 1 :-> (null) \+ x1 .+ 2 :-> (a1));
sslauto.
ssl_close 2;
exists (vx11), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vy11 s1y11 wy11.
ex_elim h_dll_wy11y11s1y11_0y11.
move=>[phi_dll_y11c1s1x1s2_310].
move=>[sigma_dll_y11c1s1x1s2_31].
subst h_dll_y11c1s1x1s2_31.
move=>H_dll_wy11y11s1y11_0y11.
ssl_read y11.
try rename vy11 into vy111.
ssl_read (y11 .+ 1).
try rename wy11 into wy111.
try rename h_dll_wy11y11s1y11_0y11 into h_dll_wy111y11s1y11_0y11.
try rename H_dll_wy11y11s1y11_0y11 into H_dll_wy111y11s1y11_0y11.
ssl_read (y11 .+ 2).
try rename c1 into c11.
try rename h_dll_y11c1s1x1s2_31 into h_dll_y11c11s1x1s2_31.
try rename H_dll_y11c1s1x1s2_31 into H_dll_y11c11s1x1s2_31.
try rename h_dll_wyys12y_0y into h_dll_wyyvwys12wy_0y.
try rename H_dll_wyys12y_0y into H_dll_wyyvwys12wy_0y.
try rename h_dll_wwywys12wy_0wy into h_dll_wy111y11s1y11_0y11.
try rename H_dll_wwywys12wy_0wy into H_dll_wy111y11s1y11_0y11.
try rename h_dll_wyyvwys12wy_0y into h_dll_wyyvwys1y11_0y.
try rename H_dll_wyyvwys12wy_0y into H_dll_wyyvwys1y11_0y.
try rename h_dll_wyyvwys1y11_0y into h_dll_y11yvwys1y11_0y.
try rename H_dll_wyyvwys1y11_0y into H_dll_y11yvwys1y11_0y.
try rename h_dll_y11yvwys1y11_0y into h_dll_y11x1vwys1y11_0y.
try rename H_dll_y11yvwys1y11_0y into H_dll_y11x1vwys1y11_0y.
try rename h_dll_ycvx11s1x1s2_3 into h_dll_x1cvx11s1x1s2_3.
try rename H_dll_ycvx11s1x1s2_3 into H_dll_x1cvx11s1x1s2_3.
ssl_write (y11 .+ 2).
ssl_write_post (y11 .+ 2).
ssl_write r.
ssl_write_post r.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
try rename h_dll_x1cvx11s1x1s2_3 into h_dll_x1a1vx11s1x1s2_3.
try rename H_dll_x1cvx11s1x1s2_3 into H_dll_x1a1vx11s1x1s2_3.
try rename h_dll_y11x1vwys1y11_0y into h_dll_y11x1vy111s1y11_0y.
try rename H_dll_y11x1vwys1y11_0y into H_dll_y11x1vy111s1y11_0y.
ssl_emp;
exists ((([:: vx11]) ++ (s1x1)) ++ (s2)), (x1), (a1);
exists (x1 :-> (vx11) \+ x1 .+ 1 :-> (y11) \+ x1 .+ 2 :-> (a1) \+ y11 :-> (vy111) \+ y11 .+ 1 :-> (wy111) \+ y11 .+ 2 :-> (x1) \+ h_dll_wy111y11s1y11_0y11);
sslauto.
ssl_close 2;
exists (vx11), (([:: vy111]) ++ (s1y11)), (y11), (y11 :-> (vy111) \+ y11 .+ 1 :-> (wy111) \+ y11 .+ 2 :-> (x1) \+ h_dll_wy111y11s1y11_0y11);
sslauto.
ssl_close 2;
exists (vy111), (s1y11), (wy111), (h_dll_wy111y11s1y11_0y11);
sslauto.
ssl_frame_unfold.
Qed.