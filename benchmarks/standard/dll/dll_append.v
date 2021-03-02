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

Lemma pure30 (vx12 : nat) (s1x1 : seq nat) (s2 : seq nat) : ((s1x1) ++ (s2)) = (@nil nat) -> ((([:: vx12]) ++ (s1x1)) ++ (s2)) = ([:: vx12]). intros; hammer. Qed.
Hint Resolve pure30: ssl_pure.
Lemma pure31 (s1x1 : seq nat) (s1y12 : seq nat) (s2 : seq nat) (vy122 : nat) (vx12 : nat) : ((s1x1) ++ (s2)) = (([:: vy122]) ++ (s1y12)) -> ((([:: vx12]) ++ (s1x1)) ++ (s2)) = (([:: vx12]) ++ (([:: vy122]) ++ (s1y12))). intros; hammer. Qed.
Hint Resolve pure31: ssl_pure.

Definition dll_append_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : ptr * seq nat * ptr * ptr * seq nat)},
  STsep (
    fun h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists h_dll_x1as1_536 h_dll_x2bs2_537,
      h = r :-> x2 \+ h_dll_x1as1_536 \+ h_dll_x2bs2_537 /\ dll x1 a s1 h_dll_x1as1_536 /\ dll x2 b s2 h_dll_x2bs2_537,
    [vfun (_: unit) h =>
      let: (x1, r) := vprogs in
      let: (a, s1, x2, b, s2) := vghosts in
      exists s y c,
      exists h_dll_ycs_538,
      (s) == ((s1) ++ (s2)) /\ h = r :-> y \+ h_dll_ycs_538 /\ dll y c s h_dll_ycs_538
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
ex_elim h_dll_x1as1_536 h_dll_x2bs2_537.
move=>[sigma_self].
subst h_self.
move=>[H_dll_x1as1_536 H_dll_x2bs2_537].
ssl_ghostelim_post.
try rename h_dll_ycs_538 into h_dll_ycs1s2_538.
try rename H_dll_ycs_538 into H_dll_ycs1s2_538.
ssl_read r.
try rename x2 into x22.
try rename h_dll_x2bs2_537 into h_dll_x22bs2_537.
try rename H_dll_x2bs2_537 into H_dll_x22bs2_537.
ssl_open ((x1) == (null)) H_dll_x1as1_536.
move=>[phi_dll_x1as1_5360].
move=>[sigma_dll_x1as1_536].
subst h_dll_x1as1_536.
try rename h_dll_ycs1s2_538 into h_dll_ycs2_538.
try rename H_dll_ycs1s2_538 into H_dll_ycs2_538.
try rename h_dll_x1as1_536 into h_dll_x1a_536.
try rename H_dll_x1as1_536 into H_dll_x1a_536.
try rename h_dll_ycs2_538 into h_dll_x22bs2_537.
try rename H_dll_ycs2_538 into H_dll_x22bs2_537.
ssl_emp;
exists (s2), (x22), (b);
exists (h_dll_x22bs2_537);
sslauto.
ssl_frame_unfold.
ex_elim vx1 s1x1 wx1.
ex_elim h_dll_wx1x1s1x1_535x1.
move=>[phi_dll_x1as1_5360].
move=>[sigma_dll_x1as1_536].
subst h_dll_x1as1_536.
move=>H_dll_wx1x1s1x1_535x1.
try rename h_dll_ycs1s2_538 into h_dll_ycvx1s1x1s2_538.
try rename H_dll_ycs1s2_538 into H_dll_ycvx1s1x1s2_538.
try rename h_dll_x1as1_536 into h_dll_x1avx1s1x1_536.
try rename H_dll_x1as1_536 into H_dll_x1avx1s1x1_536.
ssl_read x1.
try rename vx1 into vx12.
try rename h_dll_x1avx1s1x1_536 into h_dll_x1avx12s1x1_536.
try rename H_dll_x1avx1s1x1_536 into H_dll_x1avx12s1x1_536.
try rename h_dll_ycvx1s1x1s2_538 into h_dll_ycvx12s1x1s2_538.
try rename H_dll_ycvx1s1x1s2_538 into H_dll_ycvx12s1x1s2_538.
ssl_read (x1 .+ 1).
try rename wx1 into wx12.
try rename h_dll_wx1x1s1x1_535x1 into h_dll_wx12x1s1x1_535x1.
try rename H_dll_wx1x1s1x1_535x1 into H_dll_wx12x1s1x1_535x1.
ssl_read (x1 .+ 2).
try rename a into a2.
try rename h_dll_x1avx12s1x1_536 into h_dll_x1a2vx12s1x1_536.
try rename H_dll_x1avx12s1x1_536 into H_dll_x1a2vx12s1x1_536.
try rename h_dll_x11a1s11_5361 into h_dll_wx12x1s1x1_535x1.
try rename H_dll_x11a1s11_5361 into H_dll_wx12x1s1x1_535x1.
try rename h_dll_x21b1s21_5371 into h_dll_x22bs2_537.
try rename H_dll_x21b1s21_5371 into H_dll_x22bs2_537.
ssl_call_pre (r :-> x22 \+ h_dll_wx12x1s1x1_535x1 \+ h_dll_x22bs2_537).
ssl_call (x1, s1x1, x22, b, s2).
exists (h_dll_wx12x1s1x1_535x1), (h_dll_x22bs2_537);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
move=>h_call0.
ex_elim s3 y1 c1.
ex_elim h_dll_y1c1s3_5381.
move=>[phi_call00].
move=>[sigma_call0].
subst h_call0.
move=>H_dll_y1c1s3_5381.
store_valid.
try rename h_dll_y1c1s3_5381 into h_dll_y1c1s1x1s2_5381.
try rename H_dll_y1c1s3_5381 into H_dll_y1c1s1x1s2_5381.
ssl_read r.
try rename y1 into y12.
try rename h_dll_y1c1s1x1s2_5381 into h_dll_y12c1s1x1s2_5381.
try rename H_dll_y1c1s1x1s2_5381 into H_dll_y12c1s1x1s2_5381.
ssl_open ((y12) == (null)) H_dll_y12c1s1x1s2_5381.
move=>[phi_dll_y12c1s1x1s2_53810].
move=>[sigma_dll_y12c1s1x1s2_5381].
subst h_dll_y12c1s1x1s2_5381.
try rename h_dll_wyys12y_535y into h_dll_wyy_535y.
try rename H_dll_wyys12y_535y into H_dll_wyy_535y.
try rename h_dll_wyy_535y into h_dll_y_535y.
try rename H_dll_wyy_535y into H_dll_y_535y.
try rename h_dll_ycvx12s1x1s2_538 into h_dll_x1cvx12s1x1s2_538.
try rename H_dll_ycvx12s1x1s2_538 into H_dll_x1cvx12s1x1s2_538.
try rename h_dll_y_535y into h_dll_x1_535y.
try rename H_dll_y_535y into H_dll_x1_535y.
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_538 into h_dll_x1a2vx12s1x1s2_538.
try rename H_dll_x1cvx12s1x1s2_538 into H_dll_x1a2vx12s1x1s2_538.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> null \+ x1 .+ 2 :-> a2);
sslauto.
ssl_close 2;
exists (vx12), (@nil nat), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim vy12 s1y12 wy12.
ex_elim h_dll_wy12y12s1y12_535y12.
move=>[phi_dll_y12c1s1x1s2_53810].
move=>[sigma_dll_y12c1s1x1s2_5381].
subst h_dll_y12c1s1x1s2_5381.
move=>H_dll_wy12y12s1y12_535y12.
ssl_read y12.
try rename vy12 into vy122.
ssl_read (y12 .+ 1).
try rename wy12 into wy122.
try rename h_dll_wy12y12s1y12_535y12 into h_dll_wy122y12s1y12_535y12.
try rename H_dll_wy12y12s1y12_535y12 into H_dll_wy122y12s1y12_535y12.
ssl_read (y12 .+ 2).
try rename c1 into c12.
try rename h_dll_y12c1s1x1s2_5381 into h_dll_y12c12s1x1s2_5381.
try rename H_dll_y12c1s1x1s2_5381 into H_dll_y12c12s1x1s2_5381.
try rename h_dll_wyys12y_535y into h_dll_wyyvwys12wy_535y.
try rename H_dll_wyys12y_535y into H_dll_wyyvwys12wy_535y.
try rename h_dll_wwywys12wy_535wy into h_dll_wy122y12s1y12_535y12.
try rename H_dll_wwywys12wy_535wy into H_dll_wy122y12s1y12_535y12.
try rename h_dll_wyyvwys12wy_535y into h_dll_wyyvwys1y12_535y.
try rename H_dll_wyyvwys12wy_535y into H_dll_wyyvwys1y12_535y.
try rename h_dll_wyyvwys1y12_535y into h_dll_y12yvwys1y12_535y.
try rename H_dll_wyyvwys1y12_535y into H_dll_y12yvwys1y12_535y.
try rename h_dll_ycvx12s1x1s2_538 into h_dll_x1cvx12s1x1s2_538.
try rename H_dll_ycvx12s1x1s2_538 into H_dll_x1cvx12s1x1s2_538.
try rename h_dll_y12yvwys1y12_535y into h_dll_y12x1vwys1y12_535y.
try rename H_dll_y12yvwys1y12_535y into H_dll_y12x1vwys1y12_535y.
ssl_write (y12 .+ 2).
ssl_write_post (y12 .+ 2).
ssl_write (x1 .+ 1).
ssl_write_post (x1 .+ 1).
ssl_write r.
ssl_write_post r.
try rename h_dll_x1cvx12s1x1s2_538 into h_dll_x1a2vx12s1x1s2_538.
try rename H_dll_x1cvx12s1x1s2_538 into H_dll_x1a2vx12s1x1s2_538.
try rename h_dll_y12x1vwys1y12_535y into h_dll_y12x1vy122s1y12_535y.
try rename H_dll_y12x1vwys1y12_535y into H_dll_y12x1vy122s1y12_535y.
ssl_emp;
exists ((([:: vx12]) ++ (s1x1)) ++ (s2)), (x1), (a2);
exists (x1 :-> vx12 \+ x1 .+ 1 :-> y12 \+ x1 .+ 2 :-> a2 \+ y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_535y12);
sslauto.
ssl_close 2;
exists (vx12), (([:: vy122]) ++ (s1y12)), (y12), (y12 :-> vy122 \+ y12 .+ 1 :-> wy122 \+ y12 .+ 2 :-> x1 \+ h_dll_wy122y12s1y12_535y12);
sslauto.
ssl_close 2;
exists (vy122), (s1y12), (wy122), (h_dll_wy122y12s1y12_535y12);
sslauto.
ssl_frame_unfold.
Qed.