From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| sll_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| sll_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_sll_nxtlen1lo1hi1_519,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_519 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_519.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_520,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_520 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_520.

Lemma pure6 : (0) <= (0). Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 : (1) == (1). Admitted.
Hint Resolve pure7: ssl_pure.
Lemma pure8 k2 : (k2) <= (7) -> (0) <= (k2) -> ((if (0) <= (k2) then k2 else 0)) == ((if (0) <= (k2) then k2 else 0)). Admitted.
Hint Resolve pure8: ssl_pure.
Lemma pure9 k2 : (k2) <= (7) -> (0) <= (k2) -> ((if (k2) <= (7) then k2 else 7)) == ((if (k2) <= (7) then k2 else 7)). Admitted.
Hint Resolve pure9: ssl_pure.
Lemma pure10 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) == ((1) + ((1) + (len1x))). Admitted.
Hint Resolve pure10: ssl_pure.
Lemma pure11 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) == ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))). Admitted.
Hint Resolve pure11: ssl_pure.
Lemma pure12 vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). Admitted.
Hint Resolve pure12: ssl_pure.
Lemma pure13 k2 vx2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) == ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))). Admitted.
Hint Resolve pure13: ssl_pure.
Lemma pure14 k2 lo1x vx2 : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (k2) <= (lo1x). Admitted.
Hint Resolve pure14: ssl_pure.
Lemma pure15 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (0) <= ((len1x) + (1)). Admitted.
Hint Resolve pure15: ssl_pure.
Lemma pure16 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) == ((1) + ((len1x) + (1))). Admitted.
Hint Resolve pure16: ssl_pure.
Lemma pure17 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) == ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))). Admitted.
Hint Resolve pure17: ssl_pure.
Lemma pure18 vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). Admitted.
Hint Resolve pure18: ssl_pure.
Lemma pure19 k2 vx2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) == ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))). Admitted.
Hint Resolve pure19: ssl_pure.
Lemma pure20 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) == ((1) + ((1) + (len1x))). Admitted.
Hint Resolve pure20: ssl_pure.
Lemma pure21 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) == ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))). Admitted.
Hint Resolve pure21: ssl_pure.
Lemma pure22 k2 vx2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure22: ssl_pure.
Lemma pure23 k2 vx2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) == ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))). Admitted.
Hint Resolve pure23: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_521,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_521 /\ srtl x n lo hi h_srtl_xnlohi_521,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_522,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((n) + (1)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_522 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_522
    ]).

Program Definition srtl_insert : srtl_insert_type :=
  Fix (fun (srtl_insert : srtl_insert_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      k2 <-- @read nat r;
      if (x) == (null)
      then
        y2 <-- allocb null 2;
        r ::= y2;;
        (y2 .+ 1) ::= null;;
        y2 ::= k2;;
        ret tt
      else
        vx2 <-- @read nat x;
        if ((k2) <= (vx2)) && ((vx2) <= (k2))
        then
          nxtx2 <-- @read ptr (x .+ 1);
          nxty2 <-- allocb null 2;
          (x .+ 1) ::= nxty2;;
          r ::= x;;
          (nxty2 .+ 1) ::= nxtx2;;
          nxty2 ::= k2;;
          ret tt
        else
          if (vx2) <= (k2)
          then
            nxtx2 <-- @read ptr (x .+ 1);
            srtl_insert (nxtx2, r);;
            y12 <-- @read ptr r;
            (x .+ 1) ::= y12;;
            r ::= x;;
            ret tt
          else
            nxtx2 <-- @read ptr (x .+ 1);
            nxty2 <-- allocb null 2;
            (x .+ 1) ::= nxty2;;
            r ::= x;;
            (nxty2 .+ 1) ::= nxtx2;;
            x ::= k2;;
            nxty2 ::= vx2;;
            ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[k n] lo] hi].
ex_elim h_srtl_xnlohi_521.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_521.
ssl_ghostelim_post.
try rename h_srtl_yn1lo1hi1_522 into h_srtl_yn1lo1hikkhi_522.
try rename H_srtl_yn1lo1hi1_522 into H_srtl_yn1lo1hikkhi_522.
try rename h_srtl_yn1lo1hikkhi_522 into h_srtl_yn1kloklohikkhi_522.
try rename H_srtl_yn1lo1hikkhi_522 into H_srtl_yn1kloklohikkhi_522.
try rename h_srtl_yn1kloklohikkhi_522 into h_srtl_ynkloklohikkhi_522.
try rename H_srtl_yn1kloklohikkhi_522 into H_srtl_ynkloklohikkhi_522.
ssl_read r.
try rename k into k2.
try rename h_srtl_ynkloklohikkhi_522 into h_srtl_ynk2lok2lohik2k2hi_522.
try rename H_srtl_ynkloklohikkhi_522 into H_srtl_ynk2lok2lohik2k2hi_522.
ssl_open ((x) == (null)) H_srtl_xnlohi_521.
move=>[phi_srtl_xnlohi_5210] [phi_srtl_xnlohi_5211] [phi_srtl_xnlohi_5212].
move=>[sigma_srtl_xnlohi_521].
subst h_srtl_xnlohi_521.
try rename h_srtl_ynk2lok2lohik2k2hi_522 into h_srtl_ynk2lok2lok2k2_522.
try rename H_srtl_ynk2lok2lohik2k2hi_522 into H_srtl_ynk2lok2lok2k2_522.
try rename h_srtl_xnlohi_521 into h_srtl_xnlo_521.
try rename H_srtl_xnlohi_521 into H_srtl_xnlo_521.
try rename h_srtl_xnlo_521 into h_srtl_xn_521.
try rename H_srtl_xnlo_521 into H_srtl_xn_521.
try rename h_srtl_ynk2lok2lok2k2_522 into h_srtl_ynk2k2k2k2_522.
try rename H_srtl_ynk2lok2lok2k2_522 into H_srtl_ynk2k2k2k2_522.
try rename h_srtl_xn_521 into h_srtl_x_521.
try rename H_srtl_xn_521 into H_srtl_x_521.
try rename h_srtl_ynk2k2k2k2_522 into h_srtl_yk2k2k2k2_522.
try rename H_srtl_ynk2k2k2k2_522 into H_srtl_yk2k2k2k2_522.
try rename h_srtl_nxtylen1ylo11yhi11y_520y into h_srtl_nxtylen1ylo11y_520y.
try rename H_srtl_nxtylen1ylo11yhi11y_520y into H_srtl_nxtylen1ylo11y_520y.
try rename h_srtl_nxtylen1ylo11y_520y into h_srtl_nxtylo11y_520y.
try rename H_srtl_nxtylen1ylo11y_520y into H_srtl_nxtylo11y_520y.
try rename h_srtl_nxtylo11y_520y into h_srtl_nxty_520y.
try rename H_srtl_nxtylo11y_520y into H_srtl_nxty_520y.
try rename h_srtl_nxty_520y into h_srtl__520y.
try rename H_srtl_nxty_520y into H_srtl__520y.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_yk2k2k2k2_522 into h_srtl_y2k2k2k2k2_522.
try rename H_srtl_yk2k2k2k2_522 into H_srtl_y2k2k2k2k2_522.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ((if (0) <= (k2) then k2 else 0)), ((if (k2) <= (7) then k2 else 7)), ((0) + (1)), (y2);
exists (y2 :-> k2 \+ y2 .+ 1 :-> null);
sslauto.
unfold_constructor 2;
exists (0), (k2), (0), (7), (null), (empty);
sslauto.
unfold_constructor 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_srtl_nxtxlen1xlo1xhi1x_520x.
move=>[phi_srtl_xnlohi_5210] [phi_srtl_xnlohi_5211] [phi_srtl_xnlohi_5212] [phi_srtl_xnlohi_5213] [phi_srtl_xnlohi_5214] [phi_srtl_xnlohi_5215] [phi_srtl_xnlohi_5216].
move=>[sigma_srtl_xnlohi_521].
subst h_srtl_xnlohi_521.
move=>H_srtl_nxtxlen1xlo1xhi1x_520x.
try rename h_srtl_ynk2lok2lohik2k2hi_522 into h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename H_srtl_ynk2lok2lohik2k2hi_522 into H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename h_srtl_xnlohi_521 into h_srtl_xnlohi1xvxvxhi1x_521.
try rename H_srtl_xnlohi_521 into H_srtl_xnlohi1xvxvxhi1x_521.
try rename h_srtl_xnlohi1xvxvxhi1x_521 into h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename H_srtl_xnlohi1xvxvxhi1x_521 into H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522.
try rename h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_521 into h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_521 into H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521.
ssl_read x.
try rename vx into vx2.
try rename h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
try rename H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_522 into H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
try rename h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521 into h_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521.
try rename H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521 into H_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521.
ssl_abduce_branch (((k2) <= (vx2)) && ((vx2) <= (k2))).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_520x into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_nxtxlen1xlo1xhi1x_520x into H_srtl_nxtx2len1xlo1xhi1x_520x.
try rename h_srtl_nxtylen1ylo11yhi11y_520y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1ylo11yhi11y_520y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_520nxty into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_520nxty into H_srtl_nxtx2len1xlo1xhi1x_520x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_520y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_520y.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
unfold_constructor 2;
exists ((1) + (len1x)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (nxty2), (nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
unfold_constructor 2;
exists (len1x), (k2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
ssl_frame_unfold.
ssl_abduce_branch ((vx2) <= (k2)).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_520x into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_nxtxlen1xlo1xhi1x_520x into H_srtl_nxtx2len1xlo1xhi1x_520x.
try rename h_srtl_x1n2lo2hi2_5211 into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_x1n2lo2hi2_5211 into H_srtl_nxtx2len1xlo1xhi1x_520x.
ssl_call_pre (r :-> k2 \+ h_srtl_nxtx2len1xlo1xhi1x_520x).
ssl_call (k2, len1x, lo1x, hi1x).
exists (h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_srtl_y1n11lo11hi11_5221.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1n11lo11hi11_5221.
store_valid.
try rename h_srtl_y1n11lo11hi11_5221 into h_srtl_y1n11lo11hi1xk2k2hi1x_5221.
try rename H_srtl_y1n11lo11hi11_5221 into H_srtl_y1n11lo11hi1xk2k2hi1x_5221.
try rename h_srtl_y1n11lo11hi1xk2k2hi1x_5221 into h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename H_srtl_y1n11lo11hi1xk2k2hi1x_5221 into H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5221 into h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5221 into H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221 into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221 into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename h_srtl_nxtylen1ylo12yhi12y_520y into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename H_srtl_nxtylen1ylo12yhi12y_520y into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> y12 \+ h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221);
sslauto.
unfold_constructor 2;
exists ((len1x) + (1)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (y12), (h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5221);
sslauto.
ssl_frame_unfold.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_520x into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_nxtxlen1xlo1xhi1x_520x into H_srtl_nxtx2len1xlo1xhi1x_520x.
try rename h_srtl_nxtylen1ylo11yhi11y_520y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1ylo11yhi11y_520y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_520nxty into h_srtl_nxtx2len1xlo1xhi1x_520x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_520nxty into H_srtl_nxtx2len1xlo1xhi1x_520x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_520y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_522.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into h_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_520y into H_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520y.
ssl_write x.
ssl_write_post x.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> k2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
unfold_constructor 2;
exists ((1) + (len1x)), (k2), ((if (hi1x) <= (vx2) then vx2 else hi1x)), ((if (vx2) <= (lo1x) then vx2 else lo1x)), (nxty2), (nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
unfold_constructor 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_520x);
sslauto.
ssl_frame_unfold.
Qed.