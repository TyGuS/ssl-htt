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
  exists h_sll_nxtlen1lo1hi1_624,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_624 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_624.

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of (x) == (null) of
  (hi) == (0) /\ (len) == (0) /\ (lo) == (7) /\ h = empty
| srtl_2 of ~~ ((x) == (null)) of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_625,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ (v) <= (lo1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_625 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_625.

Lemma pure133 : (0) <= (0). Admitted.
Hint Resolve pure133: ssl_pure.
Lemma pure134 : (1) = (1). Admitted.
Hint Resolve pure134: ssl_pure.
Lemma pure135 k2 : (0) <= (k2) -> (k2) <= (7) -> ((if (0) <= (k2) then k2 else 0)) = ((if (0) <= (k2) then k2 else 0)). Admitted.
Hint Resolve pure135: ssl_pure.
Lemma pure136 k2 : (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= (7) then k2 else 7)) = ((if (k2) <= (7) then k2 else 7)). Admitted.
Hint Resolve pure136: ssl_pure.
Lemma pure137 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) = ((1) + ((1) + (len1x))). Admitted.
Hint Resolve pure137: ssl_pure.
Lemma pure138 k2 lo1x vx2 : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (k2) <= (lo1x). Admitted.
Hint Resolve pure138: ssl_pure.
Lemma pure139 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))). Admitted.
Hint Resolve pure139: ssl_pure.
Lemma pure140 vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). Admitted.
Hint Resolve pure140: ssl_pure.
Lemma pure141 k2 vx2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))). Admitted.
Hint Resolve pure141: ssl_pure.
Lemma pure142 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (0) <= ((len1x) + (1)). Admitted.
Hint Resolve pure142: ssl_pure.
Lemma pure143 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) = ((1) + ((len1x) + (1))). Admitted.
Hint Resolve pure143: ssl_pure.
Lemma pure144 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))). Admitted.
Hint Resolve pure144: ssl_pure.
Lemma pure145 vx2 k2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). Admitted.
Hint Resolve pure145: ssl_pure.
Lemma pure146 k2 vx2 lo1x : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))). Admitted.
Hint Resolve pure146: ssl_pure.
Lemma pure147 len1x : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) = ((1) + ((1) + (len1x))). Admitted.
Hint Resolve pure147: ssl_pure.
Lemma pure148 k2 vx2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)). Admitted.
Hint Resolve pure148: ssl_pure.
Lemma pure149 k2 vx2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))). Admitted.
Hint Resolve pure149: ssl_pure.
Lemma pure150 hi1x vx2 k2 lo1x : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))). Admitted.
Hint Resolve pure150: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_626,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_626 /\ srtl x n lo hi h_srtl_xnlohi_626,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_627,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((n) + (1)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_627 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_627
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
ex_elim h_srtl_xnlohi_626.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_626.
ssl_ghostelim_post.
try rename h_srtl_yn1lo1hi1_627 into h_srtl_yn1lo1hikkhi_627.
try rename H_srtl_yn1lo1hi1_627 into H_srtl_yn1lo1hikkhi_627.
try rename h_srtl_yn1lo1hikkhi_627 into h_srtl_yn1kloklohikkhi_627.
try rename H_srtl_yn1lo1hikkhi_627 into H_srtl_yn1kloklohikkhi_627.
try rename h_srtl_yn1kloklohikkhi_627 into h_srtl_ynkloklohikkhi_627.
try rename H_srtl_yn1kloklohikkhi_627 into H_srtl_ynkloklohikkhi_627.
ssl_read r.
try rename k into k2.
try rename h_srtl_ynkloklohikkhi_627 into h_srtl_ynk2lok2lohik2k2hi_627.
try rename H_srtl_ynkloklohikkhi_627 into H_srtl_ynk2lok2lohik2k2hi_627.
ssl_open ((x) == (null)) H_srtl_xnlohi_626.
move=>[phi_srtl_xnlohi_6260] [phi_srtl_xnlohi_6261] [phi_srtl_xnlohi_6262].
move=>[sigma_srtl_xnlohi_626].
subst h_srtl_xnlohi_626.
try rename h_srtl_ynk2lok2lohik2k2hi_627 into h_srtl_ynk2lok2lok2k2_627.
try rename H_srtl_ynk2lok2lohik2k2hi_627 into H_srtl_ynk2lok2lok2k2_627.
try rename h_srtl_xnlohi_626 into h_srtl_xnlo_626.
try rename H_srtl_xnlohi_626 into H_srtl_xnlo_626.
try rename h_srtl_ynk2lok2lok2k2_627 into h_srtl_ynk2k2k2k2_627.
try rename H_srtl_ynk2lok2lok2k2_627 into H_srtl_ynk2k2k2k2_627.
try rename h_srtl_xnlo_626 into h_srtl_xn_626.
try rename H_srtl_xnlo_626 into H_srtl_xn_626.
try rename h_srtl_xn_626 into h_srtl_x_626.
try rename H_srtl_xn_626 into H_srtl_x_626.
try rename h_srtl_ynk2k2k2k2_627 into h_srtl_yk2k2k2k2_627.
try rename H_srtl_ynk2k2k2k2_627 into H_srtl_yk2k2k2k2_627.
try rename h_srtl_nxtylen1ylo11yhi11y_625y into h_srtl_nxtylen1ylo11y_625y.
try rename H_srtl_nxtylen1ylo11yhi11y_625y into H_srtl_nxtylen1ylo11y_625y.
try rename h_srtl_nxtylen1ylo11y_625y into h_srtl_nxtylo11y_625y.
try rename H_srtl_nxtylen1ylo11y_625y into H_srtl_nxtylo11y_625y.
try rename h_srtl_nxtylo11y_625y into h_srtl_nxty_625y.
try rename H_srtl_nxtylo11y_625y into H_srtl_nxty_625y.
try rename h_srtl_nxty_625y into h_srtl__625y.
try rename H_srtl_nxty_625y into H_srtl__625y.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_yk2k2k2k2_627 into h_srtl_y2k2k2k2k2_627.
try rename H_srtl_yk2k2k2k2_627 into H_srtl_y2k2k2k2k2_627.
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
ssl_close 2;
exists (0), (k2), (0), (7), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_srtl_nxtxlen1xlo1xhi1x_625x.
move=>[phi_srtl_xnlohi_6260] [phi_srtl_xnlohi_6261] [phi_srtl_xnlohi_6262] [phi_srtl_xnlohi_6263] [phi_srtl_xnlohi_6264] [phi_srtl_xnlohi_6265] [phi_srtl_xnlohi_6266].
move=>[sigma_srtl_xnlohi_626].
subst h_srtl_xnlohi_626.
move=>H_srtl_nxtxlen1xlo1xhi1x_625x.
try rename h_srtl_ynk2lok2lohik2k2hi_627 into h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename H_srtl_ynk2lok2lohik2k2hi_627 into H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename h_srtl_xnlohi_626 into h_srtl_xnlohi1xvxvxhi1x_626.
try rename H_srtl_xnlohi_626 into H_srtl_xnlohi1xvxvxhi1x_626.
try rename h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename h_srtl_xnlohi1xvxvxhi1x_626 into h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_626.
try rename H_srtl_xnlohi1xvxvxhi1x_626 into H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_626.
try rename h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627.
try rename h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_626 into h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_626.
try rename H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_626 into H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_626.
ssl_read x.
try rename vx into vx2.
try rename h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_626 into h_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_626.
try rename H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_626 into H_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_626.
try rename h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
try rename H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_627 into H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
ssl_branch (((k2) <= (vx2)) && ((vx2) <= (k2))).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_625x into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_nxtxlen1xlo1xhi1x_625x into H_srtl_nxtx2len1xlo1xhi1x_625x.
try rename h_srtl_nxtylen1ylo11yhi11y_625y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1ylo11yhi11y_625y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_625nxty into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_625nxty into H_srtl_nxtx2len1xlo1xhi1x_625x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_625y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_625y.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_close 2;
exists ((1) + (len1x)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (nxty2), (nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_close 2;
exists (len1x), (k2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_frame_unfold.
ssl_branch ((vx2) <= (k2)).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_625x into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_nxtxlen1xlo1xhi1x_625x into H_srtl_nxtx2len1xlo1xhi1x_625x.
try rename h_srtl_x1n2lo2hi2_6261 into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_x1n2lo2hi2_6261 into H_srtl_nxtx2len1xlo1xhi1x_625x.
ssl_call_pre (r :-> k2 \+ h_srtl_nxtx2len1xlo1xhi1x_625x).
ssl_call (k2, len1x, lo1x, hi1x).
exists (h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_srtl_y1n11lo11hi11_6271.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1n11lo11hi11_6271.
store_valid.
try rename h_srtl_y1n11lo11hi11_6271 into h_srtl_y1n11lo11hi1xk2k2hi1x_6271.
try rename H_srtl_y1n11lo11hi11_6271 into H_srtl_y1n11lo11hi1xk2k2hi1x_6271.
try rename h_srtl_y1n11lo11hi1xk2k2hi1x_6271 into h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename H_srtl_y1n11lo11hi1xk2k2hi1x_6271 into H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_6271 into h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_6271 into H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271 into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271 into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename h_srtl_nxtylen1ylo12yhi12y_625y into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename H_srtl_nxtylen1ylo12yhi12y_625y into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> y12 \+ h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271);
sslauto.
ssl_close 2;
exists ((len1x) + (1)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (y12), (h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_6271);
sslauto.
ssl_frame_unfold.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_625x into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_nxtxlen1xlo1xhi1x_625x into H_srtl_nxtx2len1xlo1xhi1x_625x.
try rename h_srtl_nxtylen1ylo11yhi11y_625y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1ylo11yhi11y_625y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_625nxty into h_srtl_nxtx2len1xlo1xhi1x_625x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_625nxty into H_srtl_nxtx2len1xlo1xhi1x_625x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_625y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_627.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into h_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_625y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_625y into H_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_625y.
ssl_write x.
ssl_write_post x.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> k2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_close 2;
exists ((1) + (len1x)), (k2), ((if (hi1x) <= (vx2) then vx2 else hi1x)), ((if (vx2) <= (lo1x) then vx2 else lo1x)), (nxty2), (nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_625x);
sslauto.
ssl_frame_unfold.
Qed.