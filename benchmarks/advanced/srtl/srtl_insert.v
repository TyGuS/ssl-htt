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

Lemma pure65 : (0) <= (0). intros; hammer. Qed.
Hint Resolve pure65: ssl_pure.
Lemma pure66 : (1) = (1). intros; hammer. Qed.
Hint Resolve pure66: ssl_pure.
Lemma pure67 (k2 : nat) : (0) <= (k2) -> (k2) <= (7) -> ((if (0) <= (k2) then k2 else 0)) = ((if (0) <= (k2) then k2 else 0)). intros; hammer. Qed.
Hint Resolve pure67: ssl_pure.
Lemma pure68 (k2 : nat) : (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= (7) then k2 else 7)) = ((if (k2) <= (7) then k2 else 7)). intros; hammer. Qed.
Hint Resolve pure68: ssl_pure.
Lemma pure69 (len1x : nat) : (0) <= (len1x) -> (0) <= ((1) + (len1x)) -> (((1) + (len1x)) + (1)) = ((1) + ((1) + (len1x))). intros; hammer. Qed.
Hint Resolve pure69: ssl_pure.
Lemma pure70 (k2 : nat) (vx2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx2 <= lo1x) eqn:H6;
  destruct (k2 <= lo1x) eqn:H7;
  sauto.
Qed.
Hint Resolve pure70: ssl_pure.
Lemma pure71 (k2 : nat) (lo1x : nat) (vx2 : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (k2) <= (lo1x).
  (* intros; hammer. *)
  intros.
  exact (leq_trans H2 H).
Qed.
Hint Resolve pure71: ssl_pure.
Lemma pure72 (hi1x : nat) (vx2 : nat) (k2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))).
  (* intros; hammer. *)
  intros.
  destruct (hi1x <= vx2) eqn:H6;
  destruct (hi1x <= k2) eqn:H7;
  sauto.
Qed.
Hint Resolve pure72: ssl_pure.
Lemma pure73 (vx2 : nat) (k2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure73: ssl_pure.
Lemma pure74 (len1x : nat) : (0) <= (len1x) -> (0) <= ((1) + (len1x)) -> (0) <= ((len1x) + (1)). intros; hammer. Qed.
Hint Resolve pure74: ssl_pure.
Lemma pure75 (len1x : nat) : (0) <= (len1x) -> (0) <= ((1) + (len1x)) -> (((1) + (len1x)) + (1)) = ((1) + ((len1x) + (1))). intros; hammer. Qed.
Hint Resolve pure75: ssl_pure.
Lemma pure76 (k2 : nat) (vx2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx2 <= lo1x) eqn:H6;
  destruct (k2 <= lo1x) eqn:H7;
  sauto.
Qed.
Hint Resolve pure76: ssl_pure.
Lemma pure77 (hi1x : nat) (vx2 : nat) (k2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2) then vx2 else (if (hi1x) <= (k2) then k2 else hi1x))).
  (* intros; hammer. Qed. *)
  intros.
  destruct (hi1x <= vx2) eqn:H6;
  destruct (hi1x <= k2) eqn:H7;
  sauto.
Qed.
Hint Resolve pure77: ssl_pure.
Lemma pure78 (vx2 : nat) (k2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (vx2) <= (k2) -> (0) <= (vx2) -> (~~ ((k2) <= (vx2))) || (~~ ((vx2) <= (k2))) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure78: ssl_pure.
Lemma pure79 (len1x : nat) : (0) <= (len1x) -> (0) <= ((1) + (len1x)) -> (((1) + (len1x)) + (1)) = ((1) + ((1) + (len1x))). intros; hammer. Qed.
Hint Resolve pure79: ssl_pure.
Lemma pure80 (hi1x : nat) (vx2 : nat) (k2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))) = ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))). intros; hammer. Qed.
Hint Resolve pure80: ssl_pure.
Lemma pure81 (k2 : nat) (vx2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure81: ssl_pure.
Lemma pure82 (k2 : nat) (vx2 : nat) (lo1x : nat) : (vx2) <= (lo1x) -> (0) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((vx2) <= (k2)) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))). intros; hammer. Qed.
Hint Resolve pure82: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_549,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> k \+ h_srtl_xnlohi_549 /\ srtl x n lo hi h_srtl_xnlohi_549,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_550,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((n) + (1)) /\ h = r :-> y \+ h_srtl_yn1lo1hi1_550 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_550
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
ex_elim h_srtl_xnlohi_549.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_549.
ssl_ghostelim_post.
try rename h_srtl_yn1lo1hi1_550 into h_srtl_yn1lo1hikkhi_550.
try rename H_srtl_yn1lo1hi1_550 into H_srtl_yn1lo1hikkhi_550.
try rename h_srtl_yn1lo1hikkhi_550 into h_srtl_yn1kloklohikkhi_550.
try rename H_srtl_yn1lo1hikkhi_550 into H_srtl_yn1kloklohikkhi_550.
try rename h_srtl_yn1kloklohikkhi_550 into h_srtl_ynkloklohikkhi_550.
try rename H_srtl_yn1kloklohikkhi_550 into H_srtl_ynkloklohikkhi_550.
ssl_read r.
try rename k into k2.
try rename h_srtl_ynkloklohikkhi_550 into h_srtl_ynk2lok2lohik2k2hi_550.
try rename H_srtl_ynkloklohikkhi_550 into H_srtl_ynk2lok2lohik2k2hi_550.
ssl_open ((x) == (null)) H_srtl_xnlohi_549.
move=>[phi_srtl_xnlohi_5490] [phi_srtl_xnlohi_5491] [phi_srtl_xnlohi_5492].
move=>[sigma_srtl_xnlohi_549].
subst h_srtl_xnlohi_549.
try rename h_srtl_ynk2lok2lohik2k2hi_550 into h_srtl_ynk2lok2lok2k2_550.
try rename H_srtl_ynk2lok2lohik2k2hi_550 into H_srtl_ynk2lok2lok2k2_550.
try rename h_srtl_xnlohi_549 into h_srtl_xnlo_549.
try rename H_srtl_xnlohi_549 into H_srtl_xnlo_549.
try rename h_srtl_ynk2lok2lok2k2_550 into h_srtl_ynk2k2k2k2_550.
try rename H_srtl_ynk2lok2lok2k2_550 into H_srtl_ynk2k2k2k2_550.
try rename h_srtl_xnlo_549 into h_srtl_xn_549.
try rename H_srtl_xnlo_549 into H_srtl_xn_549.
try rename h_srtl_ynk2k2k2k2_550 into h_srtl_yk2k2k2k2_550.
try rename H_srtl_ynk2k2k2k2_550 into H_srtl_yk2k2k2k2_550.
try rename h_srtl_xn_549 into h_srtl_x_549.
try rename H_srtl_xn_549 into H_srtl_x_549.
try rename h_srtl_nxtylen1ylo11yhi11y_548y into h_srtl_nxtylen1ylo11y_548y.
try rename H_srtl_nxtylen1ylo11yhi11y_548y into H_srtl_nxtylen1ylo11y_548y.
try rename h_srtl_nxtylen1ylo11y_548y into h_srtl_nxtylo11y_548y.
try rename H_srtl_nxtylen1ylo11y_548y into H_srtl_nxtylo11y_548y.
try rename h_srtl_nxtylo11y_548y into h_srtl_nxty_548y.
try rename H_srtl_nxtylo11y_548y into H_srtl_nxty_548y.
try rename h_srtl_nxty_548y into h_srtl__548y.
try rename H_srtl_nxty_548y into H_srtl__548y.
ssl_alloc y2.
try rename y into y2.
try rename h_srtl_yk2k2k2k2_550 into h_srtl_y2k2k2k2k2_550.
try rename H_srtl_yk2k2k2k2_550 into H_srtl_y2k2k2k2k2_550.
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
ex_elim h_srtl_nxtxlen1xlo1xhi1x_548x.
move=>[phi_srtl_xnlohi_5490] [phi_srtl_xnlohi_5491] [phi_srtl_xnlohi_5492] [phi_srtl_xnlohi_5493] [phi_srtl_xnlohi_5494] [phi_srtl_xnlohi_5495] [phi_srtl_xnlohi_5496].
move=>[sigma_srtl_xnlohi_549].
subst h_srtl_xnlohi_549.
move=>H_srtl_nxtxlen1xlo1xhi1x_548x.
try rename h_srtl_ynk2lok2lohik2k2hi_550 into h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename H_srtl_ynk2lok2lohik2k2hi_550 into H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename h_srtl_xnlohi_549 into h_srtl_xnlohi1xvxvxhi1x_549.
try rename H_srtl_xnlohi_549 into H_srtl_xnlohi1xvxvxhi1x_549.
try rename h_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename H_srtl_ynk2lok2lohi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename h_srtl_xnlohi1xvxvxhi1x_549 into h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_549.
try rename H_srtl_xnlohi1xvxvxhi1x_549 into H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_549.
try rename h_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename H_srtl_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550.
try rename h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_549 into h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_549.
try rename H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_549 into H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_549.
ssl_read x.
try rename vx into vx2.
try rename h_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
try rename H_srtl_ylen1xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi1xvxvxhi1xk2k2hi1xvxvxhi1x_550 into H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
try rename h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_549 into h_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_549.
try rename H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_549 into H_srtl_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_549.
ssl_branch (((k2) <= (vx2)) && ((vx2) <= (k2))).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_548x into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_nxtxlen1xlo1xhi1x_548x into H_srtl_nxtx2len1xlo1xhi1x_548x.
try rename h_srtl_nxtylen1ylo11yhi11y_548y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1ylo11yhi11y_548y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_548nxty into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_548nxty into H_srtl_nxtx2len1xlo1xhi1x_548x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_548y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxty2len1xk2lo1xk2lo1xhi1xk2k2hi1x_548y.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_close 2;
exists ((1) + (len1x)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (nxty2), (nxty2 :-> k2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_close 2;
exists (len1x), (k2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_frame_unfold.
ssl_branch ((vx2) <= (k2)).
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_548x into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_nxtxlen1xlo1xhi1x_548x into H_srtl_nxtx2len1xlo1xhi1x_548x.
try rename h_srtl_x1n2lo2hi2_5491 into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_x1n2lo2hi2_5491 into H_srtl_nxtx2len1xlo1xhi1x_548x.
ssl_call_pre (r :-> k2 \+ h_srtl_nxtx2len1xlo1xhi1x_548x).
ssl_call (k2, len1x, lo1x, hi1x).
exists (h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_srtl_y1n11lo11hi11_5501.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1n11lo11hi11_5501.
store_valid.
try rename h_srtl_y1n11lo11hi11_5501 into h_srtl_y1n11lo11hi1xk2k2hi1x_5501.
try rename H_srtl_y1n11lo11hi11_5501 into H_srtl_y1n11lo11hi1xk2k2hi1x_5501.
try rename h_srtl_y1n11lo11hi1xk2k2hi1x_5501 into h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename H_srtl_y1n11lo11hi1xk2k2hi1x_5501 into H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename h_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5501 into h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename H_srtl_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_5501 into H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501 into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename H_srtl_y1len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501 into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename h_srtl_nxtylen1ylo12yhi12y_548y into h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename H_srtl_nxtylen1ylo12yhi12y_548y into H_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> vx2 \+ x .+ 1 :-> y12 \+ h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501);
sslauto.
ssl_close 2;
exists ((len1x) + (1)), (vx2), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (y12), (h_srtl_y12len1xk2lo1xk2lo1xhi1xk2k2hi1x_5501);
sslauto.
ssl_frame_unfold.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_srtl_nxtxlen1xlo1xhi1x_548x into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_nxtxlen1xlo1xhi1x_548x into H_srtl_nxtx2len1xlo1xhi1x_548x.
try rename h_srtl_nxtylen1ylo11yhi11y_548y into h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1ylo11yhi11y_548y into H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1ylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename H_srtl_nxtylen1nxtylo11yhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y.
try rename h_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_548nxty into h_srtl_nxtx2len1xlo1xhi1x_548x.
try rename H_srtl_nxtnxtylen1nxtylo11nxtyhi11nxty_548nxty into H_srtl_nxtx2len1xlo1xhi1x_548x.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y into h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi11nxtyvnxtyvnxtyhi11nxty_548y into H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1nxtyvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1xvnxtylo11nxtyvnxtylo11nxtyhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename h_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into h_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
try rename H_srtl_ylen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550 into H_srtl_xlen1xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi1xvx2vx2hi1xk2k2hi1xvx2vx2hi1x_550.
ssl_alloc nxty2.
try rename nxty into nxty2.
try rename h_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
try rename H_srtl_nxtylen1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write r.
ssl_write_post r.
ssl_write (nxty2 .+ 1).
ssl_write_post (nxty2 .+ 1).
try rename h_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into h_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_548y.
try rename H_srtl_nxty2len1xvnxtylo1xvnxtylo1xhi1xvnxtyvnxtyhi1x_548y into H_srtl_nxty2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_548y.
ssl_write x.
ssl_write_post x.
ssl_write nxty2.
ssl_write_post nxty2.
ssl_emp;
exists ((if ((if (hi1x) <= (vx2) then vx2 else hi1x)) <= (k2) then k2 else (if (hi1x) <= (vx2) then vx2 else hi1x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> k2 \+ x .+ 1 :-> nxty2 \+ nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_close 2;
exists ((1) + (len1x)), (k2), ((if (hi1x) <= (vx2) then vx2 else hi1x)), ((if (vx2) <= (lo1x) then vx2 else lo1x)), (nxty2), (nxty2 :-> vx2 \+ nxty2 .+ 1 :-> nxtx2 \+ h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_srtl_nxtx2len1xlo1xhi1x_548x);
sslauto.
ssl_frame_unfold.
Qed.
