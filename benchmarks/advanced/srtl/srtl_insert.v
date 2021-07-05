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

Lemma pure1 : (1) = (1). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 (k1 : nat) : (k1) <= (7) -> (0) <= (k1) -> ((if (0) <= (k1) then k1 else 0)) = ((if (0) <= (k1) then k1 else 0)). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (k1 : nat) : (k1) <= (7) -> (0) <= (k1) -> ((if (k1) <= (7) then k1 else 7)) = ((if (k1) <= (7) then k1 else 7)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (len1x : nat) : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (0) <= ((len1x) + (1)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (len1x : nat) : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) = ((1) + ((len1x) + (1))). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (vx1 : nat) (k1 : nat) (lo1x : nat) : (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (vx1) <= (k1) -> (0) <= (k1) -> (vx1) <= ((if (k1) <= (lo1x) then k1 else lo1x)). intros; hammer. Qed.
Hint Resolve pure6: ssl_pure.
Lemma pure7 (hi1x : nat) (vx1 : nat) (k1 : nat) (lo1x : nat) : (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (vx1) <= (k1) -> (0) <= (k1) -> ((if ((if (hi1x) <= (vx1) then vx1 else hi1x)) <= (k1) then k1 else (if (hi1x) <= (vx1) then vx1 else hi1x))) = ((if ((if (hi1x) <= (k1) then k1 else hi1x)) <= (vx1) then vx1 else (if (hi1x) <= (k1) then k1 else hi1x))).
  (* intros; hammer. *)
  intros.
  destruct (hi1x <= vx1) eqn:H5;
  destruct (hi1x <= k1) eqn:H6;
  destruct (vx1 <= k1) eqn:H7;
  sauto.
Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 (k1 : nat) (vx1 : nat) (lo1x : nat) : (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (vx1) <= (k1) -> (0) <= (k1) -> ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))) = ((if (vx1) <= ((if (k1) <= (lo1x) then k1 else lo1x)) then vx1 else (if (k1) <= (lo1x) then k1 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx1 <= lo1x) eqn:H5;
  destruct (k1 <= lo1x) eqn:H6;
  sauto.
Qed.
Hint Resolve pure8: ssl_pure.
Lemma pure9 (len1x : nat) : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (0) <= ((len1x) + (1)). intros; hammer. Qed.
Hint Resolve pure9: ssl_pure.
Lemma pure10 (len1x : nat) : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> (((1) + (len1x)) + (1)) = ((1) + ((len1x) + (1))). intros; hammer. Qed.
Hint Resolve pure10: ssl_pure.
Lemma pure11 (k1 : nat) (vx1 : nat) (lo1x : nat) : ~~ ((vx1) <= (k1)) -> (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (0) <= (k1) -> (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)).
  (* intros; hammer. *)
  intros.
  rewrite -ltnNge in H. sauto.
Qed.
Hint Resolve pure11: ssl_pure.
Lemma pure12 (k1 : nat) (vx1 : nat) (lo1x : nat) : ~~ ((vx1) <= (k1)) -> (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (0) <= (k1) -> ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))) = ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx1 <= lo1x) eqn:H5;
  sauto.
Qed.
Hint Resolve pure12: ssl_pure.
Lemma pure13 (hi1x : nat) (vx1 : nat) (k1 : nat) (lo1x : nat) : ~~ ((vx1) <= (k1)) -> (vx1) <= (7) -> (k1) <= (7) -> (vx1) <= (lo1x) -> (0) <= (vx1) -> (0) <= (k1) -> ((if ((if (hi1x) <= (vx1) then vx1 else hi1x)) <= (k1) then k1 else (if (hi1x) <= (vx1) then vx1 else hi1x))) = ((if ((if (hi1x) <= (vx1) then vx1 else hi1x)) <= (k1) then k1 else (if (hi1x) <= (vx1) then vx1 else hi1x))).
  (* intros; hammer. *)
  intros.
  destruct (hi1x <= vx1) eqn:H5;
  sauto.
Qed.
Hint Resolve pure13: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_2,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> (k) \+ h_srtl_xnlohi_2 /\ srtl x n lo hi h_srtl_xnlohi_2,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_3,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((n) + (1)) /\ h = r :-> (y) \+ h_srtl_yn1lo1hi1_3 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_3
    ]).

Program Definition srtl_insert : srtl_insert_type :=
  Fix (fun (srtl_insert : srtl_insert_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      k1 <-- @read nat r;
      if (x) == (null)
      then
        y1 <-- allocb null 2;
        r ::= y1;;
        (y1 .+ 1) ::= null;;
        y1 ::= k1;;
        ret tt
      else
        vx1 <-- @read nat x;
        nxtx1 <-- @read ptr (x .+ 1);
        if (vx1) <= (k1)
        then
          srtl_insert (nxtx1, r);;
          y11 <-- @read ptr r;
          r ::= x;;
          (x .+ 1) ::= y11;;
          ret tt
        else
          r ::= vx1;;
          srtl_insert (nxtx1, r);;
          y11 <-- @read ptr r;
          r ::= x;;
          (x .+ 1) ::= y11;;
          x ::= k1;;
          ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[k n] lo] hi].
ex_elim h_srtl_xnlohi_2.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_srtl_xnlohi_2.
ssl_ghostelim_post.
try rename h_srtl_yn1lo1hi1_3 into h_srtl_yn1lo1hikkhi_3.
try rename H_srtl_yn1lo1hi1_3 into H_srtl_yn1lo1hikkhi_3.
try rename h_srtl_yn1lo1hikkhi_3 into h_srtl_yn1kloklohikkhi_3.
try rename H_srtl_yn1lo1hikkhi_3 into H_srtl_yn1kloklohikkhi_3.
try rename h_srtl_yn1kloklohikkhi_3 into h_srtl_ynkloklohikkhi_3.
try rename H_srtl_yn1kloklohikkhi_3 into H_srtl_ynkloklohikkhi_3.
ssl_read r.
try rename k into k1.
try rename h_srtl_ynkloklohikkhi_3 into h_srtl_ynk1lok1lohik1k1hi_3.
try rename H_srtl_ynkloklohikkhi_3 into H_srtl_ynk1lok1lohik1k1hi_3.
ssl_open ((x) == (null)) H_srtl_xnlohi_2.
move=>[phi_srtl_xnlohi_20] [phi_srtl_xnlohi_21] [phi_srtl_xnlohi_22].
move=>[sigma_srtl_xnlohi_2].
subst h_srtl_xnlohi_2.
try rename h_srtl_xnlohi_2 into h_srtl_xnlo_2.
try rename H_srtl_xnlohi_2 into H_srtl_xnlo_2.
try rename h_srtl_ynk1lok1lohik1k1hi_3 into h_srtl_ynk1lok1lok1k1_3.
try rename H_srtl_ynk1lok1lohik1k1hi_3 into H_srtl_ynk1lok1lok1k1_3.
try rename h_srtl_ynk1lok1lok1k1_3 into h_srtl_ynk1k1k1k1_3.
try rename H_srtl_ynk1lok1lok1k1_3 into H_srtl_ynk1k1k1k1_3.
try rename h_srtl_xnlo_2 into h_srtl_xn_2.
try rename H_srtl_xnlo_2 into H_srtl_xn_2.
try rename h_srtl_xn_2 into h_srtl_x_2.
try rename H_srtl_xn_2 into H_srtl_x_2.
try rename h_srtl_ynk1k1k1k1_3 into h_srtl_yk1k1k1k1_3.
try rename H_srtl_ynk1k1k1k1_3 into H_srtl_yk1k1k1k1_3.
try rename h_srtl_nxtylen1ylo11yhi11y_1y into h_srtl_nxtylen1ylo11y_1y.
try rename H_srtl_nxtylen1ylo11yhi11y_1y into H_srtl_nxtylen1ylo11y_1y.
try rename h_srtl_nxtylen1ylo11y_1y into h_srtl_nxtylo11y_1y.
try rename H_srtl_nxtylen1ylo11y_1y into H_srtl_nxtylo11y_1y.
try rename h_srtl_nxtylo11y_1y into h_srtl_nxty_1y.
try rename H_srtl_nxtylo11y_1y into H_srtl_nxty_1y.
try rename h_srtl_nxty_1y into h_srtl__1y.
try rename H_srtl_nxty_1y into H_srtl__1y.
ssl_alloc y1.
try rename y into y1.
try rename h_srtl_yk1k1k1k1_3 into h_srtl_y1k1k1k1k1_3.
try rename H_srtl_yk1k1k1k1_3 into H_srtl_y1k1k1k1k1_3.
ssl_write r.
ssl_write_post r.
ssl_write (y1 .+ 1).
ssl_write_post (y1 .+ 1).
ssl_write y1.
ssl_write_post y1.
ssl_emp;
exists ((if (0) <= (k1) then k1 else 0)), ((if (k1) <= (7) then k1 else 7)), ((0) + (1)), (y1);
exists (y1 :-> (k1) \+ y1 .+ 1 :-> (null));
sslauto.
ssl_close 2;
exists (0), (k1), (0), (7), (null), (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_srtl_nxtxlen1xlo1xhi1x_1x.
move=>[phi_srtl_xnlohi_20] [phi_srtl_xnlohi_21] [phi_srtl_xnlohi_22] [phi_srtl_xnlohi_23] [phi_srtl_xnlohi_24] [phi_srtl_xnlohi_25] [phi_srtl_xnlohi_26].
move=>[sigma_srtl_xnlohi_2].
subst h_srtl_xnlohi_2.
move=>H_srtl_nxtxlen1xlo1xhi1x_1x.
try rename h_srtl_xnlohi_2 into h_srtl_xnlohi1xvxvxhi1x_2.
try rename H_srtl_xnlohi_2 into H_srtl_xnlohi1xvxvxhi1x_2.
try rename h_srtl_ynk1lok1lohik1k1hi_3 into h_srtl_ynk1lok1lohi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
try rename H_srtl_ynk1lok1lohik1k1hi_3 into H_srtl_ynk1lok1lohi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
try rename h_srtl_ynk1lok1lohi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into h_srtl_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
try rename H_srtl_ynk1lok1lohi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into H_srtl_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
try rename h_srtl_xnlohi1xvxvxhi1x_2 into h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename H_srtl_xnlohi1xvxvxhi1x_2 into H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename h_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_2 into h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename H_srtl_xnvxlo1xvxlo1xhi1xvxvxhi1x_2 into H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename h_srtl_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into h_srtl_ylen1xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
try rename H_srtl_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into H_srtl_ylen1xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3.
ssl_read x.
try rename vx into vx1.
try rename h_srtl_ylen1xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into h_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
try rename H_srtl_ylen1xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi1xvxvxhi1xk1k1hi1xvxvxhi1x_3 into H_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
try rename h_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2 into h_srtl_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
try rename H_srtl_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2 into H_srtl_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
ssl_read (x .+ 1).
try rename nxtx into nxtx1.
try rename h_srtl_nxtxlen1xlo1xhi1x_1x into h_srtl_nxtx1len1xlo1xhi1x_1x.
try rename H_srtl_nxtxlen1xlo1xhi1x_1x into H_srtl_nxtx1len1xlo1xhi1x_1x.
ssl_branch ((vx1) <= (k1)).
try rename h_srtl_x1n2lo2hi2_21 into h_srtl_nxtx1len1xlo1xhi1x_1x.
try rename H_srtl_x1n2lo2hi2_21 into H_srtl_nxtx1len1xlo1xhi1x_1x.
ssl_call_pre (r :-> (k1) \+ h_srtl_nxtx1len1xlo1xhi1x_1x).
ssl_call (k1, len1x, lo1x, hi1x).
exists (h_srtl_nxtx1len1xlo1xhi1x_1x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_srtl_y1n11lo11hi11_31.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1n11lo11hi11_31.
store_valid.
try rename h_srtl_y1n11lo11hi11_31 into h_srtl_y1n11lo11hi1xk1k1hi1x_31.
try rename H_srtl_y1n11lo11hi11_31 into H_srtl_y1n11lo11hi1xk1k1hi1x_31.
try rename h_srtl_y1n11lo11hi1xk1k1hi1x_31 into h_srtl_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename H_srtl_y1n11lo11hi1xk1k1hi1x_31 into H_srtl_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename h_srtl_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_31 into h_srtl_y1len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename H_srtl_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_31 into H_srtl_y1len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
ssl_read r.
try rename y1 into y11.
try rename h_srtl_y1len1xk1lo1xk1lo1xhi1xk1k1hi1x_31 into h_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename H_srtl_y1len1xk1lo1xk1lo1xhi1xk1k1hi1x_31 into H_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename h_srtl_nxtylen1ylo12yhi12y_1y into h_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename H_srtl_nxtylen1ylo12yhi12y_1y into H_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31.
try rename h_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3 into h_srtl_xlen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
try rename H_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3 into H_srtl_xlen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
ssl_write r.
ssl_write_post r.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_emp;
exists ((if ((if (hi1x) <= (vx1) then vx1 else hi1x)) <= (k1) then k1 else (if (hi1x) <= (vx1) then vx1 else hi1x))), ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> (vx1) \+ x .+ 1 :-> (y11) \+ h_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31);
sslauto.
ssl_close 2;
exists ((len1x) + (1)), (vx1), ((if (hi1x) <= (k1) then k1 else hi1x)), ((if (k1) <= (lo1x) then k1 else lo1x)), (y11), (h_srtl_y11len1xk1lo1xk1lo1xhi1xk1k1hi1x_31);
sslauto.
ssl_frame_unfold.
try rename h_srtl_x1n2lo2hi2_21 into h_srtl_nxtx1len1xlo1xhi1x_1x.
try rename H_srtl_x1n2lo2hi2_21 into H_srtl_nxtx1len1xlo1xhi1x_1x.
ssl_write r.
ssl_call_pre (r :-> (vx1) \+ h_srtl_nxtx1len1xlo1xhi1x_1x).
ssl_call (vx1, len1x, lo1x, hi1x).
exists (h_srtl_nxtx1len1xlo1xhi1x_1x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_srtl_y1n11lo11hi11_31.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1n11lo11hi11_31.
store_valid.
try rename h_srtl_y1n11lo11hi11_31 into h_srtl_y1n11lo11hi1xvx1vx1hi1x_31.
try rename H_srtl_y1n11lo11hi11_31 into H_srtl_y1n11lo11hi1xvx1vx1hi1x_31.
try rename h_srtl_y1n11lo11hi1xvx1vx1hi1x_31 into h_srtl_y1n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename H_srtl_y1n11lo11hi1xvx1vx1hi1x_31 into H_srtl_y1n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename h_srtl_y1n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_31 into h_srtl_y1len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename H_srtl_y1n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_31 into H_srtl_y1len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
ssl_read r.
try rename y1 into y11.
try rename h_srtl_y1len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31 into h_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename H_srtl_y1len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31 into H_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename h_srtl_nxtylen1ylo12yhi12y_1y into h_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename H_srtl_nxtylen1ylo12yhi12y_1y into H_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31.
try rename h_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3 into h_srtl_xlen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
try rename H_srtl_ylen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3 into H_srtl_xlen1xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi1xvx1vx1hi1xk1k1hi1xvx1vx1hi1x_3.
ssl_write r.
ssl_write_post r.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write x.
ssl_write_post x.
ssl_emp;
exists ((if ((if (hi1x) <= (vx1) then vx1 else hi1x)) <= (k1) then k1 else (if (hi1x) <= (vx1) then vx1 else hi1x))), ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))), (((1) + (len1x)) + (1)), (x);
exists (x :-> (k1) \+ x .+ 1 :-> (y11) \+ h_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31);
sslauto.
ssl_close 2;
exists ((len1x) + (1)), (k1), ((if (hi1x) <= (vx1) then vx1 else hi1x)), ((if (vx1) <= (lo1x) then vx1 else lo1x)), (y11), (h_srtl_y11len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_31);
sslauto.
ssl_frame_unfold.
Qed.
