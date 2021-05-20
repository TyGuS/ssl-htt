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

Lemma pure1 : (0) <= (0). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 : (1) = (1). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (k2 : nat) : (k2) <= (7) -> (0) <= (k2) -> ((if (0) <= (k2) then k2 else 0)) = ((if (0) <= (k2) then k2 else 0)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (a : nat) : (a) < ((a) + (3)).
  (* intros; hammer. *)
  scongruence use: addSnnS, leq_addr.
Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (k2 : nat) : (k2) <= (7) -> (0) <= (k2) -> ((if (k2) <= (7) then k2 else 7)) = ((if (k2) <= (7) then k2 else 7)). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (sz1x : nat) (sz2x : nat) : (0) <= (sz2x) -> (0) <= (sz1x) -> (0) <= (((1) + (sz1x)) + (sz2x)) -> ((((1) + (sz1x)) + (sz2x)) + (1)) = (((1) + ((sz1x) + (1))) + (sz2x)). intros; hammer. Qed.
Hint Resolve pure6: ssl_pure.
Lemma pure7 (sz1x : nat) (sz2x : nat) : (0) <= (sz2x) -> (0) <= (sz1x) -> (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= ((sz1x) + (1)). intros; hammer. Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 (lo2x : nat) (vx2 : nat) (k2 : nat) (hi1x : nat) (lo1x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= ((if (k2) <= (lo1x) then k2 else lo1x)) then vx2 else (if (k2) <= (lo1x) then k2 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx2 <= lo1x) eqn:H6;
  destruct (k2 <= lo1x) eqn:H7;
  sauto.
Qed.
Hint Resolve pure8: ssl_pure.
Lemma pure9 (lo2x : nat) (vx2 : nat) (k2 : nat) (hi1x : nat) (hi2x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if ((if (hi2x) <= (vx2) then vx2 else hi2x)) <= (k2) then k2 else (if (hi2x) <= (vx2) then vx2 else hi2x))) = ((if (hi2x) <= (vx2) then vx2 else hi2x)).
  (* intros; hammer. *)
  intros; destruct (hi2x <= vx2) eqn:H6; sauto.
Qed.
Hint Resolve pure9: ssl_pure.
Lemma pure10 (hi1x : nat) (k2 : nat) (vx2 : nat) (lo2x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (k2) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> (k2) <= (7) -> ((if (hi1x) <= (k2) then k2 else hi1x)) <= (vx2). intros; hammer. Qed.
Hint Resolve pure10: ssl_pure.
Lemma pure11 (sz2x : nat) (sz1x : nat) : (0) <= (sz2x) -> (0) <= (sz1x) -> (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= ((sz2x) + (1)). intros; hammer. Qed.
Hint Resolve pure11: ssl_pure.
Lemma pure12 (sz1x : nat) (sz2x : nat) : (0) <= (sz2x) -> (0) <= (sz1x) -> (0) <= (((1) + (sz1x)) + (sz2x)) -> ((((1) + (sz1x)) + (sz2x)) + (1)) = (((1) + (sz1x)) + ((sz2x) + (1))). intros; hammer. Qed.
Hint Resolve pure12: ssl_pure.
Lemma pure13 (lo2x : nat) (vx2 : nat) (k2 : nat) (hi1x : nat) (lo1x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((k2) <= (vx2)) -> (k2) <= (7) -> ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))) = ((if (vx2) <= (lo1x) then vx2 else lo1x)).
  (* intros; hammer. *)
  intros.
  destruct (vx2 <= lo1x) eqn:H6; sauto.
Qed.
Hint Resolve pure13: ssl_pure.
Lemma pure14 (lo2x : nat) (vx2 : nat) (k2 : nat) (hi1x : nat) (hi2x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((k2) <= (vx2)) -> (k2) <= (7) -> ((if ((if (hi2x) <= (vx2) then vx2 else hi2x)) <= (k2) then k2 else (if (hi2x) <= (vx2) then vx2 else hi2x))) = ((if ((if (hi2x) <= (k2) then k2 else hi2x)) <= (vx2) then vx2 else (if (hi2x) <= (k2) then k2 else hi2x))).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx2) eqn:H6;
  destruct (hi2x <= k2) eqn:H7;
  sauto.
Qed.
Hint Resolve pure14: ssl_pure.
Lemma pure15 (vx2 : nat) (k2 : nat) (lo2x : nat) (hi1x : nat) : (vx2) <= (lo2x) -> (0) <= (vx2) -> (hi1x) <= (vx2) -> (vx2) <= (7) -> (0) <= (k2) -> ~~ ((k2) <= (vx2)) -> (k2) <= (7) -> (vx2) <= ((if (k2) <= (lo2x) then k2 else lo2x)).
  (* intros; hammer. *)
  intros.
  destruct (k2 <= lo2x) eqn:H6; last by done.
  rewrite -ltnNge in H4; by apply ltnW.
Qed.
Hint Resolve pure15: ssl_pure.

Definition bst_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_bst_xnlohi_a,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = retv :-> (k) \+ h_bst_xnlohi_a /\ bst x n lo hi h_bst_xnlohi_a,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_bst_yn1lo1hi1_b,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((n) + (1)) /\ h = retv :-> (y) \+ h_bst_yn1lo1hi1_b /\ bst y n1 lo1 hi1 h_bst_yn1lo1hi1_b
    ]).

Program Definition bst_insert : bst_insert_type :=
  Fix (fun (bst_insert : bst_insert_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      k2 <-- @read nat retv;
      if (x) == (null)
      then
        y2 <-- allocb null 3;
        retv ::= y2;;
        (y2 .+ 1) ::= null;;
        (y2 .+ 2) ::= null;;
        y2 ::= k2;;
        ret tt
      else
        vx2 <-- @read nat x;
        if (k2) <= (vx2)
        then
          lx2 <-- @read ptr (x .+ 1);
          rx2 <-- @read ptr (x .+ 2);
          bst_insert (lx2, retv);;
          y12 <-- @read ptr retv;
          (x .+ 1) ::= y12;;
          retv ::= x;;
          ret tt
        else
          lx2 <-- @read ptr (x .+ 1);
          rx2 <-- @read ptr (x .+ 2);
          bst_insert (rx2, retv);;
          y12 <-- @read ptr retv;
          (x .+ 2) ::= y12;;
          retv ::= x;;
          ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[k n] lo] hi].
ex_elim h_bst_xnlohi_a.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_bst_xnlohi_a.
ssl_ghostelim_post.
try rename h_bst_yn1lo1hi1_b into h_bst_yn1lo1hi1_a.
try rename H_bst_yn1lo1hi1_b into H_bst_yn1lo1hi1_a.
try rename h_bst_yn1lo1hi1_a into h_bst_yn1lo1hikkhi_a.
try rename H_bst_yn1lo1hi1_a into H_bst_yn1lo1hikkhi_a.
try rename h_bst_yn1lo1hikkhi_a into h_bst_yn1kloklohikkhi_a.
try rename H_bst_yn1lo1hikkhi_a into H_bst_yn1kloklohikkhi_a.
try rename h_bst_yn1kloklohikkhi_a into h_bst_ynkloklohikkhi_a.
try rename H_bst_yn1kloklohikkhi_a into H_bst_ynkloklohikkhi_a.
ssl_read retv.
try rename k into k2.
try rename h_bst_ynkloklohikkhi_a into h_bst_ynk2lok2lohik2k2hi_a.
try rename H_bst_ynkloklohikkhi_a into H_bst_ynk2lok2lohik2k2hi_a.
ssl_open ((x) == (null)) H_bst_xnlohi_a.
move=>[phi_bst_xnlohi_a0] [phi_bst_xnlohi_a1] [phi_bst_xnlohi_a2].
move=>[sigma_bst_xnlohi_a].
subst h_bst_xnlohi_a.
try rename h_bst_xnlohi_a into h_bst_xnlo_a.
try rename H_bst_xnlohi_a into H_bst_xnlo_a.
try rename h_bst_ynk2lok2lohik2k2hi_a into h_bst_ynk2lok2lok2k2_a.
try rename H_bst_ynk2lok2lohik2k2hi_a into H_bst_ynk2lok2lok2k2_a.
try rename h_bst_xnlo_a into h_bst_xn_a.
try rename H_bst_xnlo_a into H_bst_xn_a.
try rename h_bst_ynk2lok2lok2k2_a into h_bst_ynk2k2k2k2_a.
try rename H_bst_ynk2lok2lok2k2_a into H_bst_ynk2k2k2k2_a.
try rename h_bst_xn_a into h_bst_x_a.
try rename H_bst_xn_a into H_bst_x_a.
try rename h_bst_ynk2k2k2k2_a into h_bst_yk2k2k2k2_a.
try rename H_bst_ynk2k2k2k2_a into H_bst_yk2k2k2k2_a.
try rename h_bst_lysz1ylo11yhi11y_521y into h_bst_lysz1ylo11y_521y.
try rename H_bst_lysz1ylo11yhi11y_521y into H_bst_lysz1ylo11y_521y.
try rename h_bst_lysz1ylo11y_521y into h_bst_lysz1y_521y.
try rename H_bst_lysz1ylo11y_521y into H_bst_lysz1y_521y.
try rename h_bst_lysz1y_521y into h_bst_sz1y_521y.
try rename H_bst_lysz1y_521y into H_bst_sz1y_521y.
try rename h_bst_sz1y_521y into h_bst__521y.
try rename H_bst_sz1y_521y into H_bst__521y.
try rename h_bst_rysz2ylo2yhi2y_522y into h_bst_rysz2ylo2y_522y.
try rename H_bst_rysz2ylo2yhi2y_522y into H_bst_rysz2ylo2y_522y.
try rename h_bst_rysz2ylo2y_522y into h_bst_rysz2y_522y.
try rename H_bst_rysz2ylo2y_522y into H_bst_rysz2y_522y.
try rename h_bst_rysz2y_522y into h_bst_sz2y_522y.
try rename H_bst_rysz2y_522y into H_bst_sz2y_522y.
try rename h_bst_sz2y_522y into h_bst__522y.
try rename H_bst_sz2y_522y into H_bst__522y.
ssl_alloc y2.
try rename y into y2.
try rename h_bst_yk2k2k2k2_a into h_bst_y2k2k2k2k2_a.
try rename H_bst_yk2k2k2k2_a into H_bst_y2k2k2k2k2_a.
ssl_write retv.
ssl_write_post retv.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write (y2 .+ 2).
ssl_write_post (y2 .+ 2).
try rename h_bst__521y into h_bst__a.
try rename H_bst__521y into H_bst__a.
try rename h_bst__522y into h_bst__a.
try rename H_bst__522y into H_bst__a.
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists ((if (0) <= (k2) then k2 else 0)), ((if (k2) <= (7) then k2 else 7)), ((0) + (1)), (y2);
exists (y2 :-> (k2) \+ y2 .+ 1 :-> (null) \+ y2 .+ 2 :-> (null));
sslauto.
ssl_close 2;
exists (0), (0), (k2), (0), (0), (7), (7), (null), (null), (empty), (empty);
sslauto.
ssl_close 1;
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1x sz2x vx hi2x hi1x.
ex_elim lo1x lo2x lx rx.
ex_elim h_bst_lxsz1xlo1xhi1x_521x h_bst_rxsz2xlo2xhi2x_522x.
move=>[phi_bst_xnlohi_a0] [phi_bst_xnlohi_a1] [phi_bst_xnlohi_a2] [phi_bst_xnlohi_a3] [phi_bst_xnlohi_a4] [phi_bst_xnlohi_a5] [phi_bst_xnlohi_a6] [phi_bst_xnlohi_a7] [phi_bst_xnlohi_a8].
move=>[sigma_bst_xnlohi_a].
subst h_bst_xnlohi_a.
move=>[H_bst_lxsz1xlo1xhi1x_521x H_bst_rxsz2xlo2xhi2x_522x].
try rename h_bst_xnlohi_a into h_bst_xnlohi2xvxvxhi2x_a.
try rename H_bst_xnlohi_a into H_bst_xnlohi2xvxvxhi2x_a.
try rename h_bst_ynk2lok2lohik2k2hi_a into h_bst_ynk2lok2lohi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename H_bst_ynk2lok2lohik2k2hi_a into H_bst_ynk2lok2lohi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename h_bst_xnlohi2xvxvxhi2x_a into h_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xnlohi2xvxvxhi2x_a into H_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename h_bst_ynk2lok2lohi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into h_bst_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename H_bst_ynk2lok2lohi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into H_bst_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename h_bst_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into h_bst_ysz1xsz2xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename H_bst_ynk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into H_bst_ysz1xsz2xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a.
try rename h_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
ssl_read x.
try rename vx into vx2.
try rename h_bst_ysz1xsz2xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into h_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
try rename H_bst_ysz1xsz2xk2vxlo1xvxlo1xk2vxlo1xvxlo1xhi2xvxvxhi2xk2k2hi2xvxvxhi2x_a into H_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
try rename h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvx2lo1xvx2lo1xhi2xvx2vx2hi2x_a.
try rename H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvx2lo1xvx2lo1xhi2xvx2vx2hi2x_a.
ssl_branch ((k2) <= (vx2)).
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_bst_lxsz1xlo1xhi1x_521x into h_bst_lx2sz1xlo1xhi1x_521x.
try rename H_bst_lxsz1xlo1xhi1x_521x into H_bst_lx2sz1xlo1xhi1x_521x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_bst_rxsz2xlo2xhi2x_522x into h_bst_rx2sz2xlo2xhi2x_522x.
try rename H_bst_rxsz2xlo2xhi2x_522x into H_bst_rx2sz2xlo2xhi2x_522x.
try rename h_bst_x1n2lo2hi2_a1 into h_bst_lx2sz1xlo1xhi1x_521x.
try rename H_bst_x1n2lo2hi2_a1 into H_bst_lx2sz1xlo1xhi1x_521x.
ssl_call_pre (retv :-> (k2) \+ h_bst_lx2sz1xlo1xhi1x_521x).
ssl_call (k2, sz1x, lo1x, hi1x).
exists (h_bst_lx2sz1xlo1xhi1x_521x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_bst_y1n11lo11hi11_b1.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_bst_y1n11lo11hi11_b1.
store_valid.
try rename h_bst_y1n11lo11hi11_b1 into h_bst_y1n11lo11hi11_521x.
try rename H_bst_y1n11lo11hi11_b1 into H_bst_y1n11lo11hi11_521x.
try rename h_bst_y1n11lo11hi11_521x into h_bst_y1n11lo11hi1xk2k2hi1x_521x.
try rename H_bst_y1n11lo11hi11_521x into H_bst_y1n11lo11hi1xk2k2hi1x_521x.
try rename h_bst_y1n11lo11hi1xk2k2hi1x_521x into h_bst_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename H_bst_y1n11lo11hi1xk2k2hi1x_521x into H_bst_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename h_bst_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_521x into h_bst_y1sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename H_bst_y1n11k2lo1xk2lo1xhi1xk2k2hi1x_521x into H_bst_y1sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
ssl_read retv.
try rename y1 into y12.
try rename h_bst_y1sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x into h_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename H_bst_y1sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x into H_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename h_bst_lysz1ylo12yhi12y_521y into h_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename H_bst_lysz1ylo12yhi12y_521y into H_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x.
try rename h_bst_rysz2ylo21yhi21y_522y into h_bst_rx2sz2xlo2xhi2x_522x.
try rename H_bst_rysz2ylo21yhi21y_522y into H_bst_rx2sz2xlo2xhi2x_522x.
try rename h_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a into h_bst_xsz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
try rename H_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a into H_bst_xsz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if ((if (hi2x) <= (vx2) then vx2 else hi2x)) <= (k2) then k2 else (if (hi2x) <= (vx2) then vx2 else hi2x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), ((((1) + (sz1x)) + (sz2x)) + (1)), (x);
exists (x :-> (vx2) \+ x .+ 1 :-> (y12) \+ x .+ 2 :-> (rx2) \+ h_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x \+ h_bst_rx2sz2xlo2xhi2x_522x);
sslauto.
ssl_close 2;
exists ((sz1x) + (1)), (sz2x), (vx2), (hi2x), ((if (hi1x) <= (k2) then k2 else hi1x)), ((if (k2) <= (lo1x) then k2 else lo1x)), (lo2x), (y12), (rx2), (h_bst_y12sz1xk2lo1xk2lo1xhi1xk2k2hi1x_521x), (h_bst_rx2sz2xlo2xhi2x_522x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
ssl_read (x .+ 1).
try rename lx into lx2.
try rename h_bst_lxsz1xlo1xhi1x_521x into h_bst_lx2sz1xlo1xhi1x_521x.
try rename H_bst_lxsz1xlo1xhi1x_521x into H_bst_lx2sz1xlo1xhi1x_521x.
ssl_read (x .+ 2).
try rename rx into rx2.
try rename h_bst_rxsz2xlo2xhi2x_522x into h_bst_rx2sz2xlo2xhi2x_522x.
try rename H_bst_rxsz2xlo2xhi2x_522x into H_bst_rx2sz2xlo2xhi2x_522x.
try rename h_bst_x1n2lo2hi2_a1 into h_bst_rx2sz2xlo2xhi2x_522x.
try rename H_bst_x1n2lo2hi2_a1 into H_bst_rx2sz2xlo2xhi2x_522x.
ssl_call_pre (retv :-> (k2) \+ h_bst_rx2sz2xlo2xhi2x_522x).
ssl_call (k2, sz2x, lo2x, hi2x).
exists (h_bst_rx2sz2xlo2xhi2x_522x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim hi11 lo11 n11 y1.
ex_elim h_bst_y1n11lo11hi11_b1.
move=>[phi_call00] [phi_call01] [phi_call02].
move=>[sigma_call0].
subst h_call0.
move=>H_bst_y1n11lo11hi11_b1.
store_valid.
try rename h_bst_y1n11lo11hi11_b1 into h_bst_y1n11lo11hi11_522x.
try rename H_bst_y1n11lo11hi11_b1 into H_bst_y1n11lo11hi11_522x.
try rename h_bst_y1n11lo11hi11_522x into h_bst_y1n11lo11hi2xk2k2hi2x_522x.
try rename H_bst_y1n11lo11hi11_522x into H_bst_y1n11lo11hi2xk2k2hi2x_522x.
try rename h_bst_y1n11lo11hi2xk2k2hi2x_522x into h_bst_y1n11k2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename H_bst_y1n11lo11hi2xk2k2hi2x_522x into H_bst_y1n11k2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename h_bst_y1n11k2lo2xk2lo2xhi2xk2k2hi2x_522x into h_bst_y1sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename H_bst_y1n11k2lo2xk2lo2xhi2xk2k2hi2x_522x into H_bst_y1sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
ssl_read retv.
try rename y1 into y12.
try rename h_bst_y1sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x into h_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename H_bst_y1sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x into H_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename h_bst_lysz1ylo12yhi12y_521y into h_bst_lx2sz1xlo1xhi1x_521x.
try rename H_bst_lysz1ylo12yhi12y_521y into H_bst_lx2sz1xlo1xhi1x_521x.
try rename h_bst_rysz2ylo21yhi21y_522y into h_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename H_bst_rysz2ylo21yhi21y_522y into H_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x.
try rename h_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a into h_bst_xsz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
try rename H_bst_ysz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a into H_bst_xsz1xsz2xk2vx2lo1xvx2lo1xk2vx2lo1xvx2lo1xhi2xvx2vx2hi2xk2k2hi2xvx2vx2hi2x_a.
ssl_write (x .+ 2).
ssl_write_post (x .+ 2).
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists ((if ((if (hi2x) <= (vx2) then vx2 else hi2x)) <= (k2) then k2 else (if (hi2x) <= (vx2) then vx2 else hi2x))), ((if (k2) <= ((if (vx2) <= (lo1x) then vx2 else lo1x)) then k2 else (if (vx2) <= (lo1x) then vx2 else lo1x))), ((((1) + (sz1x)) + (sz2x)) + (1)), (x);
exists (x :-> (vx2) \+ x .+ 1 :-> (lx2) \+ x .+ 2 :-> (y12) \+ h_bst_lx2sz1xlo1xhi1x_521x \+ h_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x);
sslauto.
ssl_close 2;
exists (sz1x), ((sz2x) + (1)), (vx2), ((if (hi2x) <= (k2) then k2 else hi2x)), (hi1x), (lo1x), ((if (k2) <= (lo2x) then k2 else lo2x)), (lx2), (y12), (h_bst_lx2sz1xlo1xhi1x_521x), (h_bst_y12sz2xk2lo2xk2lo2xhi2xk2k2hi2x_522x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.