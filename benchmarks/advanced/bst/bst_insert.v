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
Lemma pure4 (a : nat) : (a) < ((a) + (3)).
  (* intros; hammer. *)
  scongruence use: addSnnS, leq_addr.
Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (a : nat) : (a) < ((a) + (3)).
  (* intros; hammer. *)
  scongruence use: addSnnS, leq_addr.
Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (sz1x : nat) (sz2x : nat) : (0) <= (sz1x) -> (0) <= (sz2x) -> (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= ((sz1x) + (1)). intros; hammer. Qed.
Hint Resolve pure6: ssl_pure.
Lemma pure7 (sz1x : nat) (sz2x : nat) : (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= (sz1x) -> (0) <= (sz2x) -> ((((1) + (sz1x)) + (sz2x)) + (1)) = (((1) + ((sz1x) + (1))) + (sz2x)). intros; hammer. Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 (k1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (k1) <= (vx1) -> (vx1) <= (lo2x) -> (vx1) <= (7) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> ((if ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (k1) then k1 else (if (hi2x) <= (vx1) then vx1 else hi2x))) = ((if (hi2x) <= (vx1) then vx1 else hi2x)).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H6;
  sauto.
Qed.
Hint Resolve pure8: ssl_pure.
Lemma pure9 (k1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (lo1x : nat) : (k1) <= (vx1) -> (vx1) <= (lo2x) -> (vx1) <= (7) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))) = ((if (vx1) <= ((if (k1) <= (lo1x) then k1 else lo1x)) then vx1 else (if (k1) <= (lo1x) then k1 else lo1x))).
  (* intros; hammer. *)
  intros.
  destruct (vx1 <= lo1x) eqn:H6;
  destruct (k1 <= lo1x) eqn:H7;
  sauto.
Qed.
Hint Resolve pure9: ssl_pure.
Lemma pure10 (hi1x : nat) (k1 : nat) (vx1 : nat) (lo2x : nat) : (k1) <= (vx1) -> (vx1) <= (lo2x) -> (vx1) <= (7) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> ((if (hi1x) <= (k1) then k1 else hi1x)) <= (vx1). intros; hammer. Qed.
Hint Resolve pure10: ssl_pure.
Lemma pure11 (sz2x : nat) (sz1x : nat) : (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= (sz1x) -> (0) <= (sz2x) -> (0) <= ((sz2x) + (1)). intros; hammer. Qed.
Hint Resolve pure11: ssl_pure.
Lemma pure12 (sz1x : nat) (sz2x : nat) : (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= (sz1x) -> (0) <= (sz2x) -> ((((1) + (sz1x)) + (sz2x)) + (1)) = (((1) + (sz1x)) + ((sz2x) + (1))). intros; hammer. Qed.
Hint Resolve pure12: ssl_pure.
Lemma pure13 (k1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (lo1x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ~~ ((k1) <= (vx1)) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))) = ((if (vx1) <= (lo1x) then vx1 else lo1x)).
  (* intros; hammer. *)
  intros.
  destruct (vx1 <= lo1x) eqn:H6;
  sauto.
Qed.
Hint Resolve pure13: ssl_pure.
Lemma pure14 (k1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ~~ ((k1) <= (vx1)) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> ((if ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (k1) then k1 else (if (hi2x) <= (vx1) then vx1 else hi2x))) = ((if ((if (hi2x) <= (k1) then k1 else hi2x)) <= (vx1) then vx1 else (if (hi2x) <= (k1) then k1 else hi2x))).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H6;
  destruct (hi2x <= k1) eqn:H7;
  sauto.
Qed.
Hint Resolve pure14: ssl_pure.
Lemma pure15 (vx1 : nat) (k1 : nat) (lo2x : nat) (hi1x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ~~ ((k1) <= (vx1)) -> (k1) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (k1) -> (vx1) <= ((if (k1) <= (lo2x) then k1 else lo2x)).
  (* intros; hammer. *)
  intros.
  rewrite -ltnNge in H1.
  sauto.
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
      k1 <-- @read nat retv;
      if (x) == (null)
      then
        y1 <-- allocb null 3;
        retv ::= y1;;
        (y1 .+ 1) ::= null;;
        (y1 .+ 2) ::= null;;
        y1 ::= k1;;
        ret tt
      else
        vx1 <-- @read nat x;
        lx1 <-- @read ptr (x .+ 1);
        rx1 <-- @read ptr (x .+ 2);
        if (k1) <= (vx1)
        then
          bst_insert (lx1, retv);;
          y11 <-- @read ptr retv;
          retv ::= x;;
          (x .+ 1) ::= y11;;
          ret tt
        else
          bst_insert (rx1, retv);;
          y11 <-- @read ptr retv;
          retv ::= x;;
          (x .+ 2) ::= y11;;
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
try rename k into k1.
try rename h_bst_ynkloklohikkhi_a into h_bst_ynk1lok1lohik1k1hi_a.
try rename H_bst_ynkloklohikkhi_a into H_bst_ynk1lok1lohik1k1hi_a.
ssl_open ((x) == (null)) H_bst_xnlohi_a.
move=>[phi_bst_xnlohi_a0] [phi_bst_xnlohi_a1] [phi_bst_xnlohi_a2].
move=>[sigma_bst_xnlohi_a].
subst h_bst_xnlohi_a.
try rename h_bst_xnlohi_a into h_bst_xnlo_a.
try rename H_bst_xnlohi_a into H_bst_xnlo_a.
try rename h_bst_ynk1lok1lohik1k1hi_a into h_bst_ynk1lok1lok1k1_a.
try rename H_bst_ynk1lok1lohik1k1hi_a into H_bst_ynk1lok1lok1k1_a.
try rename h_bst_ynk1lok1lok1k1_a into h_bst_ynk1k1k1k1_a.
try rename H_bst_ynk1lok1lok1k1_a into H_bst_ynk1k1k1k1_a.
try rename h_bst_xnlo_a into h_bst_xn_a.
try rename H_bst_xnlo_a into H_bst_xn_a.
try rename h_bst_ynk1k1k1k1_a into h_bst_yk1k1k1k1_a.
try rename H_bst_ynk1k1k1k1_a into H_bst_yk1k1k1k1_a.
try rename h_bst_xn_a into h_bst_x_a.
try rename H_bst_xn_a into H_bst_x_a.
try rename h_bst_lysz1ylo11yhi11y_0y into h_bst_lysz1ylo11y_0y.
try rename H_bst_lysz1ylo11yhi11y_0y into H_bst_lysz1ylo11y_0y.
try rename h_bst_lysz1ylo11y_0y into h_bst_lysz1y_0y.
try rename H_bst_lysz1ylo11y_0y into H_bst_lysz1y_0y.
try rename h_bst_lysz1y_0y into h_bst_sz1y_0y.
try rename H_bst_lysz1y_0y into H_bst_sz1y_0y.
try rename h_bst_sz1y_0y into h_bst__0y.
try rename H_bst_sz1y_0y into H_bst__0y.
try rename h_bst_rysz2ylo2yhi2y_1y into h_bst_rysz2ylo2y_1y.
try rename H_bst_rysz2ylo2yhi2y_1y into H_bst_rysz2ylo2y_1y.
try rename h_bst_rysz2ylo2y_1y into h_bst_rysz2y_1y.
try rename H_bst_rysz2ylo2y_1y into H_bst_rysz2y_1y.
try rename h_bst_rysz2y_1y into h_bst_sz2y_1y.
try rename H_bst_rysz2y_1y into H_bst_sz2y_1y.
try rename h_bst_sz2y_1y into h_bst__1y.
try rename H_bst_sz2y_1y into H_bst__1y.
ssl_alloc y1.
try rename y into y1.
try rename h_bst_yk1k1k1k1_a into h_bst_y1k1k1k1k1_a.
try rename H_bst_yk1k1k1k1_a into H_bst_y1k1k1k1k1_a.
ssl_write retv.
ssl_write_post retv.
ssl_write (y1 .+ 1).
ssl_write_post (y1 .+ 1).
ssl_write (y1 .+ 2).
ssl_write_post (y1 .+ 2).
ssl_write y1.
ssl_write_post y1.
try rename h_bst__0y into h_bst__a.
try rename H_bst__0y into H_bst__a.
try rename h_bst__1y into h_bst__a.
try rename H_bst__1y into H_bst__a.
ssl_emp;
exists ((if (0) <= (k1) then k1 else 0)), ((if (k1) <= (7) then k1 else 7)), ((0) + (1)), (y1);
exists (y1 :-> (k1) \+ y1 .+ 1 :-> (null) \+ y1 .+ 2 :-> (null));
sslauto.
ssl_close 2;
exists (0), (0), (k1), (0), (0), (7), (7), (null), (null), (empty), (empty);
sslauto.
ssl_close 1;
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1x sz2x vx hi2x hi1x.
ex_elim lo1x lo2x lx rx.
ex_elim h_bst_lxsz1xlo1xhi1x_0x h_bst_rxsz2xlo2xhi2x_1x.
move=>[phi_bst_xnlohi_a0] [phi_bst_xnlohi_a1] [phi_bst_xnlohi_a2] [phi_bst_xnlohi_a3] [phi_bst_xnlohi_a4] [phi_bst_xnlohi_a5] [phi_bst_xnlohi_a6] [phi_bst_xnlohi_a7] [phi_bst_xnlohi_a8].
move=>[sigma_bst_xnlohi_a].
subst h_bst_xnlohi_a.
move=>[H_bst_lxsz1xlo1xhi1x_0x H_bst_rxsz2xlo2xhi2x_1x].
try rename h_bst_xnlohi_a into h_bst_xnlohi2xvxvxhi2x_a.
try rename H_bst_xnlohi_a into H_bst_xnlohi2xvxvxhi2x_a.
try rename h_bst_ynk1lok1lohik1k1hi_a into h_bst_ynk1lok1lohi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
try rename H_bst_ynk1lok1lohik1k1hi_a into H_bst_ynk1lok1lohi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
try rename h_bst_ynk1lok1lohi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into h_bst_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
try rename H_bst_ynk1lok1lohi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into H_bst_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
try rename h_bst_xnlohi2xvxvxhi2x_a into h_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xnlohi2xvxvxhi2x_a into H_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename h_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xnvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename h_bst_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into h_bst_ysz1xsz2xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
try rename H_bst_ynk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into H_bst_ysz1xsz2xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a.
ssl_read x.
try rename vx into vx1.
try rename h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a.
try rename H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a.
try rename h_bst_ysz1xsz2xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into h_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
try rename H_bst_ysz1xsz2xk1vxlo1xvxlo1xk1vxlo1xvxlo1xhi2xvxvxhi2xk1k1hi2xvxvxhi2x_a into H_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
ssl_read (x .+ 1).
try rename lx into lx1.
try rename h_bst_lxsz1xlo1xhi1x_0x into h_bst_lx1sz1xlo1xhi1x_0x.
try rename H_bst_lxsz1xlo1xhi1x_0x into H_bst_lx1sz1xlo1xhi1x_0x.
ssl_read (x .+ 2).
try rename rx into rx1.
try rename h_bst_rxsz2xlo2xhi2x_1x into h_bst_rx1sz2xlo2xhi2x_1x.
try rename H_bst_rxsz2xlo2xhi2x_1x into H_bst_rx1sz2xlo2xhi2x_1x.
ssl_branch ((k1) <= (vx1)).
try rename h_bst_x1n2lo2hi2_a1 into h_bst_lx1sz1xlo1xhi1x_0x.
try rename H_bst_x1n2lo2hi2_a1 into H_bst_lx1sz1xlo1xhi1x_0x.
ssl_call_pre (retv :-> (k1) \+ h_bst_lx1sz1xlo1xhi1x_0x).
ssl_call (k1, sz1x, lo1x, hi1x).
exists (h_bst_lx1sz1xlo1xhi1x_0x);
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
try rename h_bst_y1n11lo11hi11_b1 into h_bst_y1n11lo11hi11_0x.
try rename H_bst_y1n11lo11hi11_b1 into H_bst_y1n11lo11hi11_0x.
try rename h_bst_y1n11lo11hi11_0x into h_bst_y1n11lo11hi1xk1k1hi1x_0x.
try rename H_bst_y1n11lo11hi11_0x into H_bst_y1n11lo11hi1xk1k1hi1x_0x.
try rename h_bst_y1n11lo11hi1xk1k1hi1x_0x into h_bst_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename H_bst_y1n11lo11hi1xk1k1hi1x_0x into H_bst_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename h_bst_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_0x into h_bst_y1sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename H_bst_y1n11k1lo1xk1lo1xhi1xk1k1hi1x_0x into H_bst_y1sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
ssl_read retv.
try rename y1 into y11.
try rename h_bst_y1sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x into h_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename H_bst_y1sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x into H_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename h_bst_lysz1ylo12yhi12y_0y into h_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename H_bst_lysz1ylo12yhi12y_0y into H_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x.
try rename h_bst_rysz2ylo21yhi21y_1y into h_bst_rx1sz2xlo2xhi2x_1x.
try rename H_bst_rysz2ylo21yhi21y_1y into H_bst_rx1sz2xlo2xhi2x_1x.
try rename h_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a into h_bst_xsz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
try rename H_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a into H_bst_xsz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
ssl_write retv.
ssl_write_post retv.
ssl_write (x .+ 1).
ssl_write_post (x .+ 1).
ssl_emp;
exists ((if ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (k1) then k1 else (if (hi2x) <= (vx1) then vx1 else hi2x))), ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))), ((((1) + (sz1x)) + (sz2x)) + (1)), (x);
exists (x :-> (vx1) \+ x .+ 1 :-> (y11) \+ x .+ 2 :-> (rx1) \+ h_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x \+ h_bst_rx1sz2xlo2xhi2x_1x);
sslauto.
ssl_close 2;
exists ((sz1x) + (1)), (sz2x), (vx1), (hi2x), ((if (hi1x) <= (k1) then k1 else hi1x)), ((if (k1) <= (lo1x) then k1 else lo1x)), (lo2x), (y11), (rx1), (h_bst_y11sz1xk1lo1xk1lo1xhi1xk1k1hi1x_0x), (h_bst_rx1sz2xlo2xhi2x_1x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
try rename h_bst_x1n2lo2hi2_a1 into h_bst_rx1sz2xlo2xhi2x_1x.
try rename H_bst_x1n2lo2hi2_a1 into H_bst_rx1sz2xlo2xhi2x_1x.
ssl_call_pre (retv :-> (k1) \+ h_bst_rx1sz2xlo2xhi2x_1x).
ssl_call (k1, sz2x, lo2x, hi2x).
exists (h_bst_rx1sz2xlo2xhi2x_1x);
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
try rename h_bst_y1n11lo11hi11_b1 into h_bst_y1n11lo11hi11_1x.
try rename H_bst_y1n11lo11hi11_b1 into H_bst_y1n11lo11hi11_1x.
try rename h_bst_y1n11lo11hi11_1x into h_bst_y1n11lo11hi2xk1k1hi2x_1x.
try rename H_bst_y1n11lo11hi11_1x into H_bst_y1n11lo11hi2xk1k1hi2x_1x.
try rename h_bst_y1n11lo11hi2xk1k1hi2x_1x into h_bst_y1n11k1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename H_bst_y1n11lo11hi2xk1k1hi2x_1x into H_bst_y1n11k1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename h_bst_y1n11k1lo2xk1lo2xhi2xk1k1hi2x_1x into h_bst_y1sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename H_bst_y1n11k1lo2xk1lo2xhi2xk1k1hi2x_1x into H_bst_y1sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
ssl_read retv.
try rename y1 into y11.
try rename h_bst_y1sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x into h_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename H_bst_y1sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x into H_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename h_bst_lysz1ylo12yhi12y_0y into h_bst_lx1sz1xlo1xhi1x_0x.
try rename H_bst_lysz1ylo12yhi12y_0y into H_bst_lx1sz1xlo1xhi1x_0x.
try rename h_bst_rysz2ylo21yhi21y_1y into h_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename H_bst_rysz2ylo21yhi21y_1y into H_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x.
try rename h_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a into h_bst_xsz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
try rename H_bst_ysz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a into H_bst_xsz1xsz2xk1vx1lo1xvx1lo1xk1vx1lo1xvx1lo1xhi2xvx1vx1hi2xk1k1hi2xvx1vx1hi2x_a.
ssl_write retv.
ssl_write_post retv.
ssl_write (x .+ 2).
ssl_write_post (x .+ 2).
ssl_emp;
exists ((if ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (k1) then k1 else (if (hi2x) <= (vx1) then vx1 else hi2x))), ((if (k1) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) then k1 else (if (vx1) <= (lo1x) then vx1 else lo1x))), ((((1) + (sz1x)) + (sz2x)) + (1)), (x);
exists (x :-> (vx1) \+ x .+ 1 :-> (lx1) \+ x .+ 2 :-> (y11) \+ h_bst_lx1sz1xlo1xhi1x_0x \+ h_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x);
sslauto.
ssl_close 2;
exists (sz1x), ((sz2x) + (1)), (vx1), ((if (hi2x) <= (k1) then k1 else hi2x)), (hi1x), (lo1x), ((if (k1) <= (lo2x) then k1 else lo2x)), (lx1), (y11), (h_bst_lx1sz1xlo1xhi1x_0x), (h_bst_y11sz2xk1lo2xk1lo2xhi2xk1k1hi2x_1x);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.
