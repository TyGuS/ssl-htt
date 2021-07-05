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

Lemma pure1 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure1: ssl_pure.
Lemma pure2 : (7) = (7). intros; hammer. Qed.
Hint Resolve pure2: ssl_pure.
Lemma pure3 (lo2x : nat) (vx1 : nat) (hi1x : nat) (lo1x : nat) (hi2x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (0) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= (lo1x). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (lo2x : nat) (vx1 : nat) (hi1x : nat) (lo1x : nat) (hi2x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (0) <= ((if (vx1) <= (lo1x) then vx1 else lo1x)) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (hi1x) <= (7).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H5.
  destruct (vx1 <= lo1x) eqn:H6;
  apply: (leq_trans H3 H1).
  destruct (vx1 <= lo1x) eqn:H6;
  apply: (leq_trans H3 H0).
Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (lo1x1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= ((if (vx1) <= (lo1x1) then vx1 else lo1x1)) -> (0) <= (lo2x).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H5;
  destruct (vx1 <= lo1x1) eqn:H6;
  sauto.
Qed.
Hint Resolve pure5: ssl_pure.
Lemma pure6 (lo1x1 : nat) (lo2x : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (vx1) <= (lo2x) -> (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (hi1x) <= (vx1) -> (0) <= (vx1) -> (0) <= ((if (vx1) <= (lo1x1) then vx1 else lo1x1)) -> (hi2x) <= (7).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H5.
  destruct (vx1 <= lo1x1) eqn:H6;
  apply: (leq_trans H5 H1).
  sauto.
Qed.
Hint Resolve pure6: ssl_pure.
Lemma pure7 (sz1x : nat) (sz2x : nat) : (0) <= (((1) + (sz1x)) + (sz2x)) -> (0) <= (sz1x) -> (0) <= (sz2x) -> (((1) + (sz1x)) + (sz2x)) = (((1) + (sz1x)) + (sz2x)). intros; hammer. Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 (c1 : nat) (c2 : nat) : (c1) < (((if (c1) < (c2) then c2 else c1)) + (1)).
  (* intros; hammer. *)
  destruct (c1 < c2) eqn:H1.
  apply: ltn_addr=>//=.
  rewrite addn1; apply: ltnSn.
Qed.
Hint Resolve pure8: ssl_pure.
Lemma pure9 (c2 : nat) (c1 : nat) : (c2) < (((if (c1) < (c2) then c2 else c1)) + (1)).
  (* intros; hammer. *)
  destruct (c1 < c2) eqn:H1.
  rewrite addn1; apply: ltnSn.
  apply negbT in H1.
  rewrite -leqNgt in H1.
  rewrite -ltnS in H1.
  by rewrite addn1.
Qed.
Hint Resolve pure9: ssl_pure.
Lemma pure10 (lo2x1 : nat) (lo1x1 : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (hi1x) <= (vx1) -> (vx1) <= (lo2x1) -> (0) <= (vx1) -> (0) <= ((if (vx1) <= (lo1x1) then vx1 else lo1x1)) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) = ((if (hi2x) <= (vx1) then vx1 else hi2x)).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H5;
  destruct (vx1 <= lo1x1) eqn:H6;
  sauto.
Qed.
Hint Resolve pure10: ssl_pure.
Lemma pure11 (lo2x1 : nat) (lo1x1 : nat) (vx1 : nat) (hi1x : nat) (hi2x : nat) : (vx1) <= (7) -> ((if (hi2x) <= (vx1) then vx1 else hi2x)) <= (7) -> (hi1x) <= (vx1) -> (vx1) <= (lo2x1) -> (0) <= (vx1) -> (0) <= ((if (vx1) <= (lo1x1) then vx1 else lo1x1)) -> ((if (vx1) <= (lo1x1) then vx1 else lo1x1)) = ((if (vx1) <= (lo1x1) then vx1 else lo1x1)).
  (* intros; hammer. *)
  intros.
  destruct (hi2x <= vx1) eqn:H5;
  destruct (vx1 <= lo1x1) eqn:H6;
  sauto.
Qed.
Hint Resolve pure11: ssl_pure.

Definition bst_find_smallest_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, retv) := vprogs in
      let: (lo, sz, hi) := vghosts in
      exists h_bst_xszlohi_a,
      (0) <= (lo) /\ (0) <= (sz) /\ (hi) <= (7) /\ h = retv :-> (666) \+ h_bst_xszlohi_a /\ bst x sz lo hi h_bst_xszlohi_a,
    [vfun (_: unit) h =>
      let: (x, retv) := vprogs in
      let: (lo, sz, hi) := vghosts in
      exists h_bst_xszlohi_c,
      h = retv :-> (lo) \+ h_bst_xszlohi_c /\ bst x sz lo hi h_bst_xszlohi_c
    ]).

Program Definition bst_find_smallest : bst_find_smallest_type :=
  Fix (fun (bst_find_smallest : bst_find_smallest_type) vprogs =>
    let: (x, retv) := vprogs in
    Do (
      if (x) == (null)
      then
        retv ::= 7;;
        ret tt
      else
        vx1 <-- @read nat x;
        lx1 <-- @read ptr (x .+ 1);
        rx1 <-- @read ptr (x .+ 2);
        bst_find_smallest (lx1, retv);;
        lo1x1 <-- @read nat retv;
        retv ::= 666;;
        bst_find_smallest (rx1, retv);;
        lo2x1 <-- @read nat retv;
        retv ::= (if (vx1) <= (lo1x1) then vx1 else lo1x1);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x retv]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[lo sz] hi].
ex_elim h_bst_xszlohi_a.
move=>[phi_self0] [phi_self1] [phi_self2].
move=>[sigma_self].
subst h_self.
move=>H_bst_xszlohi_a.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_bst_xszlohi_a.
move=>[phi_bst_xszlohi_a0] [phi_bst_xszlohi_a1] [phi_bst_xszlohi_a2].
move=>[sigma_bst_xszlohi_a].
subst h_bst_xszlohi_a.
try rename h_bst_xszlohi_a into h_bst_xszlo_a.
try rename H_bst_xszlohi_a into H_bst_xszlo_a.
try rename h_bst_xszlohi_c into h_bst_xszlo_c.
try rename H_bst_xszlohi_c into H_bst_xszlo_c.
try rename h_bst_xszlo_a into h_bst_xsz_a.
try rename H_bst_xszlo_a into H_bst_xsz_a.
try rename h_bst_xszlo_c into h_bst_xsz_c.
try rename H_bst_xszlo_c into H_bst_xsz_c.
try rename h_bst_xsz_a into h_bst_x_a.
try rename H_bst_xsz_a into H_bst_x_a.
try rename h_bst_xsz_c into h_bst_x_c.
try rename H_bst_xsz_c into H_bst_x_c.
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim sz1x sz2x vx hi2x hi1x.
ex_elim lo1x lo2x lx rx.
ex_elim h_bst_lxsz1xlo1xhi1x_0x h_bst_rxsz2xlo2xhi2x_1x.
move=>[phi_bst_xszlohi_a0] [phi_bst_xszlohi_a1] [phi_bst_xszlohi_a2] [phi_bst_xszlohi_a3] [phi_bst_xszlohi_a4] [phi_bst_xszlohi_a5] [phi_bst_xszlohi_a6] [phi_bst_xszlohi_a7] [phi_bst_xszlohi_a8].
move=>[sigma_bst_xszlohi_a].
subst h_bst_xszlohi_a.
move=>[H_bst_lxsz1xlo1xhi1x_0x H_bst_rxsz2xlo2xhi2x_1x].
try rename h_bst_xszlohi_a into h_bst_xszlohi2xvxvxhi2x_a.
try rename H_bst_xszlohi_a into H_bst_xszlohi2xvxvxhi2x_a.
try rename h_bst_xszlohi_c into h_bst_xszlohi2xvxvxhi2x_c.
try rename H_bst_xszlohi_c into H_bst_xszlohi2xvxvxhi2x_c.
try rename h_bst_xszlohi2xvxvxhi2x_c into h_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_c.
try rename H_bst_xszlohi2xvxvxhi2x_c into H_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_c.
try rename h_bst_xszlohi2xvxvxhi2x_a into h_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xszlohi2xvxvxhi2x_a into H_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename h_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename H_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a.
try rename h_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_c into h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_c.
try rename H_bst_xszvxlo1xvxlo1xhi2xvxvxhi2x_c into H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_c.
ssl_read x.
try rename vx into vx1.
try rename h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into h_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a.
try rename H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_a into H_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a.
try rename h_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_c into h_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_c.
try rename H_bst_xsz1xsz2xvxlo1xvxlo1xhi2xvxvxhi2x_c into H_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_c.
ssl_read (x .+ 1).
try rename lx into lx1.
try rename h_bst_lxsz1xlo1xhi1x_0x into h_bst_lx1sz1xlo1xhi1x_0x.
try rename H_bst_lxsz1xlo1xhi1x_0x into H_bst_lx1sz1xlo1xhi1x_0x.
ssl_read (x .+ 2).
try rename rx into rx1.
try rename h_bst_rxsz2xlo2xhi2x_1x into h_bst_rx1sz2xlo2xhi2x_1x.
try rename H_bst_rxsz2xlo2xhi2x_1x into H_bst_rx1sz2xlo2xhi2x_1x.
try rename h_bst_x1sz1lo1hi1_a1 into h_bst_lx1sz1xlo1xhi1x_0x.
try rename H_bst_x1sz1lo1hi1_a1 into H_bst_lx1sz1xlo1xhi1x_0x.
ssl_call_pre (retv :-> (666) \+ h_bst_lx1sz1xlo1xhi1x_0x).
ssl_call (lo1x, sz1x, hi1x).
exists (h_bst_lx1sz1xlo1xhi1x_0x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_bst_lx1sz1xlo1xhi1x_c1.
move=>[sigma_call0].
subst h_call0.
move=>H_bst_lx1sz1xlo1xhi1x_c1.
store_valid.
ssl_read retv.
try rename lo1x into lo1x1.
try rename h_bst_lx1sz1xlo1xhi1x_c1 into h_bst_lx1sz1xlo1x1hi1x_c1.
try rename H_bst_lx1sz1xlo1xhi1x_c1 into H_bst_lx1sz1xlo1x1hi1x_c1.
try rename h_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_c into h_bst_xsz1xsz2xvx1lo1x1vx1lo1x1hi2xvx1vx1hi2x_c.
try rename H_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_c into H_bst_xsz1xsz2xvx1lo1x1vx1lo1x1hi2xvx1vx1hi2x_c.
try rename h_bst_lx1sz1xlo1xhi1x_0x into h_bst_lx1sz1xlo1x1hi1x_0x.
try rename H_bst_lx1sz1xlo1xhi1x_0x into H_bst_lx1sz1xlo1x1hi1x_0x.
try rename h_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a into h_bst_xsz1xsz2xvx1lo1x1vx1lo1x1hi2xvx1vx1hi2x_a.
try rename H_bst_xsz1xsz2xvx1lo1xvx1lo1xhi2xvx1vx1hi2x_a into H_bst_xsz1xsz2xvx1lo1x1vx1lo1x1hi2xvx1vx1hi2x_a.
try rename h_bst_x2sz2lo2hi2_a2 into h_bst_rx1sz2xlo2xhi2x_1x.
try rename H_bst_x2sz2lo2hi2_a2 into H_bst_rx1sz2xlo2xhi2x_1x.
ssl_write retv.
ssl_call_pre (retv :-> (666) \+ h_bst_rx1sz2xlo2xhi2x_1x).
ssl_call (lo2x, sz2x, hi2x).
exists (h_bst_rx1sz2xlo2xhi2x_1x);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim h_bst_rx1sz2xlo2xhi2x_c2.
move=>[sigma_call1].
subst h_call1.
move=>H_bst_rx1sz2xlo2xhi2x_c2.
store_valid.
ssl_read retv.
try rename lo2x into lo2x1.
try rename h_bst_rx1sz2xlo2xhi2x_1x into h_bst_rx1sz2xlo2x1hi2x_1x.
try rename H_bst_rx1sz2xlo2xhi2x_1x into H_bst_rx1sz2xlo2x1hi2x_1x.
try rename h_bst_rx1sz2xlo2xhi2x_c2 into h_bst_rx1sz2xlo2x1hi2x_c2.
try rename H_bst_rx1sz2xlo2xhi2x_c2 into H_bst_rx1sz2xlo2x1hi2x_c2.
try rename h_bst_lx2sz11xlo11xhi11x_0x1 into h_bst_lx1sz1xlo1x1hi1x_c1.
try rename H_bst_lx2sz11xlo11xhi11x_0x1 into H_bst_lx1sz1xlo1x1hi1x_c1.
try rename h_bst_rx2sz21xlo21xhi21x_1x1 into h_bst_rx1sz2xlo2x1hi2x_c2.
try rename H_bst_rx2sz21xlo21xhi21x_1x1 into H_bst_rx1sz2xlo2x1hi2x_c2.
ssl_write retv.
ssl_write_post retv.
ssl_emp;
exists (x :-> (vx1) \+ x .+ 1 :-> (lx1) \+ x .+ 2 :-> (rx1) \+ h_bst_lx1sz1xlo1x1hi1x_c1 \+ h_bst_rx1sz2xlo2x1hi2x_c2);
sslauto.
ssl_close 2;
exists (sz1x), (sz2x), (vx1), (hi2x), (hi1x), (lo1x1), (lo2x1), (lx1), (rx1), (h_bst_lx1sz1xlo1x1hi1x_c1), (h_bst_rx1sz2xlo2x1hi2x_c2);
sslauto.
ssl_frame_unfold.
ssl_frame_unfold.
Qed.
