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

Lemma pure7 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure7: ssl_pure.
Lemma pure8 : (7) = (7). intros; hammer. Qed.
Hint Resolve pure8: ssl_pure.
Lemma pure9 (len1x : nat) : (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). intros; hammer. Qed.
Hint Resolve pure9: ssl_pure.
Lemma pure10 (hi1x : nat) (vx2 : nat) : (0) <= (vx2) -> (vx2) <= (7) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). intros; hammer. Qed.
Hint Resolve pure10: ssl_pure.
Lemma pure11 (vx2 : nat) (lo1x2 : nat) : (0) <= (vx2) -> (vx2) <= (7) -> ((if (vx2) <= (lo1x2) then vx2 else lo1x2)) = ((if (vx2) <= (lo1x2) then vx2 else lo1x2)). intros; hammer. Qed.
Hint Resolve pure11: ssl_pure.

Definition sll_min_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_514,
      h = r :-> a \+ h_sll_xnlohi_514 /\ sll x n lo hi h_sll_xnlohi_514,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_515,
      h = r :-> lo \+ h_sll_xnlohi_515 /\ sll x n lo hi h_sll_xnlohi_515
    ]).

Program Definition sll_min : sll_min_type :=
  Fix (fun (sll_min : sll_min_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      if (x) == (null)
      then
        r ::= 7;;
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_min (nxtx2, r);;
        lo1x2 <-- @read nat r;
        r ::= (if (vx2) <= (lo1x2) then vx2 else lo1x2);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_514.
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_514.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open ((x) == (null)) H_sll_xnlohi_514.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
try rename h_sll_xnlohi_514 into h_sll_xnlo_514.
try rename H_sll_xnlohi_514 into H_sll_xnlo_514.
try rename h_sll_xnlohi_515 into h_sll_xnlo_515.
try rename H_sll_xnlohi_515 into H_sll_xnlo_515.
try rename h_sll_xnlo_514 into h_sll_xn_514.
try rename H_sll_xnlo_514 into H_sll_xn_514.
try rename h_sll_xnlo_515 into h_sll_xn_515.
try rename H_sll_xnlo_515 into H_sll_xn_515.
try rename h_sll_xn_515 into h_sll_x_515.
try rename H_sll_xn_515 into H_sll_x_515.
try rename h_sll_xn_514 into h_sll_x_514.
try rename H_sll_xn_514 into H_sll_x_514.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_513x.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142] [phi_sll_xnlohi_5143] [phi_sll_xnlohi_5144] [phi_sll_xnlohi_5145].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
move=>H_sll_nxtxlen1xlo1xhi1x_513x.
try rename h_sll_xnlohi_514 into h_sll_xnlohi1xvxvxhi1x_514.
try rename H_sll_xnlohi_514 into H_sll_xnlohi1xvxvxhi1x_514.
try rename h_sll_xnlohi_515 into h_sll_xnlohi1xvxvxhi1x_515.
try rename H_sll_xnlohi_515 into H_sll_xnlohi1xvxvxhi1x_515.
try rename h_sll_xnlohi1xvxvxhi1x_514 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename H_sll_xnlohi1xvxvxhi1x_514 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename h_sll_xnlohi1xvxvxhi1x_515 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename H_sll_xnlohi1xvxvxhi1x_515 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_513x into h_sll_nxtx2len1xlo1xhi1x_513x.
try rename H_sll_nxtxlen1xlo1xhi1x_513x into H_sll_nxtx2len1xlo1xhi1x_513x.
try rename h_sll_x1n1lo1hi1_5141 into h_sll_nxtx2len1xlo1xhi1x_513x.
try rename H_sll_x1n1lo1hi1_5141 into H_sll_nxtx2len1xlo1xhi1x_513x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_513x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_513x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5151.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5151.
store_valid.
ssl_read r.
try rename lo1x into lo1x2.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_515.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_515.
try rename h_sll_nxtx2len1xlo1xhi1x_513x into h_sll_nxtx2len1xlo1x2hi1x_513x.
try rename H_sll_nxtx2len1xlo1xhi1x_513x into H_sll_nxtx2len1xlo1x2hi1x_513x.
try rename h_sll_nxtx2len1xlo1xhi1x_5151 into h_sll_nxtx2len1xlo1x2hi1x_5151.
try rename H_sll_nxtx2len1xlo1xhi1x_5151 into H_sll_nxtx2len1xlo1x2hi1x_5151.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_514.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_514.
try rename h_sll_nxtx1len1x1lo11xhi11x_513x1 into h_sll_nxtx2len1xlo1x2hi1x_5151.
try rename H_sll_nxtx1len1x1lo11xhi11x_513x1 into H_sll_nxtx2len1xlo1x2hi1x_5151.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1x2hi1x_5151);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x2), (nxtx2), (h_sll_nxtx2len1xlo1x2hi1x_5151);
sslauto.
ssl_frame_unfold.
Qed.