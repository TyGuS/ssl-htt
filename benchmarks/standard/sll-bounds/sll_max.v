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

Lemma pure17 : (0) = (0). intros; hammer. Qed.
Hint Resolve pure17: ssl_pure.
Lemma pure18 : (7) = (7). intros; hammer. Qed.
Hint Resolve pure18: ssl_pure.
Lemma pure19 (len1x : nat) : (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). intros; hammer. Qed.
Hint Resolve pure19: ssl_pure.
Lemma pure20 (hi1x2 : nat) (vx2 : nat) : (0) <= (vx2) -> (vx2) <= (7) -> ((if (hi1x2) <= (vx2) then vx2 else hi1x2)) = ((if (hi1x2) <= (vx2) then vx2 else hi1x2)). intros; hammer. Qed.
Hint Resolve pure20: ssl_pure.
Lemma pure21 (vx2 : nat) (lo1x : nat) : (0) <= (vx2) -> (vx2) <= (7) -> ((if (vx2) <= (lo1x) then vx2 else lo1x)) = ((if (vx2) <= (lo1x) then vx2 else lo1x)). intros; hammer. Qed.
Hint Resolve pure21: ssl_pure.

Definition sll_max_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_520,
      h = r :-> a \+ h_sll_xnlohi_520 /\ sll x n lo hi h_sll_xnlohi_520,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_521,
      h = r :-> hi \+ h_sll_xnlohi_521 /\ sll x n lo hi h_sll_xnlohi_521
    ]).

Program Definition sll_max : sll_max_type :=
  Fix (fun (sll_max : sll_max_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      if (x) == (null)
      then
        r ::= 0;;
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_max (nxtx2, r);;
        hi1x2 <-- @read nat r;
        r ::= (if (hi1x2) <= (vx2) then vx2 else hi1x2);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_520.
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_520.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open ((x) == (null)) H_sll_xnlohi_520.
move=>[phi_sll_xnlohi_5200] [phi_sll_xnlohi_5201] [phi_sll_xnlohi_5202].
move=>[sigma_sll_xnlohi_520].
subst h_sll_xnlohi_520.
try rename h_sll_xnlohi_520 into h_sll_xnlo_520.
try rename H_sll_xnlohi_520 into H_sll_xnlo_520.
try rename h_sll_xnlohi_521 into h_sll_xnlo_521.
try rename H_sll_xnlohi_521 into H_sll_xnlo_521.
try rename h_sll_xnlo_520 into h_sll_xn_520.
try rename H_sll_xnlo_520 into H_sll_xn_520.
try rename h_sll_xnlo_521 into h_sll_xn_521.
try rename H_sll_xnlo_521 into H_sll_xn_521.
try rename h_sll_xn_521 into h_sll_x_521.
try rename H_sll_xn_521 into H_sll_x_521.
try rename h_sll_xn_520 into h_sll_x_520.
try rename H_sll_xn_520 into H_sll_x_520.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_519x.
move=>[phi_sll_xnlohi_5200] [phi_sll_xnlohi_5201] [phi_sll_xnlohi_5202] [phi_sll_xnlohi_5203] [phi_sll_xnlohi_5204] [phi_sll_xnlohi_5205].
move=>[sigma_sll_xnlohi_520].
subst h_sll_xnlohi_520.
move=>H_sll_nxtxlen1xlo1xhi1x_519x.
try rename h_sll_xnlohi_520 into h_sll_xnlohi1xvxvxhi1x_520.
try rename H_sll_xnlohi_520 into H_sll_xnlohi1xvxvxhi1x_520.
try rename h_sll_xnlohi_521 into h_sll_xnlohi1xvxvxhi1x_521.
try rename H_sll_xnlohi_521 into H_sll_xnlohi1xvxvxhi1x_521.
try rename h_sll_xnlohi1xvxvxhi1x_520 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_520.
try rename H_sll_xnlohi1xvxvxhi1x_520 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_520.
try rename h_sll_xnlohi1xvxvxhi1x_521 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename H_sll_xnlohi1xvxvxhi1x_521 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_520 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_520.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_520 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_520.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_521 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_521 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_520 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_520 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_521 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_519x into h_sll_nxtx2len1xlo1xhi1x_519x.
try rename H_sll_nxtxlen1xlo1xhi1x_519x into H_sll_nxtx2len1xlo1xhi1x_519x.
try rename h_sll_x1n1lo1hi1_5201 into h_sll_nxtx2len1xlo1xhi1x_519x.
try rename H_sll_x1n1lo1hi1_5201 into H_sll_nxtx2len1xlo1xhi1x_519x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_519x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_519x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5211.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5211.
store_valid.
ssl_read r.
try rename hi1x into hi1x2.
try rename h_sll_nxtx2len1xlo1xhi1x_519x into h_sll_nxtx2len1xlo1xhi1x2_519x.
try rename H_sll_nxtx2len1xlo1xhi1x_519x into H_sll_nxtx2len1xlo1xhi1x2_519x.
try rename h_sll_nxtx2len1xlo1xhi1x_5211 into h_sll_nxtx2len1xlo1xhi1x2_5211.
try rename H_sll_nxtx2len1xlo1xhi1x_5211 into H_sll_nxtx2len1xlo1xhi1x2_5211.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520 into h_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_520.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_520 into H_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_520.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521 into h_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_521.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_521 into H_sll_xlen1xvx2lo1xvx2lo1xhi1x2vx2vx2hi1x2_521.
try rename h_sll_nxtx1len1x1lo11xhi11x_519x1 into h_sll_nxtx2len1xlo1xhi1x2_5211.
try rename H_sll_nxtx1len1x1lo11xhi11x_519x1 into H_sll_nxtx2len1xlo1xhi1x2_5211.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x2_5211);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x2), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x2_5211);
sslauto.
ssl_frame_unfold.
Qed.