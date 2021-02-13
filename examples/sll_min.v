From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive sll (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| sll_1 of x == null of
  hi == 0 /\ len == 0 /\ lo == 7 /\ h = empty
| sll_2 of (x == null) = false of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_sll_nxtlen1lo1hi1_513,
  0 <= len1 /\ 0 <= v /\ hi == (if hi1 <= v then v else hi1) /\ len == 1 + len1 /\ lo == (if v <= lo1 then v else lo1) /\ v <= 7 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_513 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_513.

Lemma pure1 : 0 == 0. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 : 7 == 7. Admitted.
Hint Resolve pure2: ssl_pure.
Lemma pure3 len1x : 0 <= len1x -> 1 + len1x == 1 + len1x. Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 hi1x vx2 : 0 <= vx2 -> vx2 <= 7 -> (if hi1x <= vx2 then vx2 else hi1x) == (if hi1x <= vx2 then vx2 else hi1x). Admitted.
Hint Resolve pure4: ssl_pure.
Lemma pure5 vx2 lo1x2 : 0 <= vx2 -> vx2 <= 7 -> (if vx2 <= lo1x2 then vx2 else lo1x2) == (if vx2 <= lo1x2 then vx2 else lo1x2). Admitted.
Hint Resolve pure5: ssl_pure.

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
      if x == null
      then
        r ::= 7;;
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_min (nxtx2, r);;
        lo1x2 <-- @read nat r;
        r ::= (if vx2 <= lo1x2 then vx2 else lo1x2);;
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
ssl_open (x == null) H_sll_xnlohi_514.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
shelve.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_513x.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142] [phi_sll_xnlohi_5143] [phi_sll_xnlohi_5144] [phi_sll_xnlohi_5145].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
move=>H_sll_nxtxlen1xlo1xhi1x_513x.
shelve.
Unshelve.
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
unfold_constructor 1;
sslauto.
try rename h_sll_xnlohi_514 into h_sll_xnlohi1xvxvxhi1x_514.
try rename H_sll_xnlohi_514 into H_sll_xnlohi1xvxvxhi1x_514.
try rename h_sll_xnlohi_515 into h_sll_xnlohi1xvxvxhi1x_515.
try rename H_sll_xnlohi_515 into H_sll_xnlohi1xvxvxhi1x_515.
try rename h_sll_xnlohi1xvxvxhi1x_514 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename H_sll_xnlohi1xvxvxhi1x_514 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename h_sll_xnlohi1xvxvxhi1x_515 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename H_sll_xnlohi1xvxvxhi1x_515 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_514 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_515 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_514 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_515 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_513x into h_sll_nxtx2len1xlo1xhi1x_513x.
try rename H_sll_nxtxlen1xlo1xhi1x_513x into H_sll_nxtx2len1xlo1xhi1x_513x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_513x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_513x);
sslauto.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5151.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5151.
store_valid.
ssl_read r.
try rename lo1x into lo1x2.
try rename h_sll_nxtx2len1xlo1xhi1x_513x into h_sll_nxtx2len1xlo1x2hi1x_513x.
try rename H_sll_nxtx2len1xlo1xhi1x_513x into H_sll_nxtx2len1xlo1x2hi1x_513x.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_514.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_514 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_514.
try rename h_sll_nxtx2len1xlo1xhi1x_5151 into h_sll_nxtx2len1xlo1x2hi1x_5151.
try rename H_sll_nxtx2len1xlo1xhi1x_5151 into H_sll_nxtx2len1xlo1x2hi1x_5151.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_515.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_515 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_515.
try rename h_sll_nxtx1len1x1lo11xhi11x_513x1 into h_sll_nxtx1len1x1lo11xhi11x_5151.
try rename H_sll_nxtx1len1x1lo11xhi11x_513x1 into H_sll_nxtx1len1x1lo11xhi11x_5151.
try rename h_sll_nxtx1len1x1lo11xhi11x_5151 into h_sll_nxtx1len1x1lo11xhi1x_5151.
try rename H_sll_nxtx1len1x1lo11xhi11x_5151 into H_sll_nxtx1len1x1lo11xhi1x_5151.
try rename h_sll_nxtx1len1x1lo11xhi1x_5151 into h_sll_nxtx1len1xlo11xhi1x_5151.
try rename H_sll_nxtx1len1x1lo11xhi1x_5151 into H_sll_nxtx1len1xlo11xhi1x_5151.
try rename h_sll_nxtx1len1xlo11xhi1x_5151 into h_sll_nxtx1len1xlo1x2hi1x_5151.
try rename H_sll_nxtx1len1xlo11xhi1x_5151 into H_sll_nxtx1len1xlo1x2hi1x_5151.
try rename h_sll_nxtx1len1xlo1x2hi1x_5151 into h_sll_nxtx2len1xlo1x2hi1x_5151.
try rename H_sll_nxtx1len1xlo1x2hi1x_5151 into H_sll_nxtx2len1xlo1x2hi1x_5151.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1x2hi1x_5151);
sslauto.
unfold_constructor 2;
exists (len1x), (vx2), (hi1x), (lo1x2), (nxtx2), (h_sll_nxtx2len1xlo1x2hi1x_5151);
sslauto.
Qed.