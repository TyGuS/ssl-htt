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
  exists h_sll_nxtlen1lo1hi1_573,
  (0) <= (len1) /\ (0) <= (v) /\ (hi) == ((if (hi1) <= (v) then v else hi1)) /\ (len) == ((1) + (len1)) /\ (lo) == ((if (v) <= (lo1) then v else lo1)) /\ (v) <= (7) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_573 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_573.

Lemma pure49 : (0) = (0). Admitted.
Hint Resolve pure49: ssl_pure.
Lemma pure50 : (7) = (7). Admitted.
Hint Resolve pure50: ssl_pure.
Lemma pure51 len1x : (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). Admitted.
Hint Resolve pure51: ssl_pure.
Lemma pure52 hi1x vx2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (hi1x) <= (vx2) then vx2 else hi1x)) = ((if (hi1x) <= (vx2) then vx2 else hi1x)). Admitted.
Hint Resolve pure52: ssl_pure.
Lemma pure53 vx2 lo1x2 : (vx2) <= (7) -> (0) <= (vx2) -> ((if (vx2) <= (lo1x2) then vx2 else lo1x2)) = ((if (vx2) <= (lo1x2) then vx2 else lo1x2)). Admitted.
Hint Resolve pure53: ssl_pure.

Definition sll_min_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_574,
      h = r :-> a \+ h_sll_xnlohi_574 /\ sll x n lo hi h_sll_xnlohi_574,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_575,
      h = r :-> lo \+ h_sll_xnlohi_575 /\ sll x n lo hi h_sll_xnlohi_575
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
ex_elim h_sll_xnlohi_574.
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_574.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open ((x) == (null)) H_sll_xnlohi_574.
move=>[phi_sll_xnlohi_5740] [phi_sll_xnlohi_5741] [phi_sll_xnlohi_5742].
move=>[sigma_sll_xnlohi_574].
subst h_sll_xnlohi_574.
try rename h_sll_xnlohi_574 into h_sll_xnlo_574.
try rename H_sll_xnlohi_574 into H_sll_xnlo_574.
try rename h_sll_xnlohi_575 into h_sll_xnlo_575.
try rename H_sll_xnlohi_575 into H_sll_xnlo_575.
try rename h_sll_xnlo_574 into h_sll_xn_574.
try rename H_sll_xnlo_574 into H_sll_xn_574.
try rename h_sll_xnlo_575 into h_sll_xn_575.
try rename H_sll_xnlo_575 into H_sll_xn_575.
try rename h_sll_xn_575 into h_sll_x_575.
try rename H_sll_xn_575 into H_sll_x_575.
try rename h_sll_xn_574 into h_sll_x_574.
try rename H_sll_xn_574 into H_sll_x_574.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_573x.
move=>[phi_sll_xnlohi_5740] [phi_sll_xnlohi_5741] [phi_sll_xnlohi_5742] [phi_sll_xnlohi_5743] [phi_sll_xnlohi_5744] [phi_sll_xnlohi_5745].
move=>[sigma_sll_xnlohi_574].
subst h_sll_xnlohi_574.
move=>H_sll_nxtxlen1xlo1xhi1x_573x.
try rename h_sll_xnlohi_574 into h_sll_xnlohi1xvxvxhi1x_574.
try rename H_sll_xnlohi_574 into H_sll_xnlohi1xvxvxhi1x_574.
try rename h_sll_xnlohi_575 into h_sll_xnlohi1xvxvxhi1x_575.
try rename H_sll_xnlohi_575 into H_sll_xnlohi1xvxvxhi1x_575.
try rename h_sll_xnlohi1xvxvxhi1x_574 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_574.
try rename H_sll_xnlohi1xvxvxhi1x_574 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_574.
try rename h_sll_xnlohi1xvxvxhi1x_575 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_575.
try rename H_sll_xnlohi1xvxvxhi1x_575 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_575.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_575 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_575.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_575 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_575.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_574 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_574.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_574 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_574.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_575 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_575.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_575 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_575.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_574 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_574.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_574 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_574.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_573x into h_sll_nxtx2len1xlo1xhi1x_573x.
try rename H_sll_nxtxlen1xlo1xhi1x_573x into H_sll_nxtx2len1xlo1xhi1x_573x.
try rename h_sll_x1n1lo1hi1_5741 into h_sll_nxtx2len1xlo1xhi1x_573x.
try rename H_sll_x1n1lo1hi1_5741 into H_sll_nxtx2len1xlo1xhi1x_573x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_573x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_573x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5751.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5751.
store_valid.
ssl_read r.
try rename lo1x into lo1x2.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_574 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_574.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_574 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_574.
try rename h_sll_nxtx2len1xlo1xhi1x_573x into h_sll_nxtx2len1xlo1x2hi1x_573x.
try rename H_sll_nxtx2len1xlo1xhi1x_573x into H_sll_nxtx2len1xlo1x2hi1x_573x.
try rename h_sll_nxtx2len1xlo1xhi1x_5751 into h_sll_nxtx2len1xlo1x2hi1x_5751.
try rename H_sll_nxtx2len1xlo1xhi1x_5751 into H_sll_nxtx2len1xlo1x2hi1x_5751.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_575 into h_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_575.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_575 into H_sll_xlen1xvx2lo1x2vx2lo1x2hi1xvx2vx2hi1x_575.
try rename h_sll_nxtx1len1x1lo11xhi11x_573x1 into h_sll_nxtx2len1xlo1x2hi1x_5751.
try rename H_sll_nxtx1len1x1lo11xhi11x_573x1 into H_sll_nxtx2len1xlo1x2hi1x_5751.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1x2hi1x_5751);
sslauto.
ssl_close 2;
exists (len1x), (vx2), (hi1x), (lo1x2), (nxtx2), (h_sll_nxtx2len1xlo1x2hi1x_5751);
sslauto.
ssl_frame_unfold.
Qed.