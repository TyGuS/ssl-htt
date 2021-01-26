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
Lemma pure3 len1x2 : 0 <= 1 + len1x2 -> 0 <= len1x2 -> 1 + len1x2 == 1 + len1x2. Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 hi1x vx2 : vx2 <= 7 -> 0 <= vx2 -> (if hi1x <= vx2 then vx2 else hi1x) == (if hi1x <= vx2 then vx2 else hi1x). Admitted.
Hint Resolve pure4: ssl_pure.
Lemma pure5 vx2 lo1x : vx2 <= 7 -> 0 <= vx2 -> (if vx2 <= lo1x then vx2 else lo1x) == (if vx2 <= lo1x then vx2 else lo1x). Admitted.
Hint Resolve pure5: ssl_pure.

Definition sll_len_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_514,
      0 <= n /\ h = r :-> a \+ h_sll_xnlohi_514 /\ sll x n lo hi h_sll_xnlohi_514,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_515,
      h = r :-> n \+ h_sll_xnlohi_515 /\ sll x n lo hi h_sll_xnlohi_515
    ]).

Program Definition sll_len : sll_len_type :=
  Fix (fun (sll_len : sll_len_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if x == null
      then
        r ::= 0;;
        ret tt
      else
        nxtx2 <-- @read ptr (x .+ 1);
        sll_len (nxtx2, r);;
        len1x2 <-- @read nat r;
        r ::= 1 + len1x2;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a2].
ex_elim h_sll_xnlohi_514.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_514.
ssl_ghostelim_post.
ssl_open (x == null);
ssl_open_post H_sll_xnlohi_514.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto;
solve [
unfold_constructor 1;
sslauto ].
ex_elim len1x2 vx2 hi1x lo1x nxtx2.
ex_elim h_sll_nxtx2len1x2lo1xhi1x_513x.
move=>[phi_sll_xnlohi_5140] [phi_sll_xnlohi_5141] [phi_sll_xnlohi_5142] [phi_sll_xnlohi_5143] [phi_sll_xnlohi_5144] [phi_sll_xnlohi_5145].
move=>[sigma_sll_xnlohi_514].
subst h_sll_xnlohi_514.
move=>H_sll_nxtx2len1x2lo1xhi1x_513x.
ssl_read (x .+ 1).
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1x2lo1xhi1x_513x).
ssl_call (len1x2, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1x2lo1xhi1x_513x);
sslauto.
move=>h_call1.
ex_elim h_sll_nxtx2len1x2lo1xhi1x_5151.
move=>[sigma_call1].
subst h_call1.
move=>H_sll_nxtx2len1x2lo1xhi1x_5151.
store_valid.
ssl_read r.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1x2lo1xhi1x_5151);
sslauto;
solve [
unfold_constructor 2;
exists (len1x2), (vx2), (hi1x), (lo1x), (nxtx2);
exists (h_sll_nxtx2len1x2lo1xhi1x_5151);
sslauto ].
Qed.
