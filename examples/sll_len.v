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
  exists h_sll_nxtlen1lo1hi1_516,
  0 <= len1 /\ 0 <= v /\ hi == (if hi1 <= v then v else hi1) /\ len == 1 + len1 /\ lo == (if v <= lo1 then v else lo1) /\ v <= 7 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxtlen1lo1hi1_516 /\ sll nxt len1 lo1 hi1 h_sll_nxtlen1lo1hi1_516.

Lemma pure6 : 0 == 0. Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 : 7 == 7. Admitted.
Hint Resolve pure7: ssl_pure.
Lemma pure8 len1x2 : 0 <= 1 + len1x2 -> 0 <= len1x2 -> 1 + len1x2 == 1 + len1x2. Admitted.
Hint Resolve pure8: ssl_pure.
Lemma pure9 hi1x vx2 : 0 <= vx2 -> vx2 <= 7 -> (if hi1x <= vx2 then vx2 else hi1x) == (if hi1x <= vx2 then vx2 else hi1x). Admitted.
Hint Resolve pure9: ssl_pure.
Lemma pure10 vx2 lo1x : 0 <= vx2 -> vx2 <= 7 -> (if vx2 <= lo1x then vx2 else lo1x) == (if vx2 <= lo1x then vx2 else lo1x). Admitted.
Hint Resolve pure10: ssl_pure.

Definition sll_len_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_517,
      0 <= n /\ h = r :-> a \+ h_sll_xnlohi_517 /\ sll x n lo hi h_sll_xnlohi_517,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_518,
      h = r :-> n \+ h_sll_xnlohi_518 /\ sll x n lo hi h_sll_xnlohi_518
    ]).

Program Definition sll_len : sll_len_type :=
  Fix (fun (sll_len : sll_len_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a2 <-- @read ptr r;
      if x == null
      then
        r ::= 0;;
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        sll_len (nxtx2, r);;
        len1x2 <-- @read nat r;
        r ::= 1 + len1x2;;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_517.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_517.
ssl_ghostelim_post.
ssl_read r.
try rename a into a2.
ssl_open (x == null) H_sll_xnlohi_517.
move=>[phi_sll_xnlohi_5170] [phi_sll_xnlohi_5171] [phi_sll_xnlohi_5172].
move=>[sigma_sll_xnlohi_517].
subst h_sll_xnlohi_517.
shelve.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_516x.
move=>[phi_sll_xnlohi_5170] [phi_sll_xnlohi_5171] [phi_sll_xnlohi_5172] [phi_sll_xnlohi_5173] [phi_sll_xnlohi_5174] [phi_sll_xnlohi_5175].
move=>[sigma_sll_xnlohi_517].
subst h_sll_xnlohi_517.
move=>H_sll_nxtxlen1xlo1xhi1x_516x.
shelve.
Unshelve.
try rename h_sll_xnlohi_517 into h_sll_xnlo_517.
try rename H_sll_xnlohi_517 into H_sll_xnlo_517.
try rename h_sll_xnlohi_518 into h_sll_xnlo_518.
try rename H_sll_xnlohi_518 into H_sll_xnlo_518.
try rename h_sll_xnlo_517 into h_sll_xn_517.
try rename H_sll_xnlo_517 into H_sll_xn_517.
try rename h_sll_xnlo_518 into h_sll_xn_518.
try rename H_sll_xnlo_518 into H_sll_xn_518.
try rename h_sll_xn_517 into h_sll_x_517.
try rename H_sll_xn_517 into H_sll_x_517.
try rename h_sll_xn_518 into h_sll_x_518.
try rename H_sll_xn_518 into H_sll_x_518.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
try rename h_sll_xnlohi_517 into h_sll_xnlohi1xvxvxhi1x_517.
try rename H_sll_xnlohi_517 into H_sll_xnlohi1xvxvxhi1x_517.
try rename h_sll_xnlohi_518 into h_sll_xnlohi1xvxvxhi1x_518.
try rename H_sll_xnlohi_518 into H_sll_xnlohi1xvxvxhi1x_518.
try rename h_sll_xnlohi1xvxvxhi1x_517 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename H_sll_xnlohi1xvxvxhi1x_517 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename h_sll_xnlohi1xvxvxhi1x_518 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename H_sll_xnlohi1xvxvxhi1x_518 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_516x into h_sll_nxtx2len1xlo1xhi1x_516x.
try rename H_sll_nxtxlen1xlo1xhi1x_516x into H_sll_nxtx2len1xlo1xhi1x_516x.
ssl_call_pre (r :-> a2 \+ h_sll_nxtx2len1xlo1xhi1x_516x).
ssl_call (len1x, lo1x, hi1x, a2).
exists (h_sll_nxtx2len1xlo1xhi1x_516x);
sslauto.
move=>h_call0.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5181.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx2len1xlo1xhi1x_5181.
store_valid.
ssl_read r.
try rename len1x into len1x2.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518 into h_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518 into H_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename h_sll_nxtx2len1xlo1xhi1x_5181 into h_sll_nxtx2len1x2lo1xhi1x_5181.
try rename H_sll_nxtx2len1xlo1xhi1x_5181 into H_sll_nxtx2len1x2lo1xhi1x_5181.
try rename h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517 into h_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
try rename H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517 into H_sll_xlen1x2vx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
try rename h_sll_nxtx2len1xlo1xhi1x_516x into h_sll_nxtx2len1x2lo1xhi1x_516x.
try rename H_sll_nxtx2len1xlo1xhi1x_516x into H_sll_nxtx2len1x2lo1xhi1x_516x.
try rename h_sll_nxtx1len1x1lo11xhi11x_516x1 into h_sll_nxtx1len1x1lo11xhi11x_5181.
try rename H_sll_nxtx1len1x1lo11xhi11x_516x1 into H_sll_nxtx1len1x1lo11xhi11x_5181.
try rename h_sll_nxtx1len1x1lo11xhi11x_5181 into h_sll_nxtx1len1x1lo11xhi1x_5181.
try rename H_sll_nxtx1len1x1lo11xhi11x_5181 into H_sll_nxtx1len1x1lo11xhi1x_5181.
try rename h_sll_nxtx1len1x1lo11xhi1x_5181 into h_sll_nxtx1len1x2lo11xhi1x_5181.
try rename H_sll_nxtx1len1x1lo11xhi1x_5181 into H_sll_nxtx1len1x2lo11xhi1x_5181.
try rename h_sll_nxtx1len1x2lo11xhi1x_5181 into h_sll_nxtx1len1x2lo1xhi1x_5181.
try rename H_sll_nxtx1len1x2lo11xhi1x_5181 into H_sll_nxtx1len1x2lo1xhi1x_5181.
try rename h_sll_nxtx1len1x2lo1xhi1x_5181 into h_sll_nxtx2len1x2lo1xhi1x_5181.
try rename H_sll_nxtx1len1x2lo1xhi1x_5181 into H_sll_nxtx2len1x2lo1xhi1x_5181.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1x2lo1xhi1x_5181);
sslauto.
unfold_constructor 2;
exists (len1x2), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1x2lo1xhi1x_5181);
sslauto.
Qed.