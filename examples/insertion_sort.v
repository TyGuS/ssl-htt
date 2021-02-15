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

Inductive srtl (x : ptr) (len : nat) (lo : nat) (hi : nat) (h : heap) : Prop :=
| srtl_1 of x == null of
  hi == 0 /\ len == 0 /\ lo == 7 /\ h = empty
| srtl_2 of (x == null) = false of
  exists (len1 : nat) (v : nat) (hi1 : nat) (lo1 : nat) (nxt : ptr),
  exists h_srtl_nxtlen1lo1hi1_514,
  0 <= len1 /\ 0 <= v /\ hi == (if hi1 <= v then v else hi1) /\ len == 1 + len1 /\ lo == (if v <= lo1 then v else lo1) /\ v <= 7 /\ v <= lo1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_srtl_nxtlen1lo1hi1_514 /\ srtl nxt len1 lo1 hi1 h_srtl_nxtlen1lo1hi1_514.

Lemma pure1 : 0 == 0. Admitted.
Hint Resolve pure1: ssl_pure.
Lemma pure2 : 7 == 7. Admitted.
Hint Resolve pure2: ssl_pure.
Lemma pure3 hi1x vx2 : 0 <= vx2 -> vx2 <= 7 -> (if hi1x <= vx2 then vx2 else hi1x) == (if hi1x <= vx2 then vx2 else hi1x). Admitted.
Hint Resolve pure3: ssl_pure.
Lemma pure4 len1x : 0 <= 1 + len1x -> 0 <= len1x -> 1 + len1x == 1 + len1x. Admitted.
Hint Resolve pure4: ssl_pure.
Lemma pure5 vx2 lo1x : 0 <= vx2 -> vx2 <= 7 -> (if vx2 <= lo1x then vx2 else lo1x) == (if vx2 <= lo1x then vx2 else lo1x). Admitted.
Hint Resolve pure5: ssl_pure.
Lemma pure6 hi1x vx2 : 0 <= vx2 -> vx2 <= 7 -> (if hi1x <= vx2 then vx2 else hi1x) == (if hi1x <= vx2 then vx2 else hi1x). Admitted.
Hint Resolve pure6: ssl_pure.
Lemma pure7 vx2 lo1x : 0 <= vx2 -> vx2 <= 7 -> (if vx2 <= lo1x then vx2 else lo1x) == (if vx2 <= lo1x then vx2 else lo1x). Admitted.
Hint Resolve pure7: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_515,
      0 <= k /\ 0 <= n /\ k <= 7 /\ h = r :-> k \+ h_srtl_xnlohi_515 /\ srtl x n lo hi h_srtl_xnlohi_515,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_516,
      hi1 == (if hi <= k then k else hi) /\ lo1 == (if k <= lo then k else lo) /\ n1 == 1 + n /\ h = r :-> y \+ h_srtl_yn1lo1hi1_516 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_516
    ]).

Variable srtl_insert : srtl_insert_type.

Definition insertion_sort_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_517,
      0 <= n /\ h = r :-> null \+ h_sll_xnlohi_517 /\ sll x n lo hi h_sll_xnlohi_517,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_sll_xnlohi_518 h_srtl_ynlohi_519,
      h = r :-> y \+ h_sll_xnlohi_518 \+ h_srtl_ynlohi_519 /\ sll x n lo hi h_sll_xnlohi_518 /\ srtl y n lo hi h_srtl_ynlohi_519
    ]).

Program Definition insertion_sort : insertion_sort_type :=
  Fix (fun (insertion_sort : insertion_sort_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if x == null
      then
        ret tt
      else
        vx2 <-- @read nat x;
        nxtx2 <-- @read ptr (x .+ 1);
        insertion_sort (nxtx2, r);;
        y12 <-- @read ptr r;
        r ::= vx2;;
        srtl_insert (y12, r);;
        y22 <-- @read ptr r;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[n lo] hi].
ex_elim h_sll_xnlohi_517.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_517.
ssl_ghostelim_post.
ssl_open (x == null) H_sll_xnlohi_517.
move=>[phi_sll_xnlohi_5170] [phi_sll_xnlohi_5171] [phi_sll_xnlohi_5172].
move=>[sigma_sll_xnlohi_517].
subst h_sll_xnlohi_517.
shelve.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_513x.
move=>[phi_sll_xnlohi_5170] [phi_sll_xnlohi_5171] [phi_sll_xnlohi_5172] [phi_sll_xnlohi_5173] [phi_sll_xnlohi_5174] [phi_sll_xnlohi_5175].
move=>[sigma_sll_xnlohi_517].
subst h_sll_xnlohi_517.
move=>H_sll_nxtxlen1xlo1xhi1x_513x.
shelve.
Unshelve.
try rename h_sll_xnlohi_517 into h_sll_xnlo_517.
try rename H_sll_xnlohi_517 into H_sll_xnlo_517.
try rename h_sll_xnlohi_518 into h_sll_xnlo_518.
try rename H_sll_xnlohi_518 into H_sll_xnlo_518.
try rename h_srtl_ynlohi_519 into h_srtl_ynlo_519.
try rename H_srtl_ynlohi_519 into H_srtl_ynlo_519.
try rename h_srtl_ynlo_519 into h_srtl_yn_519.
try rename H_srtl_ynlo_519 into H_srtl_yn_519.
try rename h_sll_xnlo_518 into h_sll_xn_518.
try rename H_sll_xnlo_518 into H_sll_xn_518.
try rename h_sll_xnlo_517 into h_sll_xn_517.
try rename H_sll_xnlo_517 into H_sll_xn_517.
try rename h_sll_xn_517 into h_sll_x_517.
try rename H_sll_xn_517 into H_sll_x_517.
try rename h_srtl_yn_519 into h_srtl_y_519.
try rename H_srtl_yn_519 into H_srtl_y_519.
try rename h_sll_xn_518 into h_sll_x_518.
try rename H_sll_xn_518 into H_sll_x_518.
try rename h_srtl_y_519 into h_srtl__519.
try rename H_srtl_y_519 into H_srtl__519.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
unfold_constructor 1;
sslauto.
try rename h_sll_xnlohi_517 into h_sll_xnlohi1xvxvxhi1x_517.
try rename H_sll_xnlohi_517 into H_sll_xnlohi1xvxvxhi1x_517.
try rename h_sll_xnlohi_518 into h_sll_xnlohi1xvxvxhi1x_518.
try rename H_sll_xnlohi_518 into H_sll_xnlohi1xvxvxhi1x_518.
try rename h_srtl_ynlohi_519 into h_srtl_ynlohi1xvxvxhi1x_519.
try rename H_srtl_ynlohi_519 into H_srtl_ynlohi1xvxvxhi1x_519.
try rename h_sll_xnlohi1xvxvxhi1x_517 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename H_sll_xnlohi1xvxvxhi1x_517 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename h_sll_xnlohi1xvxvxhi1x_518 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename H_sll_xnlohi1xvxvxhi1x_518 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename h_srtl_ynlohi1xvxvxhi1x_519 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_519.
try rename H_srtl_ynlohi1xvxvxhi1x_519 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_519.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_519 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_519.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_519 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_519.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_518 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_517 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517.
ssl_read x.
try rename vx into vx2.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_518 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_518.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517 into h_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_517 into H_sll_xlen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_517.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_519 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_519.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_519 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_519.
ssl_read (x .+ 1).
try rename nxtx into nxtx2.
try rename h_sll_nxtxlen1xlo1xhi1x_513x into h_sll_nxtx2len1xlo1xhi1x_513x.
try rename H_sll_nxtxlen1xlo1xhi1x_513x into H_sll_nxtx2len1xlo1xhi1x_513x.
ssl_call_pre (r :-> null \+ h_sll_nxtx2len1xlo1xhi1x_513x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx2len1xlo1xhi1x_513x);
sslauto.
move=>h_call0.
ex_elim y1.
ex_elim h_sll_nxtx2len1xlo1xhi1x_5181 h_srtl_y1len1xlo1xhi1x_5191.
move=>[sigma_call0].
subst h_call0.
move=>[H_sll_nxtx2len1xlo1xhi1x_5181 H_srtl_y1len1xlo1xhi1x_5191].
store_valid.
ssl_read r.
try rename y1 into y12.
try rename h_srtl_y1len1xlo1xhi1x_5191 into h_srtl_y12len1xlo1xhi1x_5191.
try rename H_srtl_y1len1xlo1xhi1x_5191 into H_srtl_y12len1xlo1xhi1x_5191.
ssl_write r.
ssl_call_pre (r :-> vx2 \+ h_srtl_y12len1xlo1xhi1x_5191).
ssl_call (vx2, len1x, lo1x, hi1x).
exists (h_srtl_y12len1xlo1xhi1x_5191);
sslauto.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_516.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_516.
store_valid.
try rename h_srtl_y2n11lo11hi11_516 into h_srtl_y2n11lo11hi1xvx2vx2hi1x_516.
try rename H_srtl_y2n11lo11hi11_516 into H_srtl_y2n11lo11hi1xvx2vx2hi1x_516.
try rename h_srtl_y2n11lo11hi1xvx2vx2hi1x_516 into h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename H_srtl_y2n11lo11hi1xvx2vx2hi1x_516 into H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename h_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename H_srtl_y2n11vx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
ssl_read r.
try rename y2 into y22.
try rename h_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename H_srtl_y2len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_519 into h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_519 into H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename h_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename H_srtl_ylen1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516 into H_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516.
try rename h_sll_nxtx1len1x1lo12xhi12x_513x1 into h_sll_nxtx1len1x1lo12xhi12x_5181.
try rename H_sll_nxtx1len1x1lo12xhi12x_513x1 into H_sll_nxtx1len1x1lo12xhi12x_5181.
try rename h_sll_nxtx1len1x1lo12xhi12x_5181 into h_sll_nxtx1len1x1lo12xhi1x_5181.
try rename H_sll_nxtx1len1x1lo12xhi12x_5181 into H_sll_nxtx1len1x1lo12xhi1x_5181.
try rename h_sll_nxtx1len1x1lo12xhi1x_5181 into h_sll_nxtx1len1xlo12xhi1x_5181.
try rename H_sll_nxtx1len1x1lo12xhi1x_5181 into H_sll_nxtx1len1xlo12xhi1x_5181.
try rename h_sll_nxtx1len1xlo12xhi1x_5181 into h_sll_nxtx1len1xlo1xhi1x_5181.
try rename H_sll_nxtx1len1xlo12xhi1x_5181 into H_sll_nxtx1len1xlo1xhi1x_5181.
try rename h_sll_nxtx1len1xlo1xhi1x_5181 into h_sll_nxtx2len1xlo1xhi1x_5181.
try rename H_sll_nxtx1len1xlo1xhi1x_5181 into H_sll_nxtx2len1xlo1xhi1x_5181.
ssl_emp;
exists (y22);
exists (x :-> vx2 \+ x .+ 1 :-> nxtx2 \+ h_sll_nxtx2len1xlo1xhi1x_5181);
exists (h_srtl_y22len1xvx2lo1xvx2lo1xhi1xvx2vx2hi1x_516);
sslauto.
unfold_constructor 2;
exists (len1x), (vx2), (hi1x), (lo1x), (nxtx2), (h_sll_nxtx2len1xlo1xhi1x_5181);
sslauto.
Qed.
