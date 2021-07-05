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
Lemma pure3 (hi1x : nat) (vx1 : nat) : (vx1) <= (7) -> (0) <= (vx1) -> ((if (hi1x) <= (vx1) then vx1 else hi1x)) = ((if (hi1x) <= (vx1) then vx1 else hi1x)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (vx1 : nat) (lo1x : nat) : (vx1) <= (7) -> (0) <= (vx1) -> ((if (vx1) <= (lo1x) then vx1 else lo1x)) = ((if (vx1) <= (lo1x) then vx1 else lo1x)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (len1x : nat) : (0) <= ((1) + (len1x)) -> (0) <= (len1x) -> ((1) + (len1x)) = ((1) + (len1x)). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.

Definition srtl_insert_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists h_srtl_xnlohi_2,
      (0) <= (k) /\ (0) <= (n) /\ (k) <= (7) /\ h = r :-> (k) \+ h_srtl_xnlohi_2 /\ srtl x n lo hi h_srtl_xnlohi_2,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (k, n, lo, hi) := vghosts in
      exists hi1 lo1 n1 y,
      exists h_srtl_yn1lo1hi1_3,
      (hi1) == ((if (hi) <= (k) then k else hi)) /\ (lo1) == ((if (k) <= (lo) then k else lo)) /\ (n1) == ((1) + (n)) /\ h = r :-> (y) \+ h_srtl_yn1lo1hi1_3 /\ srtl y n1 lo1 hi1 h_srtl_yn1lo1hi1_3
    ]).

Variable srtl_insert : srtl_insert_type.

Definition insertion_sort_free_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists h_sll_xnlohi_4,
      (0) <= (n) /\ h = r :-> (null) \+ h_sll_xnlohi_4 /\ sll x n lo hi h_sll_xnlohi_4,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi) := vghosts in
      exists y,
      exists h_srtl_ynlohi_5,
      h = r :-> (y) \+ h_srtl_ynlohi_5 /\ srtl y n lo hi h_srtl_ynlohi_5
    ]).

Program Definition insertion_sort_free : insertion_sort_free_type :=
  Fix (fun (insertion_sort_free : insertion_sort_free_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      if (x) == (null)
      then
        ret tt
      else
        vx1 <-- @read nat x;
        nxtx1 <-- @read ptr (x .+ 1);
        insertion_sort_free (nxtx1, r);;
        y11 <-- @read ptr r;
        r ::= vx1;;
        srtl_insert (y11, r);;
        y21 <-- @read ptr r;
        dealloc x;;
        dealloc (x .+ 1);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[n lo] hi].
ex_elim h_sll_xnlohi_4.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_4.
ssl_ghostelim_post.
ssl_open ((x) == (null)) H_sll_xnlohi_4.
move=>[phi_sll_xnlohi_40] [phi_sll_xnlohi_41] [phi_sll_xnlohi_42].
move=>[sigma_sll_xnlohi_4].
subst h_sll_xnlohi_4.
try rename h_sll_xnlohi_4 into h_sll_xnlo_4.
try rename H_sll_xnlohi_4 into H_sll_xnlo_4.
try rename h_srtl_ynlohi_5 into h_srtl_ynlo_5.
try rename H_srtl_ynlohi_5 into H_srtl_ynlo_5.
try rename h_sll_xnlo_4 into h_sll_xn_4.
try rename H_sll_xnlo_4 into H_sll_xn_4.
try rename h_srtl_ynlo_5 into h_srtl_yn_5.
try rename H_srtl_ynlo_5 into H_srtl_yn_5.
try rename h_srtl_yn_5 into h_srtl_y_5.
try rename H_srtl_yn_5 into H_srtl_y_5.
try rename h_sll_xn_4 into h_sll_x_4.
try rename H_sll_xn_4 into H_sll_x_4.
try rename h_srtl_y_5 into h_srtl__5.
try rename H_srtl_y_5 into H_srtl__5.
ssl_emp;
exists (null);
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_0x.
move=>[phi_sll_xnlohi_40] [phi_sll_xnlohi_41] [phi_sll_xnlohi_42] [phi_sll_xnlohi_43] [phi_sll_xnlohi_44] [phi_sll_xnlohi_45].
move=>[sigma_sll_xnlohi_4].
subst h_sll_xnlohi_4.
move=>H_sll_nxtxlen1xlo1xhi1x_0x.
try rename h_sll_xnlohi_4 into h_sll_xnlohi1xvxvxhi1x_4.
try rename H_sll_xnlohi_4 into H_sll_xnlohi1xvxvxhi1x_4.
try rename h_srtl_ynlohi_5 into h_srtl_ynlohi1xvxvxhi1x_5.
try rename H_srtl_ynlohi_5 into H_srtl_ynlohi1xvxvxhi1x_5.
try rename h_sll_xnlohi1xvxvxhi1x_4 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_4.
try rename H_sll_xnlohi1xvxvxhi1x_4 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_4.
try rename h_srtl_ynlohi1xvxvxhi1x_5 into h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_5.
try rename H_srtl_ynlohi1xvxvxhi1x_5 into H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_5.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_4 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_4.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_4 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_4.
try rename h_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_5 into h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_5.
try rename H_srtl_ynvxlo1xvxlo1xhi1xvxvxhi1x_5 into H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_5.
ssl_read x.
try rename vx into vx1.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_4 into h_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_4.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_4 into H_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_4.
try rename h_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_5 into h_srtl_ylen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_5.
try rename H_srtl_ylen1xvxlo1xvxlo1xhi1xvxvxhi1x_5 into H_srtl_ylen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_5.
ssl_read (x .+ 1).
try rename nxtx into nxtx1.
try rename h_sll_nxtxlen1xlo1xhi1x_0x into h_sll_nxtx1len1xlo1xhi1x_0x.
try rename H_sll_nxtxlen1xlo1xhi1x_0x into H_sll_nxtx1len1xlo1xhi1x_0x.
try rename h_sll_x1n1lo1hi1_41 into h_sll_nxtx1len1xlo1xhi1x_0x.
try rename H_sll_x1n1lo1hi1_41 into H_sll_nxtx1len1xlo1xhi1x_0x.
ssl_call_pre (r :-> (null) \+ h_sll_nxtx1len1xlo1xhi1x_0x).
ssl_call (len1x, lo1x, hi1x).
exists (h_sll_nxtx1len1xlo1xhi1x_0x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim y1.
ex_elim h_srtl_y1len1xlo1xhi1x_51.
move=>[sigma_call0].
subst h_call0.
move=>H_srtl_y1len1xlo1xhi1x_51.
store_valid.
ssl_read r.
try rename y1 into y11.
try rename h_srtl_y1len1xlo1xhi1x_51 into h_srtl_y11len1xlo1xhi1x_51.
try rename H_srtl_y1len1xlo1xhi1x_51 into H_srtl_y11len1xlo1xhi1x_51.
try rename h_srtl_x2n2lo2hi2_2 into h_srtl_y11len1xlo1xhi1x_51.
try rename H_srtl_x2n2lo2hi2_2 into H_srtl_y11len1xlo1xhi1x_51.
ssl_write r.
ssl_call_pre (r :-> (vx1) \+ h_srtl_y11len1xlo1xhi1x_51).
ssl_call (vx1, len1x, lo1x, hi1x).
exists (h_srtl_y11len1xlo1xhi1x_51);
sslauto.
ssl_frame_unfold.
move=>h_call1.
ex_elim hi11 lo11 n11 y2.
ex_elim h_srtl_y2n11lo11hi11_3.
move=>[phi_call10] [phi_call11] [phi_call12].
move=>[sigma_call1].
subst h_call1.
move=>H_srtl_y2n11lo11hi11_3.
store_valid.
try rename h_srtl_y2n11lo11hi11_3 into h_srtl_y2n11lo11hi1xvx1vx1hi1x_3.
try rename H_srtl_y2n11lo11hi11_3 into H_srtl_y2n11lo11hi1xvx1vx1hi1x_3.
try rename h_srtl_y2n11lo11hi1xvx1vx1hi1x_3 into h_srtl_y2n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename H_srtl_y2n11lo11hi1xvx1vx1hi1x_3 into H_srtl_y2n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename h_srtl_y2n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_3 into h_srtl_y2len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename H_srtl_y2n11vx1lo1xvx1lo1xhi1xvx1vx1hi1x_3 into H_srtl_y2len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
ssl_read r.
try rename y2 into y21.
try rename h_srtl_y2len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3 into h_srtl_y21len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename H_srtl_y2len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3 into H_srtl_y21len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename h_srtl_ylen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_5 into h_srtl_y21len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
try rename H_srtl_ylen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_5 into H_srtl_y21len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3.
ssl_dealloc x.
ssl_dealloc (x .+ 1).
ssl_emp;
exists (y21);
exists (h_srtl_y21len1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_3);
sslauto.
ssl_frame_unfold.
Qed.