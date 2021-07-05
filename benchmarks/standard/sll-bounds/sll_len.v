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
Lemma pure3 (len1x1 : nat) : (0) <= (len1x1) -> (0) <= ((1) + (len1x1)) -> ((1) + (len1x1)) = ((1) + (len1x1)). intros; hammer. Qed.
Hint Resolve pure3: ssl_pure.
Lemma pure4 (hi1x : nat) (vx1 : nat) : (vx1) <= (7) -> (0) <= (vx1) -> ((if (hi1x) <= (vx1) then vx1 else hi1x)) = ((if (hi1x) <= (vx1) then vx1 else hi1x)). intros; hammer. Qed.
Hint Resolve pure4: ssl_pure.
Lemma pure5 (vx1 : nat) (lo1x : nat) : (vx1) <= (7) -> (0) <= (vx1) -> ((if (vx1) <= (lo1x) then vx1 else lo1x)) = ((if (vx1) <= (lo1x) then vx1 else lo1x)). intros; hammer. Qed.
Hint Resolve pure5: ssl_pure.

Definition sll_len_type :=
  forall (vprogs : ptr * ptr),
  {(vghosts : nat * nat * nat * ptr)},
  STsep (
    fun h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_1,
      (0) <= (n) /\ h = r :-> (a) \+ h_sll_xnlohi_1 /\ sll x n lo hi h_sll_xnlohi_1,
    [vfun (_: unit) h =>
      let: (x, r) := vprogs in
      let: (n, lo, hi, a) := vghosts in
      exists h_sll_xnlohi_2,
      h = r :-> (n) \+ h_sll_xnlohi_2 /\ sll x n lo hi h_sll_xnlohi_2
    ]).

Program Definition sll_len : sll_len_type :=
  Fix (fun (sll_len : sll_len_type) vprogs =>
    let: (x, r) := vprogs in
    Do (
      a1 <-- @read ptr r;
      if (x) == (null)
      then
        r ::= 0;;
        ret tt
      else
        vx1 <-- @read nat x;
        nxtx1 <-- @read ptr (x .+ 1);
        sll_len (nxtx1, r);;
        len1x1 <-- @read nat r;
        r ::= (1) + (len1x1);;
        ret tt
    )).
Obligation Tactic := intro; move=>[x r]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[n lo] hi] a].
ex_elim h_sll_xnlohi_1.
move=>[phi_self0].
move=>[sigma_self].
subst h_self.
move=>H_sll_xnlohi_1.
ssl_ghostelim_post.
ssl_read r.
try rename a into a1.
ssl_open ((x) == (null)) H_sll_xnlohi_1.
move=>[phi_sll_xnlohi_10] [phi_sll_xnlohi_11] [phi_sll_xnlohi_12].
move=>[sigma_sll_xnlohi_1].
subst h_sll_xnlohi_1.
try rename h_sll_xnlohi_1 into h_sll_xnlo_1.
try rename H_sll_xnlohi_1 into H_sll_xnlo_1.
try rename h_sll_xnlohi_2 into h_sll_xnlo_2.
try rename H_sll_xnlohi_2 into H_sll_xnlo_2.
try rename h_sll_xnlo_1 into h_sll_xn_1.
try rename H_sll_xnlo_1 into H_sll_xn_1.
try rename h_sll_xnlo_2 into h_sll_xn_2.
try rename H_sll_xnlo_2 into H_sll_xn_2.
try rename h_sll_xn_2 into h_sll_x_2.
try rename H_sll_xn_2 into H_sll_x_2.
try rename h_sll_xn_1 into h_sll_x_1.
try rename H_sll_xn_1 into H_sll_x_1.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (empty);
sslauto.
ssl_close 1;
sslauto.
ex_elim len1x vx hi1x lo1x nxtx.
ex_elim h_sll_nxtxlen1xlo1xhi1x_0x.
move=>[phi_sll_xnlohi_10] [phi_sll_xnlohi_11] [phi_sll_xnlohi_12] [phi_sll_xnlohi_13] [phi_sll_xnlohi_14] [phi_sll_xnlohi_15].
move=>[sigma_sll_xnlohi_1].
subst h_sll_xnlohi_1.
move=>H_sll_nxtxlen1xlo1xhi1x_0x.
try rename h_sll_xnlohi_1 into h_sll_xnlohi1xvxvxhi1x_1.
try rename H_sll_xnlohi_1 into H_sll_xnlohi1xvxvxhi1x_1.
try rename h_sll_xnlohi_2 into h_sll_xnlohi1xvxvxhi1x_2.
try rename H_sll_xnlohi_2 into H_sll_xnlohi1xvxvxhi1x_2.
try rename h_sll_xnlohi1xvxvxhi1x_2 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename H_sll_xnlohi1xvxvxhi1x_2 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename h_sll_xnlohi1xvxvxhi1x_1 into h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_1.
try rename H_sll_xnlohi1xvxvxhi1x_1 into H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_1.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_2 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_2 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2.
try rename h_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_1 into h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_1.
try rename H_sll_xnvxlo1xvxlo1xhi1xvxvxhi1x_1 into H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_1.
ssl_read x.
try rename vx into vx1.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_1 into h_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_1.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_1 into H_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_1.
try rename h_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2 into h_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
try rename H_sll_xlen1xvxlo1xvxlo1xhi1xvxvxhi1x_2 into H_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
ssl_read (x .+ 1).
try rename nxtx into nxtx1.
try rename h_sll_nxtxlen1xlo1xhi1x_0x into h_sll_nxtx1len1xlo1xhi1x_0x.
try rename H_sll_nxtxlen1xlo1xhi1x_0x into H_sll_nxtx1len1xlo1xhi1x_0x.
try rename h_sll_x1n1lo1hi1_11 into h_sll_nxtx1len1xlo1xhi1x_0x.
try rename H_sll_x1n1lo1hi1_11 into H_sll_nxtx1len1xlo1xhi1x_0x.
ssl_call_pre (r :-> (a1) \+ h_sll_nxtx1len1xlo1xhi1x_0x).
ssl_call (len1x, lo1x, hi1x, a1).
exists (h_sll_nxtx1len1xlo1xhi1x_0x);
sslauto.
ssl_frame_unfold.
move=>h_call0.
ex_elim h_sll_nxtx1len1xlo1xhi1x_21.
move=>[sigma_call0].
subst h_call0.
move=>H_sll_nxtx1len1xlo1xhi1x_21.
store_valid.
ssl_read r.
try rename len1x into len1x1.
try rename h_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_1 into h_sll_xlen1x1vx1lo1xvx1lo1xhi1xvx1vx1hi1x_1.
try rename H_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_1 into H_sll_xlen1x1vx1lo1xvx1lo1xhi1xvx1vx1hi1x_1.
try rename h_sll_nxtx1len1xlo1xhi1x_21 into h_sll_nxtx1len1x1lo1xhi1x_21.
try rename H_sll_nxtx1len1xlo1xhi1x_21 into H_sll_nxtx1len1x1lo1xhi1x_21.
try rename h_sll_nxtx1len1xlo1xhi1x_0x into h_sll_nxtx1len1x1lo1xhi1x_0x.
try rename H_sll_nxtx1len1xlo1xhi1x_0x into H_sll_nxtx1len1x1lo1xhi1x_0x.
try rename h_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2 into h_sll_xlen1x1vx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
try rename H_sll_xlen1xvx1lo1xvx1lo1xhi1xvx1vx1hi1x_2 into H_sll_xlen1x1vx1lo1xvx1lo1xhi1xvx1vx1hi1x_2.
try rename h_sll_nxtx2len1x2lo11xhi11x_0x1 into h_sll_nxtx1len1x1lo1xhi1x_21.
try rename H_sll_nxtx2len1x2lo11xhi11x_0x1 into H_sll_nxtx1len1x1lo1xhi1x_21.
ssl_write r.
ssl_write_post r.
ssl_emp;
exists (x :-> (vx1) \+ x .+ 1 :-> (nxtx1) \+ h_sll_nxtx1len1x1lo1xhi1x_21);
sslauto.
ssl_close 2;
exists (len1x1), (vx1), (hi1x), (lo1x), (nxtx1), (h_sll_nxtx1len1x1lo1xhi1x_21);
sslauto.
ssl_frame_unfold.
Qed.