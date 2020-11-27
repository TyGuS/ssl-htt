From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg1 of x == null of
  perm_eq (s) (nil) /\ h = empty
| lseg2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_lseg_nxts1_515,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg_nxts1_515 /\ lseg nxt s1 h_lseg_nxts1_515.

Definition listcopy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_lseg_xs_516,
      h = r :-> x \+ h_lseg_xs_516 /\ lseg x s h_lseg_xs_516,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_lseg_xs_517 h_lseg_ys_518,
      h = r :-> y \+ h_lseg_xs_517 \+ h_lseg_ys_518 /\ lseg x s h_lseg_xs_517 /\ lseg y s h_lseg_ys_518
    ]).
Program Definition listcopy : listcopy_type :=
  Fix (fun (listcopy : listcopy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        r ::= nxtx22;;
        listcopy (r);;
        y12 <-- @read ptr r;
        y2 <-- allocb null 2;
        r ::= y2;;
        (y2 .+ 1) ::= y12;;
        y2 ::= vx22;;
        ret tt
    )).
Obligation Tactic := intro; move=>r; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
ex_elim h_lseg_x2s_516.
move=>[sigma_self].
subst.
move=>H_lseg_x2s_516.
ssl_ghostelim_post.
ssl_read r.
ssl_open.
ssl_open_post H_lseg_x2s_516.
move=>[phi_lseg_x2s_516].
move=>[sigma_lseg_x2s_516].
subst.
ssl_emp;
exists (null);
exists (empty);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_lseg_x2s_516.
ex_elim vx22 s1x2 nxtx22.
ex_elim h_lseg_nxtx22s1x2_515x2.
move=>[phi_lseg_x2s_516].
move=>[sigma_lseg_x2s_516].
subst.
move=>H_lseg_nxtx22s1x2_515x2.
ssl_read x2.
ssl_read (x2 .+ 1).
ssl_write r.
ssl_call_pre (r :-> nxtx22 \+ h_lseg_nxtx22s1x2_515x2).
ssl_call (nxtx22, s1x2).
exists (h_lseg_nxtx22s1x2_515x2);
sslauto.
move=>h_call2.
ex_elim y12.
ex_elim h_lseg_nxtx22s1x2_5171 h_lseg_y12s1x2_5181.
move=>[sigma_call2].
subst.
move=>[H_lseg_nxtx22s1x2_5171 H_lseg_y12s1x2_5181].
store_valid.
ssl_read r.
ssl_alloc y2.
ssl_write r.
ssl_write_post r.
ssl_write (y2 .+ 1).
ssl_write_post (y2 .+ 1).
ssl_write y2.
ssl_write_post y2.
ssl_emp;
exists (y2);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> nxtx22 \+ h_lseg_nxtx22s1x2_5171);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> y12 \+ h_lseg_y12s1x2_5181);
sslauto.
unfold_constructor 2;
exists (vx22), (s1x2), (nxtx22);
exists (h_lseg_nxtx22s1x2_5171);
sslauto.
unfold_constructor 2;
exists (vx22), (s1x2), (y12);
exists (h_lseg_y12s1x2_5181);
sslauto.

Qed.
