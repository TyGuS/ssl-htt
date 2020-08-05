From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg1 of x == 0 of
  s = nil /\ h = empty
| lseg2 of ~~ (x == 0) of
  exists v s1 nxt,
  exists h_lseg515,
  s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg515 /\ lseg nxt s1 h_lseg515.

Definition listcopy_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists h_lseg516,
      h = r :-> x \+ h_lseg516 /\ lseg x s h_lseg516,
    [vfun (_: unit) h =>
      let: (r) := vprogs in
      let: (x, s) := vghosts in
      exists y,
      exists h_lseg517 h_lseg518,
      h = r :-> y \+ h_lseg517 \+ h_lseg518 /\ lseg x s h_lseg517 /\ lseg y s h_lseg518
    ]).
Program Definition listcopy : listcopy_type :=
  Fix (fun (listcopy : listcopy_type) vprogs =>
    let: (r) := vprogs in
    Do (
      x2 <-- @read ptr r;
      if x2 == 0
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
move=>[h_lseg516].
move=>[sigma_self].
rewrite->sigma_self in *.
move=>H_lseg516.
ssl_ghostelim_post.
ssl_read.
ssl_open.
ssl_open_post H_lseg516.
move=>[phi_lseg516].
move=>[sigma_lseg516].
rewrite->sigma_lseg516 in *.
ssl_emp;
exists (0);
exists (empty);
exists (empty);
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.
ssl_open_post H_lseg516.
move=>[vx22] [s1x2] [nxtx22].
move=>[h_lseg515x2].
move=>[phi_lseg516].
move=>[sigma_lseg516].
rewrite->sigma_lseg516 in *.
move=>H_lseg515x2.
ssl_read.
ssl_read.
ssl_write.
ssl_call_pre (r :-> nxtx22 \+ h_lseg515x2).
ssl_call (nxtx22, s1x2).
exists (h_lseg515x2);
ssl_emp_post.
move=>h_call2.
move=>[y12].
move=>[h_lseg5171] [h_lseg5181].
move=>[sigma_call2].
rewrite->sigma_call2 in *.
move=>[H_lseg5171 H_lseg5181].
store_valid.
ssl_read.
ssl_alloc y2.
ssl_write.
ssl_write_post r.
ssl_write.
ssl_write_post (y2 .+ 1).
ssl_write.
ssl_write_post y2.
ssl_emp;
exists (y2);
exists (x2 :-> vx22 \+ x2 .+ 1 :-> nxtx22 \+ h_lseg5171);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> y12 \+ h_lseg5181);
ssl_emp_post.
unfold_constructor 2;
exists (vx22), (s1x2), (nxtx22);
exists (h_lseg5171);
ssl_emp_post.
unfold_constructor 2;
exists (vx22), (s1x2), (y12);
exists (h_lseg5181);
ssl_emp_post.

Qed.
