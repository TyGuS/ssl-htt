From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

(*
void listcopy (loc r) {
  let x = *r;
  if (x == 0) {
  } else {
    let v = *x;
    let n = *(x + 1);
    *r = n;
    listcopy(r);
    let y1 = *r;
    let y = malloc(2);
    *r = y;
    *(y + 1) = y1;
    *y = v;
  }
}
 *)

Inductive lseg (x : ptr) (s : seq nat) (h : heap) : Prop :=
| lseg0 of x == 0 of
    s = nil /\ h = empty
| lseg1 of x != 0 of
  exists nxt s1 v,
  exists h_lseg513,
    s = [:: v] ++ s1 /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_lseg513 /\ lseg nxt s1 h_lseg513
.
Definition listcopy_type :=
  forall (r : ptr),
  {(args: ptr * seq nat)},
    STsep (
      fun h =>
        let: (x, s) := args in
        exists h_lseg514,
          h = r :-> x \+ h_lseg514 /\ lseg x s h_lseg514,
      [vfun (_: unit) h =>
        let: (x, s) := args in
        exists y,
        exists h_lseg515 h_lseg516,
          h = r :-> y \+ h_lseg515 \+ h_lseg516 /\ lseg x s h_lseg515 /\ lseg y s h_lseg516
      ]).
Program Definition listcopy : listcopy_type :=
  Fix (fun (listcopy : listcopy_type) r =>
    Do (
  x2 <-- @read ptr r;
  if x2 == 0
  then
    ret tt
  else
    vx22 <-- @read nat x2;
    nxtx22 <-- @read ptr (x2 .+ 1);
    r ::= nxtx22;;
    listcopy r;;
    y12 <-- @read ptr r;
    y2 <-- allocb null 2;
    r ::= y2;;
    (y2 .+ 1) ::= y12;;
    y2 ::= vx22;;
    ret tt
    )).
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
move=>[h_lseg514].
move=>[sigma_root].
rewrite->sigma_root in *.
move=>H_lseg514.
ssl_ghostelim_post.
ssl_read.
ssl_open.
ssl_open_post H_lseg514.
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
ssl_emp;
exists (0);
exists (empty);
exists (empty);
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.
unfold_constructor 1;
ssl_emp_post.
ssl_open_post H_lseg514.
move=>[nxtx22] [s1x2] [vx22].
move=>[h_lseg513x2].
move=>[phi_lseg514].
move=>[sigma_lseg514].
rewrite->sigma_lseg514 in *.
move=>H_lseg513x2.
ssl_read.
ssl_read.
ssl_write.
ssl_call_pre (r :-> nxtx22 \+ h_lseg513x2).
ssl_call (nxtx22, s1x2).
exists (h_lseg513x2);
ssl_emp_post.
move=>h_call1776063260.
move=>[y12].
move=>[h_lseg5151] [h_lseg5161].
move=>[sigma_call1776063260].
rewrite->sigma_call1776063260 in *.
move=>[H_lseg5151 H_lseg5161].
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
exists (x2 :-> vx22 \+ x2 .+ 1 :-> nxtx22 \+ h_lseg5151);
exists (y2 :-> vx22 \+ y2 .+ 1 :-> y12 \+ h_lseg5161);
ssl_emp_post.
unfold_constructor 2;
exists (nxtx22), (s1x2), (vx22);
exists (h_lseg5151);
ssl_emp_post.
unfold_constructor 2;
exists (y12), (s1x2), (vx22);
exists (h_lseg5161);
ssl_emp_post.

Qed.
