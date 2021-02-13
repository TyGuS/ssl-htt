From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Definition swap1_type :=
  forall (vprogs : ptr * ptr * ptr * ptr),
  {(vghosts : ptr * ptr * ptr * ptr)},
  STsep (
    fun h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> a \+ y :-> c \+ z :-> b \+ t :-> q,
    [vfun (_: unit) h =>
      let: (x, z, y, t) := vprogs in
      let: (a, c, b, q) := vghosts in
      h = x :-> c \+ z :-> b \+ t :-> q \+ y :-> 41
    ]).

Program Definition swap1 : swap1_type :=
  Fix (fun (swap1 : swap1_type) vprogs =>
    let: (x, z, y, t) := vprogs in
    Do (
      a2 <-- @read ptr x;
      c2 <-- @read ptr y;
      b2 <-- @read ptr z;
      q2 <-- @read ptr t;
      x ::= c2;;
      y ::= 41;;
      ret tt
    )).
Obligation Tactic := intro; move=>[[[x z] y] t]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[[[a c] b] q].
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
ssl_read x.
try rename a into a2.
ssl_read y.
try rename c into c2.
ssl_read z.
try rename b into b2.
ssl_read t.
try rename q into q2.
ssl_write x.
ssl_write_post x.
ssl_write y.
ssl_write_post y.
ssl_emp;
sslauto.
Qed.