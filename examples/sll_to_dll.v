From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive dll (x : ptr) (z : ptr) (s : seq nat) (h : heap) : Prop :=
| dll1 of x == null of
  perm_eq (s) (nil) /\ h = empty
| dll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (w : ptr),
  exists h_dll_wxs1_552,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> w \+ x .+ 2 :-> z \+ h_dll_wxs1_552 /\ dll w x s1 h_dll_wxs1_552.

Inductive sll (x : ptr) (s : seq nat) (h : heap) : Prop :=
| sll1 of x == null of
  perm_eq (s) (nil) /\ h = empty
| sll2 of ~~ (x == null) of
  exists (v : nat) (s1 : seq nat) (nxt : ptr),
  exists h_sll_nxts1_553,
  perm_eq (s) ([:: v] ++ s1) /\ h = x :-> v \+ x .+ 1 :-> nxt \+ h_sll_nxts1_553 /\ sll nxt s1 h_sll_nxts1_553.

Definition sll_to_dll_type :=
  forall (vprogs : ptr),
  {(vghosts : ptr * seq nat)},
  STsep (
    fun h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists h_sll_xs_554,
      h = f :-> x \+ h_sll_xs_554 /\ sll x s h_sll_xs_554,
    [vfun (_: unit) h =>
      let: (f) := vprogs in
      let: (x, s) := vghosts in
      exists i,
      exists h_dll_is_555,
      h = f :-> i \+ h_dll_is_555 /\ dll i null s h_dll_is_555
    ]).
Program Definition sll_to_dll : sll_to_dll_type :=
  Fix (fun (sll_to_dll : sll_to_dll_type) vprogs =>
    let: (f) := vprogs in
    Do (
      x2 <-- @read ptr f;
      if x2 == null
      then
        ret tt
      else
        vx22 <-- @read nat x2;
        nxtx22 <-- @read ptr (x2 .+ 1);
        f ::= nxtx22;;
        sll_to_dll (f);;
        i12 <-- @read ptr f;
        if i12 == null
        then
          i2 <-- allocb null 3;
          dealloc x2;;
          dealloc (x2 .+ 1);;
          f ::= i2;;
          (i2 .+ 1) ::= null;;
          (i2 .+ 2) ::= null;;
          i2 ::= vx22;;
          ret tt
        else
          i2 <-- allocb null 3;
          dealloc x2;;
          dealloc (x2 .+ 1);;
          (i12 .+ 2) ::= i2;;
          f ::= i2;;
          (i2 .+ 1) ::= i12;;
          (i2 .+ 2) ::= null;;
          i2 ::= vx22;;
          ret tt
    )).
Obligation Tactic := intro; move=>f; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>[x2 s].
ex_elim h_sll_x2s_554.
move=>[sigma_self].
subst.
move=>H_sll_x2s_554.
ssl_ghostelim_post.
ssl_read f.
ssl_open.
ssl_open_post H_sll_x2s_554.
move=>[phi_sll_x2s_554].
move=>[sigma_sll_x2s_554].
subst.
ssl_emp;
exists (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_sll_x2s_554.
ex_elim vx22 s1x2 nxtx22.
ex_elim h_sll_nxtx22s1x2_553x2.
move=>[phi_sll_x2s_554].
move=>[sigma_sll_x2s_554].
subst.
move=>H_sll_nxtx22s1x2_553x2.
ssl_read x2.
ssl_read (x2 .+ 1).
ssl_write f.
ssl_call_pre (f :-> nxtx22 \+ h_sll_nxtx22s1x2_553x2).
ssl_call (nxtx22, s1x2).
exists (h_sll_nxtx22s1x2_553x2);
sslauto.
move=>h_call13.
ex_elim i12.
ex_elim h_dll_i12s1x2_5551.
move=>[sigma_call13].
subst.
move=>H_dll_i12s1x2_5551.
store_valid.
ssl_read f.
ssl_open.
ssl_open_post H_dll_i12s1x2_5551.
move=>[phi_dll_i12s1x2_5551].
move=>[sigma_dll_i12s1x2_5551].
subst.
ssl_alloc i2.
ssl_dealloc (x2).
ssl_dealloc (x2 .+ 1).
ssl_write f.
ssl_write_post f.
ssl_write (i2 .+ 1).
ssl_write_post (i2 .+ 1).
ssl_write (i2 .+ 2).
ssl_write_post (i2 .+ 2).
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> null \+ i2 .+ 2 :-> null);
sslauto.
unfold_constructor 2;
exists (vx22), (nil), (null);
exists (empty);
sslauto.
unfold_constructor 1;
sslauto.
ssl_open_post H_dll_i12s1x2_5551.
ex_elim vi122 s1i12 wi122.
ex_elim h_dll_wi122i12s1i12_552i12.
move=>[phi_dll_i12s1x2_5551].
move=>[sigma_dll_i12s1x2_5551].
subst.
move=>H_dll_wi122i12s1i12_552i12.
ssl_alloc i2.
ssl_dealloc (x2).
ssl_dealloc (x2 .+ 1).
ssl_write (i12 .+ 2).
ssl_write_post (i12 .+ 2).
ssl_write f.
ssl_write_post f.
ssl_write (i2 .+ 1).
ssl_write_post (i2 .+ 1).
ssl_write (i2 .+ 2).
ssl_write_post (i2 .+ 2).
ssl_write i2.
ssl_write_post i2.
ssl_emp;
exists (i2);
exists (i2 :-> vx22 \+ i2 .+ 1 :-> i12 \+ i2 .+ 2 :-> null \+ i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_552i12);
sslauto.
unfold_constructor 2;
exists (vx22), ([:: vi122] ++ s1i12), (i12);
exists (i12 :-> vi122 \+ i12 .+ 1 :-> wi122 \+ i12 .+ 2 :-> i2 \+ h_dll_wi122i12s1i12_552i12);
sslauto.
unfold_constructor 2;
exists (vi122), (s1i12), (wi122);
exists (h_dll_wi122i12s1i12_552i12);
sslauto.

Qed.
