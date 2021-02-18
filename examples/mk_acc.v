From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From fcsl
Require Import prelude pred pcm unionmap heap.
From HTT
Require Import stmod stsep stlog stlogR.
From SSL
Require Import core.

Inductive account (x : ptr) (id : nat) (bal : nat) (h : heap) : Prop :=
| account_1 of true of
  h = x :-> id \+ x .+ 1 :-> bal.

Definition mk_acc_type :=
  forall (vprogs : ptr * nat),
  {(vghosts : nat)},
  STsep (
    fun h =>
      let: (r, id) := vprogs in
      let: (bal) := vghosts in
      h = r :-> bal,
    [vfun (_: unit) h =>
      let: (r, id) := vprogs in
      let: (bal) := vghosts in
      exists x,
      exists h_account_xidbal_513,
      h = r :-> x \+ h_account_xidbal_513 /\ account x id bal h_account_xidbal_513
    ]).

Program Definition mk_acc : mk_acc_type :=
  Fix (fun (mk_acc : mk_acc_type) vprogs =>
    let: (r, id) := vprogs in
    Do (
      bal2 <-- @read nat r;
      x2 <-- allocb null 2;
      r ::= x2;;
      x2 ::= id;;
      (x2 .+ 1) ::= bal2;;
      ret tt
    )).
Obligation Tactic := intro; move=>[r id]; ssl_program_simpl.
Next Obligation.
ssl_ghostelim_pre.
move=>bal.
move=>[sigma_self].
subst h_self.
ssl_ghostelim_post.
ssl_read r.
try rename bal into bal2.
try rename h_account_xidbal_513 into h_account_xidbal2_513.
try rename H_account_xidbal_513 into H_account_xidbal2_513.
ssl_alloc x2.
try rename x into x2.
try rename h_account_xidbal2_513 into h_account_x2idbal2_513.
try rename H_account_xidbal2_513 into H_account_x2idbal2_513.
ssl_write r.
ssl_write_post r.
ssl_write x2.
ssl_write_post x2.
ssl_write (x2 .+ 1).
ssl_write_post (x2 .+ 1).
ssl_emp;
exists (x2);
exists (x2 :-> id \+ x2 .+ 1 :-> bal2);
sslauto.
unfold_constructor 1;
sslauto.
Qed.