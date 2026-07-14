(* Example submission proof — n * 1 = n.
   Self-contained: compiles with `coqc proof.v`. *)
Require Import Arith.

Theorem mul_one_r : forall n : nat, n * 1 = n.
Proof.
  intros n. induction n as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
