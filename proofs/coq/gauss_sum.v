Require Import Arith Lia.

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0    => 0
  | S k  => n + sum_to k
  end.

(* 1 + 2 + ... + n = n(n+1)/2, stated without division. *)
Theorem gauss_sum : forall n, 2 * sum_to n = n * (n + 1).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - simpl sum_to. nia.
Qed.
