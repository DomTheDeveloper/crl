Require Import Arith.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.
