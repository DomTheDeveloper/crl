Require Import Arith.

Definition Even (n : nat) := exists k, n = 2 * k.

Theorem even_plus_even : forall n m,
  Even n -> Even m -> Even (n + m).
Proof.
  intros n m [a Ha] [b Hb].
  exists (a + b).
  rewrite Ha, Hb.
  symmetry. apply Nat.mul_add_distr_l.
Qed.
