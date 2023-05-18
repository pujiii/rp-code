Require Export UniMath.Foundations.All.

Module Export S1.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : base = base)
  : forall x : S1, P x :=
  fun x =>
    match x with
    | base => transportf P l b
    end.

End S1.

Lemma circle_connected : forall (z: S1), exists p : z = base, True.
Proof.
  intro x.
  apply (S1_ind (fun x => exists p : x = base, True)).
  - exists (idpath base).
    exact I.
  - apply loop.
Qed.

Lemma base_refl : base = base.
Proof.
  reflexivity.
Qed.

Lemma circle_eq_sym : forall (x y : S1), x = y -> y = x.
Proof.
  intros x y eqxy.
  rewrite eqxy.
  reflexivity.
Qed.

Definition ev (A : Type) : 
  (S1 → A) → exists (a : A), a = a :=
  