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

Definition S1_recur (A : Type) (b : A) (l : b = b) : S1 -> A :=
  fun x =>
    match x with
    | base => transportf (fun _ => A) l b
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

(* Try to prove: forall (z: S1), z = base *)
Lemma circle_connected' : forall (z: S1), z = base.
Proof.
  intro x.
  apply (S1_ind (fun x => x = base)).
  - exact (idpath base).
  - exact (idpath base).
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
  (S1 → A) → ∑ (a : A), a = a :=
  fun g => tpair (fun a => a = a) (g base) (paths_refl (g base)).

Definition ve (A : Type) :
  (∑ (a : A), a = a) → (S1 → A) :=
  fun p => S1_recur A (pr1 p) (paths_refl (pr1 p)).


(* TO DO *)
(* Theorem ev_equiv: Equivalence ev.
Proof.
  
Qed. *)

