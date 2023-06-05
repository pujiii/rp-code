Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Definition apD {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  transportf Y p (s x) = s x'.
Proof.
  now induction p.
Defined.

Module Export S1.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : transportf P loop b = b)
  : forall x : S1, P x :=
  fun x =>
    match x with
    | base => b
    end.

Axiom S1_ind_loop : forall (P : S1 -> Type) (b : P base) (l : transportf P loop b = b),
  apD (S1_ind P b l) loop = l.

Definition S1_recur (A : Type) (a : A) (l : a = a) : S1 -> A :=
  fun x =>
    match x with
    | base => a
    end.

Axiom S1_recur_loop : forall (A : Type) (a : A) (l : a = a) ,
  maponpaths (S1_recur A a l) loop = l.

End S1.


Lemma circle_eq_sym : forall (x y : S1), x = y -> y = x.
Proof.
  intros x y eqxy.
  rewrite eqxy.
  reflexivity.
Qed.

Lemma base_refl : base = base.
Proof.
  reflexivity.
Qed.

Lemma circle_connected : forall (z: S1), ∥ z = base ∥.
Proof.
  intro z.
  use (S1_ind (fun z => ∥ z = base ∥) _ _ z).
  - exact (hinhpr (idpath base)). 
  - apply propproperty.
Qed.

Definition ev (A : Type) : 
  (S1 → A) → ∑ (a : A), a = a :=
  fun g => tpair (fun a => a = a) (g base) (maponpaths g loop).

(* Definition ev' (A : Type) (a : A) :
  (S1 -> A × a = a) -> (a = a) :=
  fun t => (pr2 t) @ (maponpaths (pr1 t) loop). *)

Definition ve (A : Type) :
  (∑ (a : A), a = a) → (S1 → A) :=
  fun p => S1_recur A (pr1 p) (pr2 p).

Theorem evisweq (A : UU) : isweq (ev A).
Proof.
  use isweq_iso.
  - exact (ve A).
  - intro f.
    unfold ve.
    unfold ev.
    simpl.
    apply funextfun.
    use S1_ind.
    + reflexivity.
    + Check transportf_paths_FlFr.
      simpl.
      rewrite transportf_paths_FlFr.
      rewrite S1_recur_loop.
      simpl.
      use pathsinv0l.
  - intro p.
    unfold ev.
    unfold ve.
    simpl.
    rewrite S1_recur_loop.
    reflexivity.
Qed.

