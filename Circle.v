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

Definition S1_recur (A : Type) (b : A) (l : b = b) : S1 -> A :=
  fun x =>
    match x with
    | base => transportf (fun _ => A) l b
    end.
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

(* Try to prove: forall (z: S1), z = base *)
(* Lemma circle_connected' : forall (z: S1), z = base.
Proof.
  intro z.
  use (S1_ind (fun z => z = base) _ _ z).
  - exact (idpath base). 
  - give_up. *)

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