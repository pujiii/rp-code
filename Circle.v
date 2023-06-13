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
    apply funextfun. (* provided by Copilot *)
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

Search isaset.

Check hfiber.

Definition SetBundle (B : UU) : UU := ∑ (A : UU) (f : A -> B), ∏ (b : B), isaset (hfiber f b).

Definition is_groupoid (A : UU) := ∏ (x: A) (y : A), isaset (x = y).

Lemma map_rl {A : UU} : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) -> (A -> hSet).
Proof.
  intro Bf.
  intro a.
  exact (make_hSet _ ((pr2 (pr2 Bf)) a)).
Defined.

Lemma map_lr {A : UU} : (A -> hSet) -> (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)).
Proof.
  intro f.
  use tpair.
  - exact (∑ (a : A), f a).
  - simpl.
    use tpair.
    + exact pr1.
    + simpl.
      intro a.
      use (isofhlevelweqf 2).
      * exact (∑ (a : A), f a).
      * use weq_iso.
        -- intro x.
           use make_hfiber. 
           ++ exact x.
           ++ 
      Search (isofhlevel _ ≃ isaset _).
      
Admitted.

Lemma map_inv_eq_lrrl {A : Type} (Bf : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a))) : (map_lr (map_rl Bf)) = Bf.
Proof.
  
Admitted.

Lemma map_inv_eq_rllr {A : UU} (f : A -> hSet) : (map_rl (map_lr f)) = f.
Proof.
Admitted.

Lemma set_families (A : UU) : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) ≃ (A -> hSet).
Proof.
  exists map_rl. 
  apply (isweq_iso map_rl map_lr).
  - exact map_inv_eq_lrrl.
  - exact map_inv_eq_rllr.
Qed.

Lemma setbundle_isgroupoid (B : UU) : is_groupoid (SetBundle B).
Proof.
unfold is_groupoid.
unfold SetBundle.
intros x y.
Admitted.

Theorem ev_set_equiv (B : UU) : isweq (ev (hSet)).
Proof.
use evisweq.
Qed.

Theorem setbundle_s1_set : SetBundle S1 ≃ (S1 -> hSet).
Proof.
simpl.  
unfold SetBundle.
simpl.
use (set_families S1).
  use weq_iso.
  - intro p.
    unfold SetBundle in p.
    intro x.
    Check ((pr1 (pr2 p))).
    admit.
  - intro f.
    exact (ve (hSet) f).
  - intro f.
    unfold ve.
    unfold ev.
    simpl.
    use funextfun.
    use S1_ind.
    + reflexivity.
    + simpl.
      rewrite transportf_paths_FlFr.
      rewrite S1_recur_loop.
      simpl.
      use pathsinv0l.
  - intro p.
    unfold ve.
    unfold ev.
    simpl.
    rewrite S1_recur_loop.
    reflexivity. 
(* 
Admitted. *)
(* Search (_ ≃ (_ -> hSet)) .
Theorem circ_groupoid_func_equiv : is_groupoid S1.
Proof.
  unfold is_groupoid.
  intros x y.
  use isweqhomot.
  - exact (fun p => p @ loop).
  - intro p.
    induction p.
    simpl.
    use pathsinv0l.
  - intro p.
    induction p.
    simpl.
    use pathsinv0l. *)
(* 
Definition f (P : S1 -> UU) (R : S1 -> UU) : ∏ (z : S1), (P z -> R z) := fun z => fun p => transportf R p. *)