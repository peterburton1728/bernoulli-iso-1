module

public import BernoulliIso.InputOperators
public import BernoulliIso.Recovery
public import Mathlib.LinearAlgebra.Pi

/-!
The finite stages are built by composing the concrete rectangle splitting
with coordinate charts. Repetition and zero-output inverse sections are
defined, not supplied as additional hypotheses about an extraction tower.
The marker-dependent coordinate charts are a separate input to this file.
-/

@[expose] public section
noncomputable section

namespace BernoulliIso
namespace FiniteStages

variable {K : Type*} [CommRing K]

def piProduct (C X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Module K X] [Module K Y] : (C → X × Y) ≃ₗ[K] ((C → X) × (C → Y)) where
  toFun f := (fun c => (f c).1, fun c => (f c).2)
  invFun p c := (p.1 c, p.2 c)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def uncurryLinear (C I X : Type*) [AddCommGroup X] [Module K X] :
    (C → I → X) ≃ₗ[K] ((C × I) → X) where
  toFun f p := f p.1 p.2
  invFun f c i := f (c, i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All copies of the actual range/residual splitting, in one equivalence. -/
def splitCopies {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module K X] [Module K Y] (s : SplitData K X Y) (C : Type*) :
    (C → s.P.range) ≃ₗ[K] ((C → Y) × (C → s.Q.range)) :=
  (LinearEquiv.piCongrRight fun _ : C => s.linearEquiv).trans (piProduct C Y s.Q.range)

/-- Finite output tracks are partitioned into retained and newly extracted tracks. -/
def splitTracks {C I V W S : Type*} (slots : C × I ≃ V ⊕ W) :
    (C → I → S → K) ≃ₗ[K] ((V → S → K) × (W → S → K)) where
  toFun f := (fun v => f (slots.symm (Sum.inl v)).1 (slots.symm (Sum.inl v)).2,
    fun w => f (slots.symm (Sum.inr w)).1 (slots.symm (Sum.inr w)).2)
  invFun p c i := Sum.elim p.1 p.2 (slots (c, i))
  left_inv f := by
    funext c i
    change Sum.elim _ _ (slots (c, i)) = f c i
    cases h : slots (c, i) with
    | inl v =>
      have hv : slots.symm (Sum.inl v) = (c, i) := by rw [← h, slots.symm_apply_apply]
      simp only [Sum.elim_inl, hv]
    | inr w =>
      have hw : slots.symm (Sum.inr w) = (c, i) := by rw [← h, slots.symm_apply_apply]
      simp only [Sum.elim_inr, hw]
  right_inv p := by
    apply Prod.ext
    · funext v
      change Sum.elim p.1 p.2 (slots ((slots.symm (Sum.inl v)).1,
        (slots.symm (Sum.inl v)).2)) = p.1 v
      simp only [Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inl]
    · funext w
      change Sum.elim p.1 p.2 (slots ((slots.symm (Sum.inr w)).1,
        (slots.symm (Sum.inr w)).2)) = p.2 w
      simp only [Prod.mk.eta, Equiv.apply_symm_apply, Sum.elim_inr]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Amplification by finite coordinate charts. The group-ring splitting is
the previously proved one; only the actual coordinate chart is supplied. -/
def amplifiedSplit {C I V W S : Type*}
    (s : SplitData K (V → S → K) (I → S → K))
    (chart : (C → s.P.range) ≃ₗ[K] (V → S → K))
    (slots : C × I ≃ V ⊕ W) :
    (V → S → K) ≃ₗ[K] ((V → S → K) × ((W → S → K) × (C → s.Q.range))) :=
  chart.symm.trans <| (splitCopies s C).trans <|
    ((splitTracks (K := K) slots).prodCongr (LinearEquiv.refl K _)).trans
      (LinearEquiv.prodAssoc K _ _ _)

section Iteration

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module K X] [Module K Y]

def emptyOutputs : X ≃ₗ[K] (X × (Fin 0 → Y)) where
  toFun x := (x, fun i => Fin.elim0 i)
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i

/-- Repeating an exact finite splitting extracts one output at each step. -/
def iterateSplit (e : X ≃ₗ[K] (X × Y)) : (k : ℕ) → X ≃ₗ[K] (X × (Fin k → Y))
  | 0 => emptyOutputs
  | k + 1 => (iterateSplit e k).trans <|
      (e.prodCongr (LinearEquiv.refl K _)).trans <|
      (LinearEquiv.prodAssoc K X Y (Fin k → Y)).trans
        ((LinearEquiv.refl K X).prodCongr
          (Fin.consLinearEquiv K (fun _ : Fin (k + 1) => Y)))

/-- The inverse section of a single split sets its extracted coordinate to zero. -/
def inverseSection (e : X ≃ₗ[K] (X × Y)) : Module.End K X :=
  e.symm.toLinearMap.comp (LinearMap.inl K X Y)

@[simp] theorem inverseSection_apply (e : X ≃ₗ[K] (X × Y)) (x : X) :
    inverseSection e x = e.symm (x, 0) := rfl

theorem repeat_symm_zero (e : X ≃ₗ[K] (X × Y)) (k : ℕ) (x : X) :
    (iterateSplit e k).symm (x, 0) = (inverseSection e ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change (iterateSplit e k).symm
      (e.symm (x, ((Fin.consLinearEquiv K (fun _ : Fin (k + 1) => Y)).symm 0).1),
        ((Fin.consLinearEquiv K (fun _ : Fin (k + 1) => Y)).symm 0).2) = _
    rw [map_zero]
    change (iterateSplit e k).symm (inverseSection e x, 0) = _
    rw [ih, pow_succ, Module.End.mul_apply]

/-- A coordinate regrouping followed by repeated splitting is an actual stage. -/
def regroupAndRepeat {X₀ W : Type*} [AddCommGroup X₀] [AddCommGroup W]
    [Module K X₀] [Module K W]
    (regroup : X₀ ≃ₗ[K] (X × W)) (e : X ≃ₗ[K] (X × Y)) (k : ℕ) :
    X₀ ≃ₗ[K] (X × ((Fin k → Y) × W)) :=
  regroup.trans <| ((iterateSplit e k).prodCongr (LinearEquiv.refl K W)).trans
    (LinearEquiv.prodAssoc K X (Fin k → Y) W)

theorem regroupAndRepeat_symm_zero {X₀ W : Type*} [AddCommGroup X₀] [AddCommGroup W]
    [Module K X₀] [Module K W]
    (regroup : X₀ ≃ₗ[K] (X × W)) (e : X ≃ₗ[K] (X × Y)) (k : ℕ) (x : X) :
    (regroupAndRepeat regroup e k).symm (x, 0) =
      regroup.symm ((inverseSection e ^ k) x, 0) := by
  change regroup.symm ((iterateSplit e k).symm (x, 0), 0) = _
  rw [repeat_symm_zero]

end Iteration
end FiniteStages
end BernoulliIso
