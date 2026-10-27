module

public import BernoulliIso.FiniteStages
public import BernoulliIso.MeasuredExtraction

/-! Regularity of the finite compositions used by the concrete tower. -/

@[expose] public section
noncomputable section

open MeasureTheory

namespace BernoulliIso
namespace FiniteStages

variable {K X Y : Type*} [CommRing K]
  [AddCommGroup X] [AddCommGroup Y] [Module K X] [Module K Y]

theorem iterateSplit_succ_apply (e : X ≃ₗ[K] (X × Y)) (k : ℕ) (x : X) :
    iterateSplit e (k + 1) x =
      ((e (iterateSplit e k x).1).1,
        Fin.cons (α := fun _ : Fin (k + 1) => Y) (e (iterateSplit e k x).1).2 (iterateSplit e k x).2) := rfl

section Topology
variable [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_iterateSplit (e : X ≃ₗ[K] (X × Y)) (he : Continuous e) (k : ℕ) :
    Continuous (iterateSplit e k) := by
  induction k with
  | zero =>
    exact continuous_id.prodMk (continuous_pi fun i => Fin.elim0 i)
  | succ k ih =>
    have h := he.comp ih.fst
    change Continuous (fun x => ((e (iterateSplit e k x).1).1,
      Fin.cons (α := fun _ : Fin (k + 1) => Y) (e (iterateSplit e k x).1).2 (iterateSplit e k x).2))
    apply h.fst.prodMk
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact h.snd
    | succ i => exact (continuous_apply i).comp ih.snd

theorem continuous_regroupAndRepeat {X₀ W : Type*}
    [AddCommGroup X₀] [AddCommGroup W] [Module K X₀] [Module K W]
    [TopologicalSpace X₀] [TopologicalSpace W]
    (r : X₀ ≃ₗ[K] (X × W)) (e : X ≃ₗ[K] (X × Y))
    (hr : Continuous r) (he : Continuous e) (k : ℕ) :
    Continuous (regroupAndRepeat r e k) := by
  have h := (continuous_iterateSplit e he k).comp hr.fst
  exact h.fst.prodMk (h.snd.prodMk hr.snd)

end Topology

section Measurability
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_iterateSplit (e : Ω → X ≃ₗ[K] (X × Y))
    (he : Measurable (fun p : Ω × X => e p.1 p.2)) (k : ℕ) :
    Measurable (fun p : Ω × X => iterateSplit (e p.1) k p.2) := by
  induction k with
  | zero =>
    exact measurable_snd.prodMk (Measurable.of_eval fun i => Fin.elim0 i)
  | succ k ih =>
    have h := he.comp (measurable_fst.prodMk ih.fst)
    change Measurable (fun p : Ω × X =>
      ((e p.1 (iterateSplit (e p.1) k p.2).1).1,
        Fin.cons (α := fun _ : Fin (k + 1) => Y) (e p.1 (iterateSplit (e p.1) k p.2).1).2
          (iterateSplit (e p.1) k p.2).2))
    apply h.fst.prodMk
    apply Measurable.of_eval
    intro i
    cases i using Fin.cases with
    | zero => exact h.snd
    | succ i => exact (measurable_pi_apply i).comp ih.snd

theorem measurable_regroupAndRepeat {X₀ W : Type*}
    [AddCommGroup X₀] [AddCommGroup W] [Module K X₀] [Module K W]
    [MeasurableSpace X₀] [MeasurableSpace W]
    (r : Ω → X₀ ≃ₗ[K] (X × W)) (e : Ω → X ≃ₗ[K] (X × Y))
    (hr : Measurable (fun p : Ω × X₀ => r p.1 p.2))
    (he : Measurable (fun p : Ω × X => e p.1 p.2)) (k : ℕ) :
    Measurable (fun p : Ω × X₀ => regroupAndRepeat (r p.1) (e p.1) k p.2) := by
  have h := (measurable_iterateSplit e he k).comp (measurable_fst.prodMk hr.fst)
  exact h.fst.prodMk (h.snd.prodMk hr.snd)

end Measurability
end FiniteStages

namespace ExtractionTower

variable {K Ω : Type*} [Ring K] {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]

theorem continuous_remainder [∀ n, TopologicalSpace (X n)]
    [∀ n, TopologicalSpace (Y n)] (t : ExtractionTower K X Y)
    (hs : ∀ n, Continuous (t.stage n)) (n : ℕ) : Continuous (t.remainder n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact ((hs n).comp ih).fst

theorem continuous_output [∀ n, TopologicalSpace (X n)]
    [∀ n, TopologicalSpace (Y n)] (t : ExtractionTower K X Y)
    (hs : ∀ n, Continuous (t.stage n)) (n : ℕ) : Continuous (t.output n) :=
  ((hs n).comp (t.continuous_remainder hs n)).snd

theorem measurable_remainder [MeasurableSpace Ω]
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (tower : Ω → ExtractionTower K X Y)
    (hs : ∀ n, Measurable (fun p : Ω × X n => (tower p.1).stage n p.2)) (n : ℕ) :
    Measurable (fun p : Ω × X 0 => (tower p.1).remainder n p.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih => exact ((hs n).comp (measurable_fst.prodMk ih)).fst

theorem measurable_output [MeasurableSpace Ω]
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (tower : Ω → ExtractionTower K X Y)
    (hs : ∀ n, Measurable (fun p : Ω × X n => (tower p.1).stage n p.2)) (n : ℕ) :
    Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2) :=
  ((hs n).comp (measurable_fst.prodMk (measurable_remainder tower hs n))).snd

end ExtractionTower
end BernoulliIso

#print axioms BernoulliIso.FiniteStages.continuous_regroupAndRepeat
#print axioms BernoulliIso.FiniteStages.measurable_regroupAndRepeat
#print axioms BernoulliIso.ExtractionTower.continuous_output
#print axioms BernoulliIso.ExtractionTower.measurable_output
