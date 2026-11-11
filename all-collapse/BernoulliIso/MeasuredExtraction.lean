module

public import BernoulliIso.CompactExtraction
public import BernoulliIso.Conjugacy
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
The measure-theoretic upgrade of exact extraction towers. Surjectivity comes
from compactness and finite exactness; preservation of Haar probability comes
from the continuous homomorphism theorem. Joint inverse measurability follows
from the standard Borel measurable embedding theorem.

The marker type can itself be a measurable conull subtype of the original
marker space. No statement about uninstantiated concrete marker laws is made.
-/

@[expose] public section

open MeasureTheory

namespace BernoulliIso

variable {K : Type*} [Ring K] {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]

namespace ExtractionTower

/-- Infinite extraction is an additive homomorphism, before any measure or
topology is introduced. -/
def extractHom (t : ExtractionTower K X Y) : X 0 →+ (∀ n, Y n) where
  toFun := t.extract
  map_zero' := by ext n; exact map_zero (t.output n)
  map_add' x y := by ext n; exact map_add (t.output n) x y

@[simp] theorem extractHom_apply (t : ExtractionTower K X Y) (x : X 0) :
    t.extractHom x = t.extract x := rfl

section Covariance

variable {G Ω : Type*} [Group G] [MulAction G Ω]
  [∀ n, MulAction G (X n)] [∀ n, MulAction G (Y n)]

/-- Equivariance of actual stages propagates through all remaining inputs. -/
theorem remainder_covariant (tower : Ω → ExtractionTower K X Y)
    (hstage : ∀ (g : G) (ω : Ω) (n : ℕ) (x : X n),
      (tower (g • ω)).stage n (g • x) = g • (tower ω).stage n x)
    (g : G) (ω : Ω) (n : ℕ) (x : X 0) :
    (tower (g • ω)).remainder n (g • x) = g • (tower ω).remainder n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((tower (g • ω)).stage n
      ((tower (g • ω)).remainder n (g • x))).1 =
      g • ((tower ω).stage n ((tower ω).remainder n x)).1
    rw [ih, hstage]
    rfl

/-- Equivariance of actual stages propagates to each extracted output. -/
theorem output_covariant (tower : Ω → ExtractionTower K X Y)
    (hstage : ∀ (g : G) (ω : Ω) (n : ℕ) (x : X n),
      (tower (g • ω)).stage n (g • x) = g • (tower ω).stage n x)
    (g : G) (ω : Ω) (n : ℕ) (x : X 0) :
    (tower (g • ω)).output n (g • x) = g • (tower ω).output n x := by
  change ((tower (g • ω)).stage n
    ((tower (g • ω)).remainder n (g • x))).2 =
    g • ((tower ω).stage n ((tower ω).remainder n x)).2
  rw [remainder_covariant tower hstage, hstage]
  rfl

/-- Equivariance of the infinite extraction is derived from stage covariance. -/
theorem extract_covariant (tower : Ω → ExtractionTower K X Y)
    (hstage : ∀ (g : G) (ω : Ω) (n : ℕ) (x : X n),
      (tower (g • ω)).stage n (g • x) = g • (tower ω).stage n x)
    (g : G) (ω : Ω) (x : X 0) :
    (tower (g • ω)).extract (g • x) = g • (tower ω).extract x := by
  funext n
  exact output_covariant tower hstage g ω n x

end Covariance

variable [TopologicalSpace (X 0)] [CompactSpace (X 0)]
  [IsTopologicalAddGroup (X 0)] [MeasurableSpace (X 0)] [BorelSpace (X 0)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
  [∀ n, T2Space (Y n)] [∀ n, IsTopologicalAddGroup (Y n)]
  [∀ n, MeasurableSpace (Y n)] [BorelSpace (∀ n, Y n)]

/-- Every continuous exact extraction tower sends source Haar probability to
the full output Haar probability, even without exhaustion/injectivity. -/
theorem measurePreserving_extract (t : ExtractionTower K X Y)
    (hcont : ∀ n, Continuous (t.output n))
    (μ : Measure (X 0)) (ν : Measure (∀ n, Y n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving t.extract μ ν := by
  exact t.extractHom.measurePreserving (continuous_pi hcont)
    (t.extract_surjective hcont) (by simp)

end ExtractionTower

section RelativeExtraction

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [TopologicalSpace (X 0)] [CompactSpace (X 0)]
  [IsTopologicalAddGroup (X 0)] [MeasurableSpace (X 0)] [BorelSpace (X 0)]
  [StandardBorelSpace (X 0)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
  [∀ n, T2Space (Y n)] [∀ n, IsTopologicalAddGroup (Y n)]
  [∀ n, MeasurableSpace (Y n)] [BorelSpace (∀ n, Y n)]
  [∀ n, StandardBorelSpace (Y n)]

/-- The actual marker-retaining map, with no choices in its forward direction. -/
def relativeExtraction (tower : Ω → ExtractionTower K X Y)
    (p : Ω × X 0) : Ω × (∀ n, Y n) := (p.1, (tower p.1).extract p.2)

theorem measurable_relativeExtraction (tower : Ω → ExtractionTower K X Y)
    (hmeas : ∀ n, Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2)) :
    Measurable (relativeExtraction tower) :=
  measurable_fst.prodMk (Measurable.of_eval hmeas)

theorem bijective_relativeExtraction (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (hinj : ∀ ω, Function.Injective (tower ω).extract) :
    Function.Bijective (relativeExtraction tower) := by
  constructor
  · rintro ⟨ω, x⟩ ⟨ω', x'⟩ h
    have hω : ω = ω' := congrArg Prod.fst h
    subst ω'
    have hx : x = x' := hinj ω (congrArg Prod.snd h)
    exact Prod.ext rfl hx
  · rintro ⟨ω, y⟩
    obtain ⟨x, hx⟩ := (tower ω).extract_surjective (hcont ω) y
    exact ⟨(ω, x), Prod.ext rfl hx⟩

/-- A jointly measurable exact extraction tower which is injective on every
good marker gives a measure-preserving Borel isomorphism of the two product
spaces, retaining that marker. Both joint inverse measurability and the
push-forward law are conclusions, not hypotheses. -/
noncomputable def relativeExtractionIso
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (hmeas : ∀ n, Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2))
    (hinj : ∀ ω, Function.Injective (tower ω).extract)
    (μ : Measure Ω) (ν : Measure (X 0)) (ρ : Measure (∀ n, Y n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [ν.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] :
    ProbabilityIso (μ.prod ν) (μ.prod ρ) where
  equiv := measurableEquivOfBijective (relativeExtraction tower)
    (measurable_relativeExtraction tower hmeas)
    (bijective_relativeExtraction tower hcont hinj)
  measurePreserving := by
    change MeasurePreserving (relativeExtraction tower) (μ.prod ν) (μ.prod ρ)
    exact (MeasurePreserving.id μ).skew_product
      (Measurable.of_eval hmeas)
      (Filter.Eventually.of_forall fun ω =>
        ((tower ω).measurePreserving_extract (hcont ω) ν ρ).map_eq)

@[simp] theorem relativeExtractionIso_apply
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (hmeas : ∀ n, Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2))
    (hinj : ∀ ω, Function.Injective (tower ω).extract)
    (μ : Measure Ω) (ν : Measure (X 0)) (ρ : Measure (∀ n, Y n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [ν.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] (p : Ω × X 0) :
    (relativeExtractionIso tower hcont hmeas hinj μ ν ρ).equiv p =
      (p.1, (tower p.1).extract p.2) := rfl

/-- End-to-end measured extraction: almost-sure recovery of an actual,
jointly measurable, stage-covariant exact tower yields a probability-preserving
equivariant Borel isomorphism on invariant conull subsets of the full product
spaces. No measurability of the recovery event, inverse map, or fiber Haar
push-forward is assumed.

This theorem is an integration interface, not an assertion that a particular
Bernoulli construction has already supplied its concrete hypotheses. -/
theorem exists_conullConjugacy_of_ae_extraction
    {G : Type*} [Group G] [Countable G] [MulAction G Ω]
    [∀ n, MulAction G (X n)] [∀ n, MulAction G (Y n)]
    (tower : Ω → ExtractionTower K X Y)
    (hcont : ∀ ω n, Continuous ((tower ω).output n))
    (hmeas : ∀ n, Measurable (fun p : Ω × X 0 => (tower p.1).output n p.2))
    (hstage : ∀ (g : G) (ω : Ω) (n : ℕ) (x : X n),
      (tower (g • ω)).stage n (g • x) = g • (tower ω).stage n x)
    (μ : Measure Ω) (ν : Measure (X 0)) (ρ : Measure (∀ n, Y n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [ν.IsAddHaarMeasure] [ρ.IsAddHaarMeasure]
    (hmarkerPres : ∀ g : G, MeasurePreserving (fun ω : Ω => g • ω) μ μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective (tower ω).extract) :
    Nonempty (ConullConjugacy G (Ω × X 0) (Ω × (∀ n, Y n))
      (μ.prod ν) (μ.prod ρ)) := by
  obtain ⟨s, hs, hfull, hinv, hgood⟩ :=
    exists_invariant_conull_subset μ hmarkerPres
      (fun ω => Function.Injective (tower ω).extract) hinj
  letI : StandardBorelSpace s := hs.standardBorel
  letI : IsProbabilityMeasure (μ.comap (Subtype.val : s → Ω)) :=
    (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
      (by simpa using hfull)
  let towerS : s → ExtractionTower K X Y := fun ω => tower ω.val
  have hcontS : ∀ ω n, Continuous ((towerS ω).output n) := fun ω => hcont ω.val
  have hmeasS : ∀ n, Measurable (fun p : s × X 0 => (towerS p.1).output n p.2) := by
    intro n
    exact (hmeas n).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hinjS : ∀ ω : s, Function.Injective (towerS ω).extract :=
    fun ω => hgood ω.val ω.property
  let e := relativeExtractionIso towerS hcontS hmeasS hinjS
    (μ.comap (Subtype.val : s → Ω)) ν ρ
  refine ⟨conullConjugacyOfRelativeIso μ ν ρ hs hfull hinv e ?_ ?_⟩
  · intro p
    rfl
  · intro g ω x
    change (tower (g • ω.val)).extract (g • x) = g • (tower ω.val).extract x
    exact ExtractionTower.extract_covariant tower hstage g ω.val x

end RelativeExtraction

end BernoulliIso

#print axioms BernoulliIso.ExtractionTower.measurePreserving_extract
#print axioms BernoulliIso.relativeExtractionIso
#print axioms BernoulliIso.exists_conullConjugacy_of_ae_extraction
