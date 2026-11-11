module

public import Mathlib.LinearAlgebra.Prod

/-!
The deterministic core of exhaustive extraction.

Every stage is an exact linear equivalence, and the inverse section is
defined by setting the extracted coordinates to zero. The theorem below
proves injectivity from vanishing of every coordinate on some finite
inverse section. No injectivity of the infinite extraction is assumed.
-/

@[expose] public section

namespace BernoulliIso

variable {K : Type*} [Ring K]
variable {X Y : ℕ → Type*}
  [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
  [∀ n, Module K (X n)] [∀ n, Module K (Y n)]

/-- An exact sequence of extraction stages; `X n` is the remaining input. -/
structure ExtractionTower (K : Type*) [Ring K] (X Y : ℕ → Type*)
    [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
    [∀ n, Module K (X n)] [∀ n, Module K (Y n)] where
  stage : ∀ n, X n ≃ₗ[K] (X (n + 1) × Y n)

namespace ExtractionTower

variable (t : ExtractionTower K X Y)

/-- The input left after `n` stages, expressed as a linear function of the source. -/
def remainder : (n : ℕ) → X 0 →ₗ[K] X n
  | 0 => LinearMap.id
  | n + 1 => (LinearMap.fst K (X (n + 1)) (Y n)).comp
      ((t.stage n).toLinearMap.comp (remainder n))

/-- The output of a single stage, expressed as a function of the source. -/
def output (n : ℕ) : X 0 →ₗ[K] Y n :=
  (LinearMap.snd K (X (n + 1)) (Y n)).comp
    ((t.stage n).toLinearMap.comp (t.remainder n))

/-- The infinite extraction map. -/
def extract (x : X 0) : ∀ n, Y n := fun n => t.output n x

/-- The genuine inverse section of one stage: all extracted labels are zero. -/
def sectionMap (n : ℕ) : X (n + 1) →ₗ[K] X n :=
  (t.stage n).symm.toLinearMap.comp (LinearMap.inl K (X (n + 1)) (Y n))

/-- The inverse section after finitely many stages, exactly the manuscript's `Π_n`. -/
def prefixSection : (n : ℕ) → X n →ₗ[K] X 0
  | 0 => LinearMap.id
  | n + 1 => (prefixSection n).comp (t.sectionMap n)

@[simp] theorem stage_sectionMap (n : ℕ) (z : X (n + 1)) :
    t.stage n (t.sectionMap n z) = (z, 0) := by
  exact (t.stage n).apply_symm_apply (z, 0)

/-- If two sources have identical outputs, their difference at every finite
stage comes entirely from the remaining input through the inverse section. -/
theorem difference_eq_prefixSection {x y : X 0} (h : t.extract x = t.extract y)
    (n : ℕ) : x - y = t.prefixSection n (t.remainder n x - t.remainder n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hout : t.output n x = t.output n y := congrFun h n
    have hstep : t.remainder n x - t.remainder n y =
        t.sectionMap n (t.remainder (n + 1) x - t.remainder (n + 1) y) := by
      apply (t.stage n).injective
      rw [t.stage_sectionMap, map_sub]
      apply Prod.ext
      · rfl
      · change t.output n x - t.output n y = 0
        rw [hout, sub_self]
    rw [ih, hstep]
    rfl

/-- Deterministic recovery. The observers may be coordinate evaluations.
The hypothesis states that each observer vanishes on one finite inverse
section, rather than assuming the desired injectivity. -/
theorem extract_injective_of_exhaustion {I : Type*} (obs : I → X 0 →ₗ[K] K)
    (separates : ∀ x y : X 0, (∀ i, obs i x = obs i y) → x = y)
    (exhaustion : ∀ i, ∃ n, ∀ z : X n, obs i (t.prefixSection n z) = 0) :
    Function.Injective t.extract := by
  intro x y h
  apply separates x y
  intro i
  obtain ⟨n, hn⟩ := exhaustion i
  have hz : obs i (x - y) = 0 := by
    rw [t.difference_eq_prefixSection h n]
    exact hn _
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Every finite output prefix and every terminal remaining input can be
prescribed. This is derived from the stage equivalences, not assumed. -/
theorem exists_remainder_and_prefix (y : ∀ n, Y n) (n : ℕ) (z : X n) :
    ∃ x : X 0, t.remainder n x = z ∧ ∀ m, m < n → t.output m x = y m := by
  induction n with
  | zero =>
    refine ⟨z, rfl, ?_⟩
    intro m hm
    exact (Nat.not_lt_zero m hm).elim
  | succ n ih =>
    obtain ⟨x, hx, hp⟩ := ih ((t.stage n).symm (z, y n))
    refine ⟨x, ?_, ?_⟩
    · change (t.stage n (t.remainder n x)).1 = z
      rw [hx, LinearEquiv.apply_symm_apply]
    · intro m hm
      by_cases heq : m = n
      · subst m
        change (t.stage n (t.remainder n x)).2 = y n
        rw [hx, LinearEquiv.apply_symm_apply]
      · exact hp m (by omega)

end ExtractionTower
end BernoulliIso

#print axioms BernoulliIso.ExtractionTower.difference_eq_prefixSection
#print axioms BernoulliIso.ExtractionTower.extract_injective_of_exhaustion
#print axioms BernoulliIso.ExtractionTower.exists_remainder_and_prefix
