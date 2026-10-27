module

public import BernoulliIso.CosetCoordinates
public import BernoulliIso.SparseRows

/-!
The actual regrouping stage retains slot zero in each coarse coset and
extracts the successor slots. Its zero-output inverse is exactly the sparse
coordinate insertion used by the support-contraction argument.
-/

@[expose] public section
noncomputable section
open scoped Classical
open MeasureTheory

namespace BernoulliIso.Regroup

variable {K A B Ω : Type*} [CommRing K] {n : ℕ}

/-- Retain the zero-labelled coordinate and extract every other coordinate. -/
def linearEquiv (e : A ≃ B × Fin (n + 1)) :
    (A → K) ≃ₗ[K] ((B → K) × (Fin n → B → K)) where
  toFun f := (fun b => f (e.symm (b, 0)), fun i b => f (e.symm (b, i.succ)))
  invFun p a := Fin.cases (motive := fun _ => K) (p.1 (e a).1) (fun i => p.2 i (e a).1) (e a).2
  left_inv f := by
    funext a
    obtain ⟨⟨b, i⟩, rfl⟩ := e.symm.surjective a
    cases i using Fin.cases <;> simp
  right_inv p := by
    apply Prod.ext
    · funext b
      simp
    · funext i b
      simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linearEquiv_fst (e : A ≃ B × Fin (n + 1)) (f : A → K) (b : B) :
    (linearEquiv (K := K) e f).1 b = f (e.symm (b, 0)) := rfl

@[simp] theorem linearEquiv_snd (e : A ≃ B × Fin (n + 1))
    (f : A → K) (i : Fin n) (b : B) :
    (linearEquiv (K := K) e f).2 i b = f (e.symm (b, i.succ)) := rfl

/-- The selected fine site in each coarse fiber is precisely its rank-zero site. -/
def selected (e : A ≃ B × Fin (n + 1)) (a : A) : Option B :=
  if (e a).2 = 0 then some (e a).1 else none

/-- The inverse with every extracted coordinate zero is literal insertion. -/
theorem symm_zero_eq_insertion (e : A ≃ B × Fin (n + 1)) (f : B → K) :
    (linearEquiv (K := K) e).symm (f, 0) = SparseRows.insertion (selected e) f := by
  funext a
  obtain ⟨⟨b, i⟩, rfl⟩ := e.symm.surjective a
  cases i using Fin.cases <;> simp [linearEquiv, selected, SparseRows.insertion]

theorem symm_zero_rows (e : A ≃ B × Fin (n + 1)) (f : B → K) (a : A) :
    (linearEquiv (K := K) e).symm (f, 0) a =
      SparseRows.eval (SparseRows.insertionRows (selected e) a) f := by
  rw [symm_zero_eq_insertion, SparseRows.eval_insertionRows]

section Topology

variable [TopologicalSpace K]

theorem continuous_linearEquiv (e : A ≃ B × Fin (n + 1)) :
    Continuous (linearEquiv (K := K) e) :=
  (continuous_pi fun b => continuous_apply (e.symm (b, 0))).prodMk
    (continuous_pi fun i => continuous_pi fun b => continuous_apply (e.symm (b, i.succ)))

theorem continuous_linearEquiv_symm (e : A ≃ B × Fin (n + 1)) :
    Continuous (linearEquiv (K := K) e).symm := by
  apply continuous_pi
  intro a
  change Continuous (fun p : (B → K) × (Fin n → B → K) =>
    Fin.cases (motive := fun _ => K) (p.1 (e a).1) (fun i => p.2 i (e a).1) (e a).2)
  cases h : (e a).2 using Fin.cases
  · exact (continuous_apply (e a).1).comp continuous_fst
  · exact (continuous_apply (e a).1).comp
      ((continuous_apply _).comp continuous_snd)

end Topology

section Measurability

variable [MeasurableSpace Ω] [MeasurableSpace K]
  [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  (e : Ω → A ≃ B × Fin (n + 1))
  (he : Measurable (fun p : Ω × A => e p.1 p.2))

include he

/-- The stage is jointly measurable in marker and configuration. -/
theorem measurable_linearEquiv :
    Measurable (fun p : Ω × (A → K) => linearEquiv (e p.1) p.2) := by
  have hi := CosetCoordinates.measurable_inverse_family e he
  have hev : Measurable (fun p : (A → K) × A => p.1 p.2) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply a
  have hm (b : B) (i : Fin (n + 1)) :
      Measurable (fun p : Ω × (A → K) => p.2 ((e p.1).symm (b, i))) :=
    hev.comp (measurable_snd.prodMk (hi.comp (measurable_fst.prodMk measurable_const)))
  exact (Measurable.of_eval fun b => hm b 0).prodMk
    (Measurable.of_eval fun i => Measurable.of_eval fun b => hm b i.succ)

/-- The full inverse is jointly measurable, including all residual slots. -/
theorem measurable_linearEquiv_symm :
    Measurable (fun p : Ω × ((B → K) × (Fin n → B → K)) =>
      (linearEquiv (e p.1)).symm p.2) := by
  have hj : Measurable (fun p : Ω × ((B → K) × (Fin n → B → K)) =>
      fun q : B × Fin (n + 1) =>
        Fin.cases (motive := fun _ => K) (p.2.1 q.1) (fun i => p.2.2 i q.1) q.2) := by
    apply Measurable.of_eval
    rintro ⟨b, i⟩
    cases i using Fin.cases
    · exact (measurable_pi_apply b).comp measurable_snd.fst
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply _).comp measurable_snd.snd)
  have hev : Measurable (fun p : ((B × Fin (n + 1)) → K) × (B × Fin (n + 1)) =>
      p.1 p.2) := measurable_from_prod_countable_left fun q => measurable_pi_apply q
  apply Measurable.of_eval
  intro a
  exact hev.comp (hj.prodMk (he.comp (measurable_fst.prodMk measurable_const)))

end Measurability


section Probability

variable [MeasurableSpace Ω] [MeasurableSpace K]
  [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
  [IsTopologicalAddGroup K] [BorelSpace K]

/-- An actual relative probability isomorphism for the regrouping stage.
Its product law follows from the continuous additive coordinate isomorphism
and uniqueness of normalized Haar measure. -/
def relativeIso (e : Ω → A ≃ B × Fin (n + 1))
    (he : Measurable (fun p : Ω × A => e p.1 p.2))
    (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure] :
    RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : A => μ))
      ((Measure.infinitePi (fun _ : B => μ)).prod
        (Measure.infinitePi (fun _ : Fin n => Measure.infinitePi (fun _ : B => μ)))) := by
  letI := infinitePi_isAddHaarMeasure (fun _ : A => μ)
  letI := infinitePi_isAddHaarMeasure (fun _ : B => μ)
  letI := infinitePi_isAddHaarMeasure
    (fun _ : Fin n => Measure.infinitePi (fun _ : B => μ))
  refine {
    equiv := fun ω => {
      toEquiv := (linearEquiv (K := K) (e ω)).toEquiv
      measurable_toFun := (continuous_linearEquiv (K := K) (e ω)).measurable
      measurable_invFun := (continuous_linearEquiv_symm (K := K) (e ω)).measurable }
    jointlyMeasurable := measurable_linearEquiv e he
    jointlyMeasurable_symm := measurable_linearEquiv_symm e he
    measurePreserving := fun ω => ?_ }
  exact (linearEquiv (K := K) (e ω)).toAddEquiv.toAddMonoidHom.measurePreserving
    (continuous_linearEquiv (K := K) (e ω)) (linearEquiv (K := K) (e ω)).surjective (by simp)

end Probability

/-- Covariance is inherited from the actual coordinate chart. -/
theorem linearEquiv_covariant {G : Type*} [Group G] [MulAction G A] [MulAction G B]
    (e e' : A ≃ B × Fin (n + 1)) (g : G)
    (he : ∀ a, e' (g • a) = (g • (e a).1, (e a).2)) (f : A → K) :
    linearEquiv (K := K) e' (fun a => f (g⁻¹ • a)) =
      (fun b => (linearEquiv e f).1 (g⁻¹ • b),
        fun i b => (linearEquiv e f).2 i (g⁻¹ • b)) := by
  have hi (b : B) (i : Fin (n + 1)) :
      e'.symm (b, i) = g • e.symm (g⁻¹ • b, i) := by
    apply e'.injective
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, smul_inv_smul]
  apply Prod.ext
  · funext b
    simp only [linearEquiv_fst, hi, inv_smul_smul]
  · funext i b
    simp only [linearEquiv_snd, hi, inv_smul_smul]

end BernoulliIso.Regroup

#print axioms BernoulliIso.Regroup.linearEquiv
#print axioms BernoulliIso.Regroup.symm_zero_eq_insertion
#print axioms BernoulliIso.Regroup.linearEquiv_covariant

#print axioms BernoulliIso.Regroup.relativeIso
