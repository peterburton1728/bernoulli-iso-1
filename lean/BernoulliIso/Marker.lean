module

public import BernoulliIso.Selection
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
Concrete digit addresses and product marker laws. The geometry is stated
for an arbitrary group with a height homomorphism, so the actual
N × (C₂ wr ℤ) construction can instantiate it without changing probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BernoulliIso

/-- Geometry supplying disjoint marker addresses inside one D-coset. -/
structure MarkerGeometry (G : Type*) [Group G] where
  D : Subgroup G
  height : G →* Multiplicative ℤ
  step : G
  height_step : height step = Multiplicative.ofAdd 1
  height_D : ∀ u : D, height u = 1
  serial : ℕ × ℕ → ℕ
  serial_injective : Function.Injective serial

namespace MarkerGeometry

variable {G : Type*} [Group G] (a : MarkerGeometry G)

abbrev DigitIndex := a.D × (ℕ × ℕ)

def address (g : G) (i : a.DigitIndex) : G :=
  g * i.1.val * a.step ^ a.serial i.2

/-- Height separates serial numbers; cancellation then separates D-sites. -/
theorem address_injective (g : G) : Function.Injective (a.address g) := by
  intro i j hij
  have hbase : i.1.val * a.step ^ a.serial i.2 =
      j.1.val * a.step ^ a.serial j.2 := by
    apply mul_left_cancel (a := g)
    simpa only [address, mul_assoc] using hij
  have hh := congrArg (fun x => (a.height x).toAdd) hbase
  have hn : a.serial i.2 = a.serial j.2 := by
    simpa [map_mul, map_pow, a.height_D, a.height_step,
      toAdd_pow, toAdd_mul] using hh
  have hpair : i.2 = j.2 := a.serial_injective hn
  have hu : i.1 = j.1 := by
    apply Subtype.ext
    apply mul_right_cancel (b := a.step ^ a.serial j.2)
    simpa only [hn] using hbase
  exact Prod.ext hu hpair

@[simp] theorem address_left_mul (b g : G) (i : a.DigitIndex) :
    a.address (b * g) i = b * a.address g i := by
  simp [address, mul_assoc]

/-- Standard left shift, with the action convention made explicit. -/
def markerShift {K : Type*} (b : G) (ω : G → K) : G → K :=
  fun g => ω (b⁻¹ * g)

def digits {K : Type*} (g : G) (ω : G → K) : a.DigitIndex → K :=
  fun i => ω (a.address g i)

@[simp] theorem digits_covariant {K : Type*} (b g : G) (ω : G → K) :
    a.digits (b * g) (markerShift b ω) = a.digits g ω := by
  funext i
  simp [digits, markerShift, a.address_left_mul]

variable (K : Type*) [Fintype K] [Nonempty K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

/-- The actual finite uniform base law. -/
noncomputable def uniformBase : Measure K := Measure.uniformOfFinset Finset.univ

instance uniformBase_probability : IsProbabilityMeasure (uniformBase K) := by
  constructor
  have hn : (Fintype.card K : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  simpa [uniformBase, Measure.uniformOfFinset_apply] using
    (ENNReal.div_self hn (by simp : (Fintype.card K : ℝ≥0∞) ≠ ∞))

omit [Nonempty K] in
@[simp] theorem uniformBase_singleton (k : K) :
    uniformBase K {k} = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  simp [uniformBase]

/-- One finite-alphabet coordinate per group element. -/
noncomputable def markerLaw : Measure (G → K) :=
  Measure.infinitePi (fun _ : G => uniformBase K)

instance markerLaw_probability : IsProbabilityMeasure (markerLaw (G := G) K) := by
  unfold markerLaw
  infer_instance

variable {K}

omit [Fintype K] [Nonempty K] [MeasurableSingletonClass K] in
@[fun_prop] theorem measurable_digits (g : G) : Measurable (a.digits (K := K) g) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (a.address g i))

/-- All digits addressed within one D-coset have exactly the iid uniform law. -/
theorem digits_joint_law (g : G) :
    (markerLaw (G := G) K).map (a.digits g) =
      Measure.infinitePi (fun _ : a.DigitIndex => uniformBase K) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (a.address_injective g)

/-- Independence follows from actual injective coordinates of the product marker. -/
theorem digits_independent (g : G) :
    iIndepFun (fun i ω => a.digits g ω i) (markerLaw (G := G) K) := by
  exact (iIndepFun_infinitePi (P := fun _ : G => uniformBase K)
    (X := fun _ ω => ω) (fun _ => measurable_id)).precomp (a.address_injective g)

def pastIndices (n : ℕ) : Set a.DigitIndex := {i | i.2.1 < n}
def freshIndices (n : ℕ) : Set a.DigitIndex := {i | i.2.1 = n}

def pastRead (g : G) (n : ℕ) (ω : G → K) : a.pastIndices n → K :=
  fun i => a.digits g ω i.val

def freshRead (g : G) (n : ℕ) (ω : G → K) : a.freshIndices n → K :=
  fun i => a.digits g ω i.val

omit [Fintype K] [Nonempty K] [MeasurableSingletonClass K] in
@[fun_prop] theorem measurable_pastRead (g : G) (n : ℕ) :
    Measurable (a.pastRead (K := K) g n) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (a.address g i.val))

omit [Fintype K] [Nonempty K] [MeasurableSingletonClass K] in
@[fun_prop] theorem measurable_freshRead (g : G) (n : ℕ) :
    Measurable (a.freshRead (K := K) g n) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (a.address g i.val))

/-- The whole earlier-stream field is independent of the whole new-stream field. -/
theorem past_fresh_independent (g : G) (n : ℕ) :
    IndepFun (a.pastRead (K := K) g n) (a.freshRead g n)
      (markerLaw (G := G) K) := by
  apply (a.digits_independent (K := K) g).indepFun_set
  · apply Set.disjoint_left.2
    intro i hi hj
    exact (Nat.ne_of_lt hi) hj
  · intro i
    exact measurable_pi_apply (a.address g i)

/-- The concrete sigma-algebra generated by all earlier digits in this coset. -/
abbrev pastSigma (g : G) (n : ℕ) : MeasurableSpace (G → K) :=
  MeasurableSpace.comap (a.pastRead g n) inferInstance

abbrev freshSigma (g : G) (n : ℕ) : MeasurableSpace (G → K) :=
  MeasurableSpace.comap (a.freshRead g n) inferInstance

/-- Every past event is independent of every event of the fresh stream.
This is derived from the actual finite uniform product marker law. -/
theorem past_inter_fresh (g : G) (n : ℕ) {E F : Set (G → K)}
    (hE : MeasurableSet[a.pastSigma g n] E)
    (hF : MeasurableSet[a.freshSigma g n] F) :
    markerLaw (G := G) K (E ∩ F) = markerLaw (G := G) K E * markerLaw (G := G) K F := by
  exact (IndepFun_iff _ _ _).1 (a.past_fresh_independent (K := K) g n) E F hE hF

/-- Freshness on an arbitrary adapted support fiber, with the conditional
law derived from product-coordinate independence. -/
theorem support_fiber_fresh {A : Type*} (g : G) (n : ℕ)
    (support : (G → K) → Finset A) (s : Finset A)
    (hs : MeasurableSet[a.pastSigma g n] {ω | support ω = s})
    {F : Set (G → K)} (hF : MeasurableSet[a.freshSigma g n] F) :
    markerLaw (G := G) K ({ω | support ω = s} ∩ F) =
      markerLaw (G := G) K F * markerLaw (G := G) K {ω | support ω = s} := by
  rw [a.past_inter_fresh g n hs hF, mul_comm]

/-- Independent digit sequences at a fixed finite or infinite family of D-sites. -/
def blockDigits {I : Type*} (g : G) (r : ℕ) (sites : I ↪ a.D)
    (ω : G → K) (i : I) (j : ℕ) : K :=
  a.digits g ω (sites i, (r, j))

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
@[simp] theorem blockDigits_covariant {I : Type*} (b g : G) (r : ℕ)
    (sites : I ↪ a.D) (ω : G → K) :
    a.blockDigits (b * g) r sites (markerShift b ω) = a.blockDigits g r sites ω := by
  funext i j
  exact congrFun (a.digits_covariant b g ω) (sites i, (r, j))

omit [Fintype K] [Nonempty K] [MeasurableSingletonClass K] in
@[fun_prop] theorem measurable_blockDigits {I : Type*} (g : G) (r : ℕ)
    (sites : I ↪ a.D) : Measurable (a.blockDigits (K := K) g r sites) := by
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    measurable_pi_apply (a.address g (sites i, (r, j)))

noncomputable def streamLaw : Measure (ℕ → K) :=
  Measure.infinitePi (fun _ : ℕ => uniformBase K)

instance streamLaw_probability : IsProbabilityMeasure (streamLaw (K := K)) := by
  unfold streamLaw
  infer_instance

/-- An exact distribution identity for the actual coordinate streams. -/
theorem blockDigits_joint_law {I : Type*} (g : G) (r : ℕ) (sites : I ↪ a.D) :
    (markerLaw (G := G) K).map (a.blockDigits g r sites) =
      Measure.infinitePi (fun _ : I => streamLaw (K := K)) := by
  let f : I × ℕ → G := fun p => a.address g (sites p.1, (r, p.2))
  have hf : Function.Injective f := by
    intro p q hpq
    have h := a.address_injective g hpq
    exact Prod.ext (sites.injective (congrArg Prod.fst h))
      (congrArg (fun z : a.DigitIndex => z.2.2) h)
  have hl := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : G => uniformBase K) hf
  have hc : (MeasurableEquiv.curry I ℕ K) ∘ (fun ω i => ω (f i)) =
      a.blockDigits g r sites := rfl
  calc
    (markerLaw (G := G) K).map (a.blockDigits g r sites) =
        ((markerLaw (G := G) K).map (fun ω i => ω (f i))).map
          (MeasurableEquiv.curry I ℕ K) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop), hc]
    _ = (Measure.infinitePi (fun _ : I × ℕ => uniformBase K)).map
          (MeasurableEquiv.curry I ℕ K) := by rw [markerLaw, hl]
    _ = Measure.infinitePi (fun _ : I => streamLaw (K := K)) :=
      Measure.infinitePi_map_curry (fun (_ : I) (_ : ℕ) => uniformBase K)

/-- The cylinder bound giving null atoms of the digit-sequence law. -/
theorem stream_singleton_le (x : ℕ → K) (n : ℕ) :
    streamLaw (K := K) {x} ≤ (Fintype.card K : ℝ≥0∞)⁻¹ ^ n := by
  have hs : {x} ⊆ Set.pi (Finset.range n) (fun j => {x j}) := by
    intro y hy
    subst y
    simp
  calc
    streamLaw (K := K) {x} ≤ streamLaw (K := K)
        (Set.pi (Finset.range n) (fun j => {x j})) := measure_mono hs
    _ = (Fintype.card K : ℝ≥0∞)⁻¹ ^ n := by
      rw [streamLaw, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
      simp

/-- Distinct infinite iid streams cannot tie with positive mass. The first
step is the explicit q^(-n) bound, not a postulated atomless real variable. -/
theorem stream_singleton_zero [Nontrivial K] (x : ℕ → K) :
    streamLaw (K := K) {x} = 0 := by
  apply le_antisymm _ zero_le
  have hc : (Fintype.card K : ℝ≥0∞)⁻¹ < 1 := by
    apply ENNReal.inv_lt_one.2
    exact_mod_cast Fintype.one_lt_card
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc)
  exact Filter.Eventually.of_forall (stream_singleton_le x)

omit [Nonempty K] in
/-- The equality relation on infinite digit sequences is measurable. -/
theorem measurable_stream_diagonal :
    MeasurableSet {p : (ℕ → K) × (ℕ → K) | p.1 = p.2} := by
  have heq : {p : (ℕ → K) × (ℕ → K) | p.1 = p.2} =
      ⋂ j : ℕ, {p | p.1 j = p.2 j} := by
    ext p
    simp [funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => measurableSet_eq_fun
    ((measurable_pi_apply j).comp measurable_fst)
    ((measurable_pi_apply j).comp measurable_snd)

/-- Two independent concrete uniform digit streams tie with probability zero. -/
theorem stream_diagonal_zero [Nontrivial K] :
    ((streamLaw (K := K)).prod (streamLaw (K := K)))
      {p : (ℕ → K) × (ℕ → K) | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurable_stream_diagonal (K := K))]
  have hz : ∀ x : ℕ → K, streamLaw (K := K)
      (Prod.mk x ⁻¹' {p : (ℕ → K) × (ℕ → K) | p.1 = p.2}) = 0 := by
    intro x
    have heq : Prod.mk x ⁻¹' {p : (ℕ → K) × (ℕ → K) | p.1 = p.2} = {x} := by
      ext y
      simp [eq_comm]
    rw [heq, stream_singleton_zero]
  simp_rw [hz]
  simp

/-- Null ties in the independent stream array, proved from the concrete digit law. -/
theorem independent_streams_tie_zero {I : Type*} [Nontrivial K]
    {i j : I} (hij : i ≠ j) :
    (Measure.infinitePi (fun _ : I => streamLaw (K := K))) {x | x i = x j} = 0 := by
  have hm := measurable_stream_diagonal (K := K)
  have heq : {x : I → ℕ → K | x i = x j} =
      (fun x => (x i, x j)) ⁻¹' {p : (ℕ → K) × (ℕ → K) | p.1 = p.2} := rfl
  rw [heq, ← Measure.map_apply (by fun_prop) hm,
    Measure.infinitePi_map_eval_prod hij, stream_diagonal_zero]

/-- A single global domain on which every comparison used by finite blocks
is tie-free. The quantification is over all left translates, streams, and
distinct sites inside D. -/
def goodMarker : Set (G → K) :=
  {ω | ∀ (g : G) (r : ℕ) (u v : a.D), u ≠ v →
    a.blockDigits g r (Function.Embedding.refl a.D) ω u ≠
      a.blockDigits g r (Function.Embedding.refl a.D) ω v}

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem goodMarker_shift (b : G) {ω : G → K} (hω : ω ∈ a.goodMarker) :
    markerShift b ω ∈ a.goodMarker := by
  intro g r u v huv
  have hc : a.blockDigits g r (Function.Embedding.refl a.D) (markerShift b ω) =
      a.blockDigits (b⁻¹ * g) r (Function.Embedding.refl a.D) ω := by
    simpa using a.blockDigits_covariant b (b⁻¹ * g) r (Function.Embedding.refl a.D) ω
  rw [hc]
  exact hω (b⁻¹ * g) r u v huv

omit [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem goodMarker_shift_iff (b : G) (ω : G → K) :
    markerShift b ω ∈ a.goodMarker ↔ ω ∈ a.goodMarker := by
  constructor
  · intro h
    have hh := a.goodMarker_shift b⁻¹ h
    have heq : markerShift b⁻¹ (markerShift b ω) = ω := by
      funext g
      simp [markerShift]
    rwa [heq] at hh
  · exact a.goodMarker_shift b

omit [Nonempty K] in
theorem measurable_goodMarker [Countable G] : MeasurableSet (a.goodMarker (K := K)) := by
  have heq : a.goodMarker (K := K) =
      ⋂ g : G, ⋂ r : ℕ, ⋂ u : a.D, ⋂ v : a.D, ⋂ (_ : u ≠ v),
        {ω | a.blockDigits g r (Function.Embedding.refl a.D) ω u ≠
          a.blockDigits g r (Function.Embedding.refl a.D) ω v} := by
    ext ω
    simp [goodMarker]
  rw [heq]
  apply MeasurableSet.iInter
  intro g
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro u
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _
  exact ((measurable_stream_diagonal (K := K)).preimage
    ((((measurable_pi_apply u).comp (a.measurable_blockDigits g r _))).prodMk
      ((measurable_pi_apply v).comp (a.measurable_blockDigits g r _)))).compl

/-- The global tie-free domain has probability one for the actual finite
uniform marker, with no separately supplied real-valued random variables. -/
theorem ae_goodMarker [Countable G] [Nontrivial K] :
    ∀ᵐ ω ∂markerLaw (G := G) K, ω ∈ a.goodMarker := by
  change ∀ᵐ ω ∂markerLaw (G := G) K, ∀ (g : G) (r : ℕ) (u v : a.D), u ≠ v → _
  apply ae_all_iff.2
  intro g
  apply ae_all_iff.2
  intro r
  apply ae_all_iff.2
  intro u
  apply ae_all_iff.2
  intro v
  by_cases huv : u = v
  · exact Filter.Eventually.of_forall (fun _ h => (h huv).elim)
  · have hm : MeasurableSet {x : a.D → ℕ → K | x u = x v} := by
      change MeasurableSet ((fun x : a.D → ℕ → K => (x u, x v)) ⁻¹'
        {p : (ℕ → K) × (ℕ → K) | p.1 = p.2})
      exact (measurable_stream_diagonal (K := K)).preimage (by fun_prop)
    have hz := independent_streams_tie_zero (K := K) huv
    rw [← a.blockDigits_joint_law g r (Function.Embedding.refl a.D),
      Measure.map_apply (a.measurable_blockDigits g r _) hm] at hz
    have ha := (measure_eq_zero_iff_ae_notMem).1 hz
    exact ha.mono (fun _ h _ => h)

theorem goodMarker_probability [Countable G] [Nontrivial K] :
    markerLaw (G := G) K a.goodMarker = 1 :=
  (mem_ae_iff_prob_eq_one a.measurable_goodMarker).1 a.ae_goodMarker

end MarkerGeometry
end BernoulliIso
