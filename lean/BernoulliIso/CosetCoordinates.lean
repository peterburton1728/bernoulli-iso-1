module

public import BernoulliIso.RelativeProducts
public import BernoulliIso.FiniteOrdering
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.NoncommCoprod

/-!
Covariant coordinate charts for finite fibers, obtained from actual priority
ranks rather than a fixed transversal. The abstract chart is then specialized
to the map G/H → G/J for nested subgroups.
-/

@[expose] public section

open MeasureTheory

namespace BernoulliIso
namespace CosetCoordinates

abbrev Fiber {A B : Type*} (π : A → B) (b : B) := {a : A // π a = b}

section RankChart

variable {Ω A B K : Type*} [Fintype K] [Nonempty K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
  (π : A → B) [∀ b, Fintype (Fiber π b)] {κ : ℕ}
  (hcard : ∀ b, Fintype.card (Fiber π b) = κ)
  (priority : Ω → A → ℕ → K)
  (hinj : ∀ ω b, Function.Injective (fun a : Fiber π b => priority ω a.val))

/-- The first coordinate is the original fiber; the second is the actual
priority rank inside that fiber. -/
noncomputable def rankChart (ω : Ω) : A ≃ B × Fin κ :=
  (Equiv.sigmaFiberEquiv π).symm.trans <|
    (Equiv.sigmaCongrRight fun b =>
      FiniteOrdering.rankEquivOfCard (fun a : Fiber π b => priority ω a.val)
        (hinj ω b) (hcard b)).trans (Equiv.sigmaEquivProd B (Fin κ))

@[simp] theorem rankChart_fst (ω : Ω) (a : A) :
    (rankChart π hcard priority hinj ω a).1 = π a := rfl

@[simp] theorem rankChart_snd_val (ω : Ω) (a : A) :
    (rankChart π hcard priority hinj ω a).2.val =
      FiniteOrdering.rankNat (fun z : Fiber π (π a) => priority ω z.val) ⟨a, rfl⟩ := rfl

theorem measurable_rankChart [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [Countable A] [MeasurableSingletonClass A]
    (hm : ∀ a, Measurable (fun ω => priority ω a)) :
    Measurable (fun p : Ω × A => rankChart π hcard priority hinj p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro a
  change Measurable (fun ω => (π a, (rankChart π hcard priority hinj ω a).2))
  apply Measurable.prodMk measurable_const
  apply measurable_to_countable'
  intro k
  have hmrank := (FiniteOrdering.measurable_rankNat (⟨a, rfl⟩ : Fiber π (π a))).comp
    (Measurable.of_eval fun z => hm z.val)
  have heq : {ω | (rankChart π hcard priority hinj ω a).2 = k} =
      {ω | FiniteOrdering.rankNat (fun z : Fiber π (π a) => priority ω z.val)
        ⟨a, rfl⟩ = k.val} := by
    ext ω
    exact Fin.ext_iff
  change MeasurableSet {ω | (rankChart π hcard priority hinj ω a).2 = k}
  rw [heq]
  exact measurableSet_eq_fun hmrank measurable_const

end RankChart

/-- Inverting a measurable family of permutations of countable coordinate
sets preserves joint measurability. This is proved directly from singleton
fibers and does not impose any additional structure on the marker space. -/
theorem measurable_inverse_family {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (e : Ω → A ≃ B) (he : Measurable (fun p : Ω × A => e p.1 p.2)) :
    Measurable (fun p : Ω × B => (e p.1).symm p.2) := by
  apply measurable_from_prod_countable_left
  intro b
  apply measurable_to_countable'
  intro a
  have hm : Measurable (fun ω => e ω a) := he.comp (measurable_id.prodMk measurable_const)
  have hset : {ω | (e ω).symm b = a} = {ω | b = e ω a} := by
    ext ω
    constructor
    · intro h
      have hh := congrArg (e ω) h
      simpa using hh
    · intro h
      apply (e ω).injective
      simpa using h
  change MeasurableSet {ω | (e ω).symm b = a}
  rw [hset]
  exact measurableSet_eq_fun measurable_const hm

/-- Jointly measurable coordinate permutations induce an actual relative
isomorphism of iid probability fields. -/
def relativeReindexOfMeasurable {Ω A B Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (e : Ω → A ≃ B) (he : Measurable (fun p : Ω × A => e p.1 p.2)) :
    RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : A => μ))
      (Measure.infinitePi (fun _ : B => μ)) := by
  have hi := measurable_inverse_family e he
  have hEvalA : Measurable (fun p : (A → Z) × A => p.1 p.2) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply a
  have hEvalB : Measurable (fun p : (B → Z) × B => p.1 p.2) :=
    measurable_from_prod_countable_left fun b => measurable_pi_apply b
  apply RelativeProbabilityIso.reindex μ e
  · apply Measurable.of_eval
    intro b
    have hm : Measurable (fun p : Ω × (A → Z) => p.2 ((e p.1).symm b)) :=
      hEvalA.comp (measurable_snd.prodMk
      (hi.comp (measurable_fst.prodMk measurable_const)))
    convert hm using 1
    funext p
    simpa using MeasurableEquiv.piCongrLeft_apply_apply (e p.1) (β := fun _ => Z) p.2 ((e p.1).symm b)
  · apply Measurable.of_eval
    intro a
    have hm : Measurable (fun p : Ω × (B → Z) => p.2 (e p.1 a)) :=
      hEvalB.comp (measurable_snd.prodMk
      (he.comp (measurable_fst.prodMk measurable_const)))
    exact hm

/-- The ranked finite-fiber chart, now with its exact conditional iid law
and jointly measurable inverse. -/
noncomputable def relativeRankChart {Ω A B K Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (π : A → B) [∀ b, Fintype (Fiber π b)] {κ : ℕ}
    (hcard : ∀ b, Fintype.card (Fiber π b) = κ)
    (priority : Ω → A → ℕ → K)
    (hinj : ∀ ω b, Function.Injective (fun a : Fiber π b => priority ω a.val))
    (hm : ∀ a, Measurable (fun ω => priority ω a))
    (μ : Measure Z) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso Ω (Measure.infinitePi (fun _ : A => μ))
      (Measure.infinitePi (fun _ : B × Fin κ => μ)) :=
  relativeReindexOfMeasurable μ (rankChart π hcard priority hinj)
    (measurable_rankChart π hcard priority hinj hm)

/-- Translation identifies two fibers of any equivariant map. -/
def fiberTranslate {G A B : Type*} [Group G] [MulAction G A] [MulAction G B]
    (π : A → B) (hπ : ∀ (g : G) (a : A), π (g • a) = g • π a)
    (g : G) (b : B) : Fiber π b ≃ Fiber π (g • b) where
  toFun a := ⟨g • a.val, by rw [hπ, a.property]⟩
  invFun a := ⟨g⁻¹ • a.val, by rw [hπ, a.property, inv_smul_smul]⟩
  left_inv a := by ext; exact inv_smul_smul g a.val
  right_inv a := by ext; exact smul_inv_smul g a.val

/-- The rank chart is covariant, even though its fiber types change under
translation. The integer label itself is unchanged. -/
theorem rankChart_covariant {G Ω A B K : Type*} [Group G]
    [MulAction G Ω] [MulAction G A] [MulAction G B]
    [Fintype K] [Nonempty K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [LinearOrder K]
    (π : A → B) [∀ b, Fintype (Fiber π b)] {κ : ℕ}
    (hcard : ∀ b, Fintype.card (Fiber π b) = κ)
    (priority : Ω → A → ℕ → K)
    (hinj : ∀ ω b, Function.Injective (fun a : Fiber π b => priority ω a.val))
    (hπ : ∀ (g : G) (a : A), π (g • a) = g • π a)
    (hpriority : ∀ (g : G) (ω : Ω) (a : A), priority (g • ω) (g • a) = priority ω a)
    (g : G) (ω : Ω) (a : A) :
    rankChart π hcard priority hinj (g • ω) (g • a) =
      (g • (rankChart π hcard priority hinj ω a).1,
        (rankChart π hcard priority hinj ω a).2) := by
  apply Prod.ext
  · exact hπ g a
  · apply Fin.ext
    simp only [rankChart_snd_val]
    let e : Fiber π (π a) ≃ Fiber π (π (g • a)) :=
      { toFun z := ⟨g • z.val, by rw [hπ, z.property, hπ]⟩
        invFun z := ⟨g⁻¹ • z.val, by rw [hπ, z.property, hπ, inv_smul_smul]⟩
        left_inv z := by ext; exact inv_smul_smul g z.val
        right_inv z := by ext; exact smul_inv_smul g z.val }
    have hpre : (fun z : Fiber π (π a) => priority (g • ω) (e z).val) =
        (fun z : Fiber π (π a) => priority ω z.val) := by
      funext z
      exact hpriority g ω z.val
    have hr := FiniteOrdering.rankNat_precomp e
      (fun z : Fiber π (π (g • a)) => priority (g • ω) z.val) ⟨a, rfl⟩
    rw [hpre] at hr
    exact hr.symm

/-- The rank chart is covariant, even though its fiber types change under
translation. The integer label itself is unchanged. -/
theorem rankChart_covariant_at {G Ω A B K : Type*} [Group G]
    [MulAction G A] [MulAction G B]
    [Fintype K] [Nonempty K] [MeasurableSpace K]
    [MeasurableSingletonClass K] [LinearOrder K]
    (π : A → B) [∀ b, Fintype (Fiber π b)] {κ : ℕ}
    (hcard : ∀ b, Fintype.card (Fiber π b) = κ)
    (priority : Ω → A → ℕ → K)
    (hinj : ∀ ω b, Function.Injective (fun a : Fiber π b => priority ω a.val))
    (hπ : ∀ (g : G) (a : A), π (g • a) = g • π a)
    (g : G) (ω ω' : Ω)
    (hpriority : ∀ a, priority ω' (g • a) = priority ω a) (a : A) :
    rankChart π hcard priority hinj ω' (g • a) =
      (g • (rankChart π hcard priority hinj ω a).1,
        (rankChart π hcard priority hinj ω a).2) := by
  apply Prod.ext
  · exact hπ g a
  · apply Fin.ext
    simp only [rankChart_snd_val]
    let e : Fiber π (π a) ≃ Fiber π (π (g • a)) :=
      { toFun z := ⟨g • z.val, by rw [hπ, z.property, hπ]⟩
        invFun z := ⟨g⁻¹ • z.val, by rw [hπ, z.property, hπ, inv_smul_smul]⟩
        left_inv z := by ext; exact inv_smul_smul g z.val
        right_inv z := by ext; exact smul_inv_smul g z.val }
    have hpre : (fun z : Fiber π (π a) => priority ω' (e z).val) =
        (fun z : Fiber π (π a) => priority ω z.val) := by
      funext z
      exact hpriority z.val
    have hr := FiniteOrdering.rankNat_precomp e
      (fun z : Fiber π (π (g • a)) => priority ω' z.val) ⟨a, rfl⟩
    rw [hpre] at hr
    exact hr.symm

/-- A fixed product chart is used only to determine fiber cardinalities. -/
def fiberEquivOfProduct {A B C : Type*} (π : A → B) (e : A ≃ B × C)
    (hfst : ∀ a, (e a).1 = π a) (b : B) : Fiber π b ≃ C where
  toFun a := (e a.val).2
  invFun c := ⟨e.symm (b, c), by rw [← hfst, e.apply_symm_apply]⟩
  left_inv a := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · exact a.property.symm.trans (hfst a.val).symm
    · rfl
  right_inv c := by simp

/-- The coarse quotient map is equivariant for the actual left actions. -/
theorem quotientMap_covariant {G : Type*} [Group G] {H J : Subgroup G}
    (hHJ : H ≤ J) (g : G) (a : G ⧸ H) :
    Subgroup.quotientMapOfLE hHJ (g • a) = g • Subgroup.quotientMapOfLE hHJ a := by
  induction a using Quotient.inductionOn with
  | h a => rfl

/-- Every fiber of G/H → G/J has exactly the finite quotient J/H as its
underlying coordinate type. No normality of either subgroup is needed. -/
noncomputable def quotientFiberEquiv {G : Type*} [Group G] {H J : Subgroup G}
    (hHJ : H ≤ J) (b : G ⧸ J) :
    Fiber (Subgroup.quotientMapOfLE hHJ) b ≃ J ⧸ H.subgroupOf J :=
  fiberEquivOfProduct (Subgroup.quotientMapOfLE hHJ)
    (Subgroup.quotientEquivProdOfLE hHJ) (fun _ => rfl) b

instance quotientFiber_finite {G : Type*} [Group G] {H J : Subgroup G}
    [Finite J] (hHJ : H ≤ J) (b : G ⧸ J) :
    Finite (Fiber (Subgroup.quotientMapOfLE hHJ) b) :=
  Finite.of_equiv (J ⧸ H.subgroupOf J) (quotientFiberEquiv hHJ b).symm


/-- The actual sites in one left H-coset form a copy of H. -/
noncomputable def siteFiberEquiv {G : Type*} [Group G] (H : Subgroup G) (c : G ⧸ H) :
    Fiber (QuotientGroup.mk : G → G ⧸ H) c ≃ H :=
  fiberEquivOfProduct (QuotientGroup.mk : G → G ⧸ H)
    (Subgroup.groupEquivQuotientProdSubgroup (s := H)) (fun _ => rfl) c

instance siteFiber_finite {G : Type*} [Group G] (H : Subgroup G) [Finite H]
    (c : G ⧸ H) : Finite (Fiber (QuotientGroup.mk : G → G ⧸ H) c) :=
  Finite.of_equiv H (siteFiberEquiv H c).symm

noncomputable instance siteFiber_fintype {G : Type*} [Group G] (H : Subgroup G) [Finite H]
    (c : G ⧸ H) : Fintype (Fiber (QuotientGroup.mk : G → G ⧸ H) c) :=
  Fintype.ofFinite _

instance siteFiber_nonempty {G : Type*} [Group G] (H : Subgroup G)
    (c : G ⧸ H) : Nonempty (Fiber (QuotientGroup.mk : G → G ⧸ H) c) :=
  ⟨(siteFiberEquiv H c).symm 1⟩

instance quotient_countable {G : Type*} [Group G] [Countable G] (H : Subgroup G) :
    Countable (G ⧸ H) := (QuotientGroup.mk_surjective (s := H)).countable

section ActualPriorities

variable {G K : Type*} [Group G] (a : MarkerGeometry G)
  [Fintype K] [Nonempty K] [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]

/-- The stream belonging to an actual group site. -/
def siteStream (r : ℕ) (ω : G → K) (u : G) (n : ℕ) : K :=
  ω (u * a.step ^ a.serial (r, n))

@[fun_prop] theorem measurable_siteStream (r : ℕ) (u : G) :
    Measurable (fun ω : G → K => siteStream a r ω u) :=
  Measurable.of_eval fun n => measurable_pi_apply _

@[simp] theorem siteStream_covariant (r : ℕ) (b : G) (ω : G → K) (u : G) :
    siteStream a r (MarkerGeometry.markerShift b ω) (b * u) = siteStream a r ω u := by
  funext n
  simp [siteStream, MarkerGeometry.markerShift, mul_assoc]

/-- The priority of an H-coset is the minimum of the streams at all its
actual sites. No transversal is used in this definition. -/
noncomputable def cosetPriority (H : Subgroup G) [Finite H] (r : ℕ)
    (ω : G → K) (c : G ⧸ H) : ℕ → K :=
  FiniteOrdering.minimumStream
    (fun u : Fiber (QuotientGroup.mk : G → G ⧸ H) c => siteStream a r ω u.val)

@[fun_prop] theorem measurable_cosetPriority (H : Subgroup G) [Finite H]
    (r : ℕ) (c : G ⧸ H) : Measurable (fun ω : G → K => cosetPriority a H r ω c) :=
  FiniteOrdering.measurable_minimumStream.comp
    (Measurable.of_eval fun u => measurable_siteStream a r u.val)

@[simp] theorem cosetPriority_covariant (H : Subgroup G) [Finite H]
    (r : ℕ) (b : G) (ω : G → K) (c : G ⧸ H) :
    cosetPriority a H r (MarkerGeometry.markerShift b ω) (b • c) =
      cosetPriority a H r ω c := by
  let e := fiberTranslate (QuotientGroup.mk : G → G ⧸ H) (fun _ _ => rfl) b c
  have he := FiniteOrdering.minimumStream_precomp e
    (fun u => siteStream a r (MarkerGeometry.markerShift b ω) u.val)
  have hp : (fun u : Fiber (QuotientGroup.mk : G → G ⧸ H) c =>
      siteStream a r (MarkerGeometry.markerShift b ω) (e u).val) =
      (fun u => siteStream a r ω u.val) := by
    funext u
    exact siteStream_covariant a r b ω u.val
  rw [hp] at he
  exact he.symm

/-- On the global good marker set, actual streams distinguish every site
inside a fixed left coset of any subgroup of D. -/
theorem siteStream_injective_fiber {L : Subgroup G} (hLD : L ≤ a.D)
    (r : ℕ) {ω : G → K} (hω : ω ∈ a.goodMarker) (c : G ⧸ L) :
    Function.Injective (fun u : Fiber (QuotientGroup.mk : G → G ⧸ L) c =>
      siteStream a r ω u.val) := by
  intro u v huv
  have hu : c.out⁻¹ * u.val ∈ L :=
    QuotientGroup.eq.mp ((Quotient.out_eq' c).trans u.property.symm)
  have hv : c.out⁻¹ * v.val ∈ L :=
    QuotientGroup.eq.mp ((Quotient.out_eq' c).trans v.property.symm)
  let du : a.D := ⟨c.out⁻¹ * u.val, hLD hu⟩
  let dv : a.D := ⟨c.out⁻¹ * v.val, hLD hv⟩
  have hs : a.blockDigits c.out r (Function.Embedding.refl a.D) ω du =
      a.blockDigits c.out r (Function.Embedding.refl a.D) ω dv := by
    funext n
    simpa [MarkerGeometry.blockDigits, MarkerGeometry.digits, MarkerGeometry.address,
      du, dv, siteStream, mul_assoc] using congrFun huv n
  have hd : du = dv := by
    by_contra hne
    exact hω c.out r du dv hne hs
  apply Subtype.ext
  have hh := congrArg Subtype.val hd
  exact mul_left_cancel hh

/-- Packet minima distinguish the H-cosets in every larger L-coset. This
is the actual tie-free premise required by the ranked coordinate chart. -/
theorem cosetPriority_injective_fiber (H : Subgroup G) [Finite H]
    {L : Subgroup G} (hHL : H ≤ L) (hLD : L ≤ a.D)
    (r : ℕ) {ω : G → K} (hω : ω ∈ a.goodMarker) (c : G ⧸ L) :
    Function.Injective (fun z : Fiber (Subgroup.quotientMapOfLE hHL) c =>
      cosetPriority a H r ω z.val) := by
  intro z w hzw
  obtain ⟨u, hu⟩ := FiniteOrdering.minimumStream_mem
    (fun u : Fiber (QuotientGroup.mk : G → G ⧸ H) z.val => siteStream a r ω u.val)
  obtain ⟨v, hv⟩ := FiniteOrdering.minimumStream_mem
    (fun v : Fiber (QuotientGroup.mk : G → G ⧸ H) w.val => siteStream a r ω v.val)
  have huL : (QuotientGroup.mk u.val : G ⧸ L) = c := by
    have hh := congrArg (Subgroup.quotientMapOfLE hHL) u.property
    exact hh.trans z.property
  have hvL : (QuotientGroup.mk v.val : G ⧸ L) = c := by
    have hh := congrArg (Subgroup.quotientMapOfLE hHL) v.property
    exact hh.trans w.property
  have hs : siteStream a r ω u.val = siteStream a r ω v.val :=
    hu.symm.trans (hzw.trans hv)
  have he : (⟨u.val, huL⟩ : Fiber (QuotientGroup.mk : G → G ⧸ L) c) =
      ⟨v.val, hvL⟩ := siteStream_injective_fiber a hLD r hω c hs
  apply Subtype.ext
  exact u.property.symm.trans ((congrArg QuotientGroup.mk (congrArg Subtype.val he)).trans
    v.property)


/-- The marker-sorted quotient chart, on the invariant global good domain.
The sole cardinal input is the actual finite quotient L/H. -/
noncomputable def sortedCosetChart (H L : Subgroup G) [Finite H] [Finite L]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    (ω : a.goodMarker (K := K)) : (G ⧸ H) ≃ (G ⧸ L) × Fin κ := by
  letI : ∀ c, Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
    fun _ => Fintype.ofFinite _
  have hc : ∀ c, Fintype.card (Fiber (Subgroup.quotientMapOfLE hHL) c) = κ := by
    intro c
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (quotientFiberEquiv hHL c), hcard]
  exact rankChart (Subgroup.quotientMapOfLE hHL) hc
    (fun ω : a.goodMarker (K := K) => cosetPriority a H r ω.val)
    (fun ω c => cosetPriority_injective_fiber a H hHL hLD r ω.property c) ω

@[simp] theorem sortedCosetChart_fst (H L : Subgroup G) [Finite H] [Finite L]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    (ω : a.goodMarker (K := K)) (c : G ⧸ H) :
    (sortedCosetChart a H L hHL hLD hcard r ω c).1 =
      Subgroup.quotientMapOfLE hHL c := rfl

theorem sortedCosetChart_covariant (H L : Subgroup G) [Finite H] [Finite L]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    (b : G) (ω : a.goodMarker (K := K)) (c : G ⧸ H) :
    sortedCosetChart a H L hHL hLD hcard r
      ⟨MarkerGeometry.markerShift b ω.val, a.goodMarker_shift b ω.property⟩ (b • c) =
      (b • (sortedCosetChart a H L hHL hLD hcard r ω c).1,
        (sortedCosetChart a H L hHL hLD hcard r ω c).2) := by
  letI : ∀ c, Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
    fun _ => Fintype.ofFinite _
  unfold sortedCosetChart
  apply rankChart_covariant_at
  · exact quotientMap_covariant hHL
  · intro z
    exact cosetPriority_covariant a H r b ω.val z

theorem sortedCosetChart_symm_covariant (H L : Subgroup G) [Finite H] [Finite L]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    (b : G) (ω : a.goodMarker (K := K)) (c : G ⧸ L) (i : Fin κ) :
    (sortedCosetChart a H L hHL hLD hcard r
      ⟨MarkerGeometry.markerShift b ω.val, a.goodMarker_shift b ω.property⟩).symm (b • c, i) =
      b • (sortedCosetChart a H L hHL hLD hcard r ω).symm (c, i) := by
  apply (sortedCosetChart a H L hHL hLD hcard r
    ⟨MarkerGeometry.markerShift b ω.val, a.goodMarker_shift b ω.property⟩).injective
  rw [Equiv.apply_symm_apply, sortedCosetChart_covariant, Equiv.apply_symm_apply]

theorem measurable_sortedCosetChart [Countable G]
    (H L : Subgroup G) [Finite H] [Finite L]
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableSpace (G ⧸ L)]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ) :
    Measurable (fun p : a.goodMarker (K := K) × (G ⧸ H) =>
      sortedCosetChart a H L hHL hLD hcard r p.1 p.2) := by
  letI : ∀ c, Fintype (Fiber (Subgroup.quotientMapOfLE hHL) c) :=
    fun _ => Fintype.ofFinite _
  unfold sortedCosetChart
  apply measurable_rankChart
  intro c
  exact (measurable_cosetPriority a H r c).comp measurable_subtype_coe


theorem measurable_sortedCosetChart_symm [Countable G]
    (H L : Subgroup G) [Finite H] [Finite L]
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableSpace (G ⧸ L)] [MeasurableSingletonClass (G ⧸ L)]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ) :
    Measurable (fun p : a.goodMarker (K := K) × ((G ⧸ L) × Fin κ) =>
      (sortedCosetChart a H L hHL hLD hcard r p.1).symm p.2) :=
  measurable_inverse_family _ (measurable_sortedCosetChart a H L hHL hLD hcard r)

/-- The actual sorted coordinates preserve the full iid field law relative
to the marker, including joint measurability of both directions. -/
noncomputable def relativeSortedCosetChart [Countable G]
    (H L : Subgroup G) [Finite H] [Finite L]
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableSpace (G ⧸ L)] [MeasurableSingletonClass (G ⧸ L)]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] :
    RelativeProbabilityIso (a.goodMarker (K := K))
      (Measure.infinitePi (fun _ : G ⧸ H => μ))
      (Measure.infinitePi (fun _ : (G ⧸ L) × Fin κ => μ)) :=
  relativeReindexOfMeasurable μ (sortedCosetChart a H L hHL hLD hcard r)
    (measurable_sortedCosetChart a H L hHL hLD hcard r)


theorem relativeSortedCosetChart_apply [Countable G]
    (H L : Subgroup G) [Finite H] [Finite L]
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableSpace (G ⧸ L)] [MeasurableSingletonClass (G ⧸ L)]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ω : a.goodMarker (K := K)) (f : G ⧸ H → Z) (c : (G ⧸ L) × Fin κ) :
    (relativeSortedCosetChart a H L hHL hLD hcard r μ).equiv ω f c =
      f ((sortedCosetChart a H L hHL hLD hcard r ω).symm c) := by
  change MeasurableEquiv.piCongrLeft (fun _ => Z)
    (sortedCosetChart a H L hHL hLD hcard r ω) f c = _
  simpa using MeasurableEquiv.piCongrLeft_apply_apply
    (sortedCosetChart a H L hHL hLD hcard r ω) (β := fun _ => Z) f
    ((sortedCosetChart a H L hHL hLD hcard r ω).symm c)

/-- The actual probability reindexing intertwines the left shifts. -/
theorem relativeSortedCosetChart_covariant [Countable G]
    (H L : Subgroup G) [Finite H] [Finite L]
    [MeasurableSpace (G ⧸ H)] [MeasurableSingletonClass (G ⧸ H)]
    [MeasurableSpace (G ⧸ L)] [MeasurableSingletonClass (G ⧸ L)]
    (hHL : H ≤ L) (hLD : L ≤ a.D) {κ : ℕ}
    (hcard : Nat.card (L ⧸ H.subgroupOf L) = κ) (r : ℕ)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (b : G) (ω : a.goodMarker (K := K)) (f : G ⧸ H → Z) (c : G ⧸ L) (i : Fin κ) :
    (relativeSortedCosetChart a H L hHL hLD hcard r μ).equiv
      ⟨MarkerGeometry.markerShift b ω.val, a.goodMarker_shift b ω.property⟩
      (fun z => f (b⁻¹ • z)) (b • c, i) =
      (relativeSortedCosetChart a H L hHL hLD hcard r μ).equiv ω f (c, i) := by
  rw [relativeSortedCosetChart_apply, relativeSortedCosetChart_apply,
    sortedCosetChart_symm_covariant, inv_smul_smul]

end ActualPriorities


/-- Commuting, disjoint subgroups multiply bijectively onto their join. -/
noncomputable def commutingProductEquiv {G : Type*} [Group G] (H J : Subgroup G)
    (comm : ∀ h ∈ H, ∀ j ∈ J, Commute h j) (hd : Disjoint H J) :
    (H × J) ≃ (H ⊔ J : Subgroup G) := by
  let f := H.subtype.noncommCoprod J.subtype (fun h j => comm h.val h.property j.val j.property)
  have hf : Function.Injective f := Subgroup.mul_injective_of_disjoint hd
  have hr : f.range = H ⊔ J := by
    simpa using MonoidHom.noncommCoprod_range H.subtype J.subtype
      (fun h j => comm h.val h.property j.val j.property)
  exact (MonoidHom.ofInjective hf).toEquiv.trans
    (Equiv.cast (congrArg (fun S : Subgroup G => ↥S) hr))

theorem finite_sup_of_disjoint_commute {G : Type*} [Group G]
    (H J : Subgroup G) [Finite H] [Finite J]
    (comm : ∀ h ∈ H, ∀ j ∈ J, Commute h j) (hd : Disjoint H J) :
    Finite (H ⊔ J : Subgroup G) :=
  Finite.of_equiv (H × J) (commutingProductEquiv H J comm hd)

/-- The actual quotient (H∨J)/H has exactly |J| elements. No normality
of H in the ambient group is asserted or needed. -/
theorem card_quotient_sup_of_disjoint_commute {G : Type*} [Group G]
    (H J : Subgroup G) [Finite H]
    (comm : ∀ h ∈ H, ∀ j ∈ J, Commute h j) (hd : Disjoint H J) :
    Nat.card ((H ⊔ J : Subgroup G) ⧸ H.subgroupOf (H ⊔ J)) = Nat.card J := by
  have hprod : Nat.card (H ⊔ J : Subgroup G) = Nat.card H * Nat.card J := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (commutingProductEquiv H J comm hd).symm
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (H.subgroupOf (H ⊔ J))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show H ≤ H ⊔ J from le_sup_left)).toEquiv]
    at hlag
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  exact hlag.symm.trans (hprod.trans (mul_comm _ _))

end CosetCoordinates
end BernoulliIso

#print axioms BernoulliIso.CosetCoordinates.rankChart
#print axioms BernoulliIso.CosetCoordinates.rankChart_covariant
#print axioms BernoulliIso.CosetCoordinates.quotientFiberEquiv

#print axioms BernoulliIso.CosetCoordinates.sortedCosetChart
#print axioms BernoulliIso.CosetCoordinates.relativeSortedCosetChart
#print axioms BernoulliIso.CosetCoordinates.card_quotient_sup_of_disjoint_commute
