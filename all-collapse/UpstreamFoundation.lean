module

public import Mathlib
public import BernoulliIso.AlgebraicInput
public import BernoulliIso.CheckpointPrimeCertificate

@[expose] public section

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.Model -/
section

namespace OAI

namespace KaplanskyCounterexample

def MainClaim : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1

end KaplanskyCounterexample

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.Model -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrimeCertificate -/
section

namespace OAI

/-- A Lucas–Lehmer certificate for the Mersenne prime used in the degree bound. -/
theorem mersenne_21701_prime : (mersenne 21701).Prime :=
  BernoulliIso.CheckpointPrimeCertificate.mersenne_prime

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrimeCertificate -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.FiniteParameters -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

def sourceQ : ℕ := 2^217

lemma sourceQ_ge : 2^200 ≤ sourceQ := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 200 ≤ 217)

lemma sourceQ_large : 4800 ≤ sourceQ := by
  exact (by norm_num : 4800 ≤ (2:ℕ)^200).trans sourceQ_ge

lemma sourceQ_pos : 0 < sourceQ := lt_of_lt_of_le (by decide : 0 < 4800) sourceQ_large

lemma exponent_comparison (x : ℕ) (hx : 0 < x) : (x^13)^1200 ≤ (x^217)^72 := by
  rw [← pow_mul,← pow_mul]
  exact pow_le_pow_right₀ (by omega : 1 ≤ x) (by decide : 13*1200 ≤ 217*72)

lemma sourceQ_density : (4800:ℕ)^1200 ≤ sourceQ^72 := by
  exact (pow_le_pow_left' (by norm_num : (4800:ℕ) ≤ 2^13) 1200).trans
    (exponent_comparison 2 (by decide))

lemma source_prime_exists : ∃ p : ℕ, p.Prime ∧ sourceQ^100 ∣ p+1 := by
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one]
    rw [Nat.mul_comm]
  refine ⟨2*sourceQ^100-1,(by rw [hp]; exact mersenne_21701_prime),?_⟩
  have hpos : 0 < sourceQ^100 := pow_pos sourceQ_pos _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*sourceQ^100)]
  exact dvd_mul_left _ _

local instance : DecidablePred (fun p : ℕ => p.Prime ∧ sourceQ^100 ∣ p+1) := Classical.decPred _

def sourcePrime : ℕ := Nat.find source_prime_exists

def sourceD : ℕ := sourcePrime+1

lemma sourcePrime_prime : sourcePrime.Prime := (Nat.find_spec source_prime_exists).1
lemma sourcePrime_le (p : ℕ) (hp : p.Prime) (hc : sourceQ^100 ∣ p+1) : sourcePrime ≤ p :=
  Nat.find_min' source_prime_exists ⟨hp,hc⟩
lemma sourceD_divisible : sourceQ^100 ∣ sourceD := (Nat.find_spec source_prime_exists).2

lemma sourceD_bounds : sourceQ^100 ≤ sourceD ∧ sourceD ≤ 2*sourceQ^100 := by
  refine ⟨Nat.le_of_dvd (by unfold sourceD; omega) sourceD_divisible,?_⟩
  have hp : 2*sourceQ^100-1 = mersenne 21701 := by
    unfold sourceQ mersenne
    have h : 21701=217*100+1 := by decide
    rw [h,pow_add,pow_mul,pow_one,Nat.mul_comm]
  have hd : sourceQ^100 ∣ (2*sourceQ^100-1)+1 := by
    rw [Nat.sub_add_cancel (by have := pow_pos sourceQ_pos 100; omega)]
    exact dvd_mul_left _ _
  have hb : sourcePrime ≤ 2*sourceQ^100-1 := Nat.find_min' source_prime_exists ⟨(by rw [hp]; exact mersenne_21701_prime),hd⟩
  unfold sourceD
  have := pow_pos sourceQ_pos 100
  omega

lemma sourceD_q_dvd : sourceQ ∣ sourceD :=
  (dvd_pow_self sourceQ (by decide : 100 ≠ 0)).trans sourceD_divisible

lemma sourceD_log : Nat.log sourceQ sourceD = 100 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact sourceD_bounds.1
  · calc
      sourceD ≤ 2*sourceQ^100 := sourceD_bounds.2
      _ < sourceQ^100*sourceQ := by
        rw [Nat.mul_comm 2]
        exact Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (by decide : 2 < 4800) sourceQ_large)
          (pow_pos sourceQ_pos _)
      _ = sourceQ^(100+1) := (pow_succ _ _).symm

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.FiniteParameters -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedParameters -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

def Qcard (h : ℕ) : ℕ := 2^h

lemma prime_exists (h : ℕ) : ∃ p : ℕ, p.Prime ∧ (Qcard h)^100 ∣ p+1 := by
  have hq : (Qcard h)^100 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by decide : 2 ≠ 0))
  let : NeZero ((Qcard h)^100) := ⟨hq⟩
  obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((isUnit_one : IsUnit (1 : ZMod ((Qcard h)^100))).neg) 0
  refine ⟨p,hp,?_⟩
  apply (ZMod.natCast_eq_zero_iff (p+1) ((Qcard h)^100)).mp
  simp only [Nat.cast_add,Nat.cast_one,he,neg_add_cancel]

local instance (h : ℕ) : DecidablePred (fun p : ℕ => p.Prime ∧ (Qcard h)^100 ∣ p+1) :=
  Classical.decPred _

def prime (h : ℕ) : ℕ := Nat.find (prime_exists h)
def degree (h : ℕ) : ℕ := prime h + 1
def exponent (h : ℕ) : ℕ := Nat.log (Qcard h) (degree h)
def blockdim (h : ℕ) : ℕ := exponent h + 20
def dimension (h : ℕ) : ℕ := 10*blockdim h

lemma prime_prime (h : ℕ) : (prime h).Prime := (Nat.find_spec (prime_exists h)).1
lemma prime_congruent (h : ℕ) : (Qcard h)^100 ∣ prime h+1 :=
  (Nat.find_spec (prime_exists h)).2
lemma prime_le (h p : ℕ) (hp : p.Prime) (hc : (Qcard h)^100 ∣ p+1) : prime h ≤ p :=
  Nat.find_min' _ ⟨hp,hc⟩
lemma prime_pos (h : ℕ) : 0 < prime h := (prime_prime h).pos
lemma prime_ge (h : ℕ) (hh : 2 ≤ h) : 3 ≤ prime h := by
  have hq : 4 ≤ Qcard h := by exact Nat.pow_le_pow_right (by decide : 0 < 2) hh
  have hpow : Qcard h ≤ (Qcard h)^100 := by
    simpa using pow_le_pow_right₀ (by omega : 1 ≤ Qcard h) (by decide : 1 ≤ 100)
  have hl : Qcard h ≤ prime h+1 := hpow.trans
    (Nat.le_of_dvd (by omega) (prime_congruent h))
  omega
lemma prime_odd (h : ℕ) (hh : 2 ≤ h) : Odd (prime h) :=
  (prime_prime h).odd_of_ne_two (by have := prime_ge h hh; omega)
lemma dimension_pos (h : ℕ) : 0 < dimension h := by
  unfold dimension blockdim
  omega

lemma prime_217 : prime 217=FiniteGeometry.sourcePrime := by
  apply le_antisymm
  · exact prime_le 217 _ FiniteGeometry.sourcePrime_prime FiniteGeometry.sourceD_divisible
  · exact FiniteGeometry.sourcePrime_le _ (prime_prime 217) (prime_congruent 217)
lemma degree_217 : degree 217=FiniteGeometry.sourceD := by
  simp only [degree,prime_217,FiniteGeometry.sourceD]
lemma dimension_217 : dimension 217=1200 := by
  unfold dimension blockdim exponent
  rw [degree_217]
  change 10*(Nat.log FiniteGeometry.sourceQ FiniteGeometry.sourceD+20)=1200
  rw [FiniteGeometry.sourceD_log]

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedParameters -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.LexicographicOrder -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

/-- First successful element of a finite, linearly ordered search space. -/
def first {α : Type u_1} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) : α :=
  (Finset.univ.filter P).min' (by simpa [Finset.Nonempty] using h)

lemma first_spec {α : Type u_2} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) :
    P (first P h) := by
  have hh := Finset.min'_mem (Finset.univ.filter P) (by simpa [Finset.Nonempty] using h)
  exact (Finset.mem_filter.mp hh).2

lemma first_le {α : Type u_3} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x)
    (y : α) (hy : P y) : first P h ≤ y :=
  Finset.min'_le _ y (by simp [hy])

/-- Lexicographic order on coefficient/coordinate vectors, increasing index first. -/
@[instance_reducible] def vectorOrder {ι : Type u_4} [LinearOrder ι] [WellFoundedLT ι]
    {α : Type u_5} [LinearOrder α] : LinearOrder (ι → α) :=
  LinearOrder.lift' (toLex : (ι → α) → Lex (ι → α)) (fun _ _ h => h)

@[instance_reducible] def subsetOrder (α : Type u_6) [Fintype α] [LinearOrder α] : LinearOrder (Finset α) :=
  @LinearOrder.lift' (Finset α) (Lex (α → Bool)) inferInstance
    (fun S => toLex (fun x => decide (x ∈ S))) (by
      intro S T h
      apply Finset.ext
      intro x
      have hx := congrFun (congrArg ofLex h) x
      simpa using congrArg (fun b => b=true) hx)

/-- Residues are ordered 0,...,p-1, independently of their field operations. -/
@[instance_reducible] def residueOrder (p : ℕ) [NeZero p] : LinearOrder (ZMod p) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective p)

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.LexicographicOrder -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.QuotientField -/
section

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription

local instance two_neZero : NeZero (2 : ℕ) := inferInstance

local instance polynomialResidueOrder : LinearOrder (ZMod 2) := @residueOrder 2 two_neZero
local instance polynomialVectorOrder (d : ℕ) : LinearOrder (Fin (d+1) → ZMod 2) := vectorOrder

def irreducibleCoeffs (d : ℕ) (c : Fin (d+1) → ZMod 2) : Prop :=
  (ofFn (d+1) c).Monic ∧ (ofFn (d+1) c).natDegree=d ∧ Irreducible (ofFn (d+1) c)

lemma irreducibleCoeffs_exists (d : ℕ) (hd : 0 < d) : ∃ c, irreducibleCoeffs d c := by
  let K := GaloisField 2 d
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod 2) K
  have hb : b.dim=d := b.finrank.symm.trans (GaloisField.finrank 2 (Nat.ne_of_gt hd))
  have hi := b.isIntegral_gen
  have hdeg : (minpoly (ZMod 2) b.gen).natDegree=d := b.natDegree_minpoly.trans hb
  refine ⟨toFn (d+1) (minpoly (ZMod 2) b.gen),?_⟩
  unfold irreducibleCoeffs
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega : (minpoly (ZMod 2) b.gen).natDegree < d+1)]
  exact ⟨minpoly.monic hi,hdeg,minpoly.irreducible hi⟩

def firstCoeffs (d : ℕ) (hd : 0 < d) : Fin (d+1) → ZMod 2 :=
  first (irreducibleCoeffs d) (irreducibleCoeffs_exists d hd)

def firstPolynomial (d : ℕ) (hd : 0 < d) : (ZMod 2)[X] := ofFn (d+1) (firstCoeffs d hd)

lemma firstPolynomial_monic (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).Monic :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).1
lemma firstPolynomial_degree (d : ℕ) (hd : 0 < d) : (firstPolynomial d hd).natDegree=d :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.1
lemma firstPolynomial_irreducible (d : ℕ) (hd : 0 < d) : Irreducible (firstPolynomial d hd) :=
  (first_spec _ (irreducibleCoeffs_exists d hd)).2.2
lemma firstCoeffs_le (d : ℕ) (hd : 0 < d) (c : Fin (d+1) → ZMod 2)
    (hc : irreducibleCoeffs d c) : toLex (firstCoeffs d hd) ≤ toLex c :=
  first_le _ (irreducibleCoeffs_exists d hd) c hc

/-- Exactly F₂[Z]/(g), with g the lexicographically first monic irreducible
polynomial of the prescribed degree. -/
abbrev CoefficientField (d : ℕ) (hd : 0 < d) := AdjoinRoot (firstPolynomial d hd)

instance firstPolynomial_fact (d : ℕ) (hd : 0 < d) : Fact (Irreducible (firstPolynomial d hd)) :=
  ⟨firstPolynomial_irreducible d hd⟩

instance coefficientField_finite (d : ℕ) (hd : 0 < d) : Finite (CoefficientField d hd) := by
  let : Module.Finite (ZMod 2) (CoefficientField d hd) :=
    (AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finite
  exact Module.finite_of_finite (ZMod 2)

instance coefficientField_fintype (d : ℕ) (hd : 0 < d) : Fintype (CoefficientField d hd) :=
  Fintype.ofFinite _

lemma coefficientField_finrank (d : ℕ) (hd : 0 < d) :
    finrank (ZMod 2) (CoefficientField d hd)=d := by
  rw [(AdjoinRoot.powerBasis (firstPolynomial_monic d hd).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim,firstPolynomial_degree]

lemma coefficientField_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CoefficientField d hd)=2^d := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,coefficientField_finrank]

@[instance_reducible] def coefficientFieldOrder (d : ℕ) (hd : 0 < d) :
    LinearOrder (CoefficientField d hd) :=
  letI : LinearOrder (Fin (firstPolynomial d hd).natDegree → ZMod 2) := vectorOrder
  LinearOrder.lift' (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun
    (AdjoinRoot.powerBasisAux' (firstPolynomial_monic d hd)).equivFun.injective

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.QuotientField -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedSubfield -/
section

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription
variable (K : Type) [Field K] [CharP K 2]

def rootSubfield (h : ℕ) : Subfield K :=
  RingHom.eqLocusField (iterateFrobenius K 2 h) (RingHom.id K)

@[simp] lemma mem_rootSubfield (h : ℕ) (x : K) : x ∈ rootSubfield K h ↔ x^(2^h)=x := Iff.rfl

variable [Fintype K]

lemma rootSubfield_card_le (h : ℕ) (hh : 0 < h) :
    Fintype.card (rootSubfield K h) ≤ 2^h := by
  let p : K[X] := X^(2^h)-X
  have hq : 1 < (2:ℕ)^h := one_lt_pow₀ (by decide) (Nat.ne_of_gt hh)
  have hdeg : p.natDegree=2^h := by
    change (X^(2^h)-X : K[X]).natDegree=2^h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)]
    simp
  have hp : p ≠ 0 := by
    intro hz
    have hz' : p.natDegree=0 := hz ▸ natDegree_zero
    omega
  let f (x : rootSubfield K h) : p.roots.toFinset :=
    ⟨x.val,by
      rw [Multiset.mem_toFinset,mem_roots hp]
      change eval x.val (X^(2^h)-X : K[X])=0
      simp only [eval_sub,eval_pow,eval_X]
      exact sub_eq_zero.mpr x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (show x.val=y.val from congrArg (fun z : p.roots.toFinset => z.val) he)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hc
  exact hc.trans ((Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' p))

lemma rootSubfield_card (h : ℕ) (hh : 0 < h) [Algebra (ZMod 2) K]
    (hd : h ∣ finrank (ZMod 2) K) :
    Fintype.card (rootSubfield K h)=2^h := by
  let F := GaloisField 2 h
  let : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F=2^h := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 2 h (Nat.ne_of_gt hh)]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := F) (L := K)
    (by rwa [GaloisField.finrank 2 (Nat.ne_of_gt hh)])
  let g (x : F) : rootSubfield K h := ⟨f x,by
    change (f x)^(2^h)=f x
    rw [← map_pow,← hF,FiniteField.pow_card]⟩
  have hg : Function.Injective g := by
    intro x y he
    exact f.injective (congrArg Subtype.val he)
  apply le_antisymm (rootSubfield_card_le K h hh)
  exact hF ▸ Fintype.card_le_of_injective g hg

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedSubfield -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.PrescribedFields -/
section

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Input := {h : ℕ // 2 ≤ h}

def fieldDegree (h : Input) : ℕ := h.val*(prime h.val-1)
lemma fieldDegree_pos (h : Input) : 0 < fieldDegree h := by
  have := prime_ge h.val h.property
  exact Nat.mul_pos (by omega) (by omega)

abbrev K (h : Input) := CoefficientField (fieldDegree h) (fieldDegree_pos h)
instance K_field (input : Input) : Field (K input) := inferInstance

instance K_char (h : Input) : CharP (K h) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (K h)).injective 2

abbrev Q (h : Input) := rootSubfield (K h) h.val

instance K_order (h : Input) : LinearOrder (K h) := coefficientFieldOrder _ _

lemma K_card (h : Input) : Fintype.card (K h)=2^(fieldDegree h) :=
  coefficientField_card _ _
lemma Q_card (h : Input) : Fintype.card (Q h)=Qcard h.val := by
  apply rootSubfield_card (K h) h.val (by omega)
  rw [coefficientField_finrank]
  exact dvd_mul_right _ _

/-- The enumeration of the prescribed root subfield is in inherited coefficient order. -/
def enumeration (h : Input) : Fin (Qcard h.val) ≃ Q h :=
  (Fintype.orderIsoFinOfCardEq (Q h) (Q_card h)).toEquiv

lemma primitive_exists (h : Input) : ∃ ζ : K h, IsPrimitiveRoot ζ (prime h.val) := by
  let : Fact (prime h.val).Prime := ⟨prime_prime h.val⟩
  have hc : (2:ℕ).Coprime (prime h.val) := Nat.coprime_two_left.mpr (prime_odd h.val h.property)
  have hf := (Nat.ModEq.pow_card_sub_one_eq_one (prime_prime h.val) hc).pow h.val
  have hd : prime h.val ∣ Fintype.card (K h)ˣ := by
    rw [Fintype.card_units,K_card]
    simpa only [fieldDegree,← pow_mul,one_pow,Nat.mul_comm] using hf.symm.dvd'
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := (K h)ˣ) (prime h.val) hd
  refine ⟨u,IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  simpa only [orderOf_units] using hu

/-- The first element of multiplicative order ell in the literal coefficient order. -/
def zeta (h : Input) : K h := first (fun ζ => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)
lemma zeta_primitive (h : Input) : IsPrimitiveRoot (zeta h) (prime h.val) := by
  unfold zeta
  exact first_spec (fun ζ : K h => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)
lemma zeta_first (h : Input) (ζ : K h) (hζ : IsPrimitiveRoot ζ (prime h.val)) :
    zeta h ≤ ζ := by
  unfold zeta
  exact first_le _ _ ζ hζ

end KaplanskyCounterexample.Prescription
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.PrescribedFields -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DirectionSpaces -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

noncomputable section
open scoped BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

def curve {F : Type u_1} [Field F] (m : ℕ) (ξ : F) : Fin m → F := fun j => ξ ^ j.val

lemma curve_relation {F : Type u_2} [Field F] {k m : ℕ}
    (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ) (a : Fin k → F)
    (h : ∑ i, a i • curve m (ξ i) = 0) : a = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hξ
  intro j
  have hj := congrFun h (Fin.castLE hk j)
  simpa [curve, Finset.sum_apply, Pi.smul_apply] using hj

lemma curve_linearIndependent {F : Type u_3} [Field F] {k m : ℕ}
    (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ) :
    LinearIndependent F (fun i => curve m (ξ i)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  exact congrFun (curve_relation hk hξ a ha)

/-- The one-dimensional extension-field line, viewed over the ground field. -/
def curveMap {Q : Type u_4} {F : Type u_5} [Field Q] [Field F] [Algebra Q F]
    (m : ℕ) (ξ : F) : F →ₗ[Q] (Fin m → F) where
  toFun a := a • curve m ξ
  map_add' a b := add_smul _ _ _
  map_smul' c a := by
    ext j
    simp [Pi.smul_apply, Algebra.smul_def, mul_assoc]

lemma curveMap_injective {Q : Type u_6} {F : Type u_7} [Field Q] [Field F] [Algebra Q F]
    {m : ℕ} (hm : 0 < m) (ξ : F) : Function.Injective (curveMap (Q := Q) m ξ) := by
  intro a b hab
  have := congrFun hab ⟨0, hm⟩
  simpa [curveMap, curve] using this

/-- Any at most m of the extension-field lines have direct sum over Q.
Each chosen Q-subspace can subsequently be taken inside its own line. -/
lemma curveMap_direct {Q : Type u_8} {F : Type u_9} [Field Q] [Field F] [Algebra Q F]
    {k m : ℕ} (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ)
    (x : Fin k → (Fin m → F))
    (hx : ∀ i, x i ∈ (curveMap (Q := Q) m (ξ i)).range)
    (hsum : ∑ i, x i = 0) : ∀ i, x i = 0 := by
  choose a ha using hx
  have hrel : ∑ i, a i • curve m (ξ i) = 0 := by simpa [← ha, curveMap] using hsum
  have hz := curve_relation hk hξ a hrel
  intro i
  rw [← ha i]
  simp [hz]

/-- Select any required ground-field dimension inside a curve line. -/
lemma exists_subspace_in_curve {Q : Type u_10} {F : Type u_11} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] {m : ℕ} (hm : 0 < m) (ξ : F)
    (d : ℕ) (hd : d ≤ finrank Q F) :
    ∃ P : Submodule Q (Fin m → F), finrank Q P = d ∧
      P ≤ (curveMap (Q := Q) m ξ).range := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := F) hd
  let g := curveMap (Q := Q) m ξ
  have hg : Function.Injective g := curveMap_injective hm ξ
  refine ⟨Submodule.span Q (Set.range (g ∘ f)), ?_, ?_⟩
  · have hgf := hf.map' g (LinearMap.ker_eq_bot.mpr hg)
    simpa using finrank_span_eq_card hgf
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩

/-- Direct sum for distinct selections of at most m members of a family. -/
def ShortDirect {Q : Type u_12} {A : Type u_13} {ι : Type u_14} [Field Q] [AddCommGroup A] [Module Q A]
    (m : ℕ) (P : ι → Submodule Q A) : Prop :=
  ∀ (k : ℕ), k ≤ m → ∀ j : Fin k → ι, Function.Injective j →
    ∀ x : Fin k → A, (∀ i, x i ∈ P (j i)) → (∑ i, x i) = 0 → ∀ i, x i = 0

/-- The Vandermonde construction of all the required direction spaces. -/
theorem exists_shortDirect_subspaces {Q : Type u_15} {F : Type u_16} {ι : Type u_17} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] [Fintype F] [Fintype ι]
    {m : ℕ} (hm : 0 < m) (d : ι → ℕ) (hd : ∀ i, d i ≤ finrank Q F)
    (hcard : Fintype.card ι ≤ Fintype.card F) :
    ∃ P : ι → Submodule Q (Fin m → F),
      (∀ i, finrank Q (P i) = d i) ∧ ShortDirect m P := by
  obtain ⟨ξ⟩ := (Function.Embedding.nonempty_iff_card_le).mpr hcard
  choose P hPdim hPle using fun i => exists_subspace_in_curve hm (ξ i) (d i) (hd i)
  refine ⟨P, hPdim, ?_⟩
  intro k hk j hj x hx hsum
  exact curveMap_direct hk (ξ.injective.comp hj) x (fun i => hPle _ (hx i)) hsum

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DirectionSpaces -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ShortIndependence -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {ι : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]

lemma ShortDirect.finset_sum {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) (s : Finset ι) (hs : s.card ≤ m)
    (x : ι → A) (hx : ∀ i ∈ s, x i ∈ P i) (hz : ∑ i ∈ s, x i = 0) :
    ∀ i ∈ s, x i = 0 := by
  let e : Fin s.card ≃ s := (s.equivFin).symm
  have hh := h s.card hs (fun i => (e i).val)
    (fun i j hij => e.injective (Subtype.ext hij)) (fun i => x (e i).val)
    (fun i => hx _ (e i).property)
  have hh' : ∑ i : Fin s.card, x (e i).val = 0 := by
    rw [← hz]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans (Finset.sum_coe_sort s x)
  intro i hi
  simpa using hh hh' (e.symm ⟨i,hi⟩)

lemma ShortDirect.grouped_sum {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) {τ : Type u_4} (s : Finset τ) (hs : s.card ≤ m)
    (label : τ → ι) (x : τ → A) (hx : ∀ t ∈ s, x t ∈ P (label t))
    (hz : ∑ t ∈ s, x t = 0) :
    ∀ i, ∑ t ∈ s.filter (fun t => label t = i), x t = 0 := by
  let supp := s.image label
  let y : ι → A := fun i => ∑ t ∈ s.filter (fun t => label t = i), x t
  have hy (i : ι) : y i ∈ P i := by
    apply Submodule.sum_mem
    intro t ht
    obtain ⟨hts,he⟩ := Finset.mem_filter.mp ht
    rw [← he]
    exact hx t hts
  have hyz : ∑ i ∈ supp, y i = 0 := by
    rw [← hz]
    exact Finset.sum_fiberwise_of_maps_to (fun t ht => Finset.mem_image_of_mem label ht) x
  intro i
  by_cases hi : i ∈ supp
  · exact h.finset_sum supp ((Finset.card_image_le).trans hs) y (fun i _ => hy i) hyz i hi
  · have he : s.filter (fun t => label t = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact hi (he ▸ Finset.mem_image_of_mem label ht)
    rw [he, Finset.sum_empty]

lemma ShortDirect.disjoint {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) (hm : 2 ≤ m) {i j : ι} (hij : i ≠ j) :
    Disjoint (P i) (P j) := by
  rw [Submodule.disjoint_def]
  intro x hxi hxj
  have he : ∑ t ∈ ({i,j} : Finset ι), (if t = i then x else -x) = 0 := by
    simp [hij, hij.symm]
  have hz := h.finset_sum {i,j} (by simpa [hij] using hm)
    (fun t => if t = i then x else -x) (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ht | ht
      · subst t; simpa using hxi
      · subst t; simpa [hij.symm] using (P j).neg_mem hxj) he i (by simp)
  simpa using hz

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ShortIndependence -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.DirectionFrame -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure DirectionFrame (Q : Type u_5) (A : Type u_6) (R : Type u_7) (E : Type u_8) [Field Q] [AddCommGroup A] [Module Q A]
    [AddCommGroup E] [Module Q E] where
  w : R → (Q × Q) →ₗ[Q] A
  e : (R × Q) → E →ₗ[Q] A
  winj : ∀ r, Function.Injective (w r)
  einj : ∀ j, Function.Injective (e j)
  direct : ShortDirect 10 (Sum.elim (fun r => (w r).range) (fun j => (e j).range))

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def d (j : R × Q) : Q →ₗ[Q] A :=
  (F.w j.1).comp
    ({ toFun := fun t => (t, t * j.2)
       map_add' := by intro x y; simp [add_mul]
       map_smul' := by intro x y; simp [mul_assoc] } : Q →ₗ[Q] Q × Q)

def exc (r : R) : Q →ₗ[Q] A := (F.w r).comp (LinearMap.inr Q Q Q)

def u (j : R × Q) : (Q × E) →ₗ[Q] A := (F.d j).coprod (F.e j)

def W (r : R) : Submodule Q A := (F.w r).range

def D (j : R × Q) : Submodule Q A := (F.d j).range

def U (j : R × Q) : Submodule Q A := (F.u j).range

def exceptional (r : R) : Submodule Q A := (F.exc r).range

@[simp] lemma d_apply (j : R × Q) (t : Q) : F.d j t = F.w j.1 (t, t * j.2) := rfl
@[simp] lemma exc_apply (r : R) (t : Q) : F.exc r t = F.w r (0,t) := rfl
@[simp] lemma u_apply (j : R × Q) (x : Q × E) : F.u j x = F.d j x.1 + F.e j x.2 := rfl

lemma d_injective (j : R × Q) : Function.Injective (F.d j) := by
  intro x y he
  exact congrArg Prod.fst (F.winj _ he)

lemma exc_injective (r : R) : Function.Injective (F.exc r) := by
  intro x y he
  exact congrArg Prod.snd (F.winj _ he)

lemma w_e_disjoint (r : R) (j : R × Q) : Disjoint (F.W r) (F.e j).range :=
  F.direct.disjoint (by decide) (Sum.inl_ne_inr)

lemma u_injective (j : R × Q) : Function.Injective (F.u j) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  rintro ⟨t,x⟩ he
  have hw : F.d j t ∈ F.W j.1 := ⟨(t,t*j.2),rfl⟩
  have hE : F.d j t ∈ (F.e j).range := by
    refine ⟨-x, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he).symm
  have hz := (Submodule.disjoint_def.mp (F.w_e_disjoint j.1 j)) _ hw hE
  have ht : t = 0 := F.d_injective j (hz.trans (F.d j).map_zero.symm)
  have hx : x = 0 := F.einj j (by simpa only [u_apply, ht, map_zero, zero_add] using he)
  simp [ht,hx]

/-- Coordinate separation for the sum of two generic vectors. -/
lemma two_generic_E {j k : R × Q} (a b : Q × E)
    (he : F.u j a + F.u k b = 0) :
    F.e j a.2 + (if k = j then F.e k b.2 else 0) = 0 := by
  let labels : Fin 4 → R ⊕ (R × Q) := ![.inl j.1, .inr j, .inl k.1, .inr k]
  let v : Fin 4 → A := ![F.d j a.1, F.e j a.2, F.d k b.1, F.e k b.2]
  have hz : ∑ i : Fin 4, v i = 0 := by
    simpa [v, Fin.sum_univ_succ, u_apply, add_assoc] using he
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 4)), v i ∈
      Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (labels i) := by
    intro i _
    fin_cases i
    · exact ⟨(a.1,a.1*j.2),rfl⟩
    · exact ⟨a.2,rfl⟩
    · exact ⟨(b.1,b.1*k.2),rfl⟩
    · exact ⟨b.2,rfl⟩
  have hh := F.direct.grouped_sum Finset.univ (by simp) labels v hm hz (.inr j)
  simpa [labels, v, Finset.sum_filter, Fin.sum_univ_succ] using hh

lemma U_disjoint {j k : R × Q} (hjk : j ≠ k) : Disjoint (F.U j) (F.U k) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have he : F.u j a + F.u k (-b) = 0 := by rw [map_neg, hb, add_neg_cancel]
  have hE := F.two_generic_E a (-b) he
  simp only [ite_eq_right hjk.symm, add_zero] at hE
  have ha : a.2 = 0 := F.einj j (by simpa using hE)
  have hE' := F.two_generic_E (-b) a (by simpa [add_comm] using he)
  simp only [ite_eq_right hjk, add_zero] at hE'
  have hb0 : b.2 = 0 := by
    have hh : (-b).2 = 0 := F.einj k (by simpa using hE')
    simpa using hh
  have hw : F.d k b.1 = F.d j a.1 := by simpa [u_apply, ha, hb0] using hb
  by_cases hr : j.1 = k.1
  · have hcoord := F.winj j.1 (by simpa [hr] using hw.symm)
    have ht := congrArg Prod.fst hcoord
    change a.1 = b.1 at ht
    have hs := congrArg Prod.snd hcoord
    change a.1 * j.2 = b.1 * k.2 at hs
    have hv : j.2 ≠ k.2 := fun h => hjk (Prod.ext hr h)
    have hat : a.1 = 0 := by
      by_contra hn
      exact hv (mul_left_cancel₀ hn (by rw [← ht] at hs; exact hs))
    simp only [u_apply, ha, hat, map_zero, add_zero]
  · have hd := F.direct.disjoint (by decide : 2 ≤ 10)
      (show Sum.inl j.1 ≠ (Sum.inl k.1 : R ⊕ (R × Q)) from fun h => hr (Sum.inl.inj h))
    have hz : F.d j a.1 = 0 := (Submodule.disjoint_def.mp hd) _
      ⟨(a.1,a.1*j.2),rfl⟩ ⟨(b.1,b.1*k.2),hw⟩
    simpa only [u_apply,ha,map_zero,add_zero] using hz

lemma generic_eq_w_E_zero {j : R × Q} {r : R} (a : Q × E) (b : Q × Q)
    (he : F.u j a = F.w r b) : a.2 = 0 := by
  let labels : Fin 3 → R ⊕ (R × Q) := ![.inl j.1, .inr j, .inl r]
  let v : Fin 3 → A := ![F.d j a.1, F.e j a.2, -(F.w r b)]
  have hz : ∑ i : Fin 3, v i = 0 := by
    simpa [v, Fin.sum_univ_succ, u_apply, sub_eq_add_neg, add_assoc] using sub_eq_zero.mpr he
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), v i ∈
      Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (labels i) := by
    intro i _
    fin_cases i
    · exact ⟨(a.1,a.1*j.2),rfl⟩
    · exact ⟨a.2,rfl⟩
    · exact ⟨-b, by simp [v]⟩
  have hh := F.direct.grouped_sum Finset.univ (by simp) labels v hm hz (.inr j)
  apply F.einj j
  simpa [labels,v,Finset.sum_filter,Fin.sum_univ_succ] using hh

lemma W_disjoint {r t : R} (hrt : r ≠ t) : Disjoint (F.W r) (F.W t) :=
  F.direct.disjoint (by decide) (fun h => hrt (Sum.inl.inj h))

lemma U_inf_W_same (j : R × Q) : F.U j ⊓ F.W j.1 = F.D j := by
  apply le_antisymm
  · rintro x ⟨⟨a,rfl⟩,⟨b,hb⟩⟩
    have ha := F.generic_eq_w_E_zero a b hb.symm
    exact ⟨a.1, by simp only [u_apply,ha,map_zero,add_zero]⟩
  · rintro x ⟨a,rfl⟩
    exact ⟨⟨(a,0), by simp only [u_apply,map_zero,add_zero]⟩,⟨(a,a*j.2),rfl⟩⟩

lemma U_W_disjoint {j : R × Q} {r : R} (hjr : j.1 ≠ r) :
    Disjoint (F.U j) (F.W r) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have ha := F.generic_eq_w_E_zero a b hb.symm
  have hx : F.u j a = F.d j a.1 := by simp only [u_apply,ha,map_zero,add_zero]
  rw [hx] at hb ⊢
  exact Submodule.disjoint_def.mp (F.W_disjoint hjr) _ ⟨(a.1,a.1*j.2),rfl⟩ ⟨b,hb⟩

lemma U_exceptional_disjoint (j : R × Q) (r : R) :
    Disjoint (F.U j) (F.exceptional r) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨a,rfl⟩ ⟨b,hb⟩
  have ha := F.generic_eq_w_E_zero a (0,b) hb.symm
  have hx : F.u j a = F.d j a.1 := by simp only [u_apply,ha,map_zero,add_zero]
  rw [hx] at hb ⊢
  by_cases hr : j.1 = r
  · have hc := F.winj r (by simpa [hr] using hb)
    have ht : a.1 = 0 := (congrArg Prod.fst hc).symm
    rw [ht,map_zero]
  · exact Submodule.disjoint_def.mp (F.W_disjoint hr) _
      ⟨(a.1,a.1*j.2),rfl⟩ ⟨(0,b),hb⟩

lemma exceptional_disjoint {r t : R} (hrt : r ≠ t) :
    Disjoint (F.exceptional r) (F.exceptional t) := by
  apply (F.W_disjoint hrt).mono
  · rintro x ⟨a,rfl⟩
    exact ⟨(0,a),rfl⟩
  · rintro x ⟨a,rfl⟩
    exact ⟨(0,a),rfl⟩

lemma card_U [Fintype Q] [Fintype E] [Fintype A] (j : R × Q) :
    Fintype.card (F.U j) = Fintype.card Q * Fintype.card E := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (LinearEquiv.ofInjective (F.u j) (F.u_injective j)).toEquiv.symm

lemma card_D [Fintype Q] [Fintype A] (j : R × Q) :
    Fintype.card (F.D j) = Fintype.card Q :=
  Fintype.card_congr (LinearEquiv.ofInjective (F.d j) (F.d_injective j)).toEquiv.symm

lemma card_W [Fintype Q] [Fintype A] (r : R) :
    Fintype.card (F.W r) = Fintype.card Q ^ 2 := by
  have hc := Fintype.card_congr (LinearEquiv.ofInjective (F.w r) (F.winj r)).toEquiv.symm
  simpa [W,pow_two] using hc

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.DirectionFrame -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.FrameExistence -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

theorem exists_directionFrame {Q : Type u_1} {F : Type u_2} {R : Type u_3} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] [Fintype Q] [Fintype F] [Fintype R]
    (b : ℕ) (hb : 2 ≤ b) (hdim : finrank Q F = b)
    (hsize : Fintype.card R + Fintype.card R * Fintype.card Q ≤ Fintype.card F) :
    Nonempty (DirectionFrame Q (Fin 10 → F) R (Fin (b-1) → Q)) := by
  let ι := R ⊕ (R × Q)
  let dim : ι → ℕ := Sum.elim (fun _ => 2) (fun _ => b-1)
  obtain ⟨P,hd,hP⟩ := exists_shortDirect_subspaces (Q := Q) (F := F)
    (ι := ι) (by decide : 0 < 10) dim (by
      intro i
      cases i <;> simp [dim,hdim,hb]) (by simpa [ι] using hsize)
  let W (r : R) : (Q × Q) ≃ₗ[Q] P (.inl r) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [dim] using (hd (.inl r)).symm)
  let E (j : R × Q) : (Fin (b-1) → Q) ≃ₗ[Q] P (.inr j) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [dim] using (hd (.inr j)).symm)
  let w (r : R) := (P (.inl r)).subtype.comp (W r).toLinearMap
  let e (j : R × Q) := (P (.inr j)).subtype.comp (E j).toLinearMap
  refine ⟨{w := w, e := e, winj := ?_, einj := ?_, direct := ?_}⟩
  · intro r
    exact Subtype.val_injective.comp (W r).injective
  · intro j
    exact Subtype.val_injective.comp (E j).injective
  · intro k hk j hj x hx hz
    apply hP k hk j hj x _ hz
    intro i
    have hh := hx i
    cases hji : j i with
    | inl r =>
      simp only [hji, Sum.elim_inl] at hh
      obtain ⟨a,ha⟩ := hh
      rw [← ha]
      exact (W r a).property
    | inr t =>
      simp only [hji, Sum.elim_inr] at hh
      obtain ⟨a,ha⟩ := hh
      rw [← ha]
      exact (E t a).property

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.FrameExistence -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.FieldExtensions -/
section

namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

/-- Finite characteristic-two fields have finite extensions of every positive degree. -/
theorem exists_finite_extension (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (b : ℕ) (hb : 0 < b) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra Q F) (_ : Fintype F),
      finrank Q F = b := by
  let : Algebra (ZMod 2) Q := ZMod.algebra Q 2
  let h := finrank (ZMod 2) Q
  have hh : 0 < h := Module.finrank_pos
  let F := GaloisField 2 (h * b)
  have hFb : finrank (ZMod 2) F = h * b :=
    GaloisField.finrank 2 (Nat.ne_of_gt (Nat.mul_pos hh hb))
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := Q) (L := F)
    (by rw [hFb]; exact dvd_mul_right h b)
  algebraize [f.toRingHom]
  let : Fintype F := Fintype.ofFinite F
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  have ht := Module.finrank_mul_finrank (ZMod 2) Q F
  rw [hFb] at ht
  exact Nat.eq_of_mul_eq_mul_left hh ht

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.FieldExtensions -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.FrameTransport -/
section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A B R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [AddCommGroup E] [Module Q E]

namespace DirectionFrame

def transport (F : DirectionFrame Q A R E) (f : A ≃ₗ[Q] B) : DirectionFrame Q B R E where
  w r := f.toLinearMap.comp (F.w r)
  e j := f.toLinearMap.comp (F.e j)
  winj r := f.injective.comp (F.winj r)
  einj j := f.injective.comp (F.einj j)
  direct := by
    intro k hk j hj x hx hz
    have hm (i : Fin k) : f.symm (x i) ∈ Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (j i) := by
      have hxi := hx i
      cases he : j i with
      | inl r =>
        simp only [he,Sum.elim_inl] at hxi ⊢
        obtain ⟨a,ha⟩ := hxi
        exact ⟨a,by rw [← ha]; exact (f.symm_apply_apply _).symm⟩
      | inr t =>
        simp only [he,Sum.elim_inr] at hxi ⊢
        obtain ⟨a,ha⟩ := hxi
        exact ⟨a,by rw [← ha]; exact (f.symm_apply_apply _).symm⟩
    have hsum : ∑ i, f.symm (x i)=0 := by rw [← map_sum,hz,map_zero]
    have hh := F.direct k hk j hj (fun i => f.symm (x i)) hm hsum
    intro i
    exact f.symm.injective ((hh i).trans f.symm.map_zero.symm)

end DirectionFrame

lemma exists_coordinate_frame (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (R : Type) [Fintype R]
    (hsize : Fintype.card R + Fintype.card R * Fintype.card Q ≤ (Fintype.card Q)^120) :
    Nonempty (DirectionFrame Q (Fin 1200 → Q) R (Fin 119 → Q)) := by
  obtain ⟨F,hF,hA,hfin,hD⟩ := exists_finite_extension Q 120 (by decide)
  let _ := hF
  let _ := hA
  let _ := hfin
  have hcard : Fintype.card F=(Fintype.card Q)^120 := by
    rw [Module.card_eq_pow_finrank (K := Q) (V := F),hD]
  obtain ⟨frame⟩ := exists_directionFrame (Q := Q) (F := F) (R := R) 120 (by decide) hD (by rwa [hcard])
  let f : (Fin 10 → F) ≃ₗ[Q] (Fin 1200 → Q) := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype,Module.finrank_pi]
    simp [hD])
  exact ⟨frame.transport f⟩

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.FrameTransport -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ParameterBounds -/
section

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma sourceQ_very_large : 3305600000 ≤ sourceQ :=
  (by norm_num : 3305600000 ≤ (2:ℕ)^200).trans sourceQ_ge

lemma sourcePrime_ge : 3 ≤ sourcePrime := by
  have hp : sourceQ ≤ sourceQ^100 := by
    simpa using pow_le_pow_right₀ (by have := sourceQ_pos; omega : 1 ≤ sourceQ) (show 1 ≤ 100 by decide)
  have hb := sourceD_bounds.1
  have hq := sourceQ_large
  unfold sourceD at hb
  omega

lemma sourcePrime_odd : Odd sourcePrime := sourcePrime_prime.odd_of_ne_two (by have := sourcePrime_ge; omega)

lemma small_degree_square {q D : ℕ} (hq : 4 ≤ q) (hD : D ≤ 2*q^100) : D^2 ≤ q^1200 := by
  have hq1 : 1 ≤ q := by omega
  calc
    D^2 ≤ (2*q^100)^2 := Nat.pow_le_pow_left hD 2
    _ = 4*q^200 := by ring
    _ ≤ q*q^200 := Nat.mul_le_mul_right _ hq
    _ = q^201 := by ring
    _ ≤ q^1200 := pow_le_pow_right₀ hq1 (by decide)

lemma small_degree_frame_size {q D : ℕ} (hq : 4 ≤ q) (hD : D ≤ 2*q^100) (hdvd : q ∣ D) :
    D/q+(D/q)*q ≤ q^120 := by
  have hq1 : 1 ≤ q := by omega
  have he := Nat.div_mul_cancel hdvd
  have hb := Nat.div_le_self D q
  calc
    D/q+(D/q)*q ≤ D+D := by omega
    _ ≤ 4*q^100 := by omega
    _ ≤ q*q^100 := Nat.mul_le_mul_right _ hq
    _ = q^101 := by ring
    _ ≤ q^120 := pow_le_pow_right₀ hq1 (by decide)

lemma sourceD_square_le : sourceD^2 ≤ sourceQ^1200 :=
  small_degree_square (sourceQ_large.trans' (by decide)) sourceD_bounds.2

lemma source_frame_size : sourceD/sourceQ+(sourceD/sourceQ)*sourceQ ≤ sourceQ^120 :=
  small_degree_frame_size (sourceQ_large.trans' (by decide)) sourceD_bounds.2 sourceD_q_dvd

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ParameterBounds -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.FiniteAffine -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A] [Fintype A]

/-- Full finite affine cosets; no subset or segment convention is used. -/
def cosetPoints (U : Submodule Q A) (x : A) : Finset A :=
  Finset.univ.filter (fun y => y - x ∈ U)

@[simp] lemma mem_cosetPoints (U : Submodule Q A) (x y : A) :
    y ∈ cosetPoints U x ↔ y - x ∈ U := by simp [cosetPoints]

lemma self_mem_cosetPoints (U : Submodule Q A) (x : A) : x ∈ cosetPoints U x := by simp

lemma cosetPoints_eq {U : Submodule Q A} {x y : A} (h : y - x ∈ U) :
    cosetPoints U y = cosetPoints U x := by
  ext z
  simp only [mem_cosetPoints]
  constructor
  · intro hz
    convert U.add_mem hz h using 1; abel
  · intro hz
    convert U.sub_mem hz h using 1; abel

lemma cosetPoints_image (U : Submodule Q A) (x : A) :
    cosetPoints U x = Finset.univ.image (fun u : U => x + (u : A)) := by
  ext y
  simp only [mem_cosetPoints, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hy
    exact ⟨⟨y - x, hy⟩, by simp⟩
  · rintro ⟨u, rfl⟩
    simp [u.property]

lemma card_cosetPoints (U : Submodule Q A) (x : A) :
    (cosetPoints U x).card = Fintype.card U := by
  rw [cosetPoints_image, Finset.card_image_of_injective, Finset.card_univ]
  intro i j hij
  exact Subtype.ext (add_left_cancel hij)

lemma intersection_cosets_card_le (U W : Submodule Q A) (x o : A) :
    ((cosetPoints U x) ∩ (cosetPoints W o)).card ≤ Fintype.card ↥(U ⊓ W) := by
  by_cases hn : ((cosetPoints U x) ∩ (cosetPoints W o)).Nonempty
  · obtain ⟨z, hz⟩ := hn
    have huz : z - x ∈ U := by simpa using (Finset.mem_inter.mp hz).1
    have hwz : z - o ∈ W := by simpa using (Finset.mem_inter.mp hz).2
    rw [← cosetPoints_eq huz, ← cosetPoints_eq hwz]
    have he : cosetPoints U z ∩ cosetPoints W z = cosetPoints (U ⊓ W) z := by
      ext y
      simp
    rw [he, card_cosetPoints]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]

/-- Two independent directions yield disjoint affine cosets or a single point. -/
lemma intersection_cosets_card_le_one (U W : Submodule Q A) (h : Disjoint U W) (x o : A) :
    ((cosetPoints U x) ∩ (cosetPoints W o)).card ≤ 1 := by
  have hc := intersection_cosets_card_le U W x o
  simpa [h.eq_bot] using hc

/-- A coset variable is its full point set, so no arbitrary representatives
enter the random choices. -/
def AffineCoset (U : Submodule Q A) := {C : Finset A // ∃ x, C = cosetPoints U x}

namespace AffineCoset
variable (U : Submodule Q A)

def of (x : A) : AffineCoset U := ⟨cosetPoints U x,x,rfl⟩

instance : Fintype (AffineCoset U) := by
  unfold AffineCoset
  infer_instance

lemma of_surjective : Function.Surjective (of U) := by
  rintro ⟨C,x,rfl⟩
  exact ⟨x,rfl⟩

lemma card_le : Fintype.card (AffineCoset U) ≤ Fintype.card A :=
  Fintype.card_le_of_surjective _ (of_surjective U)

lemma card (C : AffineCoset U) : C.val.card = Fintype.card U := by
  obtain ⟨x,hx⟩ := C.property
  rw [hx,card_cosetPoints]

lemma nonempty (C : AffineCoset U) : C.val.Nonempty := by
  obtain ⟨x,hx⟩ := C.property
  exact ⟨x,hx ▸ self_mem_cosetPoints U x⟩

lemma eq_of_mem {C : AffineCoset U} {x : A} (hx : x ∈ C.val) : of U x = C := by
  obtain ⟨y,hy⟩ := C.property
  apply Subtype.ext
  change cosetPoints U x = C.val
  rw [hy] at hx ⊢
  exact cosetPoints_eq ((mem_cosetPoints U y x).mp hx)

lemma mem_iff (C : AffineCoset U) (x : A) : x ∈ C.val ↔ of U x = C := by
  refine ⟨eq_of_mem U, ?_⟩
  intro hx
  rw [← hx]
  exact self_mem_cosetPoints U x

lemma of_eq_iff (x y : A) : of U x = of U y ↔ x - y ∈ U := by
  rw [← mem_iff]
  exact mem_cosetPoints U y x

lemma add_mem_iff (C : AffineCoset U) (x v : A) (hv : v ∈ U) :
    x + v ∈ C.val ↔ x ∈ C.val := by
  obtain ⟨y,hy⟩ := C.property
  rw [hy]
  simp only [mem_cosetPoints]
  have he : x + v - y = (x - y) + v := by abel
  rw [he]
  exact (Submodule.add_mem_iff_left U hv)

end AffineCoset

variable [Fintype Q]

/-- A direction vector parametrizes every point of its full line. -/
def linePoints (x v : A) : Finset A := Finset.univ.image (fun t : Q => x + t • v)

omit [Fintype Q] [Fintype A] in
lemma lineParam_injective {x v : A} (hv : v ≠ 0) :
    Function.Injective (fun t : Q => x + t • v) := by
  intro t s ht
  exact (smul_left_injective Q hv) (add_left_cancel ht)

omit [Fintype A] in
lemma card_linePoints (x : A) {v : A} (hv : v ≠ 0) :
    (linePoints (Q := Q) x v).card = Fintype.card Q := by
  rw [linePoints, Finset.card_image_of_injective _ (lineParam_injective hv), Finset.card_univ]

omit [Fintype A] in
lemma base_mem_linePoints (x v : A) : x ∈ linePoints (Q := Q) x v := by
  simp only [linePoints, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨0, by simp⟩

lemma linePoints_eq_coset (x v : A) :
    linePoints (Q := Q) x v = cosetPoints (Submodule.span Q {v}) x := by
  ext y
  simp only [linePoints, Finset.mem_image, Finset.mem_univ, true_and, mem_cosetPoints,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [ht]; abel⟩

/-- Affine lines are identified by their actual point sets. -/
def FullLine (s : Finset A) : Prop := ∃ x v : A, v ≠ 0 ∧ s = linePoints (Q := Q) x v

omit [Fintype A] in
lemma FullLine.card {s : Finset A} (hs : FullLine (Q := Q) s) : s.card = Fintype.card Q := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  exact card_linePoints x hv

omit [Fintype A] in
lemma FullLine.nonempty {s : Finset A} (hs : FullLine (Q := Q) s) : s.Nonempty := by
  obtain ⟨x,v,hv,rfl⟩ := hs
  exact ⟨x, base_mem_linePoints x v⟩

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.FiniteAffine -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.Alteration -/
section

namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
namespace KaplanskyCounterexample.FiniteGeometry

variable {α : Type u_1} {ι : Type u_2} [Fintype α]

/-- Independent selection of points at a prescribed probability. -/
def selectionMeasure (p : Set.Icc (0 : ℝ) 1) : Measure (α → Bool) :=
  Measure.pi fun _ => bernoulliMeasure true false p

instance (p : Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (selectionMeasure (α := α) p) := by
  unfold selectionMeasure
  infer_instance

def allSelected (s : Finset α) : Set (α → Bool) := {ω | ∀ x ∈ s, ω x = true}

lemma probability_allSelected (p : Set.Icc (0 : ℝ) 1) (s : Finset α) :
    (selectionMeasure p).real (allSelected s) = p.val ^ s.card := by
  change (Measure.pi (fun _ : α => bernoulliMeasure true false p)).real
    ((s : Set α).pi fun _ => {true}) = _
  rw [Measure.real, Measure.pi_pi_finset, ENNReal.toReal_prod]
  have hval : (bernoulliMeasure true false p).real {true} = p.val := by
    apply bernoulliMeasure_real_apply_of_mem_of_notMem
    · simp
    · simp
    · simp
  simp only [← measureReal_def, hval, Finset.prod_const, Finset.card_eq_sum_ones]

lemma integral_selection_indicator (p : Set.Icc (0 : ℝ) 1) (s : Finset α) :
    (∫ ω, (if ω ∈ allSelected s then (1 : ℝ) else 0) ∂selectionMeasure p) =
      p.val ^ s.card := by
  have hm : MeasurableSet (allSelected s) := (Set.toFinite _).countable.measurableSet
  change (∫ ω, (allSelected s).indicator (fun _ => (1 : ℝ)) ω ∂selectionMeasure p) = _
  calc
    _ = (selectionMeasure p).real (allSelected s) := by
      simpa only [Pi.one_def] using integral_indicator_one (μ := selectionMeasure p) hm
    _ = _ := probability_allSelected p s

/-- Finite probabilistic alteration: delete all vertices in every fully chosen
forbidden set. Duplicate forbidden sets are permitted, and only strengthen the
upper bound on expected deletions. -/
theorem exists_avoiding_card [Fintype ι] (C : ι → Finset α)
    (hne : ∀ i, (C i).Nonempty) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset α, (∀ i, ¬ C i ⊆ O) ∧
      (Fintype.card α : ℝ) * p.val - ∑ i, (C i).card * p.val ^ (C i).card ≤ O.card := by
  let X (ω : α → Bool) : Finset α := Finset.univ.filter fun x => ω x = true
  let marks (ω : α → Bool) : Finset α :=
    Finset.univ.biUnion fun i => if C i ⊆ X ω then C i else ∅
  let cost (ω : α → Bool) : ℕ := ∑ i, if C i ⊆ X ω then (C i).card else 0
  let gain (ω : α → Bool) : ℝ := (X ω).card - cost ω
  have hmem (s : Finset α) (ω : α → Bool) : s ⊆ X ω ↔ ω ∈ allSelected s := by
    simp [X, Finset.subset_iff, allSelected]
  have hX (ω : α → Bool) : ((X ω).card : ℝ) =
      ∑ x : α, if ω ∈ allSelected {x} then (1 : ℝ) else 0 := by
    simp only [X, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro x _
    simp [allSelected]
  have hcost (ω : α → Bool) : (cost ω : ℝ) =
      ∑ i, (C i).card * if ω ∈ allSelected (C i) then (1 : ℝ) else 0 := by
    simp [cost, Nat.cast_sum, hmem]
  have hmean : (∫ ω, gain ω ∂selectionMeasure p) =
      (Fintype.card α : ℝ) * p.val - ∑ i, (C i).card * p.val ^ (C i).card := by
    simp_rw [gain, hX, hcost]
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    simp_rw [integral_const_mul, integral_selection_indicator]
    simp
  obtain ⟨ω, hω⟩ := exists_integral_le (μ := selectionMeasure p)
    (f := gain) Integrable.of_finite
  refine ⟨X ω \ marks ω, ?_, ?_⟩
  · intro i hi
    obtain ⟨x, hx⟩ := hne i
    have hxi := hi hx
    have hCX : C i ⊆ X ω := fun y hy => (Finset.mem_sdiff.mp (hi hy)).1
    have hmarked : x ∈ marks ω := by
      simp only [marks, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, by simpa [hCX] using hx⟩
    exact (Finset.mem_sdiff.mp hxi).2 hmarked
  · rw [hmean] at hω
    refine hω.trans ?_
    have hm : (marks ω).card ≤ cost ω := by
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp_all
    have hc := Finset.card_sdiff_add_card_inter (X ω) (marks ω)
    have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := X ω) (s₂ := marks ω))
    have hn : (X ω).card ≤ (X ω \ marks ω).card + cost ω := by omega
    have hr : ((X ω).card : ℝ) ≤ (X ω \ marks ω).card + cost ω := by exact_mod_cast hn
    dsimp [gain]
    linarith

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.Alteration -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.HoleEvents -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

lemma card_sup_le_mul {Q : Type u_1} {A : Type u_2} [Field Q] [AddCommGroup A] [Module Q A]
    [Fintype A] (U W : Submodule Q A) :
    Fintype.card ↥(U ⊔ W) ≤ Fintype.card U * Fintype.card W := by
  let f : U × W → ↥(U ⊔ W) := fun x => ⟨x.1.val + x.2.val,
    (U ⊔ W).add_mem ((show U ≤ U ⊔ W from le_sup_left) x.1.property) ((show W ≤ U ⊔ W from le_sup_right) x.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨u,hu⟩,⟨w,hw⟩),Subtype.ext he⟩
  simpa only [Fintype.card_prod] using Fintype.card_le_of_surjective f hf

lemma card_bounded_tuples {α : Type u_3} [Fintype α] [DecidableEq α] (n B : ℕ) (p : Fin n → α → Prop)
    (hp : ∀ i, Fintype.card {x // p i x} ≤ B) :
    Fintype.card {f : Fin n → α // Function.Injective f ∧ ∀ i, p i (f i)} ≤ B^n := by
  let f : {f : Fin n → α // Function.Injective f ∧ ∀ i, p i (f i)} →
      (i : Fin n) → {x // p i x} := fun x i => ⟨x.val i,x.property.2 i⟩
  have hf : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  apply (Fintype.card_le_of_injective f hf).trans
  rw [Fintype.card_pi]
  calc
    (∏ i : Fin n, Fintype.card {x // p i x}) ≤ ∏ _ : Fin n, B :=
      Finset.prod_le_prod (fun i _ => hp i)
    _ = B^n := by simp

namespace HoleEvents
variable {Q : Type u_4} {A : Type u_5} {R : Type u_6} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

def PairIndex := Σ r : R, Σ x : S, {y : S // y ≠ x ∧ y.val - x.val ∈ W r}
instance : Fintype (PairIndex S W) := by unfold PairIndex; infer_instance

def pairSet (i : PairIndex S W) : Finset S := {i.2.1,i.2.2.val}

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma pairSet_card (i : PairIndex S W) : (pairSet S W i).card = 2 := by
  simp [pairSet,Ne.symm i.2.2.property.1]

omit [Fintype Q] [Fintype R] in
lemma card_source_fiber (r : R) (x : A) :
    Fintype.card {y : S // y.val - x ∈ W r} ≤ Fintype.card (W r) := by
  let f : {y : S // y.val - x ∈ W r} → W r := fun y => ⟨y.val.val-x,y.property⟩
  apply Fintype.card_le_of_injective f
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun t : W r => (t : A) + x) h
  simpa only [f,sub_add_cancel] using he

omit [Fintype Q] in
lemma pairIndex_card (d : ℕ) (hW : ∀ r, Fintype.card (W r) ≤ d) :
    Fintype.card (PairIndex S W) ≤ Fintype.card R * S.card * d := by
  simp only [PairIndex,Fintype.card_sigma]
  calc
    (∑ r : R, ∑ x : S,
      Fintype.card {y : S // y ≠ x ∧ y.val - x.val ∈ W r})
      ≤ ∑ _r : R, ∑ _x : S, d := by
        apply Finset.sum_le_sum; intro r _
        apply Finset.sum_le_sum; intro x _
        exact (Fintype.card_subtype_mono _ _ (fun _ h => h.2)).trans
          ((card_source_fiber S W r x.val).trans (hW r))
    _ = Fintype.card R * S.card * d := by simp [mul_assoc]

def OccupancyIndex (k : ℕ) := Σ j : R × Q, Σ r : R, Σ x : A,
  {f : Fin k → S // Function.Injective f ∧ ∀ i, (f i).val-x ∈ U j ⊔ W r}
instance (k : ℕ) : Fintype (OccupancyIndex S W U k) := by
  unfold OccupancyIndex; infer_instance

def occupancySet {k : ℕ} (i : OccupancyIndex S W U k) : Finset S :=
  Finset.univ.image i.2.2.2.val

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma occupancySet_card {k : ℕ} (i : OccupancyIndex S W U k) :
    (occupancySet S W U i).card = k := by
  rw [occupancySet,Finset.card_image_of_injective _ i.2.2.2.property.1]
  simp

lemma occupancyIndex_card (k d : ℕ) (hU : ∀ j r, Fintype.card ↥(U j ⊔ W r) ≤ d) :
    Fintype.card (OccupancyIndex S W U k) ≤
      (Fintype.card R * Fintype.card Q) * Fintype.card R * Fintype.card A * d^k := by
  simp only [OccupancyIndex,Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : R × Q, ∑ _r : R, ∑ _x : A, d^k := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro r _
      apply Finset.sum_le_sum; intro x _
      apply card_bounded_tuples k d (fun _ (y : S) => y.val - x ∈ U j ⊔ W r)
      intro i
      exact (card_source_fiber S (fun _ : Unit => U j ⊔ W r) () x).trans (hU j r)
    _ = _ := by simp [mul_assoc]

/-- Four cyclic corners, with side labels r,r',r,r'. -/
def corner (e : R → Q → A) (r r' : R) (x : A) (u v : Q) : Fin 4 → A :=
  ![x,x+e r u,x+e r u+e r' v,x+e r' v]

def sideLabel (r r' : R) : Fin 4 → R := ![r,r',r,r']

def RectangleIndex (e : R → Q → A) := Σ r : R, Σ r' : R, Σ x : A, Σ u : Q, Σ v : Q,
  {f : Fin 4 → S // Function.Injective f ∧ ∀ i,
      (f i).val - corner e r r' x u v i ∈ W (sideLabel r r' i)}
instance (e : R → Q → A) : Fintype (RectangleIndex S W e) := by
  unfold RectangleIndex; infer_instance

def rectangleSet {e : R → Q → A} (i : RectangleIndex S W e) : Finset S :=
  Finset.univ.image i.2.2.2.2.2.val

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma rectangleSet_card {e : R → Q → A} (i : RectangleIndex S W e) :
    (rectangleSet S W i).card = 4 := by
  rw [rectangleSet,Finset.card_image_of_injective _ i.2.2.2.2.2.property.1]
  simp

lemma rectangleIndex_card (e : R → Q → A) (d : ℕ) (hW : ∀ r, Fintype.card (W r) ≤ d) :
    Fintype.card (RectangleIndex S W e) ≤
      (Fintype.card R)^2 * Fintype.card A * (Fintype.card Q)^2 * d^4 := by
  simp only [RectangleIndex,Fintype.card_sigma]
  calc
    _ ≤ ∑ _r : R, ∑ _r' : R, ∑ _x : A, ∑ _u : Q, ∑ _v : Q, d^4 := by
      apply Finset.sum_le_sum; intro r _
      apply Finset.sum_le_sum; intro r' _
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      apply card_bounded_tuples 4 d (fun i (y : S) => y.val - corner e r r' x u v i ∈ W (sideLabel r r' i))
      intro i
      exact (card_source_fiber S W (sideLabel r r' i) (corner e r r' x u v i)).trans
        (hW (sideLabel r r' i))
    _ = _ := by simp; ring

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.HoleEvents -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.HoleSelection -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

lemma exists_avoiding_three {α : Type u_1} {I : Type u_2} {J : Type u_3} {H : Type u_4} [Fintype α] [Fintype I] [Fintype J] [Fintype H]
    (C : I → Finset α) (B : J → Finset α) (T : H → Finset α)
    (hC : ∀ i, (C i).card = 2) (hB : ∀ j, (B j).card = 4)
    {k : ℕ} (hk : 0 < k) (hT : ∀ h, (T h).card = k) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset α, (∀ i, ¬ C i ⊆ O) ∧ (∀ j, ¬ B j ⊆ O) ∧ (∀ h, ¬ T h ⊆ O) ∧
      (Fintype.card α : ℝ) * p.val -
        (Fintype.card I * 2 * p.val^2 + Fintype.card J * 4 * p.val^4 +
            Fintype.card H * k * p.val^k) ≤ O.card := by
  let D : I ⊕ J ⊕ H → Finset α := Sum.elim C (Sum.elim B T)
  have hD : ∀ i, (D i).Nonempty := by
    intro i
    rw [← Finset.card_pos]
    cases i with
    | inl i => change 0 < (C i).card; rw [hC]; decide
    | inr i => cases i with
      | inl j => change 0 < (B j).card; rw [hB]; decide
      | inr h => change 0 < (T h).card; rw [hT]; exact hk
  obtain ⟨O,hO,hs⟩ := exists_avoiding_card D hD p
  refine ⟨O,(fun i => hO (.inl i)),(fun j => hO (.inr (.inl j))),
    (fun h => hO (.inr (.inr h))),?_⟩
  have hh : (∑ i, ((D i).card : ℝ) * p.val ^ (D i).card) =
      Fintype.card I * 2 * p.val^2 + Fintype.card J * 4 * p.val^4 +
            Fintype.card H * k * p.val^k := by
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp only [D,Sum.elim_inl,Sum.elim_inr,hC,hB,hT]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    push_cast
    ring
  rw [hh] at hs
  exact hs

namespace HoleEvents
variable {Q : Type u_5} {A : Type u_6} {R : Type u_7} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

structure GoodHoles (e : R → Q → A) (O : Finset A) : Prop where
  source : O ⊆ S
  collision : ∀ r, ∀ x ∈ O, ∀ y ∈ O, y-x ∈ W r → y=x
  occupancy : ∀ j r x, (O.filter (fun o => o-x ∈ U j ⊔ W r)).card ≤ 100
  rectangles : ∀ r r' x u v (f : Fin 4 → A), Function.Injective f →
    (∀ i, f i ∈ O) → (∀ i, f i - corner e r r' x u v i ∈ W (sideLabel r r' i)) → False

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma goodHoles_of_avoiding (e : R → Q → A) (O : Finset S)
    (hp : ∀ i : PairIndex S W, ¬ pairSet S W i ⊆ O)
    (ho : ∀ i : OccupancyIndex S W U 101, ¬ occupancySet S W U i ⊆ O)
    (hr : ∀ i : RectangleIndex S W e, ¬ rectangleSet S W i ⊆ O) :
    GoodHoles S W U e (O.image Subtype.val) := by
  have hmem (x : S) : x.val ∈ O.image Subtype.val ↔ x ∈ O := by
    constructor
    · rintro hx
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
      exact Subtype.val_injective he ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro r x hx y hy hdiff
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    by_contra hne
    let i : PairIndex S W := ⟨r,x',y',(fun h => hne (congrArg Subtype.val h)),hdiff⟩
    apply hp i
    intro z hz
    change z ∈ ({x', y'} : Finset S) at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx'
    · rcases Finset.mem_singleton.mp hz with rfl
      exact hy'
  · intro j r x
    let C := (O.image Subtype.val).filter (fun o => o-x ∈ U j ⊔ W r)
    by_contra hn
    have hcard : Fintype.card (Fin 101) ≤ Fintype.card C := by
      simp only [Fintype.card_fin,Fintype.card_coe]
      change ¬ C.card ≤ 100 at hn
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    let g : Fin 101 → S := fun i => ⟨(f i).val,by
      obtain ⟨o,_,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (f i).property).1
      exact he ▸ o.property⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply f.injective
      apply Subtype.ext
      exact congrArg (fun z : S => z.val) hij
    let a : OccupancyIndex S W U 101 := ⟨j,r,x,g,hg,fun i =>
      (Finset.mem_filter.mp (f i).property).2⟩
    apply ho a
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    apply (hmem _).mp
    exact (Finset.mem_filter.mp (f i).property).1
  · intro r r' x u v f hf hfo hfw
    let g : Fin 4 → S := fun i => ⟨f i,by
      obtain ⟨o,_,he⟩ := Finset.mem_image.mp (hfo i)
      exact he ▸ o.property⟩
    have hg : Function.Injective g := fun i j h => hf (congrArg Subtype.val h)
    let a : RectangleIndex S W e := ⟨r,r',x,u,v,g,hg,hfw⟩
    apply hr a
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact (hmem _).mp (hfo i)

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma GoodHoles.mono {e : R → Q → A} {O P : Finset A}
    (hO : GoodHoles S W U e O) (hP : P ⊆ O) : GoodHoles S W U e P := by
  refine ⟨hP.trans hO.source,?_,?_,?_⟩
  · exact fun r x hx y hy h => hO.collision r x (hP hx) y (hP hy) h
  · intro j r x
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hP)).trans (hO.occupancy j r x)
  · exact fun r r' x u v f hf hfo hfw => hO.rectangles r r' x u v f hf (fun i => hP (hfo i)) hfw

lemma exists_goodHoles (e : R → Q → A) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset A, GoodHoles S W U e O ∧
      (S.card : ℝ) * p.val -
        (Fintype.card (PairIndex S W) * 2 * p.val^2 +
         Fintype.card (RectangleIndex S W e) * 4 * p.val^4 +
         Fintype.card (OccupancyIndex S W U 101) * 101 * p.val^101) ≤ O.card := by
  obtain ⟨O,hp,hr,ho,hsize⟩ := exists_avoiding_three
    (pairSet S W) (rectangleSet (e := e) S W) (occupancySet (k := 101) S W U)
    (pairSet_card S W) (rectangleSet_card S W) (by decide : 0 < 101)
    (occupancySet_card S W U) p
  refine ⟨O.image Subtype.val,goodHoles_of_avoiding S W U e O hp ho hr,?_⟩
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [Fintype.card_coe, Nat.cast_ofNat] using hsize

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.HoleSelection -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.HoleNumerics -/
section

namespace OAI

noncomputable section
namespace KaplanskyCounterexample.FiniteGeometry

lemma hole_numeric_powers {q D : ℝ} (hq : 12 ≤ q) (hD : q^100 ≤ D) :
    0 < D ∧ q^73 ≤ D^2 ∧ 8*q^75 ≤ D ∧ 4*q^302 ≤ D^4 ∧ 101*q^19695 ≤ D^198 := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hd0 : 0 < D := (pow_pos hq0 _).trans_le hD
  have hp (i j : ℕ) (h : i ≤ j) : q^i ≤ q^j := pow_le_pow_right₀ hq1 h
  refine ⟨hd0,?_,?_,?_,?_⟩
  · calc
      q^73 ≤ q^200 := hp _ _ (by decide)
      _ = (q^100)^2 := by rw [← pow_mul]
      _ ≤ D^2 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _
  · calc
      8*q^75 ≤ q*q^75 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le _)
      _ = q^76 := by ring
      _ ≤ q^100 := hp _ _ (by decide)
      _ ≤ D := hD
  · calc
      4*q^302 ≤ q*q^302 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hq0.le _)
      _ = q^303 := by ring
      _ ≤ q^400 := hp _ _ (by decide)
      _ = (q^100)^4 := by rw [← pow_mul]
      _ ≤ D^4 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _
  · calc
      101*q^19695 ≤ q^2*q^19695 := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hq0.le _)
      _ = q^19697 := by rw [← pow_add]
      _ ≤ q^19800 := hp _ _ (by decide)
      _ = (q^100)^198 := by rw [← pow_mul]
      _ ≤ D^198 := pow_le_pow_left₀ (le_of_lt (pow_pos hq0 _)) hD _

lemma hole_probability_mem {q D : ℝ} (hq : 12 ≤ q) (hD : q^100 ≤ D) :
    q^73/D^2 ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨hd,hpow,_,_,_⟩ := hole_numeric_powers hq hD
  constructor
  · positivity
  · exact (div_le_one (sq_pos_of_pos hd)).mpr hpow

/-- Explicit finite alteration arithmetic. The three costs refer to the actual
pair, four-witness rectangle, and 101-point occupancy event families. -/
lemma hole_alteration_numeric {q D N S C B H : ℝ}
    (hq : 12 ≤ q) (hD : q^100 ≤ D) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hdensity : N ≤ q^72*S)
    (hC : C ≤ D*S*q^2) (hB : B ≤ D^2*N*q^10)
    (hH : H ≤ D^2*N*(q^122)^101) :
    3*N/D^2 ≤ S*(q^73/D^2) -
      (C*2*(q^73/D^2)^2 + B*4*(q^73/D^2)^4 + H*101*(q^73/D^2)^101) := by
  obtain ⟨hd,hpow,hsmall,hrect,hocc⟩ := hole_numeric_powers hq hD
  have hq0 : 0 < q := by linarith
  have hdne : D ≠ 0 := ne_of_gt hd
  let p := q^73/D^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hmass : 0 ≤ N/D^2 := div_nonneg hN (sq_nonneg D)
  have hpair : C*2*p^2 ≤ S*p/4 := by
    calc
      C*2*p^2 ≤ (D*S*q^2)*2*p^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by norm_num)) (sq_nonneg p)
      _ = (S*p)*(2*q^75/D) := by dsimp [p]; field_simp
      _ ≤ (S*p)*(1/4) := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hd).mpr (by nlinarith [hsmall])) (mul_nonneg hS hp)
      _ = S*p/4 := by ring
  have hb : B*4*p^4 ≤ N/D^2 := by
    calc
      B*4*p^4 ≤ (D^2*N*q^10)*4*p^4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (by norm_num)) (pow_nonneg hp _)
      _ = (N/D^2)*(4*q^302/D^4) := by dsimp [p]; field_simp
      _ ≤ (N/D^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hd _)).mpr hrect) hmass
      _ = N/D^2 := mul_one _
  have hh : H*101*p^101 ≤ N/D^2 := by
    calc
      H*101*p^101 ≤ (D^2*N*(q^122)^101)*101*p^101 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hH (by norm_num)) (pow_nonneg hp _)
      _ = (N/D^2)*(101*q^19695/D^198) := by dsimp [p]; field_simp
      _ ≤ (N/D^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hd _)).mpr hocc) hmass
      _ = N/D^2 := mul_one _
  have hE : 12*(N/D^2) ≤ S*p := by
    calc
      12*(N/D^2) ≤ q*(N/D^2) := mul_le_mul_of_nonneg_right hq hmass
      _ = N*(q/D^2) := by ring
      _ ≤ (q^72*S)*(q/D^2) := mul_le_mul_of_nonneg_right hdensity (by positivity)
      _ = S*p := by dsimp [p]; ring
  change 3*N/D^2 ≤ S*p - (C*2*p^2+B*4*p^4+H*101*p^101)
  have heq : 3*N/D^2=3*(N/D^2) := by ring
  rw [heq]
  linarith [hpair,hb,hh,hE]

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.HoleNumerics -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.HoleExistence -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry

lemma trimmed_card_interval {A : Type u_1} [DecidableEq A] (O : Finset A) {N D : ℕ}
    (hD : 0 < D) (hDN : D^2 ≤ N) (hO : 3*(N:ℝ)/(D:ℝ)^2 ≤ O.card) :
    ∃ P ⊆ O, 2*N ≤ P.card*D^2 ∧ P.card*D^2 ≤ 3*N := by
  let m := 2*N/D^2+1
  have hds : 0 < D^2 := pow_pos hD _
  have hm : 2*N ≤ m*D^2 := by
    have hmod := Nat.mod_lt (2*N) hds
    have he := Nat.mod_add_div (2*N) (D^2)
    dsimp [m]
    nlinarith
  have hm' : m*D^2 ≤ 3*N := by
    have hh := Nat.div_mul_le_self (2*N) (D^2)
    dsimp [m]
    nlinarith
  have hmO : m ≤ O.card := by
    have hcast : (3*N:ℕ) ≤ O.card*D^2 := by
      have hdreal : 0 < (D:ℝ)^2 := by positivity
      have hh := (div_le_iff₀ hdreal).mp hO
      exact_mod_cast hh
    nlinarith
  obtain ⟨P,hP,hcard⟩ := Finset.exists_subset_card_eq hmO
  exact ⟨P,hP,by simpa [hcard] using hm,by simpa [hcard] using hm'⟩

namespace DirectionFrame
variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

lemma exists_sized_goodHoles (F : DirectionFrame Q A R E) (S : Finset A)
    {q D : ℕ} (hqcard : Fintype.card Q=q) (hE : Fintype.card E=q^119)
    (hq : 12 ≤ q) (hD : q^100 ≤ D) (hR : Fintype.card R*q ≤ D)
    (hdensity : Fintype.card A ≤ q^72*S.card) (hDN : D^2 ≤ Fintype.card A) :
    ∃ O : Finset A, HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O ∧
      2*Fintype.card A ≤ O.card*D^2 ∧ O.card*D^2 ≤ 3*Fintype.card A := by
  have hqpos : 0 < q := by omega
  have hdpos : 0 < D := (pow_pos hqpos _).trans_le hD
  have hr : Fintype.card R ≤ D := by
    exact (Nat.le_mul_of_pos_right _ hqpos).trans hR
  have hw (r : R) : Fintype.card (F.W r) ≤ q^2 := by rw [F.card_W,hqcard]
  have hu (j : R × Q) (r : R) : Fintype.card ↥(F.U j ⊔ F.W r) ≤ q^122 := by
    calc
      _ ≤ Fintype.card (F.U j)*Fintype.card (F.W r) := card_sup_le_mul _ _
      _ = (q*q^119)*q^2 := by rw [F.card_U,F.card_W,hqcard,hE]
      _ = q^122 := by ring
  have hC : (Fintype.card (HoleEvents.PairIndex S F.W) : ℝ) ≤ D*(S.card:ℝ)*(q:ℝ)^2 := by
    exact_mod_cast (HoleEvents.pairIndex_card S F.W (q^2) hw).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr))
  have hB : (Fintype.card (HoleEvents.RectangleIndex S F.W (fun r t => F.exc r t)) : ℝ)
      ≤ (D:ℝ)^2*Fintype.card A*(q:ℝ)^10 := by
    have hh := (HoleEvents.rectangleIndex_card S F.W (fun r t => F.exc r t) (q^2) hw).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hr 2))))
    have he : D^2*Fintype.card A*q^2*(q^2)^4 = D^2*Fintype.card A*q^10 := by ring
    rw [hqcard,he] at hh
    exact_mod_cast hh
  have hH : (Fintype.card (HoleEvents.OccupancyIndex S F.W F.U 101) : ℝ)
      ≤ (D:ℝ)^2*Fintype.card A*((q:ℝ)^122)^101 := by
    have hh := HoleEvents.occupancyIndex_card S F.W F.U 101 (q^122) hu
    rw [hqcard] at hh
    have hh' : Fintype.card (HoleEvents.OccupancyIndex S F.W F.U 101)
        ≤ D^2*Fintype.card A*(q^122)^101 := hh.trans (by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by simpa [pow_two] using Nat.mul_le_mul hR hr)))
    exact_mod_cast hh'
  let p : Set.Icc (0:ℝ) 1 := ⟨(q:ℝ)^73/(D:ℝ)^2,hole_probability_mem (by exact_mod_cast hq) (by exact_mod_cast hD)⟩
  obtain ⟨O,hO,hsize⟩ := HoleEvents.exists_goodHoles S F.W F.U (fun r t => F.exc r t) p
  have hnumeric := hole_alteration_numeric (by exact_mod_cast hq : (12:ℝ) ≤ q)
    (by exact_mod_cast hD : (q:ℝ)^100 ≤ D)
    (by positivity : (0:ℝ) ≤ Fintype.card A) (by positivity : (0:ℝ) ≤ S.card)
    (by exact_mod_cast hdensity : (Fintype.card A:ℝ) ≤ (q:ℝ)^72*S.card) hC hB hH
  obtain ⟨P,hP,hlo,hhi⟩ := trimmed_card_interval O hdpos hDN (hnumeric.trans hsize)
  exact ⟨P,hO.mono S F.W F.U hP,hlo,hhi⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.HoleExistence -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CyclicLabels -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

/-- In a cyclic sequence of at most five positions with unequal neighboring
labels, no label can occur thrice. This includes the wrap-around adjacency. -/
lemma cyclic_label_count_le_two {k : ℕ} {L : Type u_1} [DecidableEq L] (lab : Fin k → L)
    (hk : k ≤ 5) (hadj : ∀ i, lab i ≠ lab (finRotate k i)) (l : L) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card ≤ 2 := by
  let s := (Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)
  have hd : Disjoint s (s.image (finRotate k)) := by
    rw [Finset.disjoint_left]
    intro i hi hir
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hir
    exact hadj j ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hi).2.symm)
  have hc : s.card + (s.image (finRotate k)).card ≤ k := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin k)
  rw [Finset.card_image_of_injective _ (finRotate k).injective] at hc
  dsimp [s] at hc
  omega

/-- A nonzero vector cannot be the sole contribution to a zero sum. -/
lemma count_ne_one_of_sum_eq_zero {I : Type u_2} {L : Type u_3} {M : Type u_4} [Fintype I] [DecidableEq L]
    [AddCommGroup M] (lab : I → L) (v : I → M) (l : L)
    (hn : ∀ i, lab i = l → v i ≠ 0)
    (hz : ∑ i ∈ (Finset.univ : Finset I).filter (fun i => lab i = l), v i = 0) :
    ((Finset.univ : Finset I).filter (fun i => lab i = l)).card ≠ 1 := by
  intro hc
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc
  have hi' : i ∈ (Finset.univ : Finset I).filter (fun i => lab i = l) := by rw [hi]; simp
  have hil : lab i = l := (Finset.mem_filter.mp hi').2
  rw [hi,Finset.sum_singleton] at hz
  exact hn i hil hz

lemma cyclic_label_count_eq_two {k : ℕ} {L : Type u_5} {M : Type u_6} [DecidableEq L] [AddCommGroup M]
    (lab : Fin k → L) (v : Fin k → M) (hk : k ≤ 5)
    (hadj : ∀ i, lab i ≠ lab (finRotate k i)) (l : L)
    (hne : ∃ i, lab i = l) (hn : ∀ i, lab i = l → v i ≠ 0)
    (hz : ∑ i ∈ (Finset.univ : Finset (Fin k)).filter (fun i => lab i = l), v i = 0) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card = 2 := by
  have hle := cyclic_label_count_le_two lab hk hadj l
  have hne1 := count_ne_one_of_sum_eq_zero lab v l hn hz
  have hp : 0 < ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card := by
    rw [Finset.card_pos]
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,by simp [hi]⟩
  omega

/-- Occurrence-count form of the pigeonhole bound, retaining the exact support. -/
lemma sum_label_counts {I : Type u_7} {L : Type u_8} [Fintype I] [DecidableEq L] (lab : I → L) :
    ∑ l ∈ Finset.univ.image lab,
      ((Finset.univ : Finset I).filter (fun i => lab i = l)).card = Fintype.card I := by
  symm
  simpa using Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset I))
    (t := Finset.univ.image lab) (f := lab) (fun i hi => Finset.mem_image_of_mem lab hi)

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CyclicLabels -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateRelations -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure GenericStep (Q : Type u_5) (R : Type u_6) (E : Type u_7) [Zero E] where
  label : R × Q
  scalar : Q
  component : E
  nonzero : component ≠ 0

structure ExceptionalStep (Q : Type u_8) (R : Type u_9) [Zero Q] where
  label : R
  scalar : Q
  nonzero : scalar ≠ 0

abbrev PolygonStep (Q : Type u_10) (R : Type u_11) (E : Type u_12) [Zero Q] [Zero E] := GenericStep Q R E ⊕ ExceptionalStep Q R

namespace PolygonStep

def label : PolygonStep Q R E → (R × Q) ⊕ R
  | .inl g => .inl g.label
  | .inr e => .inr e.label

def bundle : PolygonStep Q R E → R
  | .inl g => g.label.1
  | .inr e => e.label

def wcoord : PolygonStep Q R E → Q × Q
  | .inl g => (g.scalar,g.scalar*g.label.2)
  | .inr e => (0,e.scalar)

def ecoord : PolygonStep Q R E → E
  | .inl g => g.component
  | .inr _ => 0

def vector (F : DirectionFrame Q A R E) : PolygonStep Q R E → A
  | .inl g => F.u g.label (g.scalar,g.component)
  | .inr e => F.exc e.label e.scalar

omit [Module Q E] in
lemma ecoord_nonzero {s : PolygonStep Q R E} {j : R × Q} (hs : s.label = .inl j) :
    s.ecoord ≠ 0 := by
  cases s with
  | inl g => exact g.nonzero
  | inr e => cases hs

lemma vector_ne_zero (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    s.vector F ≠ 0 := by
  cases s with
  | inl g =>
    intro h
    have hz : (g.scalar,g.component) = 0 := F.u_injective g.label (h.trans (F.u _).map_zero.symm)
    exact g.nonzero (congrArg Prod.snd hz)
  | inr e =>
    intro h
    exact e.nonzero (F.exc_injective e.label (h.trans (F.exc _).map_zero.symm))

def blockLabel (s : PolygonStep Q R E) (b : Fin 2) : R ⊕ (R × Q) :=
  if b = 0 then .inl s.bundle else
    match s with
    | .inl g => .inr g.label
    | .inr e => .inl e.label

def blockVector (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (b : Fin 2) : A :=
  if b = 0 then F.w s.bundle s.wcoord else
    match s with
    | .inl g => F.e g.label g.component
    | .inr _ => 0

lemma blockVector_mem (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (b : Fin 2) :
    s.blockVector F b ∈ Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range)
      (s.blockLabel b) := by
  fin_cases b
  · cases s with
    | inl g => exact ⟨(g.scalar,g.scalar*g.label.2),rfl⟩
    | inr e => exact ⟨(0,e.scalar),rfl⟩
  · cases s with
    | inl g => exact ⟨g.component,rfl⟩
    | inr e => exact ⟨0,(F.w e.label).map_zero⟩

lemma sum_blocks (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    ∑ b : Fin 2, s.blockVector F b = s.vector F := by
  cases s <;> simp [blockVector,vector,bundle,wcoord,DirectionFrame.u_apply,
    Fin.sum_univ_succ]

lemma filter_blocks_E (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (j : R × Q) :
    ∑ b : Fin 2, (if s.blockLabel b = .inr j then s.blockVector F b else 0) =
      if s.label = .inl j then F.e j s.ecoord else 0 := by
  rw [Fin.sum_univ_two]
  cases s with
  | inl g =>
    dsimp [blockLabel,blockVector,label,bundle,wcoord,ecoord]
    by_cases h : g.label = j <;> simp_all
  | inr e => simp [blockLabel,label,bundle]

lemma filter_blocks_W (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (r : R) :
    ∑ b : Fin 2, (if s.blockLabel b = .inl r then s.blockVector F b else 0) =
      if s.bundle = r then F.w r s.wcoord else 0 := by
  rw [Fin.sum_univ_two]
  cases s with
  | inl g =>
    dsimp [blockLabel,blockVector,bundle,wcoord]
    by_cases h : g.label.1 = r <;> simp_all
  | inr e =>
    dsimp [blockLabel,blockVector,bundle,wcoord]
    by_cases h : e.label = r <;> simp_all

end PolygonStep

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma polygon_component_sums {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0) :
    (∀ j : R × Q, ∑ i ∈ Finset.univ.filter (fun i => (s i).label = .inl j), (s i).ecoord = 0) ∧
    (∀ r : R, ∑ i ∈ Finset.univ.filter (fun i => (s i).bundle = r), (s i).wcoord = 0) := by
  let lab (p : Fin k × Fin 2) := (s p.1).blockLabel p.2
  let v (p : Fin k × Fin 2) := (s p.1).blockVector F p.2
  have hcard : (Finset.univ : Finset (Fin k × Fin 2)).card ≤ 10 := by simp; omega
  have hvz : ∑ p : Fin k × Fin 2, v p = 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [v,PolygonStep.sum_blocks]
    exact hz
  have hsep := F.direct.grouped_sum Finset.univ hcard lab v
    (fun p _ => PolygonStep.blockVector_mem F _ _) hvz
  constructor
  · intro j
    have hh := hsep (.inr j)
    rw [Finset.sum_filter,Fintype.sum_prod_type] at hh
    simp_rw [lab,v,PolygonStep.filter_blocks_E] at hh
    apply F.einj j
    rw [map_zero,map_sum]
    simpa only [Finset.sum_filter] using hh
  · intro r
    have hh := hsep (.inl r)
    rw [Finset.sum_filter,Fintype.sum_prod_type] at hh
    simp_rw [lab,v,PolygonStep.filter_blocks_W] at hh
    apply F.winj r
    rw [map_zero,map_sum]
    simpa only [Finset.sum_filter] using hh

/-- Every occurring generic label occurs precisely twice in a candidate with
at most five steps. No exceptional-vector cancellation has been assumed. -/
lemma generic_occurs_twice {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (j : R × Q) (hj : ∃ i, (s i).label = .inl j) :
    (Finset.univ.filter (fun i => (s i).label = .inl j)).card = 2 := by
  exact cyclic_label_count_eq_two (fun i => (s i).label) (fun i => (s i).ecoord)
    hk hadj (.inl j) hj (fun _ hi => PolygonStep.ecoord_nonzero hi)
    ((F.polygon_component_sums s hk hz).1 j)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateRelations -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateClassification -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def transverse (α : Q) : (Q × Q) →ₗ[Q] Q where
  toFun x := x.2 - x.1 * α
  map_add' x y := by dsimp; ring
  map_smul' c x := by dsimp; ring

lemma exceptional_scalar_sum {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0) (r : R) (α : Q)
    (hslope : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label.1 = r → g.label.2 = α) :
    ∑ i ∈ Finset.univ.filter (fun i => (s i).label = .inr r),
      Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i) = 0 := by
  have h := congrArg (transverse α) ((F.polygon_component_sums s hk hz).2 r)
  rw [map_sum,map_zero,Finset.sum_filter] at h
  rw [Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hi : s i with
  | inl g =>
    simp only [PolygonStep.label,reduceCtorEq,ite_false,
      PolygonStep.bundle,PolygonStep.wcoord]
    by_cases hr : g.label.1 = r
    · simp [hr,transverse,hslope i g hi hr]
    · simp [hr]
  | inr e =>
    simp only [PolygonStep.label,Sum.inr.injEq,PolygonStep.bundle,PolygonStep.wcoord]
    by_cases hr : e.label = r <;> simp [hr,transverse]

lemma exceptional_occurs_twice_single_slope {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label) (r : R)
    (hr : ∃ i, (s i).label = .inr r) (α : Q)
    (hslope : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label.1 = r → g.label.2 = α) :
    (Finset.univ.filter (fun i => (s i).label = .inr r)).card = 2 := by
  apply cyclic_label_count_eq_two (fun i => (s i).label)
    (fun i => Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i))
    hk hadj (.inr r) hr
  · intro i hi
    cases h : s i with
    | inl g => simp [h,PolygonStep.label] at hi
    | inr e => exact e.nonzero
  · exact F.exceptional_scalar_sum s hk hz r α hslope

lemma all_labels_twice_length {k : ℕ} {L : Type u_5} [DecidableEq L] (lab : Fin k → L)
    (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hcount : ∀ l ∈ Finset.univ.image lab,
      (Finset.univ.filter (fun i => lab i = l)).card = 2) :
    k = 4 ∧ (Finset.univ.image lab).card = 2 := by
  have h := sum_label_counts lab
  have he : (∑ l ∈ Finset.univ.image lab,
      (Finset.univ.filter (fun i => lab i = l)).card) =
      (Finset.univ.image lab).card * 2 := by
    calc
      _ = ∑ _l ∈ Finset.univ.image lab, 2 := Finset.sum_congr rfl hcount
      _ = _ := by simp
  rw [he,Fintype.card_fin] at h
  omega

/-- With at most one generic label every occurring label occurs twice, so the
candidate is a four-step rectangle. -/
lemma one_generic_rectangle {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (j : R × Q) (honly : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label = j) :
    k = 4 ∧ (Finset.univ.image (fun i => (s i).label)).card = 2 := by
  apply all_labels_twice_length _ hk3 hk5
  intro l hl
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hl
  cases l with
  | inl j' => exact F.generic_occurs_twice s hk5 hz hadj j' ⟨i,hi⟩
  | inr r =>
    apply F.exceptional_occurs_twice_single_slope s hk5 hz hadj r ⟨i,hi⟩ j.2
    intro i g hg _
    exact congrArg Prod.snd (honly i g hg)

/-- A lone exceptional step requires two different generic slopes in its own
bundle. This is the cancellation needed for the pentagon count. -/
lemma singleton_exceptional_two_slopes {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0) (r : R)
    (hc : (Finset.univ.filter (fun i => (s i).label = .inr r)).card = 1) :
    ∃ (i i' : Fin k) (g g' : GenericStep Q R E), s i = .inl g ∧ s i' = .inl g' ∧
      g.label.1 = r ∧ g'.label.1 = r ∧ g.label.2 ≠ g'.label.2 := by
  by_contra hh
  push Not at hh
  have hslope : ∃ α : Q, ∀ i (g : GenericStep Q R E),
      s i = .inl g → g.label.1 = r → g.label.2 = α := by
    by_cases hex : ∃ (i : Fin k) (g : GenericStep Q R E), s i = .inl g ∧ g.label.1 = r
    · obtain ⟨i,g,hi,hr⟩ := hex
      refine ⟨g.label.2,?_⟩
      intro i' g' hi' hr'
      exact (hh i i' g g' hi hi' hr hr').symm
    · refine ⟨0,?_⟩
      intro i g hi hr
      exact False.elim (hex ⟨i,g,hi,hr⟩)
  obtain ⟨α,hα⟩ := hslope
  have hn := count_ne_one_of_sum_eq_zero (fun i => (s i).label)
    (fun i => Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i)) (.inr r)
    (by
      intro i hi
      cases h : s i with
      | inl g => simp [h,PolygonStep.label] at hi
      | inr e => exact e.nonzero)
    (F.exceptional_scalar_sum s hk hz r α hα)
  exact hn hc

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateClassification -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.LabelSupport -/
section

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {I : Type u_1} {J : Type u_2} {R : Type u_3} [Fintype I] [DecidableEq J] [DecidableEq R]

def genericLabels (lab : I → J ⊕ R) : Finset J := (Finset.univ.image lab).toLeft

def genericPositions (lab : I → J ⊕ R) : Finset I := Finset.univ.filter (fun i => (lab i).isLeft)

def exceptionalPositions (lab : I → J ⊕ R) : Finset I := Finset.univ.filter (fun i => (lab i).isRight)

@[simp] lemma mem_genericLabels (lab : I → J ⊕ R) (j : J) :
    j ∈ genericLabels lab ↔ ∃ i, lab i = .inl j := by simp [genericLabels]

lemma count_genericPositions (lab : I → J ⊕ R) :
    (genericPositions lab).card =
      ∑ j ∈ genericLabels lab, (Finset.univ.filter (fun i => lab i = .inl j)).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := genericPositions lab) (t := (genericLabels lab).image Sum.inl) (f := lab)
    (by
      intro i hi
      have hh : (lab i).isLeft := (Finset.mem_filter.mp hi).2
      cases he : lab i with
      | inl j => exact Finset.mem_image.mpr ⟨j,(mem_genericLabels lab j).mpr ⟨i,he⟩,rfl⟩
      | inr r => simp [he] at hh)
  rw [Finset.sum_image (by intro x _ y _ hxy; exact Sum.inl.inj hxy)] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,genericPositions]
  exact ⟨fun h => h.2,fun h => ⟨by simp [h],h⟩⟩

omit [DecidableEq J] [DecidableEq R] in
lemma card_generic_add_exceptional (lab : I → J ⊕ R) :
    (genericPositions lab).card + (exceptionalPositions lab).card = Fintype.card I := by
  have he : genericPositions lab ∪ exceptionalPositions lab = Finset.univ := by
    ext i
    cases h : lab i <;> simp [genericPositions,exceptionalPositions,h]
  have hd : Disjoint (genericPositions lab) (exceptionalPositions lab) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    cases h : lab i <;> simp_all [genericPositions,exceptionalPositions]
  rw [← Finset.card_union_of_disjoint hd,he,Finset.card_univ]

lemma genericPositions_card_eq_twice (lab : I → J ⊕ R)
    (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2) :
    (genericPositions lab).card = 2 * (genericLabels lab).card := by
  rw [count_genericPositions]
  calc
    _ = ∑ _j ∈ genericLabels lab, 2 := Finset.sum_congr rfl hc
    _ = _ := by simp [mul_comm]

lemma genericLabels_card_le_two {k : ℕ} (lab : Fin k → J ⊕ R)
    (hk : k ≤ 5) (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2) :
    (genericLabels lab).card ≤ 2 := by
  have h := card_generic_add_exceptional lab
  rw [genericPositions_card_eq_twice lab hc,Fintype.card_fin] at h
  omega

lemma exceptional_count_singleton_of_two_generic {k : ℕ} (lab : Fin k → J ⊕ R)
    (hk : k ≤ 5) (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2)
    (hg : (genericLabels lab).card = 2) (r : R) (hr : ∃ i, lab i = .inr r) :
    k = 5 ∧ (Finset.univ.filter (fun i => lab i = .inr r)).card = 1 := by
  have h := card_generic_add_exceptional lab
  rw [genericPositions_card_eq_twice lab hc,hg,Fintype.card_fin] at h
  have hs : Finset.univ.filter (fun i => lab i = .inr r) ⊆ exceptionalPositions lab := by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    simp [exceptionalPositions,hi]
  have hb := Finset.card_le_card hs
  have hp : 0 < (Finset.univ.filter (fun i => lab i = .inr r)).card := by
    rw [Finset.card_pos]
    obtain ⟨i,hi⟩ := hr
    exact ⟨i,by simp [hi]⟩
  omega

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.LabelSupport -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateGeometry -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

lemma cyclic_two_apart (k : ℕ) (hk3 : 3 ≤ k) (hk5 : k ≤ 5) :
    ∀ i j : Fin k, i ≠ j → finRotate k i ≠ j → finRotate k j ≠ i →
      finRotate k (finRotate k i) = j ∨ finRotate k (finRotate k j) = i := by
  interval_cases k <;> decide

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma vector_mem_U {s : PolygonStep Q R E} {j : R × Q} (hs : s.label = .inl j) :
    s.vector F ∈ F.U j := by
  cases s with
  | inl g => cases Sum.inl.inj hs; exact ⟨(g.scalar,g.component),rfl⟩
  | inr e => cases hs

lemma vector_not_mem_U {s : PolygonStep Q R E} {j : R × Q} (hs : s.label ≠ .inl j) :
    s.vector F ∉ F.U j := by
  intro hm
  cases s with
  | inl g =>
    have hgj : g.label ≠ j := fun he => hs (congrArg Sum.inl he)
    have hz := (Submodule.disjoint_def.mp (F.U_disjoint hgj))
      ((PolygonStep.vector F (.inl g))) ⟨(g.scalar,g.component),rfl⟩ hm
    exact PolygonStep.vector_ne_zero F (.inl g) hz
  | inr e =>
    have hz := (Submodule.disjoint_def.mp (F.U_exceptional_disjoint j e.label))
      ((PolygonStep.vector F (.inr e))) hm ⟨e.scalar,rfl⟩
    exact PolygonStep.vector_ne_zero F (.inr e) hz

lemma two_generic_bundle {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (hg : (genericLabels (fun i => (s i).label)).card = 2)
    (r : R) (hr : ∃ i, (s i).label = .inr r) :
    k = 5 ∧ ∀ j ∈ genericLabels (fun i => (s i).label), j.1 = r := by
  have hc : ∀ j ∈ genericLabels (fun i => (s i).label),
      (Finset.univ.filter (fun i => (s i).label = .inl j)).card = 2 := by
    intro j hj
    exact F.generic_occurs_twice s hk hz hadj j ((mem_genericLabels _ _).mp hj)
  obtain ⟨hk5,hcr⟩ := exceptional_count_singleton_of_two_generic _ hk hc hg r hr
  obtain ⟨i,i',g,g',hi,hi',hr',hr'',hne⟩ :=
    F.singleton_exceptional_two_slopes s hk hz r hcr
  have hne' : g.label ≠ g'.label := fun h => hne (congrArg Prod.snd h)
  have hsub : {g.label,g'.label} ⊆ genericLabels (fun i => (s i).label) := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact (mem_genericLabels _ _).mpr ⟨i,by simp [hi,PolygonStep.label]⟩
    · exact (mem_genericLabels _ _).mpr ⟨i',by simp [hi',PolygonStep.label]⟩
  have he : genericLabels (fun i => (s i).label) = {g.label,g'.label} := by
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hg,hne'])).symm
  refine ⟨hk5,?_⟩
  intro j hj
  rw [he] at hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact hr'
  · exact hr''

lemma distinct_generic_cosets [Fintype A] {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (pt : Fin k → A) (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hpt : ∀ i, pt (finRotate k i) - pt i = (s i).vector F)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    {i i' : Fin k} (hii : i ≠ i') {j : R × Q}
    (hi : (s i).label = .inl j) (hi' : (s i').label = .inl j) :
    AffineCoset.of (F.U j) (pt i) ≠ AffineCoset.of (F.U j) (pt i') := by
  have hr : finRotate k i ≠ i' := fun h => hadj i (hi.trans (h ▸ hi').symm)
  have hr' : finRotate k i' ≠ i := fun h => hadj i' (hi'.trans (h ▸ hi).symm)
  have hh (a b : Fin k) (ha : (s a).label = .inl j)
      (hab : finRotate k (finRotate k a) = b)
      (hc : AffineCoset.of (F.U j) (pt a) = AffineCoset.of (F.U j) (pt b)) : False := by
    have hd : pt b - pt a ∈ F.U j := (AffineCoset.of_eq_iff _ _ _).mp hc.symm
    have hm : (s (finRotate k a)).vector F ∈ F.U j := by
      have hsub := (F.U j).sub_mem hd (F.vector_mem_U ha)
      rw [← hpt a] at hsub
      rw [← hpt (finRotate k a),hab]
      convert hsub using 1; abel
    exact F.vector_not_mem_U (fun he => hadj a (ha.trans he.symm)) hm
  intro hc
  rcases cyclic_two_apart k hk3 hk5 i i' hii hr hr' with h | h
  · exact hh i i' hi h hc
  · exact hh i' i hi' h hc.symm

lemma closed_of_points {k : ℕ} (s : Fin k → PolygonStep Q R E) (pt : Fin k → A)
    (hpt : ∀ i, pt (finRotate k i) - pt i = (s i).vector F) :
    ∑ i, (s i).vector F = 0 := by
  simp_rw [← hpt]
  rw [Finset.sum_sub_distrib,Equiv.sum_comp (finRotate k),sub_self]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateGeometry -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateModel -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (GenericStep Q R E) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar,g.component)) (by
    rintro ⟨l,t,x,hx⟩ ⟨l',t',x',hx'⟩ h
    cases Prod.mk.inj h with
    | intro hl hrest =>
      cases hl
      obtain ⟨ht,hx⟩ := Prod.mk.inj hrest
      cases ht; cases hx; rfl)
instance [Fintype Q] [Fintype R] : Fintype (ExceptionalStep Q R) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar)) (by
    rintro ⟨l,t,ht⟩ ⟨l',t',ht'⟩ h
    obtain ⟨hl,he⟩ := Prod.mk.inj h
    cases hl; cases he; rfl)

namespace PolygonStep
lemma eq_of_label_vector_eq (F : DirectionFrame Q A R E) {s t : PolygonStep Q R E}
    (hl : s.label = t.label) (hv : s.vector F = t.vector F) : s = t := by
  cases s with
  | inl g => cases t with
    | inl h =>
      have hgh := Sum.inl.inj hl
      cases g with
      | mk j c x hx => cases h with
        | mk j' c' x' hx' =>
          dsimp at hgh
          cases hgh
          have hh := F.u_injective j hv
          obtain ⟨hc,he⟩ := Prod.mk.inj hh
          cases hc; cases he; rfl
    | inr h => cases hl
  | inr g => cases t with
    | inl h => cases hl
    | inr h =>
      have hgh := Sum.inr.inj hl
      cases g with
      | mk r c hc => cases h with
        | mk r' c' hc' =>
          dsimp at hgh
          cases hgh
          have hh := F.exc_injective r hv
          cases hh; rfl

lemma vector_mem_label (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    s.vector F ∈ Sum.elim F.U F.exceptional s.label := by
  cases s with
  | inl g => exact ⟨(g.scalar,g.component),rfl⟩
  | inr e => exact ⟨e.scalar,rfl⟩
end PolygonStep

structure Candidate (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ) where
  step : Fin k → PolygonStep Q R E
  point : Fin k → A
  shift : ∀ i, point (finRotate k i) - point i = (step i).vector F
  adjacent : ∀ i, (step i).label ≠ (step (finRotate k i)).label
  exceptional : ∀ i (e : ExceptionalStep Q R), step i = .inr e →
    point i ∈ T e.label ∧ point (finRotate k i) ∈ T e.label
  generic : ∃ i j, (step i).label = .inl j

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ}

@[ext] lemma ext {c d : Candidate F T k} (hs : c.step = d.step) (hp : c.point = d.point) : c=d := by
  cases c; cases d; cases hs; cases hp; rfl

instance [Fintype Q] [Fintype R] [Fintype E] [Fintype A] : Fintype (Candidate F T k) :=
  Fintype.ofInjective (fun c => (c.step,c.point)) (by
    intro c d h
    exact ext F T (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma closed (c : Candidate F T k) : ∑ i, (c.step i).vector F = 0 :=
  F.closed_of_points c.step c.point c.shift

def labels (c : Candidate F T k) : Finset (R × Q) := genericLabels (fun i => (c.step i).label)

def positions (c : Candidate F T k) : Finset (Fin k) := genericPositions (fun i => (c.step i).label)

lemma count_eq_two (c : Candidate F T k) (hk : k ≤ 5) (j : R × Q) (hj : j ∈ c.labels) :
    (Finset.univ.filter (fun i => (c.step i).label = .inl j)).card = 2 :=
  F.generic_occurs_twice c.step hk (c.closed F T) c.adjacent j ((mem_genericLabels _ _).mp hj)

lemma labels_card_bounds (c : Candidate F T k) (hk : k ≤ 5) : 1 ≤ c.labels.card ∧ c.labels.card ≤ 2 := by
  refine ⟨?_,genericLabels_card_le_two _ hk (fun j hj => c.count_eq_two F T hk j hj)⟩
  rw [Finset.one_le_card]
  obtain ⟨i,j,hi⟩ := c.generic
  exact ⟨j,(mem_genericLabels _ _).mpr ⟨i,hi⟩⟩

lemma positions_card (c : Candidate F T k) (hk : k ≤ 5) : c.positions.card = 2*c.labels.card :=
  genericPositions_card_eq_twice _ (fun j hj => c.count_eq_two F T hk j hj)

/-- Coordinate recovery on a cyclic sequence, used for the rooted event counts. -/
lemma points_eq (c d : Candidate F T k) (hs : c.step = d.step) (i : Fin k)
    (hi : c.point i = d.point i) : c.point = d.point := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hd (j : Fin (n+1)) : c.point (finRotate _ j) - d.point (finRotate _ j) =
        c.point j-d.point j := by
      have hc := c.shift j
      have he := d.shift j
      rw [hs] at hc
      exact sub_eq_sub_iff_sub_eq_sub.mp (hc.trans he.symm)
    have hc : ∀ j : Fin (n+1), c.point j-d.point j = c.point 0-d.point 0 := by
      intro j
      induction j using Fin.induction with
      | zero => rfl
      | succ j hj =>
        have hh := hd j.castSucc
        have hr : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
        rw [hr] at hh
        exact hh.trans hj
    have hz : c.point 0-d.point 0 = 0 := (hc i).symm.trans (sub_eq_zero.mpr hi)
    funext j
    exact sub_eq_zero.mp ((hc j).trans hz)

end Candidate

/-- In a closed vector sequence, deleting two positions in disjoint direction
spaces leaves at most one completion. This supplies all polygon count
uniqueness, including the unpaired sides of a pentagon. -/
lemma two_position_recovery {I : Type u_5} [Fintype I] [DecidableEq I]
    (U W : Submodule Q A) (hUW : Disjoint U W) (a b : I) (hab : a ≠ b)
    (v v' : I → A) (ha : v a ∈ U) (ha' : v' a ∈ U)
    (hb : v b ∈ W) (hb' : v' b ∈ W)
    (hz : ∑ i, v i = 0) (hz' : ∑ i, v' i = 0)
    (he : ∀ i, i ≠ a → i ≠ b → v i = v' i) : v = v' := by
  have hsum : ∑ i, (v i-v' i) = 0 := by rw [Finset.sum_sub_distrib,hz,hz',sub_self]
  have hpair : (v a-v' a)+(v b-v' b) = 0 := by
    have hs : ∑ i : I, (v i-v' i) = ∑ i ∈ ({a,b} : Finset I), (v i-v' i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact sub_eq_zero.mpr (he i hi.1 hi.2)
    rw [hs] at hsum
    simpa only [Finset.sum_insert,Finset.mem_singleton,hab,not_false_eq_true,Finset.sum_singleton] using hsum
  have hwa : v a-v' a ∈ W := by
    have hneg : v a-v' a = -(v b-v' b) := eq_neg_of_add_eq_zero_left hpair
    rw [hneg]
    exact W.neg_mem (W.sub_mem hb hb')
  have hza := (Submodule.disjoint_def.mp hUW) _ (U.sub_mem ha ha') hwa
  have hzb : v b-v' b = 0 := by simpa only [hza,zero_add] using hpair
  funext i
  by_cases hi : i=a
  · subst i; exact sub_eq_zero.mp hza
  by_cases hi' : i=b
  · subst i; exact sub_eq_zero.mp hzb
  exact he i hi hi'

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateModel -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateCounting -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

lemma card_le_of_unique_cover {α : Type u_5} {β : Type u_6} [Fintype α] [Fintype β]
    (Rel : α → β → Prop) (hex : ∀ a, ∃ b, Rel a b)
    (hunique : ∀ a a' b, Rel a b → Rel a' b → a=a') : Fintype.card α ≤ Fintype.card β := by
  choose f hf using hex
  apply Fintype.card_le_of_injective f
  intro a a' h
  exact hunique a a' (f a) (hf a) (h ▸ hf a')

lemma pair_set_of_card_two {I : Type u_7} [DecidableEq I] {s : Finset I}
    (hcard : s.card = 2) {i : I} (hi : i ∈ s) : ∃ a, a ≠ i ∧ s = {i,a} := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hcard
  rw [hs] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b,hab.symm,hs⟩
  · exact ⟨a,hab,by rw [hs,Finset.pair_comm]⟩

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

structure Rooted where
  cycle : Candidate F T k
  root : Fin k
  label_eq : (cycle.step root).label = .inl j
  point_mem : cycle.point root ∈ C.val

namespace Rooted
@[ext] lemma ext {c d : Rooted F T k j C} (hc : c.cycle = d.cycle) (hr : c.root = d.root) : c=d := by
  cases c; cases d; cases hc; cases hr; rfl
instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (Rooted F T k j C) :=
  Fintype.ofInjective (fun c => (c.cycle,c.root)) (by
    intro c d h
    exact ext F T k j C (congrArg Prod.fst h) (congrArg Prod.snd h))
end Rooted

/-- A deliberately generous finite codec. The last field stores k exceptional
scalars rather than just one; the final numeric load still tends to zero. -/
structure TwoCode where
  other : R × Q
  idx : Fin 4 → Fin k
  tag : Fin k → Fin 3
  point : C.val
  vec0 : Q × E
  vec1 : Q × E
  exc : Fin k → Q

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (TwoCode F k j C) :=
  Fintype.ofInjective (fun c => (c.other,c.idx,c.tag,c.point,c.vec0,c.vec1,c.exc)) (by
    rintro ⟨a,b,c,d,e,f,g⟩ ⟨a',b',c',d',e',f',g'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := h
    rfl)

def TwoCode.lab (z : TwoCode F k j C) (i : Fin k) : (R × Q) ⊕ R :=
  ![.inl j,.inl z.other,.inr j.1] (z.tag i)

def TwoCode.known (z : TwoCode F k j C) (i : Fin k) : A :=
  if i=z.idx 0 then F.u j z.vec0 else
    if i=z.idx 2 then F.u z.other z.vec1 else F.exc j.1 (z.exc i)

structure CoveredTwo (c : Rooted F T k j C) (z : TwoCode F k j C) : Prop where
  other_ne : j ≠ z.other
  root_eq : c.root = z.idx 0
  lab : ∀ i, (c.cycle.step i).label = z.lab F k j C i
  omit0 : (c.cycle.step (z.idx 1)).label = .inl j
  omit1 : (c.cycle.step (z.idx 3)).label = .inl z.other
  point : c.cycle.point (z.idx 0) = z.point.val
  known : ∀ i, i ≠ z.idx 1 → i ≠ z.idx 3 → (c.cycle.step i).vector F = z.known F k j C i

lemma CoveredTwo.unique {c d : Rooted F T k j C} {z : TwoCode F k j C}
    (hc : CoveredTwo F T k j C c z) (hd : CoveredTwo F T k j C d z) : c=d := by
  have hab : z.idx 1 ≠ z.idx 3 := by
    intro h
    exact hc.other_ne (Sum.inl.inj (hc.omit0.symm.trans (h ▸ hc.omit1)))
  have hv : (fun i => (c.cycle.step i).vector F) = fun i => (d.cycle.step i).vector F := by
    apply two_position_recovery (F.U j) (F.U z.other) (F.U_disjoint hc.other_ne)
      (z.idx 1) (z.idx 3) hab
    · exact F.vector_mem_U hc.omit0
    · exact F.vector_mem_U hd.omit0
    · exact F.vector_mem_U hc.omit1
    · exact F.vector_mem_U hd.omit1
    · exact c.cycle.closed F T
    · exact d.cycle.closed F T
    · intro i hi hi'
      exact (hc.known i hi hi').trans (hd.known i hi hi').symm
  have hs : c.cycle.step = d.cycle.step := by
    funext i
    exact PolygonStep.eq_of_label_vector_eq F ((hc.lab i).trans (hd.lab i).symm) (congrFun hv i)
  have hp := Candidate.points_eq F T c.cycle d.cycle hs (z.idx 0) (hc.point.trans hd.point.symm)
  exact Rooted.ext F T k j C (Candidate.ext F T hs hp) (hc.root_eq.trans hd.root_eq.symm)

lemma two_label_codec (c : Rooted F T k j C) (hk : k ≤ 5)
    (hg : c.cycle.labels.card = 2) : ∃ z : TwoCode F k j C, CoveredTwo F T k j C c z := by
  have hj : j ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨c.root,c.label_eq⟩
  obtain ⟨j',hj'ne,hlabels⟩ := pair_set_of_card_two hg hj
  have hj' : j' ∈ c.cycle.labels := by rw [hlabels]; simp
  have hrmem : c.root ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) := by
    simp [c.label_eq]
  obtain ⟨a,har,hgen0⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk j hj) hrmem
  obtain ⟨b,hb⟩ := (mem_genericLabels _ _).mp hj'
  have hbmem : b ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j') := by simp [hb]
  obtain ⟨d,hdb,hgen1⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk j' hj') hbmem
  have hother : j ≠ j' := hj'ne.symm
  have hgeneric (i : Fin k) (g : GenericStep Q R E) (hi : c.cycle.step i = .inl g) :
      g.label = j ∨ g.label = j' := by
    have hh : g.label ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,by rw [hi]; rfl⟩
    rw [hlabels] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hexceptional (i : Fin k) (e : ExceptionalStep Q R) (hi : c.cycle.step i = .inr e) :
      e.label = j.1 := by
    have hh := F.two_generic_bundle c.cycle.step hk (c.cycle.closed F T) c.cycle.adjacent hg
      e.label ⟨i,by rw [hi]; rfl⟩
    exact (hh.2 j hj).symm
  let coords (step : PolygonStep Q R E) : Q × E :=
    Sum.elim (fun generic => (generic.scalar,generic.component)) (fun _ => 0) step
  let tag (index : Fin k) : Fin 3 :=
    Sum.elim (fun generic => if generic.label = j then 0 else 1) (fun _ => 2) (c.cycle.step index)
  let exc (index : Fin k) : Q :=
    Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (c.cycle.step index)
  let z : TwoCode F k j C := ⟨j',![c.root,a,b,d],tag,
    ⟨c.cycle.point c.root,c.point_mem⟩,coords (c.cycle.step c.root),coords (c.cycle.step b),exc⟩
  have hgen0' (i : Fin k) : (c.cycle.step i).label = .inl j ↔ i=c.root ∨ i=a := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) ↔ i ∈ ({c.root,a} : Finset (Fin k)) := by rw [hgen0]
    simpa using hh
  have hgen1' (i : Fin k) : (c.cycle.step i).label = .inl j' ↔ i=b ∨ i=d := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j') ↔ i ∈ ({b,d} : Finset (Fin k)) := by rw [hgen1]
    simpa using hh
  have hcoord (i : Fin k) (l : R × Q) (hi : (c.cycle.step i).label = .inl l) :
      (c.cycle.step i).vector F = F.u l (coords (c.cycle.step i)) := by
    cases he : c.cycle.step i with
    | inl g =>
      rw [he] at hi
      have hh := Sum.inl.inj hi
      cases hh
      rfl
    | inr e => simp [he,PolygonStep.label] at hi
  refine ⟨z,hother,rfl,?_,(hgen0' a).mpr (Or.inr rfl),(hgen1' d).mpr (Or.inr rfl),rfl,?_⟩
  · intro i
    cases hi : c.cycle.step i with
    | inl g =>
      rcases hgeneric i g hi with hg | hg
      · simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hg]
      · simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hg,hj'ne]
    | inr e => simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hexceptional i e hi]
  · intro i hia hid
    change i ≠ a at hia
    change i ≠ d at hid
    change _ = if i=c.root then F.u j (coords (c.cycle.step c.root)) else
      if i=b then F.u j' (coords (c.cycle.step b)) else F.exc j.1 (exc i)
    by_cases hir : i=c.root
    · subst i; rw [ite_eq_left rfl]; exact hcoord c.root j c.label_eq
    rw [ite_eq_right hir]
    by_cases hib : i=b
    · subst i; rw [ite_eq_left rfl]; exact hcoord b j' hb
    rw [ite_eq_right hib]
    cases hi : c.cycle.step i with
    | inl g =>
      rcases hgeneric i g hi with hg | hg
      · have hh := (hgen0' i).mp (by rw [hi]; exact congrArg Sum.inl hg)
        exact False.elim (hh.elim hir hia)
      · have hh := (hgen1' i).mp (by rw [hi]; exact congrArg Sum.inl hg)
        exact False.elim (hh.elim hib hid)
    | inr e => simp [PolygonStep.vector,exc,hi,hexceptional i e hi]

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateCounting -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.ReplacementGeometry -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype Q] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

def replacementRegion (r : R) : Finset A := O.biUnion (fun o => cosetPoints (F.W r) o)

omit [Fintype Q] in
@[simp] lemma mem_replacementRegion (r : R) (x : A) :
    x ∈ F.replacementRegion O r ↔ ∃ o ∈ O, x-o ∈ F.W r := by
  simp [replacementRegion]

lemma generic_region_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) (C : AffineCoset (F.U j)) (r : R) :
    (C.val ∩ F.replacementRegion O r).card ≤ 100 * Fintype.card Q := by
  obtain ⟨x,hx⟩ := C.property
  let H := O.filter (fun o => o-x ∈ F.U j ⊔ F.W r)
  have hsub : C.val ∩ F.replacementRegion O r ⊆
      H.biUnion (fun o => C.val ∩ cosetPoints (F.W r) o) := by
    intro y hy
    obtain ⟨hyC,hyT⟩ := Finset.mem_inter.mp hy
    obtain ⟨o,ho,hyo⟩ := (F.mem_replacementRegion O r y).mp hyT
    have hyx : y-x ∈ F.U j := by
      rw [hx] at hyC
      exact (mem_cosetPoints _ _ _).mp hyC
    have hox : o-x ∈ F.U j ⊔ F.W r := by
      convert (F.U j ⊔ F.W r).sub_mem
        ((show F.U j ≤ F.U j ⊔ F.W r from le_sup_left) hyx)
        ((show F.W r ≤ F.U j ⊔ F.W r from le_sup_right) hyo) using 1; abel
    exact Finset.mem_biUnion.mpr ⟨o,Finset.mem_filter.mpr ⟨ho,hox⟩,
      Finset.mem_inter.mpr ⟨hyC,(mem_cosetPoints _ _ _).mpr hyo⟩⟩
  have hi (o : A) : (C.val ∩ cosetPoints (F.W r) o).card ≤ Fintype.card Q := by
    rw [hx]
    by_cases hr : j.1 = r
    · have hh := intersection_cosets_card_le (F.U j) (F.W r) x o
      rw [← hr,F.U_inf_W_same,F.card_D] at hh
      simpa only [hr] using hh
    · exact (intersection_cosets_card_le_one _ _ (F.U_W_disjoint hr) _ _).trans
        (Fintype.card_pos)
  calc
    _ ≤ (H.biUnion (fun o => C.val ∩ cosetPoints (F.W r) o)).card := Finset.card_le_card hsub
    _ ≤ ∑ o ∈ H, (C.val ∩ cosetPoints (F.W r) o).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H, Fintype.card Q := Finset.sum_le_sum (fun o _ => hi o)
    _ = H.card * Fintype.card Q := by simp
    _ ≤ 100 * Fintype.card Q := Nat.mul_le_mul_right _ (hO.occupancy j r x)

omit [Fintype Q] in
lemma holes_in_coset_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) (C : AffineCoset (F.U j)) : (O ∩ C.val).card ≤ 100 := by
  obtain ⟨x,hx⟩ := C.property
  have hs : O ∩ C.val ⊆ O.filter (fun o => o-x ∈ F.U j ⊔ F.W j.1) := by
    intro o ho
    obtain ⟨hoO,hoC⟩ := Finset.mem_inter.mp ho
    have hmember : o-x ∈ F.U j := by
      rw [hx] at hoC
      exact (mem_cosetPoints _ _ _).mp hoC
    exact Finset.mem_filter.mpr ⟨hoO,(show F.U j ≤ F.U j ⊔ F.W j.1 from le_sup_left)
      hmember⟩
  exact (Finset.card_le_card hs).trans (hO.occupancy j j.1 x)

omit [Fintype Q] [Fintype A] in
lemma different_holes_nonzero_component (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) {x y : A} (hx : x ∈ O) (hy : y ∈ O) (hne : y ≠ x)
    (v : Q × E) (hv : F.u j v = y-x) : v.2 ≠ 0 := by
  intro hz
  have hm : y-x ∈ F.W j.1 := by
    rw [← hv,F.u_apply,hz,map_zero,add_zero]
    exact ⟨(v.1,v.1*j.2),rfl⟩
  exact hne (hO.collision j.1 x hx y hy hm)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.ReplacementGeometry -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.OneCandidateCounting -/
section

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

omit [Fintype A] in
lemma one_position_recovery {I : Type u_5} [Fintype I] [DecidableEq I]
    (a : I) (v v' : I → A) (hz : ∑ i, v i = 0) (hz' : ∑ i, v' i = 0)
    (he : ∀ i, i ≠ a → v i = v' i) : v = v' := by
  have hsum : ∑ i, (v i-v' i) = 0 := by rw [Finset.sum_sub_distrib,hz,hz',sub_self]
  have hsingle : ∑ i, (v i-v' i) = v a-v' a := by
    apply Finset.sum_eq_single a
    · intro b _ hb; exact sub_eq_zero.mpr (he b hb)
    · simp
  have ha : v a = v' a := sub_eq_zero.mp (hsingle.symm.trans hsum)
  funext i
  by_cases hi : i=a
  · simpa [hi] using ha
  · exact he i hi

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

local instance oneCodeIndexNeZero : NeZero (2 : ℕ) := inferInstance

abbrev OneCode := Σ r : R, (Fin 2 → Fin k) × (Fin k → Bool) ×
  ↥(C.val ∩ T r) × ↥(C.val ∩ T r) × (Fin k → Q)

namespace OneCode
abbrev other (z : OneCode F T k j C) := z.1
abbrev idx (z : OneCode F T k j C) := z.2.1
abbrev tag (z : OneCode F T k j C) := z.2.2.1
abbrev point (z : OneCode F T k j C) := z.2.2.2.1
abbrev nextPoint (z : OneCode F T k j C) := z.2.2.2.2.1
abbrev exc (z : OneCode F T k j C) := z.2.2.2.2.2

def lab (z : OneCode F T k j C) (i : Fin k) : (R × Q) ⊕ R :=
  if z.tag F T k j C i then .inl j else .inr (z.other F T k j C)
def known (z : OneCode F T k j C) (i : Fin k) : A :=
  if i=z.idx F T k j C 0 then (z.nextPoint F T k j C).val - (z.point F T k j C).val
    else F.exc (z.other F T k j C) (z.exc F T k j C i)
end OneCode

structure CoveredOne (c : Rooted F T k j C) (z : OneCode F T k j C) : Prop where
  root_eq : c.root = z.idx F T k j C 0
  lab : ∀ i, (c.cycle.step i).label = z.lab F T k j C i
  point : c.cycle.point (z.idx F T k j C 0) = (z.point F T k j C).val
  known : ∀ i, i ≠ z.idx F T k j C 1 →
    (c.cycle.step i).vector F = z.known F T k j C i

lemma CoveredOne.unique {c d : Rooted F T k j C} {z : OneCode F T k j C}
    (hc : CoveredOne F T k j C c z) (hd : CoveredOne F T k j C d z) : c=d := by
  have hv : (fun i => (c.cycle.step i).vector F) = fun i => (d.cycle.step i).vector F := by
    apply one_position_recovery (z.idx F T k j C 1) _ _ (c.cycle.closed F T) (d.cycle.closed F T)
    intro i hi
    exact (hc.known i hi).trans (hd.known i hi).symm
  have hs : c.cycle.step = d.cycle.step := by
    funext i
    exact PolygonStep.eq_of_label_vector_eq F ((hc.lab i).trans (hd.lab i).symm) (congrFun hv i)
  have hp := Candidate.points_eq F T c.cycle d.cycle hs (z.idx F T k j C 0)
    (hc.point.trans hd.point.symm)
  exact Rooted.ext F T k j C (Candidate.ext F T hs hp) (hc.root_eq.trans hd.root_eq.symm)

lemma one_label_codec (c : Rooted F T k j C) (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hg : c.cycle.labels.card = 1) : k=4 ∧
      ∃ z : OneCode F T k j C, CoveredOne F T k j C c z := by
  have hj : j ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨c.root,c.label_eq⟩
  have hlabels : c.cycle.labels = {j} := by
    obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hg
    rw [hl] at hj
    have he : j=l := Finset.mem_singleton.mp hj
    rw [hl,he]
  have honly (i : Fin k) (g : GenericStep Q R E) (hi : c.cycle.step i = .inl g) : g.label = j := by
    have hh : g.label ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,by rw [hi]; rfl⟩
    simpa only [hlabels,Finset.mem_singleton] using hh
  obtain ⟨hk,hall⟩ := F.one_generic_rectangle c.cycle.step hk3 hk5 (c.cycle.closed F T)
    c.cycle.adjacent j honly
  have hjall : Sum.inl j ∈ Finset.univ.image (fun i => (c.cycle.step i).label) :=
    Finset.mem_image.mpr ⟨c.root,Finset.mem_univ _,c.label_eq⟩
  obtain ⟨l,hlne,hlabs⟩ := pair_set_of_card_two hall hjall
  have hlex : ∃ r : R, l = Sum.inr r := by
    cases l with
    | inr r => exact ⟨r,rfl⟩
    | inl j' =>
      have hh : Sum.inl j' ∈ Finset.univ.image (fun i => (c.cycle.step i).label) := by rw [hlabs]; simp
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh
      have hh : j' ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,hi⟩
      have he : j'=j := by simpa only [hlabels,Finset.mem_singleton] using hh
      exact False.elim (hlne (congrArg Sum.inl he))
  obtain ⟨r,rfl⟩ := hlex
  have hexceptional (i : Fin k) (e : ExceptionalStep Q R) (hi : c.cycle.step i = .inr e) : e.label = r := by
    have hh : Sum.inr e.label ∈ Finset.univ.image (fun i => (c.cycle.step i).label) :=
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [hi]; rfl⟩
    simpa only [hlabs,Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,
      reduceCtorEq,false_or] using hh
  have hnext : ∃ e : ExceptionalStep Q R, c.cycle.step (finRotate k c.root) = .inr e := by
    cases hi : c.cycle.step (finRotate k c.root) with
    | inr e => exact ⟨e,rfl⟩
    | inl g =>
      have hh := honly _ g hi
      exact False.elim (c.cycle.adjacent c.root (c.label_eq.trans (by rw [hi]; exact congrArg Sum.inl hh.symm)))
  have hprev : ∃ e : ExceptionalStep Q R, c.cycle.step ((finRotate k).symm c.root) = .inr e := by
    cases hi : c.cycle.step ((finRotate k).symm c.root) with
    | inr e => exact ⟨e,rfl⟩
    | inl g =>
      have hh := honly _ g hi
      apply False.elim
      apply c.cycle.adjacent ((finRotate k).symm c.root)
      simp only [Equiv.apply_symm_apply]
      rw [hi,c.label_eq]
      exact congrArg Sum.inl hh
  obtain ⟨en,hen⟩ := hnext
  obtain ⟨ep,hep⟩ := hprev
  have hpT : c.cycle.point c.root ∈ T r := by
    have hh := (c.cycle.exceptional _ ep hep).2
    simpa only [Equiv.apply_symm_apply,hexceptional _ ep hep] using hh
  have hnT : c.cycle.point (finRotate k c.root) ∈ T r := by
    simpa only [hexceptional _ en hen] using (c.cycle.exceptional _ en hen).1
  have hnC : c.cycle.point (finRotate k c.root) ∈ C.val := by
    have hm := (AffineCoset.add_mem_iff _ C _ _ (F.vector_mem_U c.label_eq)).mpr c.point_mem
    rw [← c.cycle.shift c.root] at hm
    convert hm using 1; abel
  have hrmem : c.root ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) := by simp [c.label_eq]
  obtain ⟨a,har,hgen⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk5 j hj) hrmem
  have hgen' (i : Fin k) : (c.cycle.step i).label = .inl j ↔ i=c.root ∨ i=a := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) ↔
        i ∈ ({c.root,a} : Finset (Fin k)) := by rw [hgen]
    simpa using hh
  let tag (index : Fin k) : Bool := Sum.elim (fun _ => true) (fun _ => false) (c.cycle.step index)
  let exc (index : Fin k) : Q :=
    Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (c.cycle.step index)
  let z : OneCode F T k j C := ⟨r,![c.root,a],tag,
    ⟨c.cycle.point c.root,Finset.mem_inter.mpr ⟨c.point_mem,hpT⟩⟩,
    ⟨c.cycle.point (finRotate k c.root),Finset.mem_inter.mpr ⟨hnC,hnT⟩⟩,exc⟩
  refine ⟨hk,z,rfl,?_,rfl,?_⟩
  · intro i
    cases hi : c.cycle.step i with
    | inl g => simp [z,OneCode.lab,OneCode.tag,tag,hi,PolygonStep.label,honly i g hi]
    | inr e => simp [z,OneCode.lab,OneCode.tag,OneCode.other,tag,hi,PolygonStep.label,hexceptional i e hi]
  · intro i hia
    change i ≠ a at hia
    change _ = if i=c.root then c.cycle.point (finRotate k c.root)-c.cycle.point c.root else F.exc r (exc i)
    by_cases hir : i=c.root
    · subst i; rw [ite_eq_left rfl]; exact (c.cycle.shift _).symm
    rw [ite_eq_right hir]
    cases hi : c.cycle.step i with
    | inl g =>
      have hh := (hgen' i).mp (by rw [hi]; exact congrArg Sum.inl (honly i g hi))
      exact False.elim (hh.elim hir hia)
    | inr e => simp [PolygonStep.vector,exc,hi,hexceptional i e hi]

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.OneCandidateCounting -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateDependencies -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

abbrev SlabVariable (F : DirectionFrame Q A R E) := Σ j : R × Q, AffineCoset (F.U j)

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ} (c : Candidate F T k)

abbrev Occurrence := {p : Fin k × GenericStep Q R E // c.step p.1 = .inl p.2}

omit [Fintype A] in
lemma occurrence_index_injective : Function.Injective (fun p : c.Occurrence F T => p.val.1) := by
  intro p p' h
  apply Subtype.ext
  apply Prod.ext h
  have hs : c.step p.val.1 = c.step p'.val.1 := congrArg c.step h
  exact Sum.inl.inj (p.property.symm.trans (hs.trans p'.property))

instance : Fintype (c.Occurrence F T) :=
  Fintype.ofInjective (fun p => p.val.1) (c.occurrence_index_injective F T)

omit [Fintype A] in
lemma occurrence_card : Fintype.card (c.Occurrence F T) = c.positions.card := by
  let f : c.Occurrence F T → c.positions := fun p => ⟨p.val.1,by
    change p.val.1 ∈ Finset.univ.filter (fun i => (c.step i).label.isLeft)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [p.property]
    rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p p' hp
      exact c.occurrence_index_injective F T (congrArg Subtype.val hp)
    · intro i
      have hi : (c.step i.val).label.isLeft = true := (Finset.mem_filter.mp i.property).2
      cases h : c.step i.val with
      | inl g => exact ⟨⟨(i.val,g),h⟩,rfl⟩
      | inr e => simp only [h,PolygonStep.label,Sum.isLeft_inr,Bool.false_eq_true] at hi
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f hf)

def occurrenceVariable (p : c.Occurrence F T) : SlabVariable F :=
  ⟨p.val.2.label,AffineCoset.of (F.U p.val.2.label) (c.point p.val.1)⟩

def occurrenceVector (p : c.Occurrence F T) : E := p.val.2.component

lemma occurrenceVariable_injective (hk3 : 3 ≤ k) (hk5 : k ≤ 5) :
    Function.Injective (c.occurrenceVariable F T) := by
  intro p p' h
  by_contra hp
  have hi : p.val.1 ≠ p'.val.1 := fun hi => hp (c.occurrence_index_injective F T hi)
  obtain ⟨⟨i,g⟩,hg⟩ := p
  obtain ⟨⟨i',g'⟩,hg'⟩ := p'
  have hl : g.label = g'.label := congrArg Sigma.fst h
  have hc : AffineCoset.of (F.U g.label) (c.point i) =
      AffineCoset.of (F.U g.label) (c.point i') := by
    have hh := congrArg (fun v : SlabVariable F => v.2.val) h
    apply Subtype.ext
    change cosetPoints (F.U g.label) (c.point i) = cosetPoints (F.U g.label) (c.point i')
    change cosetPoints (F.U g.label) (c.point i) = cosetPoints (F.U g'.label) (c.point i') at hh
    rw [hl] at hh ⊢
    exact hh
  exact F.distinct_generic_cosets c.step c.point hk3 hk5 c.shift c.adjacent hi
    (by rw [hg]; rfl) (by rw [hg']; exact congrArg Sum.inl hl.symm) hc

def deps : Finset (SlabVariable F) := Finset.univ.image (c.occurrenceVariable F T)

lemma deps_card (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : (c.deps F T).card = 2*c.labels.card := by
  rw [deps,Finset.card_image_of_injective _ (c.occurrenceVariable_injective F T hk3 hk5),
    Finset.card_univ,c.occurrence_card F T,c.positions_card F T hk5]

lemma deps_nonempty : (c.deps F T).Nonempty := by
  obtain ⟨i,j,hi⟩ := c.generic
  cases hs : c.step i with
  | inl g => exact ⟨_,Finset.mem_image.mpr ⟨⟨(i,g),hs⟩,Finset.mem_univ _,rfl⟩⟩
  | inr e => simp [hs,PolygonStep.label] at hi

lemma deps_card_le_four (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : (c.deps F T).card ≤ 4 := by
  rw [c.deps_card F T hk3 hk5]
  have := (c.labels_card_bounds F T hk5).2
  omega

lemma mem_deps_iff (v : SlabVariable F) : v ∈ c.deps F T ↔
    ∃ p : c.Occurrence F T, c.occurrenceVariable F T p = v := by
  simp [deps]

lemma mem_deps_iff_rooted (j : R × Q) (C : AffineCoset (F.U j)) :
    (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T ↔
      ∃ i : Fin k, (c.step i).label = .inl j ∧ c.point i ∈ C.val := by
  rw [c.mem_deps_iff F T]
  constructor
  · rintro ⟨p,hp⟩
    have hl : p.val.2.label = j := congrArg Sigma.fst hp
    have hC : cosetPoints (F.U p.val.2.label) (c.point p.val.1) = C.val :=
      congrArg (fun v : SlabVariable F => v.2.val) hp
    refine ⟨p.val.1,?_,?_⟩
    · rw [p.property]; exact congrArg Sum.inl hl
    · rw [← hC]; exact self_mem_cosetPoints _ _
  · rintro ⟨i,hi,hC⟩
    cases hs : c.step i with
    | inr e => simp [hs,PolygonStep.label] at hi
    | inl g =>
      rw [hs] at hi
      have hj : g.label=j := Sum.inl.inj hi
      subst j
      refine ⟨⟨(i,g),hs⟩,?_⟩
      change Sigma.mk g.label (AffineCoset.of (F.U g.label) (c.point i)) = (⟨g.label,C⟩ : SlabVariable F)
      rw [AffineCoset.eq_of_mem _ hC]

def constraintVector (v : SlabVariable F) : E :=
  if h : ∃ p : c.Occurrence F T, c.occurrenceVariable F T p = v
    then c.occurrenceVector F T h.choose else 0

lemma constraintVector_at (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (p : c.Occurrence F T) :
    c.constraintVector F T (c.occurrenceVariable F T p) = c.occurrenceVector F T p := by
  have hex : ∃ p' : c.Occurrence F T, c.occurrenceVariable F T p' = c.occurrenceVariable F T p := ⟨p,rfl⟩
  rw [constraintVector,dite_eq_left hex]
  congr 1
  exact c.occurrenceVariable_injective F T hk3 hk5 hex.choose_spec

lemma constraintVector_nonzero (v : SlabVariable F) (hv : v ∈ c.deps F T) :
    c.constraintVector F T v ≠ 0 := by
  have hex := (c.mem_deps_iff F T v).mp hv
  rw [constraintVector,dite_eq_left hex]
  exact hex.choose.val.2.nonzero

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateDependencies -/

/- BEGIN PINNED MODULE OAI.RingTheory.DirectFiniteness.CandidateBounds -/
section

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

def TwoCode.equiv : TwoCode F k j C ≃
    ((R × Q) × (Fin 4 → Fin k) × (Fin k → Fin 3) × C.val × (Q × E) × (Q × E) × (Fin k → Q)) where
  toFun c := (c.other,c.idx,c.tag,c.point,c.vec0,c.vec1,c.exc)
  invFun c := ⟨c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,c.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma twoCode_card : Fintype.card (TwoCode F k j C) =
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k := by
  rw [Fintype.card_congr (TwoCode.equiv F k j C)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
  ring

omit [Fintype E] in
lemma oneCode_card_le (M : ℕ) (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card (OneCode F T k j C) ≤ Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k := by
  change Fintype.card (Σ r : R, (Fin 2 → Fin k) × (Fin k → Bool) ×
    ↥(C.val ∩ T r) × ↥(C.val ∩ T r) × (Fin k → Q)) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
  calc
    _ ≤ ∑ _r : R, k^2 * (2^k * (M * (M * Fintype.card Q^k))) := by
      apply Finset.sum_le_sum
      intro r _
      gcongr <;> exact hM r
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]; ring

lemma two_rooted_card_le (hk : k ≤ 5) :
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=2} ≤
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k := by
  rw [← twoCode_card F k j C]
  apply card_le_of_unique_cover (fun c z => CoveredTwo F T k j C c.val z)
  · intro c; exact two_label_codec F T k j C c.val hk c.property
  · intro c d z hc hd
    exact Subtype.ext (CoveredTwo.unique F T k j C hc hd)

lemma one_rooted_card_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=1} ≤
    Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k := by
  apply le_trans (b := Fintype.card (OneCode F T k j C))
  · apply card_le_of_unique_cover (fun c z => CoveredOne F T k j C c.val z)
    · intro c; exact (one_label_codec F T k j C c.val hk3 hk5 c.property).2
    · intro c d z hc hd; exact Subtype.ext (CoveredOne.unique F T k j C hc hd)
  · exact oneCode_card_le F T k j C M hM

lemma local_card_le_rooted (g : ℕ) :
    Fintype.card {c : Candidate F T k // c.labels.card=g ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=g} := by
  apply card_le_of_unique_cover (fun c d => d.val.cycle = c.val)
  · intro c
    obtain ⟨i,hi,hC⟩ := (c.val.mem_deps_iff_rooted F T j C).mp c.property.2
    exact ⟨⟨⟨c.val,i,hi,hC⟩,c.property.1⟩,rfl⟩
  · intro c c' d hc hc'
    exact Subtype.ext (hc.symm.trans hc')

lemma local_one_card_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card {c : Candidate F T k // c.labels.card=1 ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k :=
  (local_card_le_rooted F T k j C 1).trans (one_rooted_card_le F T k j C hk3 hk5 M hM)

lemma local_two_card_le (hk5 : k ≤ 5) :
    Fintype.card {c : Candidate F T k // c.labels.card=2 ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k :=
  (local_card_le_rooted F T k j C 2).trans (two_rooted_card_le F T k j C hk5)

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
end
/- CHECKPOINT: OAI.RingTheory.DirectFiniteness.CandidateBounds -/

#print axioms OAI.mersenne_21701_prime
