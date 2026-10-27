module

public import BernoulliIso.Marker
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
The actual restricted lamplighter ambient group from the manuscript.
The finite-support type is essential: the unrestricted wreath product would
not be countable. No finite-generation claim is needed in this module.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace BernoulliIso.Ambient

abbrev Lamps := Multiplicative (ℤ →₀ ZMod 2)

instance : Countable Lamps := Countable.of_equiv (ℤ →₀ ZMod 2) Multiplicative.ofAdd

instance : Countable (Multiplicative ℤ) := Countable.of_equiv ℤ Multiplicative.ofAdd

def shiftAction : Multiplicative ℤ →* MulAut Lamps where
  toFun z := AddEquiv.toMultiplicative (Finsupp.domCongr (Equiv.addLeft z.toAdd))
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    ext i
    change a.toAdd (-(0 : ℤ) + i) = a.toAdd i
    simp
  map_mul' z w := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    ext i
    change a.toAdd (-(z.toAdd + w.toAdd) + i) =
      a.toAdd (-w.toAdd + (-z.toAdd + i))
    congr 1
    omega

abbrev Lamplighter := SemidirectProduct Lamps (Multiplicative ℤ) shiftAction

instance : Countable Lamplighter :=
  Function.Injective.countable SemidirectProduct.equivProd.injective

abbrev G (N : Type*) [Group N] := N × Lamplighter

variable (N : Type*) [Group N]

def height : G N →* Multiplicative ℤ :=
  SemidirectProduct.rightHom.comp (MonoidHom.snd N Lamplighter)

def step : G N := (1, SemidirectProduct.inr (Multiplicative.ofAdd 1))

def D : Subgroup (G N) := (height N).ker

@[simp] theorem height_step : height N (step N) = Multiplicative.ofAdd 1 := rfl

def markerGeometry : BernoulliIso.MarkerGeometry (G N) where
  D := D N
  height := height N
  step := step N
  height_step := height_step N
  height_D u := u.property
  serial := Nat.pairEquiv
  serial_injective := Nat.pairEquiv.injective

def includeN : N →* G N := MonoidHom.inl N Lamplighter

def includeLamps : Lamps →* G N :=
  (MonoidHom.inr N Lamplighter).comp SemidirectProduct.inl

theorem includeN_injective : Function.Injective (includeN N) := by
  intro x y h
  exact congrArg Prod.fst h

theorem includeLamps_injective : Function.Injective (includeLamps N) := by
  intro x y h
  exact SemidirectProduct.inl_injective (congrArg Prod.snd h)

@[simp] theorem height_includeN (n : N) : height N (includeN N n) = 1 := rfl

@[simp] theorem height_includeLamps (a : Lamps) : height N (includeLamps N a) = 1 := rfl

theorem include_commute (n : N) (a : Lamps) :
    Commute (includeN N n) (includeLamps N a) := by
  change (n, 1) * (1, SemidirectProduct.inl a) =
    (1, SemidirectProduct.inl a) * (n, 1)
  simp

/-- Lamps supported in a specified finite set of integer sites. -/
def supportedLamps (S : Finset ℤ) : Subgroup Lamps where
  carrier := { a | ∀ i, i ∉ S → a.toAdd i = 0 }
  one_mem' := by intro i hi; rfl
  mul_mem' := by
    intro a b ha hb i hi
    change a.toAdd i + b.toAdd i = 0
    rw [ha i hi, hb i hi, zero_add]
  inv_mem' := by
    intro a ha i hi
    change -a.toAdd i = 0
    rw [ha i hi, neg_zero]

def finiteLampValues (S : Finset ℤ) (a : supportedLamps S) : S → ZMod 2 :=
  fun i => a.val.toAdd i.val

theorem finiteLampValues_injective (S : Finset ℤ) :
    Function.Injective (finiteLampValues S) := by
  intro a b hab
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  ext i
  by_cases hi : i ∈ S
  · exact congrFun hab ⟨i, hi⟩
  · exact (a.property i hi).trans (b.property i hi).symm

instance (S : Finset ℤ) : Finite (supportedLamps S) :=
  Finite.of_injective (finiteLampValues S) (finiteLampValues_injective S)

theorem finiteLampValues_surjective (S : Finset ℤ) :
    Function.Surjective (finiteLampValues S) := by
  intro f
  let values : ℤ → ZMod 2 := fun i => if hi : i ∈ S then f ⟨i, hi⟩ else 0
  let a : ℤ →₀ ZMod 2 := Finsupp.onFinset S values (by
    intro i hi
    by_contra h
    exact hi (by simp [values, h]))
  refine ⟨⟨Multiplicative.ofAdd a, ?_⟩, ?_⟩
  · intro i hi
    simp [a, values, hi]
  · funext i
    simp [finiteLampValues, a, values, i.property]

noncomputable def finiteLampEquiv (S : Finset ℤ) : supportedLamps S ≃ (S → ZMod 2) :=
  Equiv.ofBijective (finiteLampValues S)
    ⟨finiteLampValues_injective S, finiteLampValues_surjective S⟩

theorem supportedLamps_card (S : Finset ℤ) : Nat.card (supportedLamps S) = 2 ^ S.card := by
  rw [Nat.card_congr (finiteLampEquiv S), Nat.card_eq_fintype_card]
  simp

def H (S : Finset ℤ) : Subgroup (G N) := (supportedLamps S).map (includeLamps N)

noncomputable def lampEquivH (S : Finset ℤ) : supportedLamps S ≃* H N S :=
  (supportedLamps S).equivMapOfInjective (includeLamps N) (includeLamps_injective N)

instance (S : Finset ℤ) : Finite (H N S) :=
  Finite.of_equiv (supportedLamps S) (lampEquivH N S).toEquiv

theorem H_card (S : Finset ℤ) : Nat.card (H N S) = 2 ^ S.card := by
  rw [← Nat.card_congr (lampEquivH N S).toEquiv]
  exact supportedLamps_card S

theorem H_le_D (S : Finset ℤ) : H N S ≤ D N := by
  rintro g ⟨a, ha, rfl⟩
  exact height_includeLamps N a

theorem commute_H (S : Finset ℤ) (n : N) (u : H N S) :
    Commute (includeN N n) u.val := by
  obtain ⟨a, ha, h⟩ := u.property
  rw [← h]
  exact include_commute N n a

theorem H_mono {S T : Finset ℤ} (hST : S ⊆ T) : H N S ≤ H N T := by
  apply Subgroup.map_mono
  intro a ha i hi
  exact ha i (fun h => hi (hST h))

theorem H_disjoint_N (S : Finset ℤ) (J : Subgroup N) :
    Disjoint (H N S) (J.map (includeN N)) := by
  apply Subgroup.disjoint_def.mpr
  intro x hx hj
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨n, hn, h⟩ := hj
  have hn1 : n = 1 := congrArg Prod.fst h
  simpa only [hn1, map_one] using h.symm

/-- The first `n` integer lamp sites in a fixed enumeration. -/
def sites (n : ℕ) : Finset ℤ :=
  (Finset.range n).map Equiv.intEquivNat.symm.toEmbedding

@[simp] theorem sites_card (n : ℕ) : (sites n).card = n := by simp [sites]

theorem sites_mono : Monotone sites := by
  intro m n hmn i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_map.mpr ⟨j,
    Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hmn), rfl⟩

theorem sites_exhaust_finite (S : Finset ℤ) : ∃ n, S ⊆ sites n := by
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (S.image Equiv.intEquivNat)
  refine ⟨n, fun i hi => ?_⟩
  exact Finset.mem_map.mpr ⟨Equiv.intEquivNat i,
    hn (Finset.mem_image.mpr ⟨i, hi, rfl⟩), Equiv.intEquivNat.symm_apply_apply i⟩

def Hseq (n : ℕ) : Subgroup (G N) := H N (sites n)

instance (n : ℕ) : Finite (Hseq N n) := inferInstanceAs (Finite (H N (sites n)))

theorem Hseq_card (n : ℕ) : Nat.card (Hseq N n) = 2 ^ n := by
  simpa only [Hseq, sites_card] using H_card N (sites n)

theorem Hseq_mono : Monotone (Hseq N) := fun _ _ h => H_mono N (sites_mono h)

theorem Hseq_unbounded (m : ℕ) : ∃ n, m < Nat.card (Hseq N n) := by
  refine ⟨m, ?_⟩
  rw [Hseq_card]
  exact Nat.lt_two_pow_self

theorem Hseq_zero_eq_bot : Hseq N 0 = ⊥ := by
  apply (Subgroup.eq_bot_iff_card (Hseq N 0)).mpr
  simp [Hseq_card]

theorem Hseq_quotient_card (a b : ℕ) :
    Nat.card ((Hseq N (a + b)) ⧸ (Hseq N a).subgroupOf (Hseq N (a + b))) = 2 ^ b := by
  have hle : Hseq N a ≤ Hseq N (a + b) := Hseq_mono N (Nat.le_add_right a b)
  have hsub : Nat.card ((Hseq N a).subgroupOf (Hseq N (a + b))) = 2 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Hseq_card]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Hseq N a).subgroupOf (Hseq N (a + b)))
  rw [Hseq_card, hsub] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ a from pow_pos (by decide) a)
  simpa only [pow_add, Nat.mul_comm] using h.symm

theorem lamps_exhaust (a : Lamps) : ∃ n, includeLamps N a ∈ Hseq N n := by
  obtain ⟨n, hn⟩ := sites_exhaust_finite a.toAdd.support
  refine ⟨n, ⟨a, ?_, rfl⟩⟩
  intro i hi
  apply Finsupp.notMem_support_iff.mp
  exact fun h => hi (hn h)

#print axioms shiftAction
#print axioms markerGeometry
#print axioms commute_H
#print axioms H_card
#print axioms Hseq_card
#print axioms Hseq_zero_eq_bot
#print axioms Hseq_quotient_card
#print axioms lamps_exhaust

end BernoulliIso.Ambient
