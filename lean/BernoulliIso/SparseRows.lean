module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Finite coefficient rows for the actual inverse sections. Composition is
defined on coefficients, so cancellation is retained and a zero row stays
zero. Bounds apply to the true support, not an overestimate that can never
become empty.
-/

@[expose] public section

noncomputable section
open scoped BigOperators Classical

namespace BernoulliIso
namespace SparseRows

variable {K A B C : Type*} [CommRing K]

/-- Evaluation of one finite row on an unrestricted configuration. -/
def eval (r : A →₀ K) (f : A → K) : K := r.sum fun a c => c * f a

@[simp] theorem eval_zero (f : A → K) : eval (0 : A →₀ K) f = 0 := by
  simp [eval]

@[simp] theorem eval_single (a : A) (c : K) (f : A → K) :
    eval (Finsupp.single a c) f = c * f a := by
  simp [eval]

theorem eval_add (r s : A →₀ K) (f : A → K) :
    eval (r + s) f = eval r f + eval s f := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..)

theorem eval_smul (c : K) (r : A →₀ K) (f : A → K) :
    eval (c • r) f = c * eval r f := by
  rw [eval, Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [eval, Finsupp.sum, mul_assoc, Finset.mul_sum]

/-- Row evaluation is additive in its finite coefficients. -/
def evalHom (f : A → K) : (A →₀ K) →+ K where
  toFun r := eval r f
  map_zero' := eval_zero f
  map_add' r s := eval_add r s f

/-- A sparse operator is a family of finite rows, one for each output site. -/
def operator (rows : A → B →₀ K) : (B → K) →ₗ[K] (A → K) where
  toFun f a := eval (rows a) f
  map_add' f g := by
    funext a
    simp only [eval, Finsupp.sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext a
    simp only [eval, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

@[simp] theorem operator_apply (rows : A → B →₀ K) (f : B → K) (a : A) :
    operator rows f a = eval (rows a) f := rfl

/-- Composition of finite rows includes all cancellations automatically. -/
def compose (r : B →₀ K) (s : B → C →₀ K) : C →₀ K :=
  r.sum fun b c => c • s b

@[simp] theorem compose_zero (s : B → C →₀ K) : compose (0 : B →₀ K) s = 0 := by
  simp [compose]

theorem eval_compose (r : B →₀ K) (s : B → C →₀ K) (f : C → K) :
    eval (compose r s) f = eval r (fun b => eval (s b) f) := by
  change evalHom f (r.sum fun b c => c • s b) = _
  rw [map_finsuppSum]
  simp only [evalHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, eval_smul]
  rfl

theorem operator_comp (r : A → B →₀ K) (s : B → C →₀ K) :
    operator (fun a => compose (r a) s) = (operator r).comp (operator s) := by
  apply LinearMap.ext
  intro f
  funext a
  exact eval_compose (r a) s f

theorem support_compose_subset (r : B →₀ K) (s : B → C →₀ K) :
    (compose r s).support ⊆ r.support.biUnion (fun b => (s b).support) := by
  classical
  exact Finsupp.support_sum.trans (Finset.biUnion_mono fun b _ => Finsupp.support_smul)

/-- The uniform finite-row bound multiplies under composition. -/
theorem card_support_compose_le (r : B →₀ K) (s : B → C →₀ K)
    (R : ℕ) (hR : ∀ b ∈ r.support, (s b).support.card ≤ R) :
    (compose r s).support.card ≤ r.support.card * R := by
  classical
  calc
    (compose r s).support.card ≤
        (r.support.biUnion fun b => (s b).support).card :=
      Finset.card_le_card (support_compose_subset r s)
    _ ≤ ∑ b ∈ r.support, (s b).support.card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ r.support, R := Finset.sum_le_sum hR
    _ = r.support.card * R := by simp

/-- Inserting only selected coordinates annihilates a row whose support
misses the selection. Subsequent linear operations cannot undo this. -/
theorem eval_insert_eq_zero (r : A →₀ K) (selected : A → Prop)
    (f : A → K) (hzero : ∀ a, ¬ selected a → f a = 0)
    (hmiss : ∀ a ∈ r.support, ¬ selected a) : eval r f = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  change r a * f a = 0
  rw [hzero a (hmiss a ha), mul_zero]

/-- Over a nontrivial field, finite rows are determined by configuration
evaluation. In particular, functional death equals empty true support. -/
theorem eq_zero_of_eval_zero (r : A →₀ K) (h : ∀ f : A → K, eval r f = 0) : r = 0 := by
  classical
  ext a
  have ha := h (Pi.single a 1)
  simpa [eval, Finsupp.sum, Pi.single_apply] using ha

theorem support_nonempty_iff (r : A →₀ K) :
    r.support.Nonempty ↔ ∃ f : A → K, eval r f ≠ 0 := by
  classical
  constructor
  · intro hr
    by_contra h
    have hz : r = 0 := eq_zero_of_eval_zero r (by simpa using h)
    simpa [hz] using hr
  · rintro ⟨f, hf⟩
    by_contra h
    have hs : r.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : r = 0 := Finsupp.support_eq_empty.mp hs
    exact hf (hz ▸ eval_zero f)

/-- Iterated sparse rows are the rows of powers of the actual operator. -/
def iterateRows (rows : A → A →₀ K) : ℕ → A → A →₀ K
  | 0, a => Finsupp.single a 1
  | n + 1, a => compose (iterateRows rows n a) rows

theorem eval_iterateRows (rows : A → A →₀ K) (n : ℕ) (f : A → K) (a : A) :
    eval (iterateRows rows n a) f = ((operator rows : Module.End K (A → K)) ^ n) f a := by
  induction n generalizing f with
  | zero => simp [iterateRows, eval_single]
  | succ n ih =>
    rw [iterateRows, eval_compose]
    change eval (iterateRows rows n a) (operator rows f) = _
    rw [ih, pow_succ, Module.End.mul_apply]

theorem card_support_iterateRows_le (rows : A → A →₀ K) (R : ℕ)
    (hR : ∀ a, (rows a).support.card ≤ R) (n : ℕ) (a : A) :
    (iterateRows rows n a).support.card ≤ R ^ n := by
  induction n with
  | zero =>
    simpa only [iterateRows, pow_zero, Finset.card_singleton] using
      Finset.card_le_card (Finsupp.support_single_subset (a := a) (b := (1 : K)))
  | succ n ih =>
    exact (card_support_compose_le (iterateRows rows n a) rows R (fun b _ => hR b)).trans
      (by simpa only [pow_succ] using Nat.mul_le_mul_right R ih)

/-- The actual insertion of a selected input coordinate, and zero otherwise. -/
def insertion (selected : A → Option B) (f : B → K) (a : A) : K :=
  match selected a with
  | none => 0
  | some b => f b

def insertionRows (selected : A → Option B) (a : A) : B →₀ K :=
  match selected a with
  | none => 0
  | some b => Finsupp.single b 1

@[simp] theorem eval_insertionRows (selected : A → Option B) (f : B → K) (a : A) :
    eval (insertionRows selected a) f = insertion selected f a := by
  cases h : selected a <;> simp [insertionRows, insertion, h]

theorem card_support_insertionRows_le (selected : A → Option B) (a : A) :
    (insertionRows (K := K) selected a).support.card ≤ 1 := by
  cases h : selected a with
  | none => simp [insertionRows, h]
  | some b =>
    simpa only [insertionRows, h, Finset.card_singleton] using
      Finset.card_le_card (Finsupp.support_single_subset (a := b) (b := (1 : K)))

/-- Coordinate insertion never increases the true support bound. -/
theorem card_support_after_insertion (r : A →₀ K) (selected : A → Option B) :
    (compose r (insertionRows selected)).support.card ≤ r.support.card := by
  simpa using card_support_compose_le r (insertionRows selected) 1
    (fun a _ => card_support_insertionRows_le selected a)

/-- A surviving row after insertion must have encountered a selected site.
This statement concerns exact coefficients, so it also handles cancellation. -/
theorem insertion_survival_requires_selection (r : A →₀ K) (selected : A → Option B)
    (halive : compose r (insertionRows selected) ≠ 0) :
    ∃ a ∈ r.support, selected a ≠ none := by
  by_contra h
  apply halive
  apply Finset.sum_eq_zero
  intro a ha
  have hn : selected a = none := by simpa using fun hs => h ⟨a, ha, hs⟩
  simp [insertionRows, hn]

end SparseRows
end BernoulliIso
