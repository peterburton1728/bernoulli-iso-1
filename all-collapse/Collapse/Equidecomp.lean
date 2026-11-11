module

public import Collapse.LocalSpace

/-!
# Equidecompositions

An equidecomposition is given by its pieces: countably many
measurable pieces of the source, each moved by one group element.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Collapse

/-- A piecewise equidecomposition of the set with levels `A j` onto the set with levels `B j'`.
`piece g j j'` is the part of `A j` which is moved by `g` into `B j'`. -/
structure Equidecomp (Λ : Type) {X J J' : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X]
    (A : J → Set X) (B : J' → Set X) where
  piece : Λ → J → J' → Set X
  measurable_piece : ∀ g j j', MeasurableSet (piece g j j')
  piece_subset : ∀ g j j', piece g j j' ⊆ A j
  /-- The pieces partition every level of the source. -/
  existsUnique_piece : ∀ j, ∀ x ∈ A j, ∃! p : Λ × J', x ∈ piece p.1 j p.2
  mapsTo : ∀ g j j', ∀ x ∈ piece g j j', g • x ∈ B j'
  /-- The images of the pieces partition every level of the target. -/
  existsUnique_source : ∀ j', ∀ y ∈ B j', ∃! q : Λ × J, q.1⁻¹ • y ∈ piece q.1 q.2 j'

namespace Equidecomp

variable {Λ X K : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
  [Ring K] [MeasurableSpace K] [DiscreteCoeff K] {J J' : Type}

section Aux

variable {A : J → Set X} {B : J' → Set X}

/-- The relation of an equidecomposition: `a = (x, j)` lies in `piece g j j'` and
`b = (g • x, j')`. -/
def Rel (E : Equidecomp Λ A B) (b : X × J') (a : X × J) : Prop :=
  ∃ g : Λ, a.1 ∈ E.piece g a.2 b.2 ∧ b.1 = g • a.1

theorem Rel.mem_A {E : Equidecomp Λ A B} {b : X × J'} {a : X × J} (h : E.Rel b a) :
    a.1 ∈ A a.2 := by
  obtain ⟨g, hx, -⟩ := h; exact E.piece_subset _ _ _ hx

theorem Rel.mem_B {E : Equidecomp Λ A B} {b : X × J'} {a : X × J} (h : E.Rel b a) :
    b.1 ∈ B b.2 := by
  obtain ⟨g, hx, hy⟩ := h; rw [hy]; exact E.mapsTo _ _ _ _ hx

theorem Rel.left_unique {E : Equidecomp Λ A B} {b : X × J'} {a a' : X × J} (h : E.Rel b a)
    (h' : E.Rel b a') : a = a' := by
  have hB := h.mem_B
  obtain ⟨g, hx, hy⟩ := h
  obtain ⟨g', hx', hy'⟩ := h'
  have e := (E.existsUnique_source b.2 b.1 hB).unique (y₁ := (g, a.2)) (y₂ := (g', a'.2))
    (show g⁻¹ • b.1 ∈ E.piece g a.2 b.2 by rw [hy, inv_smul_smul]; exact hx)
    (show g'⁻¹ • b.1 ∈ E.piece g' a'.2 b.2 by rw [hy', inv_smul_smul]; exact hx')
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, e2⟩ := e
  refine Prod.ext ?_ e2
  have := congrArg (g⁻¹ • ·) (hy.symm.trans hy')
  simpa using this

theorem Rel.right_unique {E : Equidecomp Λ A B} {b b' : X × J'} {a : X × J} (h : E.Rel b a)
    (h' : E.Rel b' a) : b = b' := by
  obtain ⟨g, hx, hy⟩ := h
  obtain ⟨g', hx', hy'⟩ := h'
  have e := (E.existsUnique_piece a.2 a.1 (E.piece_subset _ _ _ hx)).unique
    (y₁ := (g, b.2)) (y₂ := (g', b'.2)) hx hx'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, e2⟩ := e
  exact Prod.ext (hy.trans hy'.symm) e2

theorem exists_rel_of_mem_A (E : Equidecomp Λ A B) {a : X × J} (ha : a.1 ∈ A a.2) :
    ∃ b, E.Rel b a := by
  obtain ⟨⟨g, j'⟩, hp, -⟩ := E.existsUnique_piece a.2 a.1 ha
  exact ⟨(g • a.1, j'), g, hp, rfl⟩

theorem exists_rel_of_mem_B (E : Equidecomp Λ A B) {b : X × J'} (hb : b.1 ∈ B b.2) :
    ∃ a, E.Rel b a := by
  obtain ⟨⟨g, j⟩, hq, -⟩ := E.existsUnique_source b.2 b.1 hb
  exact ⟨(g⁻¹ • b.1, j), g, hq, (smul_inv_smul g b.1).symm⟩

end Aux

theorem of_ite_ne_zero {p : Prop} [Decidable p] (h : (if p then (1 : K) else 0) ≠ 0) : p := by
  by_contra hn; exact h (ite_eq_right hn)

open Classical in
/-- The kernel with entry `1` exactly on a relation which is a partial bijection. -/
noncomputable def relKernel (R : X × J' → X × J → Prop)
    (hrel : ∀ b a, R b a → b.1 ∈ MulAction.orbit Λ a.1)
    (hl : ∀ b a a', R b a → R b a' → a = a') (hr : ∀ b b' a, R b a → R b' a → b = b')
    (hm : ∀ (g : Λ) j' j, MeasurableSet {x : X | R (x, j') (g • x, j)}) :
    LKernel Λ X K J J' where
  toFun b a := if R b a then 1 else 0
  rel b a h := hrel b a (of_ite_ne_zero h)
  rowFinite b := Set.Subsingleton.finite fun a ha a' ha' =>
    hl b a a' (of_ite_ne_zero ha) (of_ite_ne_zero ha')
  colFinite a := Set.Subsingleton.finite fun b hb b' hb' =>
    hr b b' a (of_ite_ne_zero hb) (of_ite_ne_zero hb')
  measurable g j' j := Measurable.ite (hm g j' j) measurable_const measurable_const

open Classical in
theorem comp_toFun_ite [Countable J'] {J₂ : Type} {d : LKernel Λ X K J' J₂}
    {e : LKernel Λ X K J J'} (S : X × J₂ → X × J' → Prop) (R : X × J' → X × J → Prop)
    (hd : ∀ z b, d.toFun z b = if S z b then 1 else 0)
    (he : ∀ b a, e.toFun b a = if R b a then 1 else 0)
    (hu : ∀ z b b' a, S z b → R b a → S z b' → R b' a → b = b') (z : X × J₂) (a : X × J) :
    (d.comp e).toFun z a = if ∃ b, S z b ∧ R b a then 1 else 0 := by
  rw [LKernel.comp_toFun]
  by_cases h : ∃ b, S z b ∧ R b a
  · obtain ⟨b, hS, hR⟩ := h
    rw [finsum_eq_single _ b fun b' hb' => ?_, hd, he, ite_eq_left hS, ite_eq_left hR,
      ite_eq_left ⟨b, hS, hR⟩, mul_one]
    rw [hd, he]
    by_cases hS' : S z b'
    · rw [ite_eq_left hS', ite_eq_right fun hR' => hb' (hu z b' b a hS' hR' hS hR), mul_zero]
    · rw [ite_eq_right hS', zero_mul]
  · rw [ite_eq_right h, finsum_eq_zero_of_forall_eq_zero fun b => ?_]
    rw [hd, he]
    by_cases hS' : S z b
    · rw [ite_eq_left hS', ite_eq_right fun hR' => h ⟨b, hS', hR'⟩, mul_zero]
    · rw [ite_eq_right hS', zero_mul]

theorem comp_diag_of [Countable J] {A : J → Set X} (hA : ∀ j, MeasurableSet (A j))
    (e : LKernel Λ X K J J') (h : ∀ b a, e.toFun b a ≠ 0 → a.1 ∈ A a.2) :
    e.comp (LKernel.diag A hA) = e := by
  ext b a
  rw [LKernel.comp_toFun, finsum_eq_single _ a fun a' ha' => by
    rw [LKernel.diag_toFun, ite_eq_right fun hh => ha' hh.1, mul_zero], LKernel.diag_toFun]
  by_cases ha : a.1 ∈ A a.2
  · rw [ite_eq_left ⟨rfl, ha⟩, mul_one]
  · rw [ite_eq_right fun hh => ha hh.2, mul_zero]
    by_contra hne; exact ha (h b a (Ne.symm hne))

theorem diag_comp_of [Countable J'] {B : J' → Set X} (hB : ∀ j, MeasurableSet (B j))
    (e : LKernel Λ X K J J') (h : ∀ b a, e.toFun b a ≠ 0 → b.1 ∈ B b.2) :
    (LKernel.diag B hB).comp e = e := by
  ext b a
  rw [LKernel.comp_toFun, finsum_eq_single _ b fun b' hb' => by
    rw [LKernel.diag_toFun, ite_eq_right fun hh => hb' hh.1.symm, zero_mul], LKernel.diag_toFun]
  by_cases hb : b.1 ∈ B b.2
  · rw [ite_eq_left ⟨rfl, hb⟩, one_mul]
  · rw [ite_eq_right fun hh => hb hh.2, zero_mul]
    by_contra hne; exact hb (h b a (Ne.symm hne))

/-- Equidecomposable sets have isomorphic local spaces. -/
theorem toClass_eq [Countable J] [Countable J'] {A : J → Set X} {B : J' → Set X}
    (E : Equidecomp Λ A B) (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j)) :
    LocalSpace.toClass (LocalSpace.ofSet (Λ := Λ) (K := K) A hA) =
      LocalSpace.toClass (LocalSpace.ofSet B hB) := by
  classical
  have hmc : ∀ (g : Λ) (j' : J') (j : J), MeasurableSet {x : X | E.Rel (x, j') (g • x, j)} := by
    intro g j' j
    have : {x : X | E.Rel (x, j') (g • x, j)} = (fun x => g • x) ⁻¹' E.piece g⁻¹ j j' := by
      ext x
      constructor
      · rintro ⟨h, hx, he⟩
        have he' : x = h • g • x := he
        have h1 : h * g = 1 := BorelFree.free _ x (by rw [mul_smul]; exact he'.symm)
        rw [eq_inv_of_mul_eq_one_left h1] at hx
        exact hx
      · intro hx
        exact ⟨g⁻¹, hx, (inv_smul_smul g x).symm⟩
    rw [this]
    exact BorelFree.measurable_smul g (E.measurable_piece _ _ _)
  have hmc' : ∀ (g : Λ) (j' : J) (j : J'), MeasurableSet {x : X | E.Rel (g • x, j) (x, j')} := by
    intro g j' j
    have : {x : X | E.Rel (g • x, j) (x, j')} = E.piece g j' j := by
      ext x
      constructor
      · rintro ⟨h, hx, he⟩
        have he' : g • x = h • x := he
        have h1 : h⁻¹ * g = 1 := BorelFree.free _ x (by rw [mul_smul, he', inv_smul_smul])
        rw [inv_mul_eq_one.1 h1] at hx
        exact hx
      · intro hx; exact ⟨g, hx, rfl⟩
    rw [this]; exact E.measurable_piece _ _ _
  let c : LKernel Λ X K J J' := relKernel E.Rel
    (fun b a h => by obtain ⟨g, -, hy⟩ := h; rw [hy]; exact MulAction.mem_orbit _ _)
    (fun _ _ _ h h' => h.left_unique h') (fun _ _ _ h h' => h.right_unique h') hmc
  let c' : LKernel Λ X K J' J := relKernel (fun a b => E.Rel b a)
    (fun a b h => by
      obtain ⟨g, -, hy⟩ := h
      exact MulAction.mem_orbit_iff.2 ⟨g⁻¹, by rw [hy, inv_smul_smul]⟩)
    (fun _ _ _ h h' => h.right_unique h') (fun _ _ _ h h' => h.left_unique h') hmc'
  have hc : ∀ b a, c.toFun b a = if E.Rel b a then 1 else 0 := fun _ _ => rfl
  have hc' : ∀ a b, c'.toFun a b = if E.Rel b a then 1 else 0 := fun _ _ => rfl
  refine LocalSpace.toClass_eq_iff.2
    ⟨{ c := c, c' := c', c_mor := ?_, c'_mor := ?_, left := ?_, right := ?_ }⟩
  · show (LKernel.diag B hB).comp (c.comp (LKernel.diag A hA)) = c
    rw [comp_diag_of hA c fun b a h => (of_ite_ne_zero h : E.Rel b a).mem_A,
      diag_comp_of hB c fun b a h => (of_ite_ne_zero h : E.Rel b a).mem_B]
  · show (LKernel.diag A hA).comp (c'.comp (LKernel.diag B hB)) = c'
    rw [comp_diag_of hB c' fun a b h => (of_ite_ne_zero h : E.Rel b a).mem_B,
      diag_comp_of hA c' fun a b h => (of_ite_ne_zero h : E.Rel b a).mem_A]
  · show c'.comp c = LKernel.diag A hA
    ext a' a
    rw [comp_toFun_ite _ _ hc' hc (fun _ _ _ _ _ h _ h' => h.right_unique h'),
      LKernel.diag_toFun]
    refine if_congr ⟨fun ⟨b, h1, h2⟩ => ⟨h1.left_unique h2, h2.mem_A⟩, fun ⟨h1, h2⟩ => ?_⟩ rfl rfl
    subst h1
    obtain ⟨b, hb⟩ := E.exists_rel_of_mem_A h2
    exact ⟨b, hb, hb⟩
  · show c.comp c' = LKernel.diag B hB
    ext b' b
    rw [comp_toFun_ite _ _ hc hc' (fun _ _ _ _ _ h _ h' => h.left_unique h'),
      LKernel.diag_toFun]
    refine if_congr ⟨fun ⟨a, h1, h2⟩ => ⟨h1.right_unique h2, h2.mem_B⟩, fun ⟨h1, h2⟩ => ?_⟩ rfl rfl
    subst h1
    obtain ⟨a, ha⟩ := E.exists_rel_of_mem_B h2
    exact ⟨a, ha, ha⟩

/-- An equidecomposition restricts to an invariant set. -/
def restrict {A : J → Set X} {B : J' → Set X} (E : Equidecomp Λ A B) (U : Set X)
    (hU : MeasurableSet U) (hinv : ∀ (g : Λ) (x : X), x ∈ U → g • x ∈ U) :
    Equidecomp Λ (fun j => A j ∩ U) (fun j' => B j' ∩ U) where
  piece g j j' := E.piece g j j' ∩ U
  measurable_piece g j j' := (E.measurable_piece g j j').inter hU
  piece_subset g j j' := fun x hx => ⟨E.piece_subset g j j' hx.1, hx.2⟩
  existsUnique_piece j x hx := by
    obtain ⟨p, hp, hu⟩ := E.existsUnique_piece j x hx.1
    exact ⟨p, ⟨hp, hx.2⟩, fun q hq => hu q hq.1⟩
  mapsTo g j j' x hx := ⟨E.mapsTo g j j' x hx.1, hinv g x hx.2⟩
  existsUnique_source j' y hy := by
    obtain ⟨q, hq, hu⟩ := E.existsUnique_source j' y hy.1
    exact ⟨q, ⟨hq, hinv _ y hy.2⟩, fun q' hq' => hu q' hq'.1⟩

end Equidecomp

end Collapse
