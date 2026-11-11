module

public import Collapse.KernelSigma
public import Collapse.SigmaMonoid

/-!
# Local spaces and their monoid of isomorphism classes

A local space is a
countable index type `J` with an idempotent kernel on `X × J`. A set, given by its levels
`A j ⊆ X`, is the local space of the kernel `δ_A`. Isomorphism classes of local spaces, with
countable sums, form a `SigmaMonoid`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Collapse

/-- A local space `(A, e)`: here the set `A` is implicit in the idempotent kernel `e`. -/
structure LocalSpace (Λ X K : Type) [Group Λ] [MulAction Λ X] [MeasurableSpace X]
    [BorelFree Λ X] [Ring K] [MeasurableSpace K] [DiscreteCoeff K] where
  J : Type
  [countableJ : Countable J]
  e : LKernel Λ X K J J
  idem : e.comp e = e

attribute [instance] LocalSpace.countableJ

namespace LocalSpace

variable {Λ X K : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
  [Ring K] [MeasurableSpace K] [DiscreteCoeff K]

/-- An isomorphism of local spaces: morphisms `c`, `c'` with `c' * c = e` and `c * c' = e'`. -/
structure Iso (W W' : LocalSpace Λ X K) where
  c : LKernel Λ X K W.J W'.J
  c' : LKernel Λ X K W'.J W.J
  c_mor : W'.e.comp (c.comp W.e) = c
  c'_mor : W.e.comp (c'.comp W'.e) = c'
  left : c'.comp c = W.e
  right : c.comp c' = W'.e

theorem mor_left {J J' : Type} [Countable J] [Countable J'] {e' : LKernel Λ X K J' J'}
    {c : LKernel Λ X K J J'} {e : LKernel Λ X K J J} (he' : e'.comp e' = e')
    (h : e'.comp (c.comp e) = c) : e'.comp c = c := by
  rw [← h, ← LKernel.comp_assoc, he']

theorem mor_right {J J' : Type} [Countable J] [Countable J'] {e' : LKernel Λ X K J' J'}
    {c : LKernel Λ X K J J'} {e : LKernel Λ X K J J} (he : e.comp e = e)
    (h : e'.comp (c.comp e) = c) : c.comp e = c := by
  rw [← h, LKernel.comp_assoc, LKernel.comp_assoc, he]

noncomputable def Iso.refl (W : LocalSpace Λ X K) : Iso W W where
  c := W.e
  c' := W.e
  c_mor := by rw [W.idem, W.idem]
  c'_mor := by rw [W.idem, W.idem]
  left := W.idem
  right := W.idem

noncomputable def Iso.symm {W W' : LocalSpace Λ X K} (i : Iso W W') : Iso W' W where
  c := i.c'
  c' := i.c
  c_mor := i.c'_mor
  c'_mor := i.c_mor
  left := i.right
  right := i.left

noncomputable def Iso.trans {W W' W'' : LocalSpace Λ X K} (i : Iso W W') (i' : Iso W' W'') :
    Iso W W'' where
  c := i'.c.comp i.c
  c' := i.c'.comp i'.c'
  c_mor := by
    rw [LKernel.comp_assoc, mor_right W.idem i.c_mor, ← LKernel.comp_assoc, mor_left W''.idem i'.c_mor]
  c'_mor := by
    rw [LKernel.comp_assoc, mor_right W''.idem i'.c'_mor, ← LKernel.comp_assoc,
      mor_left W.idem i.c'_mor]
  left := by
    rw [LKernel.comp_assoc, ← LKernel.comp_assoc i'.c' i'.c i.c, i'.left, mor_left W'.idem i.c_mor,
      i.left]
  right := by
    rw [LKernel.comp_assoc, ← LKernel.comp_assoc i.c i.c' i'.c', i.right,
      mor_left W'.idem i'.c'_mor, i'.right]

/-- Isomorphism of local spaces, as an equivalence relation. -/
instance setoid : Setoid (LocalSpace Λ X K) where
  r W W' := Nonempty (Iso W W')
  iseqv := ⟨fun W => ⟨Iso.refl W⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨i'⟩ => ⟨i.trans i'⟩⟩

/-- The countable sum of local spaces, on the disjoint union of the index types. -/
noncomputable def sum {ι : Type} [Countable ι] (W : ι → LocalSpace Λ X K) : LocalSpace Λ X K where
  J := Σ i, (W i).J
  e := LKernel.sigma (fun i => (W i).e)
  idem := by
    rw [LKernel.sigma_comp_sigma]; exact congrArg LKernel.sigma (funext fun i => (W i).idem)

/-- The local space `(A)` of a set with levels `A j`. -/
noncomputable def ofSet {J : Type} [Countable J] (A : J → Set X) (hA : ∀ j, MeasurableSet (A j)) :
    LocalSpace Λ X K where
  J := J
  e := LKernel.diag A hA
  idem := by rw [LKernel.diag_comp_diag]; simp only [Set.inter_self]

/-- The local space `(A)` of a subset of `X`. -/
noncomputable def single (A : Set X) (hA : MeasurableSet A) : LocalSpace Λ X K :=
  ofSet (fun _ : Unit => A) (fun _ => hA)

theorem sum_e {ι : Type} [Countable ι] (W : ι → LocalSpace Λ X K) :
    (sum W).e = LKernel.sigma (fun i => (W i).e) := rfl

theorem ofSet_e {J : Type} [Countable J] (A : J → Set X) (hA : ∀ j, MeasurableSet (A j)) :
    (ofSet (Λ := Λ) (K := K) A hA).e = LKernel.diag A hA := rfl

theorem comp_ofEquiv_toFun {J J' J₂ : Type} [Countable J'] (d : LKernel Λ X K J' J₂) (ε : J ≃ J')
    (z : X × J₂) (a : X × J) :
    (d.comp (LKernel.ofEquiv ε)).toFun z a = d.toFun z (a.1, ε a.2) := by
  rw [LKernel.comp_toFun, finsum_eq_single _ (a.1, ε a.2) fun b hb => by
    rw [LKernel.ofEquiv_toFun, ite_eq_right fun hh => hb (Prod.ext hh.1 hh.2), mul_zero]]
  rw [LKernel.ofEquiv_toFun, ite_eq_left ⟨rfl, rfl⟩, mul_one]

theorem ofEquiv_comp_toFun {J J' J₂ : Type} [Countable J'] (d : LKernel Λ X K J J') (ε : J' ≃ J₂)
    (z : X × J₂) (a : X × J) :
    ((LKernel.ofEquiv ε).comp d).toFun z a = d.toFun (z.1, ε.symm z.2) a := by
  rw [LKernel.comp_toFun, finsum_eq_single _ (z.1, ε.symm z.2) fun b hb => by
    rw [LKernel.ofEquiv_toFun, ite_eq_right fun hh => hb (Prod.ext hh.1.symm
      (by rw [hh.2, Equiv.symm_apply_apply])), zero_mul]]
  rw [LKernel.ofEquiv_toFun, ite_eq_left ⟨rfl, by simp⟩, one_mul]

theorem intertwine {J J' : Type} [Countable J] [Countable J'] (d' : LKernel Λ X K J' J')
    (d : LKernel Λ X K J J) (ε : J ≃ J')
    (h : ∀ x j' y j, d'.toFun (x, ε j') (y, ε j) = d.toFun (x, j') (y, j)) :
    d'.comp (LKernel.ofEquiv ε) = (LKernel.ofEquiv ε).comp d := by
  ext ⟨x, j'⟩ ⟨y, j⟩
  rw [comp_ofEquiv_toFun, ofEquiv_comp_toFun, ← h, Equiv.apply_symm_apply]

/-- A local space transported along a bijection of index types is isomorphic to it. -/
theorem equiv_of_transport {W W' : LocalSpace Λ X K} (ε : W.J ≃ W'.J)
    (h : ∀ x j' y j, W'.e.toFun (x, ε j') (y, ε j) = W.e.toFun (x, j') (y, j)) : W ≈ W' := by
  have h1 := intertwine W'.e W.e ε h
  have h2 := intertwine W.e W'.e ε.symm fun x j' y j => by rw [← h]; simp
  have hQP : (LKernel.ofEquiv (Λ := Λ) (X := X) (K := K) ε.symm).comp (LKernel.ofEquiv ε) =
      LKernel.id W.J := by
    rw [LKernel.ofEquiv_comp_ofEquiv, Equiv.self_trans_symm, LKernel.ofEquiv_refl]
  have hPQ : (LKernel.ofEquiv (Λ := Λ) (X := X) (K := K) ε).comp (LKernel.ofEquiv ε.symm) =
      LKernel.id W'.J := by
    rw [LKernel.ofEquiv_comp_ofEquiv, Equiv.symm_trans_self, LKernel.ofEquiv_refl]
  have hc : W'.e.comp ((LKernel.ofEquiv ε).comp W.e) = (LKernel.ofEquiv ε).comp W.e := by
    rw [← LKernel.comp_assoc, h1, LKernel.comp_assoc, W.idem]
  have hc' : W.e.comp ((LKernel.ofEquiv ε.symm).comp W'.e) = (LKernel.ofEquiv ε.symm).comp W'.e := by
    rw [← LKernel.comp_assoc, h2, LKernel.comp_assoc, W'.idem]
  refine ⟨⟨(LKernel.ofEquiv ε).comp W.e, (LKernel.ofEquiv ε.symm).comp W'.e, ?_, ?_, ?_, ?_⟩⟩
  · rw [LKernel.comp_assoc, W.idem, hc]
  · rw [LKernel.comp_assoc, W'.idem, hc']
  · rw [LKernel.comp_assoc, hc, ← LKernel.comp_assoc, hQP, LKernel.id_comp]
  · rw [LKernel.comp_assoc, hc', ← LKernel.comp_assoc, hPQ, LKernel.id_comp]

theorem finsum_sigma_single {ι : Type} {T : ι → Type} (g : X × (Σ i, T i) → K) (i0 : ι)
    (hg : ∀ b : X × (Σ i, T i), b.2.1 ≠ i0 → g b = 0) :
    ∑ᶠ b, g b = ∑ᶠ y : X × T i0, g (y.1, ⟨i0, y.2⟩) := by
  refine LKernel.finsum_eq_finsum_comp (fun y : X × T i0 => (y.1, (⟨i0, y.2⟩ : Σ i, T i))) ?_ ?_
  · rintro ⟨y, l⟩ ⟨y', l'⟩ h
    simp only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    rw [h.1, h.2]
  · rintro ⟨y, i, l⟩ hb
    by_cases h : i = i0
    · subst h; exact ⟨(y, l), rfl⟩
    · exact (hb (hg _ h)).elim

theorem sigma_comp_toFun {ι J : Type} {J' J₂ : ι → Type} {_ : Countable (Σ i, J' i)}
    (f : ∀ i, LKernel Λ X K (J' i) (J₂ i)) (M : LKernel Λ X K J (Σ i, J' i)) (x : X) (i : ι)
    (j : J₂ i) (a : X × J) :
    ((LKernel.sigma f).comp M).toFun (x, ⟨i, j⟩) a =
      ∑ᶠ y : X × J' i, (f i).toFun (x, j) y * M.toFun (y.1, ⟨i, y.2⟩) a := by
  rw [LKernel.comp_toFun, finsum_sigma_single _ i fun b hb => ?_]
  · simp only [LKernel.sigma_toFun_mk]
  · rcases b with ⟨y, i', l⟩
    rw [LKernel.sigma_toFun_ne f _ _ _ _ hb, zero_mul]

theorem comp_sigma_toFun {ι J₂ : Type} {J J' : ι → Type} {_ : Countable (Σ i, J' i)}
    (M : LKernel Λ X K (Σ i, J' i) J₂) (f : ∀ i, LKernel Λ X K (J i) (J' i)) (z : X × J₂) (x : X)
    (i : ι) (j : J i) :
    (M.comp (LKernel.sigma f)).toFun z (x, ⟨i, j⟩) =
      ∑ᶠ y : X × J' i, M.toFun z (y.1, ⟨i, y.2⟩) * (f i).toFun y (x, j) := by
  rw [LKernel.comp_toFun, finsum_sigma_single _ i fun b hb => ?_]
  · simp only [LKernel.sigma_toFun_mk]
  · rcases b with ⟨y, i', l⟩
    rw [LKernel.sigma_toFun_ne f _ _ _ _ (Ne.symm hb), mul_zero]

theorem finsum_bool_split {T : Bool → Type} (g : X × (Σ i, T i) → K)
    (hg : (Function.support g).Finite) :
    ∑ᶠ b, g b = ∑ᶠ y : X × T false, g (y.1, ⟨false, y.2⟩) +
      ∑ᶠ y : X × T true, g (y.1, ⟨true, y.2⟩) := by
  have e1 : ∀ b : X × (Σ i, T i),
      g b = (if b.2.1 = false then g b else 0) + (if b.2.1 = true then g b else 0) := by
    rintro ⟨x, i, t⟩; cases i <;> simp
  rw [finsum_congr e1, finsum_add_distrib (hg.subset fun b hb h0 => hb (by simp [h0]))
    (hg.subset fun b hb h0 => hb (by simp [h0])),
    finsum_sigma_single (fun b => if b.2.1 = false then g b else 0) false (fun b hb => ite_eq_right hb),
    finsum_sigma_single (fun b => if b.2.1 = true then g b else 0) true (fun b hb => ite_eq_right hb)]
  simp

/-- The kernel into a sum with blocks `d i`. -/
noncomputable def colBlock {ι J : Type} {J' : ι → Type} (d : ∀ i, LKernel Λ X K J (J' i))
    (hfin : ∀ a, {i | ∃ b, (d i).toFun b a ≠ 0}.Finite) : LKernel Λ X K J (Σ i, J' i) where
  toFun b a := (d b.2.1).toFun (b.1, b.2.2) a
  rel b a h := (d b.2.1).rel _ a h
  rowFinite b := (d b.2.1).rowFinite (b.1, b.2.2)
  colFinite a := ((hfin a).biUnion fun i _ => ((d i).colFinite a).image
      fun p : X × J' i => (p.1, (⟨i, p.2⟩ : Σ i, J' i))).subset (by
    rintro ⟨y, i, l⟩ h
    exact Set.mem_biUnion (x := i) (⟨(y, l), h⟩ : ∃ b, (d i).toFun b a ≠ 0) ⟨(y, l), h, rfl⟩)
  measurable g j' j := (d j'.1).measurable g j'.2 j

/-- The kernel out of a sum with blocks `d i`. -/
noncomputable def rowBlock {ι J' : Type} {J : ι → Type} (d : ∀ i, LKernel Λ X K (J i) J')
    (hfin : ∀ b, {i | ∃ a, (d i).toFun b a ≠ 0}.Finite) : LKernel Λ X K (Σ i, J i) J' where
  toFun b a := (d a.2.1).toFun b (a.1, a.2.2)
  rel b a h := (d a.2.1).rel b _ h
  rowFinite b := ((hfin b).biUnion fun i _ => ((d i).rowFinite b).image
      fun p : X × J i => (p.1, (⟨i, p.2⟩ : Σ i, J i))).subset (by
    rintro ⟨y, i, l⟩ h
    exact Set.mem_biUnion (x := i) (⟨(y, l), h⟩ : ∃ a, (d i).toFun b a ≠ 0) ⟨(y, l), h, rfl⟩)
  colFinite a := (d a.2.1).colFinite (a.1, a.2.2)
  measurable g j' j := (d j.1).measurable g j' j.2

theorem rowBlock_comp_colBlock_bool {J J₂ : Type} {T : Bool → Type} [∀ i, Countable (T i)]
    {_ : Countable (Σ i, T i)}
    (d' : ∀ i, LKernel Λ X K (T i) J₂) (d : ∀ i, LKernel Λ X K J (T i))
    (h' : ∀ b, {i | ∃ a, (d' i).toFun b a ≠ 0}.Finite)
    (h : ∀ a, {i | ∃ b, (d i).toFun b a ≠ 0}.Finite) (z : X × J₂) (a : X × J) :
    ((rowBlock d' h').comp (colBlock d h)).toFun z a =
      ((d' false).comp (d false)).toFun z a + ((d' true).comp (d true)).toFun z a := by
  rw [LKernel.comp_toFun, finsum_bool_split (fun b => (rowBlock d' h').toFun z b *
    (colBlock d h).toFun b a) (((rowBlock d' h').rowFinite z).subset fun b hb =>
      left_ne_zero_of_mul hb)]
  rfl

theorem ofSet_equiv {J J' : Type} [Countable J] [Countable J'] (A : J → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (A' : J' → Set X) (hA' : ∀ j, MeasurableSet (A' j))
    (ε : J ≃ J') (h : ∀ j, A' (ε j) = A j) : ofSet (Λ := Λ) (K := K) A hA ≈ ofSet A' hA' :=
  equiv_of_transport (W := ofSet A hA) (W' := ofSet A' hA') ε fun x (j' : J) y (j : J) => by
    show (LKernel.diag A' hA').toFun (x, ε j') (y, ε j) = (LKernel.diag A hA).toFun (x, j') (y, j)
    classical
    simp [LKernel.diag_toFun, h]

theorem toFun_congr {J J' : Type} {c d : LKernel Λ X K J J'} (h : c = d) (b : X × J')
    (a : X × J) : c.toFun b a = d.toFun b a := by rw [h]

theorem diag_ne_zero {J : Type} {A : J → Set X} {hA : ∀ j, MeasurableSet (A j)} {b a : X × J}
    (h : (LKernel.diag (Λ := Λ) (K := K) A hA).toFun b a ≠ 0) : b = a ∧ a.1 ∈ A a.2 := by
  by_contra hc; exact h (by rw [LKernel.diag_toFun, ite_eq_right hc])

theorem sum_congr {ι : Type} [Countable ι] {W W' : ι → LocalSpace Λ X K}
    (h : ∀ i, W i ≈ W' i) : sum W ≈ sum W' := by
  have I : ∀ i, Iso (W i) (W' i) := fun i => Classical.choice (h i)
  refine ⟨⟨LKernel.sigma fun i => (I i).c, LKernel.sigma fun i => (I i).c', ?_, ?_, ?_, ?_⟩⟩
  · exact ((congrArg _ (LKernel.sigma_comp_sigma _ _)).trans (LKernel.sigma_comp_sigma _ _)).trans
      (congrArg LKernel.sigma (funext fun i => (I i).c_mor))
  · exact ((congrArg _ (LKernel.sigma_comp_sigma _ _)).trans (LKernel.sigma_comp_sigma _ _)).trans
      (congrArg LKernel.sigma (funext fun i => (I i).c'_mor))
  · exact (LKernel.sigma_comp_sigma _ _).trans (congrArg LKernel.sigma (funext fun i => (I i).left))
  · exact (LKernel.sigma_comp_sigma _ _).trans (congrArg LKernel.sigma (funext fun i => (I i).right))

theorem sum_unit (W : LocalSpace Λ X K) : sum (fun _ : Unit => W) ≈ W := by
  refine equiv_of_transport (W := sum fun _ : Unit => W) (W' := W)
    ⟨fun p => p.2, fun j => ⟨(), j⟩, fun _ => rfl, fun _ => rfl⟩ ?_
  rintro x ⟨⟨⟩, j'⟩ y ⟨⟨⟩, j⟩
  exact (LKernel.sigma_toFun_mk (fun _ : Unit => W.e) x y () j' j).symm

theorem sum_equiv {ι ι' : Type} [Countable ι] [Countable ι'] (e : ι' ≃ ι)
    (W : ι → LocalSpace Λ X K) : sum (fun i => W (e i)) ≈ sum W := by
  refine equiv_of_transport (W := sum fun i => W (e i)) (W' := sum W)
    (Equiv.sigmaCongrLeft (β := fun i => (W i).J) e) ?_
  rintro x ⟨a', j'⟩ y ⟨a, j⟩
  show (LKernel.sigma fun i => (W i).e).toFun (x, ⟨e a', j'⟩) (y, ⟨e a, j⟩) =
    (LKernel.sigma fun i => (W (e i)).e).toFun (x, ⟨a', j'⟩) (y, ⟨a, j⟩)
  by_cases ha : a = a'
  · subst ha; rw [LKernel.sigma_toFun_mk, LKernel.sigma_toFun_mk]
  · rw [LKernel.sigma_toFun_ne _ _ _ _ _ ha, LKernel.sigma_toFun_ne _ _ _ _ _ (e.injective.ne ha)]

theorem sum_sigma {ι : Type} {κ : ι → Type} [Countable ι] [∀ i, Countable (κ i)]
    (W : (i : ι) → κ i → LocalSpace Λ X K) :
    sum (fun p : Σ i, κ i => W p.1 p.2) ≈ sum (fun i => sum (W i)) := by
  refine equiv_of_transport (W := sum fun p : Σ i, κ i => W p.1 p.2)
    (W' := sum fun i => sum (W i)) (Equiv.sigmaAssoc fun i k => (W i k).J) ?_
  rintro x ⟨⟨i', k'⟩, j'⟩ y ⟨⟨i, k⟩, j⟩
  show (LKernel.sigma fun i => LKernel.sigma fun k => (W i k).e).toFun (x, ⟨i', k', j'⟩)
      (y, ⟨i, k, j⟩) =
    (LKernel.sigma fun p : Σ i, κ i => (W p.1 p.2).e).toFun (x, ⟨⟨i', k'⟩, j'⟩) (y, ⟨⟨i, k⟩, j⟩)
  by_cases hi : i = i'
  · subst hi
    by_cases hk : k = k'
    · subst hk; rw [LKernel.sigma_toFun_mk, LKernel.sigma_toFun_mk, LKernel.sigma_toFun_mk]
    · rw [LKernel.sigma_toFun_mk, LKernel.sigma_toFun_ne _ _ _ _ _ hk,
        LKernel.sigma_toFun_ne _ _ _ _ _ (fun hh => hk (eq_of_heq (Sigma.mk.inj_iff.1 hh).2))]
  · rw [LKernel.sigma_toFun_ne _ _ _ _ _ hi,
      LKernel.sigma_toFun_ne _ _ _ _ _ (fun hh => hi (congrArg Sigma.fst hh))]

end LocalSpace

end Collapse
