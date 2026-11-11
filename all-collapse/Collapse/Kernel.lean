module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Local kernels of a free Borel action

A countable group `Λ` acts freely on `X`
by measurable maps (`BorelFree`). A kernel is a matrix over the points of `X × J`, supported on
the orbit relation, with finite rows and columns, and measurable along every group element.
Such kernels are called local. No measure appears.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Collapse

/-- Standing assumptions on the action: `Λ` is countable and acts on `X` freely by measurable
maps. They are part of the type of kernels, so that every definition carries them. -/
class BorelFree (Λ X : Type) [Group Λ] [MulAction Λ X] [MeasurableSpace X] : Prop where
  countable : Countable Λ
  measurable_smul : ∀ g : Λ, Measurable fun x : X => g • x
  /-- No element other than `1` has a fixed point. -/
  free : ∀ (g : Λ) (x : X), g • x = x → g = 1

/-- Standing assumptions on the coefficients: countable, with every set measurable. -/
class DiscreteCoeff (K : Type) [MeasurableSpace K] : Prop where
  countable : Countable K
  discrete : ∀ s : Set K, MeasurableSet s

instance (priority := 100) DiscreteCoeff.toDiscreteMeasurableSpace (K : Type) [MeasurableSpace K]
    [DiscreteCoeff K] : DiscreteMeasurableSpace K :=
  ⟨DiscreteCoeff.discrete⟩

instance (priority := 100) DiscreteCoeff.toCountable (K : Type) [MeasurableSpace K]
    [DiscreteCoeff K] : Countable K :=
  DiscreteCoeff.countable

/-- A finite type with every set measurable satisfies the standing assumptions. -/
theorem DiscreteCoeff.of_finite (K : Type) [MeasurableSpace K] [Finite K]
    [DiscreteMeasurableSpace K] : DiscreteCoeff K :=
  ⟨inferInstance, fun _ => MeasurableSet.of_discrete⟩

/-- A local kernel from `X × J` to `X × J'`, written `c b a` for `b : X × J'` (the row) and
`a : X × J` (the column). It defines `(Λ_c f) b = ∑ a, c b a * f a`. -/
structure LKernel (Λ X K : Type) [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
    [Ring K] [MeasurableSpace K] [DiscreteCoeff K] (J J' : Type) where
  toFun : X × J' → X × J → K
  /-- Entries vanish outside the orbit relation. -/
  rel : ∀ b a, toFun b a ≠ 0 → b.1 ∈ MulAction.orbit Λ a.1
  rowFinite : ∀ b, {a | toFun b a ≠ 0}.Finite
  colFinite : ∀ a, {b | toFun b a ≠ 0}.Finite
  /-- Measurability. -/
  measurable : ∀ (g : Λ) (j' : J') (j : J), Measurable fun x : X => toFun (x, j') (g • x, j)

namespace LKernel

variable {Λ X K : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
  [Ring K] [MeasurableSpace K] [DiscreteCoeff K] {J J' J₂ J₃ : Type}

theorem ext' {c d : LKernel Λ X K J J'} (h : c.toFun = d.toFun) : c = d := by
  cases c; cases d; cases h; rfl

theorem ne_zero_of_map (op : K → K) (h0 : op 0 = 0) {k : K} (h : op k ≠ 0) : k ≠ 0 :=
  fun hk => h (by rw [hk, h0])

theorem ne_zero_or_of_map₂ (op : K → K → K) (h0 : op 0 0 = 0) {k l : K} (h : op k l ≠ 0) :
    k ≠ 0 ∨ l ≠ 0 := by
  by_contra hc; push Not at hc; exact h (by rw [hc.1, hc.2, h0])

theorem measurable_op₂ (op : K → K → K) {f g : X → K} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => op (f x) (g x) :=
  (measurable_of_countable (fun p : K × K => op p.1 p.2)).comp (hf.prodMk hg)

theorem exists_mul_ne_zero_of_finsum_ne_zero {ι : Type} {f g : ι → K}
    (h : ∑ᶠ i, f i * g i ≠ 0) : ∃ i, f i ≠ 0 ∧ g i ≠ 0 := by
  by_contra hn; push Not at hn
  exact h (finsum_eq_zero_of_forall_eq_zero fun i => by
    by_cases hf : f i = 0
    · rw [hf, zero_mul]
    · rw [hn i hf, mul_zero])

theorem measurable_finsum {ι : Type} [Countable ι] {F : ι → X → K} (hF : ∀ i, Measurable (F i))
    (hfin : ∀ x, (Function.support fun i => F i x).Finite) :
    Measurable fun x => ∑ᶠ i, F i x := by
  classical
  have : MeasurableAdd₂ K := ⟨measurable_of_countable _⟩
  refine measurable_to_countable' fun k => ?_
  have e : (fun x => ∑ᶠ i, F i x) ⁻¹' {k} = ⋃ T : Finset ι,
      ((⋂ i, ⋂ (_ : i ∉ T), F i ⁻¹' {0}) ∩ (fun x => ∑ i ∈ T, F i x) ⁻¹' {k}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · intro h
      refine ⟨(hfin x).toFinset, fun i hi => ?_, ?_⟩
      · by_contra h'; exact hi ((hfin x).mem_toFinset.2 h')
      · rw [← h]; exact (finsum_eq_sum_of_support_subset _ (by simp)).symm
    · rintro ⟨T, hT, h⟩
      rw [← h]; apply finsum_eq_sum_of_support_subset
      intro i hi; by_contra h'; exact hi (hT i h')
  rw [e]
  exact MeasurableSet.iUnion fun T => MeasurableSet.inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hF i (measurableSet_singleton 0))
    ((Finset.measurable_sum T fun i _ => hF i) (measurableSet_singleton k))

theorem finsum_eq_finsum_comp {α β : Type} {f : β → K} (e : α → β) (he : Function.Injective e)
    (h : Function.support f ⊆ Set.range e) : ∑ᶠ b, f b = ∑ᶠ a, f (e a) := by
  rw [← finsum_mem_univ f, finsum_mem_inter_support_eq' f Set.univ (Set.range e)
    fun x hx => ⟨fun _ => h hx, fun _ => trivial⟩, finsum_mem_range he]

theorem smul_prod_injective (x : X) :
    Function.Injective fun p : Λ × J => (p.1 • x, p.2) := by
  rintro ⟨g, j⟩ ⟨h, j'⟩ hgh
  simp only [Prod.mk.injEq] at hgh
  have : (h⁻¹ * g) • x = x := by rw [mul_smul, hgh.1, inv_smul_smul]
  have := BorelFree.free _ _ this
  rw [inv_mul_eq_one] at this
  rw [this, hgh.2]

@[ext] theorem ext {c d : LKernel Λ X K J J'} (h : ∀ b a, c.toFun b a = d.toFun b a) : c = d :=
  ext' (funext fun b => funext fun a => h b a)

instance : Zero (LKernel Λ X K J J') :=
  ⟨{ toFun := fun _ _ => 0
     rel := fun _ _ h => (h rfl).elim
     rowFinite := fun _ => Set.finite_empty.subset fun _ h => h rfl
     colFinite := fun _ => Set.finite_empty.subset fun _ h => h rfl
     measurable := fun _ _ _ => measurable_const }⟩

instance : Add (LKernel Λ X K J J') :=
  ⟨fun c d =>
    { toFun := fun b a => c.toFun b a + d.toFun b a
      rel := fun b a h => (ne_zero_or_of_map₂ (· + ·) (add_zero 0) h).elim (c.rel b a) (d.rel b a)
      rowFinite := fun b => ((c.rowFinite b).union (d.rowFinite b)).subset
        fun _ h => ne_zero_or_of_map₂ (· + ·) (add_zero 0) h
      colFinite := fun a => ((c.colFinite a).union (d.colFinite a)).subset
        fun _ h => ne_zero_or_of_map₂ (· + ·) (add_zero 0) h
      measurable := fun g j' j =>
        measurable_op₂ (· + ·) (c.measurable g j' j) (d.measurable g j' j) }⟩

instance : Neg (LKernel Λ X K J J') :=
  ⟨fun c =>
    { toFun := fun b a => -c.toFun b a
      rel := fun b a h => c.rel b a (ne_zero_of_map (fun k : K => -k) (neg_zero) h)
      rowFinite := fun b => (c.rowFinite b).subset fun _ h => ne_zero_of_map (fun k : K => -k) (neg_zero) h
      colFinite := fun a => (c.colFinite a).subset fun _ h => ne_zero_of_map (fun k : K => -k) (neg_zero) h
      measurable := fun g j' j => (measurable_of_countable (fun k : K => -k)).comp (c.measurable g j' j) }⟩

instance : Sub (LKernel Λ X K J J') :=
  ⟨fun c d =>
    { toFun := fun b a => c.toFun b a - d.toFun b a
      rel := fun b a h => (ne_zero_or_of_map₂ (· - ·) (sub_zero 0) h).elim (c.rel b a) (d.rel b a)
      rowFinite := fun b => ((c.rowFinite b).union (d.rowFinite b)).subset
        fun _ h => ne_zero_or_of_map₂ (· - ·) (sub_zero 0) h
      colFinite := fun a => ((c.colFinite a).union (d.colFinite a)).subset
        fun _ h => ne_zero_or_of_map₂ (· - ·) (sub_zero 0) h
      measurable := fun g j' j =>
        measurable_op₂ (· - ·) (c.measurable g j' j) (d.measurable g j' j) }⟩

instance : SMul ℕ (LKernel Λ X K J J') :=
  ⟨fun n c =>
    { toFun := fun b a => n • c.toFun b a
      rel := fun b a h => c.rel b a (ne_zero_of_map (fun k : K => n • k) (smul_zero n) h)
      rowFinite := fun b => (c.rowFinite b).subset fun _ h => ne_zero_of_map (fun k : K => n • k) (smul_zero n) h
      colFinite := fun a => (c.colFinite a).subset fun _ h => ne_zero_of_map (fun k : K => n • k) (smul_zero n) h
      measurable := fun g j' j => (measurable_of_countable (fun k : K => n • k)).comp (c.measurable g j' j) }⟩

instance : SMul ℤ (LKernel Λ X K J J') :=
  ⟨fun n c =>
    { toFun := fun b a => n • c.toFun b a
      rel := fun b a h => c.rel b a (ne_zero_of_map (fun k : K => n • k) (smul_zero n) h)
      rowFinite := fun b => (c.rowFinite b).subset fun _ h => ne_zero_of_map (fun k : K => n • k) (smul_zero n) h
      colFinite := fun a => (c.colFinite a).subset fun _ h => ne_zero_of_map (fun k : K => n • k) (smul_zero n) h
      measurable := fun g j' j => (measurable_of_countable (fun k : K => n • k)).comp (c.measurable g j' j) }⟩

@[simp] theorem zero_toFun (b : X × J') (a : X × J) : (0 : LKernel Λ X K J J').toFun b a = 0 :=
  rfl

@[simp] theorem add_toFun (c d : LKernel Λ X K J J') (b : X × J') (a : X × J) :
    (c + d).toFun b a = c.toFun b a + d.toFun b a := rfl

@[simp] theorem neg_toFun (c : LKernel Λ X K J J') (b : X × J') (a : X × J) :
    (-c).toFun b a = -c.toFun b a := rfl

@[simp] theorem sub_toFun (c d : LKernel Λ X K J J') (b : X × J') (a : X × J) :
    (c - d).toFun b a = c.toFun b a - d.toFun b a := rfl

instance : AddCommGroup (LKernel Λ X K J J') :=
  Function.Injective.addCommGroup (fun c : LKernel Λ X K J J' => c.toFun) (fun _ _ h => ext' h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Composition of kernels: `(c' * c) z a = ∑ b, c' z b * c b a`, a finite sum. -/
noncomputable def comp [Countable J'] (c' : LKernel Λ X K J' J₂) (c : LKernel Λ X K J J') :
    LKernel Λ X K J J₂ where
  toFun z a := ∑ᶠ b, c'.toFun z b * c.toFun b a
  rel z a h := by
    obtain ⟨b, h1, h2⟩ := exists_mul_ne_zero_of_finsum_ne_zero h
    obtain ⟨g, hg⟩ := c'.rel z b h1
    obtain ⟨g', hg'⟩ := c.rel b a h2
    exact ⟨g * g', by simp only [mul_smul, hg', hg]⟩
  rowFinite z := ((c'.rowFinite z).biUnion fun b _ => c.rowFinite b).subset fun a h => by
    obtain ⟨b, h1, h2⟩ := exists_mul_ne_zero_of_finsum_ne_zero h
    exact Set.mem_biUnion h1 h2
  colFinite a := ((c.colFinite a).biUnion fun b _ => c'.colFinite b).subset fun z h => by
    obtain ⟨b, h1, h2⟩ := exists_mul_ne_zero_of_finsum_ne_zero h
    exact Set.mem_biUnion h2 h1
  measurable g j₂ j := by
    have : Countable Λ := BorelFree.countable (X := X)
    have key : (fun x : X => ∑ᶠ b, c'.toFun (x, j₂) b * c.toFun b (g • x, j)) = fun x =>
        ∑ᶠ p : Λ × J', c'.toFun (x, j₂) (p.1 • x, p.2) * c.toFun (p.1 • x, p.2) (g • x, j) := by
      funext x
      refine finsum_eq_finsum_comp (fun p : Λ × J' => (p.1 • x, p.2)) (smul_prod_injective x)
        fun b hb => ?_
      obtain ⟨h, hh⟩ := c'.rel (x, j₂) b (left_ne_zero_of_mul hb)
      exact ⟨(h⁻¹, b.2), Prod.ext (show h⁻¹ • x = b.1 by rw [← show h • b.1 = x from hh, inv_smul_smul]) rfl⟩
    show Measurable fun x : X => ∑ᶠ b, c'.toFun (x, j₂) b * c.toFun b (g • x, j)
    rw [key]
    refine measurable_finsum (fun p => measurable_op₂ (· * ·) (c'.measurable p.1 j₂ p.2) ?_)
      fun x => ((c'.rowFinite (x, j₂)).preimage (smul_prod_injective x).injOn).subset
        fun p hp => left_ne_zero_of_mul hp
    have e : (fun x : X => c.toFun (p.1 • x, p.2) (g • x, j)) =
        (fun y => c.toFun (y, p.2) ((g * p.1⁻¹) • y, j)) ∘ fun x => p.1 • x := by
      funext x; simp only [Function.comp, mul_smul, inv_smul_smul]
    rw [e]
    exact (c.measurable _ _ _).comp (BorelFree.measurable_smul p.1)

open Classical in
/-- The kernel `δ_A` of a set, given by its levels `A j ⊆ X`. -/
noncomputable def diag (A : J → Set X) (hA : ∀ j, MeasurableSet (A j)) : LKernel Λ X K J J where
  toFun b a := if b = a ∧ a.1 ∈ A a.2 then 1 else 0
  rel b a h := by
    by_cases hh : b = a ∧ a.1 ∈ A a.2
    · rw [hh.1]; exact MulAction.mem_orbit_self _
    · exact (h (ite_eq_right hh)).elim
  rowFinite b := (Set.finite_singleton b).subset fun a ha => by
    by_contra h'; exact ha (ite_eq_right fun hh => h' hh.1.symm)
  colFinite a := (Set.finite_singleton a).subset fun b hb => by
    by_contra h'; exact hb (ite_eq_right fun hh => h' hh.1)
  measurable g j' j := by
    by_cases hg : g = 1 ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := hg
      simp only [one_smul, true_and]
      exact Measurable.ite (hA j') measurable_const measurable_const
    · have : ∀ x : X, ¬((x, j') = (g • x, j) ∧ g • x ∈ A j) := by
        rintro x ⟨hx, -⟩
        simp only [Prod.mk.injEq] at hx
        exact hg ⟨BorelFree.free g x hx.1.symm, hx.2⟩
      simp only [this, ite_false]
      exact measurable_const

open Classical in
theorem diag_toFun (A : J → Set X) (hA : ∀ j, MeasurableSet (A j)) (b a : X × J) :
    (diag (Λ := Λ) (K := K) A hA).toFun b a = if b = a ∧ a.1 ∈ A a.2 then 1 else 0 := rfl

/-- The identity kernel of `X × J`. -/
noncomputable def id (J : Type) : LKernel Λ X K J J :=
  diag (fun _ => Set.univ) (fun _ => MeasurableSet.univ)

theorem comp_toFun [Countable J'] (c' : LKernel Λ X K J' J₂) (c : LKernel Λ X K J J')
    (z : X × J₂) (a : X × J) : (c'.comp c).toFun z a = ∑ᶠ b, c'.toFun z b * c.toFun b a := rfl

theorem comp_assoc [Countable J'] [Countable J₂] (c₃ : LKernel Λ X K J₂ J₃)
    (c₂ : LKernel Λ X K J' J₂) (c : LKernel Λ X K J J') :
    (c₃.comp c₂).comp c = c₃.comp (c₂.comp c) := by
  classical
  refine ext fun z a => ?_
  simp only [comp_toFun]
  set S := (c₃.rowFinite z).toFinset
  set T := S.biUnion fun y => (c₂.rowFinite y).toFinset
  have hS : ∀ {y}, c₃.toFun z y ≠ 0 → y ∈ S := fun hy => (c₃.rowFinite z).mem_toFinset.2 hy
  have h1 : ∀ b, ∑ᶠ y, c₃.toFun z y * c₂.toFun y b = ∑ y ∈ S, c₃.toFun z y * c₂.toFun y b :=
    fun b => finsum_eq_sum_of_support_subset _ fun y hy => hS (left_ne_zero_of_mul hy)
  have hT : ∀ {y b}, y ∈ S → c₂.toFun y b ≠ 0 → b ∈ T := fun hy hb =>
    Finset.mem_biUnion.2 ⟨_, hy, (c₂.rowFinite _).mem_toFinset.2 hb⟩
  calc ∑ᶠ b, (∑ᶠ y, c₃.toFun z y * c₂.toFun y b) * c.toFun b a
      = ∑ b ∈ T, (∑ y ∈ S, c₃.toFun z y * c₂.toFun y b) * c.toFun b a := by
        rw [finsum_eq_sum_of_support_subset _ (s := T) fun b hb => by
          obtain ⟨y, hy1, hy2⟩ := exists_mul_ne_zero_of_finsum_ne_zero (left_ne_zero_of_mul hb)
          exact hT (hS hy1) hy2]
        exact Finset.sum_congr rfl fun b _ => by rw [h1 b]
    _ = ∑ y ∈ S, c₃.toFun z y * ∑ b ∈ T, c₂.toFun y b * c.toFun b a := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ᶠ y, c₃.toFun z y * ∑ᶠ b, c₂.toFun y b * c.toFun b a := by
        rw [finsum_eq_sum_of_support_subset _ (s := S) fun y hy => hS (left_ne_zero_of_mul hy)]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [finsum_eq_sum_of_support_subset _ (s := T) fun b hb => hT hy (left_ne_zero_of_mul hb)]

theorem id_comp [Countable J'] (c : LKernel Λ X K J J') : (id J').comp c = c := by
  refine ext fun z a => ?_
  rw [comp_toFun, finsum_eq_single _ z fun b hb => by simp [id, diag_toFun, Ne.symm hb]]
  simp [id, diag_toFun]

theorem comp_id [Countable J] (c : LKernel Λ X K J J') : c.comp (id J) = c := by
  refine ext fun z a => ?_
  rw [comp_toFun, finsum_eq_single _ a fun b hb => by simp [id, diag_toFun, hb]]
  simp [id, diag_toFun]

theorem diag_comp_diag [Countable J] (A B : J → Set X) (hA : ∀ j, MeasurableSet (A j))
    (hB : ∀ j, MeasurableSet (B j)) :
    (diag (Λ := Λ) (K := K) A hA).comp (diag B hB) =
      diag (fun j => A j ∩ B j) (fun j => (hA j).inter (hB j)) := by
  refine ext fun z a => ?_
  rw [comp_toFun, finsum_eq_single _ a fun b hb => by simp [diag_toFun, hb]]
  by_cases h1 : z = a <;> by_cases h2 : a.1 ∈ A a.2 <;> by_cases h3 : a.1 ∈ B a.2 <;>
    simp [diag_toFun, h1, h2, h3]

theorem comp_add [Countable J'] (c' : LKernel Λ X K J' J₂) (c d : LKernel Λ X K J J') :
    c'.comp (c + d) = c'.comp c + c'.comp d := by
  refine ext fun z a => ?_
  simp only [comp_toFun, add_toFun, mul_add]
  exact finsum_add_distrib ((c'.rowFinite z).subset fun _ hb => left_ne_zero_of_mul hb) ((c'.rowFinite z).subset fun _ hb => left_ne_zero_of_mul hb)

theorem add_comp [Countable J'] (c' d' : LKernel Λ X K J' J₂) (c : LKernel Λ X K J J') :
    (c' + d').comp c = c'.comp c + d'.comp c := by
  refine ext fun z a => ?_
  simp only [comp_toFun, add_toFun, add_mul]
  exact finsum_add_distrib ((c.colFinite a).subset fun _ hb => right_ne_zero_of_mul hb) ((c.colFinite a).subset fun _ hb => right_ne_zero_of_mul hb)

theorem comp_sub [Countable J'] (c' : LKernel Λ X K J' J₂) (c d : LKernel Λ X K J J') :
    c'.comp (c - d) = c'.comp c - c'.comp d := by
  refine ext fun z a => ?_
  simp only [comp_toFun, sub_toFun, mul_sub]
  exact finsum_sub_distrib ((c'.rowFinite z).subset fun _ hb => left_ne_zero_of_mul hb) ((c'.rowFinite z).subset fun _ hb => left_ne_zero_of_mul hb)

theorem sub_comp [Countable J'] (c' d' : LKernel Λ X K J' J₂) (c : LKernel Λ X K J J') :
    (c' - d').comp c = c'.comp c - d'.comp c := by
  refine ext fun z a => ?_
  simp only [comp_toFun, sub_toFun, sub_mul]
  exact finsum_sub_distrib ((c.colFinite a).subset fun _ hb => right_ne_zero_of_mul hb) ((c.colFinite a).subset fun _ hb => right_ne_zero_of_mul hb)

theorem comp_zero [Countable J'] (c' : LKernel Λ X K J' J₂) :
    c'.comp (0 : LKernel Λ X K J J') = 0 :=
  ext fun z a => by simp [comp_toFun]

theorem zero_comp [Countable J'] (c : LKernel Λ X K J J') :
    (0 : LKernel Λ X K J' J₂).comp c = 0 :=
  ext fun z a => by simp [comp_toFun]

end LKernel

end Collapse
