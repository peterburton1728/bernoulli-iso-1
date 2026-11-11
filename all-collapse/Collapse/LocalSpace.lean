module

public import Collapse.LocalSpaceBasic

/-!
# The monoid of isomorphism classes of local spaces

The classes of local spaces, with countable sums,
form a `SigmaMonoid`; sets, disjoint unions and complements. The definitions are in
`Collapse.LocalSpaceBasic`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Collapse

namespace LocalSpace

variable {Λ X K : Type} [Group Λ] [MulAction Λ X] [MeasurableSpace X] [BorelFree Λ X]
  [Ring K] [MeasurableSpace K] [DiscreteCoeff K]

variable (Λ X K) in
/-- The isomorphism classes of local spaces. -/
def Class : Type 1 := Quotient (setoid (Λ := Λ) (X := X) (K := K))

/-- The class of a local space. -/
def toClass (W : LocalSpace Λ X K) : Class Λ X K := Quotient.mk _ W

theorem toClass_eq_iff {W W' : LocalSpace Λ X K} : toClass W = toClass W' ↔ W ≈ W' :=
  Quotient.eq

/-- The classes form a monoid with countable sums. -/
noncomputable instance : SigmaMonoid (Class Λ X K) where
  sum w := toClass (sum (fun i => (w i).out))
  sum_unique a := (toClass_eq_iff.2 (sum_unit a.out)).trans (Quotient.out_eq a)
  sum_equiv := by
    intro ι ι' _ _ e w
    exact toClass_eq_iff.2 (sum_equiv e fun i => (w i).out)
  sum_sigma := by
    intro ι κ _ _ w
    exact toClass_eq_iff.2 (Setoid.trans (sum_sigma fun i k => (w i k).out)
      (sum_congr fun i => Setoid.symm (Quotient.mk_out _)))

theorem toClass_sum {ι : Type} [Countable ι] (W : ι → LocalSpace Λ X K) :
    toClass (sum W) = SigmaMonoid.sum (fun i => toClass (W i)) :=
  toClass_eq_iff.2 (sum_congr fun i => Setoid.symm (Quotient.mk_out (W i)))

/-- A countable disjoint union of sets is their sum, for the sum over an index type. -/
theorem toClass_ofSet_sigma {ι : Type} [Countable ι] {J : ι → Type} [∀ i, Countable (J i)]
    (A : ∀ i, J i → Set X) (hA : ∀ i j, MeasurableSet (A i j)) :
    toClass (ofSet (Λ := Λ) (K := K) (fun p : Σ i, J i => A p.1 p.2) (fun p => hA p.1 p.2)) =
      SigmaMonoid.sum (fun i => toClass (ofSet (A i) (hA i))) := by
  rw [← toClass_sum]
  refine toClass_eq_iff.2 (equiv_of_transport (W := ofSet (fun p : Σ i, J i => A p.1 p.2)
    (fun p => hA p.1 p.2)) (W' := sum fun i => ofSet (A i) (hA i)) (Equiv.refl _) ?_)
  intro x j' y j
  exact congrFun (congrFun (congrArg LKernel.toFun
    (LKernel.sigma_diag (Λ := Λ) (K := K) A hA)) (x, j')) (y, j)

/-- Copies of a set: `ι` copies of `(A)` are the set with levels `A j` over `ι × J`. -/
theorem toClass_ofSet_prod {ι J : Type} [Countable ι] [Countable J] (A : J → Set X)
    (hA : ∀ j, MeasurableSet (A j)) :
    toClass (ofSet (Λ := Λ) (K := K) (fun p : ι × J => A p.2) (fun p => hA p.2)) =
      SigmaMonoid.sum (fun _ : ι => toClass (ofSet A hA)) := by
  rw [toClass_eq_iff.2 (ofSet_equiv (fun p : ι × J => A p.2) (fun p => hA p.2)
    (fun p : Σ _ : ι, J => A p.2) (fun p => hA p.2) (Equiv.sigmaEquivProd ι J).symm fun _ => rfl)]
  exact toClass_ofSet_sigma (fun _ : ι => A) (fun _ => hA)

/-- A countable disjoint union of sets is their sum. -/
theorem toClass_ofSet_iUnion {ι J : Type} [Countable ι] [Countable J] (A : ι → J → Set X)
    (hA : ∀ i j, MeasurableSet (A i j))
    (hdisj : ∀ j, Pairwise fun i i' => Disjoint (A i j) (A i' j)) :
    toClass (ofSet (Λ := Λ) (K := K) (fun j => ⋃ i, A i j)
        (fun j => MeasurableSet.iUnion fun i => hA i j)) =
      SigmaMonoid.sum (fun i => toClass (ofSet (A i) (hA i))) := by
  have hcol : ∀ a : X × J,
      {i | ∃ b, (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).toFun b a ≠ 0}.Finite := fun a =>
    Set.Subsingleton.finite fun i hi i' hi' => by
      obtain ⟨b, hb⟩ := hi; obtain ⟨b', hb'⟩ := hi'
      by_contra hne
      exact Set.disjoint_left.1 (hdisj a.2 hne) (diag_ne_zero hb).2 (diag_ne_zero hb').2
  have hrow : ∀ b : X × J,
      {i | ∃ a, (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).toFun b a ≠ 0}.Finite := fun b =>
    Set.Subsingleton.finite fun i hi i' hi' => by
      obtain ⟨a, ha⟩ := hi; obtain ⟨a', ha'⟩ := hi'
      have h1 := diag_ne_zero ha; have h2 := diag_ne_zero ha'
      by_contra hne
      rw [← h1.1] at h1; rw [← h2.1] at h2
      exact Set.disjoint_left.1 (hdisj b.2 hne) h1.2 h2.2
  rw [← toClass_sum]
  refine toClass_eq_iff.2 ⟨⟨colBlock (fun i => LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)) hcol,
    rowBlock (fun i => LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)) hrow, ?_, ?_, ?_, ?_⟩⟩
  · ext ⟨x, i, (j : J)⟩ ⟨y, (l : J)⟩
    refine (sigma_comp_toFun (fun i => LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)) _ x i j _).trans ?_
    change ((LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).comp ((LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).comp
      (LKernel.diag (Λ := Λ) (K := K) (fun j => ⋃ i, A i j) (fun j => MeasurableSet.iUnion fun i => hA i j)))).toFun (x, j) (y, l) =
        (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).toFun (x, j) (y, l)
    rw [LKernel.diag_comp_diag, LKernel.diag_comp_diag]
    have hs : ∀ j, A i j ∩ (A i j ∩ ⋃ i, A i j) = A i j := fun j =>
      Set.inter_eq_left.2 (Set.subset_inter subset_rfl (Set.subset_iUnion (fun i => A i j) i))
    simp only [LKernel.diag_toFun, hs]
  · ext ⟨y, (l : J)⟩ ⟨x, i, (j : J)⟩
    refine (toFun_congr (LKernel.comp_assoc _ _ _).symm _ _).trans ?_
    refine (comp_sigma_toFun _ (fun i => LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)) _ x i j).trans ?_
    change (((LKernel.diag (Λ := Λ) (K := K) (fun j => ⋃ i, A i j) (fun j => MeasurableSet.iUnion fun i => hA i j)).comp (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i))).comp
      (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i))).toFun (y, l) (x, j) = (LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).toFun (y, l) (x, j)
    rw [LKernel.diag_comp_diag, LKernel.diag_comp_diag]
    have hs : ∀ j, (⋃ i, A i j) ∩ A i j ∩ A i j = A i j := fun j => by
      rw [Set.inter_assoc, Set.inter_self]
      exact Set.inter_eq_right.2 (Set.subset_iUnion (fun i => A i j) i)
    simp only [LKernel.diag_toFun, hs]
  · ext ⟨x, (j : J)⟩ ⟨y, (l : J)⟩
    show ∑ᶠ b : X × (Σ _ : ι, J), (LKernel.diag (Λ := Λ) (K := K) (A b.2.1) (hA b.2.1)).toFun
        (x, j) (b.1, b.2.2) * (LKernel.diag (Λ := Λ) (K := K) (A b.2.1) (hA b.2.1)).toFun (b.1, b.2.2) (y, l) =
      (LKernel.diag (Λ := Λ) (K := K) (fun j => ⋃ i, A i j) (fun j => MeasurableSet.iUnion fun i => hA i j)).toFun
        (x, j) (y, l)
    classical
    by_cases hy : ∃ i0, y ∈ A i0 l
    · obtain ⟨i0, hy0⟩ := hy
      rw [finsum_sigma_single _ i0 ?_]
      · change ((LKernel.diag (Λ := Λ) (K := K) (A i0) (hA i0)).comp (LKernel.diag (Λ := Λ) (K := K) (A i0) (hA i0))).toFun (x, j) (y, l) = _
        rw [LKernel.diag_comp_diag]
        simp [LKernel.diag_toFun, hy0, show ∃ i, y ∈ A i l from ⟨i0, hy0⟩]
      · rintro ⟨w, i, k⟩ hi
        by_contra hne
        exact Set.disjoint_left.1 (hdisj l hi) (diag_ne_zero (right_ne_zero_of_mul hne)).2 hy0
    · push Not at hy
      rw [finsum_eq_zero_of_forall_eq_zero fun b => ?_]
      · rw [LKernel.diag_toFun, ite_eq_right]
        rintro ⟨-, h⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h
        exact hy i hi
      · rcases b with ⟨w, i, k⟩
        by_contra hne
        exact hy i (diag_ne_zero (right_ne_zero_of_mul hne)).2
  · ext ⟨x, i, (j : J)⟩ ⟨y, k, (l : J)⟩
    show ((LKernel.diag (Λ := Λ) (K := K) (A i) (hA i)).comp (LKernel.diag (Λ := Λ) (K := K) (A k) (hA k))).toFun (x, j) (y, l) =
      (LKernel.sigma (fun i => LKernel.diag (Λ := Λ) (K := K) (A i) (hA i))).toFun (x, ⟨i, j⟩) (y, ⟨k, l⟩)
    rw [LKernel.diag_comp_diag]
    by_cases hik : i = k
    · subst hik
      rw [LKernel.sigma_toFun_mk]
      simp only [LKernel.diag_toFun, Set.inter_self]
    · rw [LKernel.sigma_toFun_ne _ _ _ _ _ (Ne.symm hik), LKernel.diag_toFun, ite_eq_right]
      rintro ⟨-, h⟩
      exact Set.disjoint_left.1 (hdisj l hik) h.1 h.2

theorem toClass_ofSet_empty {J : Type} [Countable J] :
    toClass (ofSet (Λ := Λ) (X := X) (K := K) (fun _ : J => ∅) (fun _ => MeasurableSet.empty)) =
      0 := by
  rw [SigmaMonoid.zero_def]
  refine toClass_eq_iff.2 ⟨⟨0, 0, ?_, ?_, ?_, ?_⟩⟩
  · rw [LKernel.zero_comp, LKernel.comp_zero]
  · rw [LKernel.zero_comp, LKernel.comp_zero]
  · rw [LKernel.comp_zero]
    ext ⟨x, (j : J)⟩ ⟨y, (l : J)⟩
    show (0 : K) = (LKernel.diag (Λ := Λ) (K := K) (fun _ : J => (∅ : Set X))
      (fun _ => MeasurableSet.empty)).toFun (x, j) (y, l)
    rw [LKernel.diag_toFun, ite_eq_right fun hh => hh.2]
  · rw [LKernel.comp_zero]
    ext ⟨y, i, l⟩ a
    exact i.elim

theorem compl_facts (W W₁ : LocalSpace Λ X K) (c : LKernel Λ X K W₁.J W.J)
    (c' : LKernel Λ X K W.J W₁.J) (hc : W.e.comp (c.comp W₁.e) = c)
    (hc' : W₁.e.comp (c'.comp W.e) = c') (h : c'.comp c = W₁.e) :
    (W.e - c.comp c').comp (W.e - c.comp c') = W.e - c.comp c' ∧
      (W.e - c.comp c').comp W.e = W.e - c.comp c' ∧
      W.e.comp (W.e - c.comp c') = W.e - c.comp c' ∧
      c'.comp (W.e - c.comp c') = 0 ∧ (W.e - c.comp c').comp c = 0 := by
  have hEc := mor_left W.idem hc
  have hcE₁ := mor_right W₁.idem hc
  have hE₁c' := mor_left W₁.idem hc'
  have hc'E := mor_right W.idem hc'
  have h1 : W.e.comp (c.comp c') = c.comp c' := by rw [← LKernel.comp_assoc, hEc]
  have h2 : (c.comp c').comp W.e = c.comp c' := by rw [LKernel.comp_assoc, hc'E]
  have h3 : (c.comp c').comp (c.comp c') = c.comp c' := by
    rw [LKernel.comp_assoc, ← LKernel.comp_assoc c' c c', h, hE₁c']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LKernel.sub_comp, LKernel.comp_sub, LKernel.comp_sub, W.idem, h1, h2, h3, sub_self,
      sub_zero]
  · rw [LKernel.sub_comp, W.idem, h2]
  · rw [LKernel.comp_sub, W.idem, h1]
  · rw [LKernel.comp_sub, hc'E, ← LKernel.comp_assoc, h, hE₁c', sub_self]
  · rw [LKernel.sub_comp, hEc, LKernel.comp_assoc, h, hcE₁, sub_self]

/-- The complement of a split morphism. -/
noncomputable def complSpace (W W₁ : LocalSpace Λ X K) (c : LKernel Λ X K W₁.J W.J)
    (c' : LKernel Λ X K W.J W₁.J) (hc : W.e.comp (c.comp W₁.e) = c)
    (hc' : W₁.e.comp (c'.comp W.e) = c') (h : c'.comp c = W₁.e) : LocalSpace Λ X K where
  J := W.J
  e := W.e - c.comp c'
  idem := (compl_facts W W₁ c c' hc hc' h).1

/-- For local spaces: a morphism `c : W₁ → W` with a left inverse
`c' : W → W₁` splits `W` as `W₁` plus a complement. -/
theorem exists_complement (W W₁ : LocalSpace Λ X K) (c : LKernel Λ X K W₁.J W.J)
    (c' : LKernel Λ X K W.J W₁.J) (hc : W.e.comp (c.comp W₁.e) = c)
    (hc' : W₁.e.comp (c'.comp W.e) = c') (h : c'.comp c = W₁.e) :
    ∃ Q : Class Λ X K, toClass W = toClass W₁ + Q := by
  obtain ⟨hpp, hpE, hEp, hc'p, hpc⟩ := compl_facts W W₁ c c' hc hc' h
  refine ⟨toClass (complSpace W W₁ c c' hc hc' h), ?_⟩
  rw [SigmaMonoid.add_def]
  have hF : (fun i : Bool => bif i then toClass (complSpace W W₁ c c' hc hc' h) else toClass W₁) =
      fun i => toClass (bif i then complSpace W W₁ c c' hc hc' h else W₁) :=
    funext fun i => by cases i <;> rfl
  rw [hF, ← toClass_sum, toClass_eq_iff]
  refine ⟨⟨colBlock (fun i => (match i with | false => c' | true => W.e - c.comp c' :
      LKernel Λ X K W.J (bif i then complSpace W W₁ c c' hc hc' h else W₁).J))
      (fun _ => Set.toFinite _),
    rowBlock (fun i => (match i with | false => c | true => W.e - c.comp c' :
      LKernel Λ X K (bif i then complSpace W W₁ c c' hc hc' h else W₁).J W.J))
      (fun _ => Set.toFinite _), ?_, ?_, ?_, ?_⟩⟩
  · ext ⟨x, i, j⟩ a
    refine (sigma_comp_toFun (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) _ x i j a).trans ?_
    cases i
    · change (W₁.e.comp (c'.comp W.e)).toFun (x, j) a = c'.toFun (x, j) a
      rw [hc']
    · change ((W.e - c.comp c').comp ((W.e - c.comp c').comp W.e)).toFun (x, j) a =
        (W.e - c.comp c').toFun (x, j) a
      rw [hpE, hpp]
  · ext z ⟨x, i, j⟩
    refine (toFun_congr (LKernel.comp_assoc _ _ _).symm _ _).trans ?_
    refine (comp_sigma_toFun _ (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) z x i j).trans ?_
    cases i
    · change ((W.e.comp c).comp W₁.e).toFun z (x, j) = c.toFun z (x, j)
      rw [LKernel.comp_assoc, hc]
    · change ((W.e.comp (W.e - c.comp c')).comp (W.e - c.comp c')).toFun z (x, j) =
        (W.e - c.comp c').toFun z (x, j)
      rw [hEp, hpp]
  · ext z a
    refine (rowBlock_comp_colBlock_bool _ _ _ _ z a).trans ?_
    change (c.comp c').toFun z a + ((W.e - c.comp c').comp (W.e - c.comp c')).toFun z a =
      W.e.toFun z a
    rw [hpp, LKernel.sub_toFun]
    abel
  · ext ⟨x, i, j⟩ ⟨y, k, l⟩
    cases i <;> cases k
    · refine Eq.trans ?_ (LKernel.sigma_toFun_mk (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) _ _ _ _ _).symm
      change (c'.comp c).toFun (x, j) (y, l) = W₁.e.toFun (x, j) (y, l)
      rw [h]
    · refine Eq.trans ?_ (LKernel.sigma_toFun_ne (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) _ _ _ _ (fun hh => Bool.noConfusion hh)).symm
      change (c'.comp (W.e - c.comp c')).toFun (x, j) (y, l) = 0
      rw [hc'p]; rfl
    · refine Eq.trans ?_ (LKernel.sigma_toFun_ne (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) _ _ _ _ (fun hh => Bool.noConfusion hh)).symm
      change ((W.e - c.comp c').comp c).toFun (x, j) (y, l) = 0
      rw [hpc]; rfl
    · refine Eq.trans ?_ (LKernel.sigma_toFun_mk (fun i : Bool => (bif i then complSpace W W₁ c c' hc hc' h else W₁).e) _ _ _ _ _).symm
      change ((W.e - c.comp c').comp (W.e - c.comp c')).toFun (x, j) (y, l) =
        (W.e - c.comp c').toFun (x, j) (y, l)
      rw [hpp]

end LocalSpace

end Collapse
