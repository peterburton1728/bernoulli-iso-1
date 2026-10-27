module

public import BernoulliIso.MarkerAdaptation

/-!
Actual finite rows of an extraction tower with changing coordinate types.
The stage rows are insertion followed by iterated sparse splitting. Prefix
rows, their cardinality bounds, and their survival implication are derived.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace BernoulliIso
namespace SparseTower

variable {K : Type*} [CommRing K] {A : ℕ → Type*}

/-- Composition preserves any coordinate locality predicate respected by
the input support and by all rows that it can actually encounter. -/
theorem compose_support_in {B C : Type*} (r : B →₀ K) (s : B → C →₀ K)
    (P : B → Prop) (Q : C → Prop)
    (hr : ∀ b ∈ r.support, P b) (hs : ∀ b, P b → ∀ c ∈ (s b).support, Q c) :
    ∀ c ∈ (SparseRows.compose r s).support, Q c := by
  intro c hc
  obtain ⟨b, hb, hc⟩ := Finset.mem_biUnion.1 (SparseRows.support_compose_subset r s hc)
  exact hs b (hr b hb) c hc

theorem iterateRows_support_in {B : Type*} (rows : B → B →₀ K) (P : B → Prop)
    (hrows : ∀ b, P b → ∀ c ∈ (rows b).support, P c) (n : ℕ) (b : B) (hb : P b) :
    ∀ c ∈ (SparseRows.iterateRows rows n b).support, P c := by
  induction n with
  | zero =>
    intro c hc
    have hcb : c = b := Finset.mem_singleton.1 (Finsupp.support_single_subset hc)
    rwa [hcb]
  | succ n ih =>
    exact compose_support_in _ _ P P ih hrows

/-- The true row of insertion followed by the repeated algebraic section. -/
def stageRows (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (n : ℕ) (a : A n) : A (n + 1) →₀ K :=
  SparseRows.compose (SparseRows.insertionRows (selected n) a)
    (SparseRows.iterateRows (split n) (k n))

/-- Prefix dependence of each original coordinate, computed on coefficients. -/
def prefixRows (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ) :
    (n : ℕ) → A 0 → A n →₀ K
  | 0, a => Finsupp.single a 1
  | n + 1, a => SparseRows.compose (prefixRows selected split k n a)
      (stageRows selected split k n)

def rowBound (C₀ : ℕ) (k : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => rowBound C₀ k n * C₀ ^ k n

theorem stageRows_card_le (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (C₀ : ℕ) (hC : ∀ n a, (split n a).support.card ≤ C₀) (n : ℕ) (a : A n) :
    (stageRows selected split k n a).support.card ≤ C₀ ^ k n := by
  calc
    (stageRows selected split k n a).support.card ≤
        (SparseRows.insertionRows (K := K) (selected n) a).support.card * C₀ ^ k n :=
      SparseRows.card_support_compose_le _ _ _
        (fun b _ => SparseRows.card_support_iterateRows_le _ _ (hC n) _ b)
    _ ≤ 1 * C₀ ^ k n :=
      Nat.mul_le_mul_right _ (SparseRows.card_support_insertionRows_le _ _)
    _ = C₀ ^ k n := Nat.one_mul _

theorem prefixRows_card_le (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (C₀ : ℕ) (hC : ∀ n a, (split n a).support.card ≤ C₀) (n : ℕ) (a : A 0) :
    (prefixRows selected split k n a).support.card ≤ rowBound C₀ k n := by
  induction n with
  | zero =>
    simpa only [prefixRows, rowBound, Finset.card_singleton] using
      Finset.card_le_card (Finsupp.support_single_subset (a := a) (b := (1 : K)))
  | succ n ih =>
    exact (SparseRows.card_support_compose_le _ _ _
      (fun b _ => stageRows_card_le selected split k C₀ hC n b)).trans
        (Nat.mul_le_mul_right _ ih)

/-- The actual next row cannot survive unless its current support meets
the insertion choice; this is derived without a row-death assumption. -/
theorem prefixRows_survival_requires_selection
    (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (n : ℕ) (a : A 0) (hnext : prefixRows selected split k (n + 1) a ≠ 0) :
    ∃ b ∈ (prefixRows selected split k n a).support, selected n b ≠ none := by
  classical
  by_contra hmiss
  apply hnext
  apply SparseRows.eq_zero_of_eval_zero
  intro f
  rw [prefixRows, SparseRows.eval_compose]
  apply SparseRows.eval_insert_eq_zero _ (fun b => selected n b ≠ none)
  · intro b hb
    have hn : selected n b = none := by simpa using hb
    simp [stageRows, SparseRows.insertionRows, hn]
  · intro b hb hs
    exact hmiss ⟨b, hb, hs⟩

theorem insertionRows_support_in {B C : Type*} (selected : B → Option C)
    (Q : B → C → Prop) (hsel : ∀ b c, selected b = some c → Q b c) (b : B) :
    ∀ c ∈ (SparseRows.insertionRows (K := K) selected b).support, Q b c := by
  intro c hc
  cases hs : selected b with
  | none => simp [SparseRows.insertionRows, hs] at hc
  | some d =>
    have hcd : c = d := by
      apply Finset.mem_singleton.1
      apply Finsupp.support_single_subset (a := d) (b := (1 : K))
      simpa only [SparseRows.insertionRows, hs] using hc
    subst c
    exact hsel b d hs

theorem stageRows_support_component {Comp : Type*}
    (component : ∀ n, A n → Comp)
    (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (hsel : ∀ n a b, selected n a = some b → component (n + 1) b = component n a)
    (hsplit : ∀ n a b, b ∈ (split n a).support →
      component (n + 1) b = component (n + 1) a)
    (n : ℕ) (a : A n) :
    ∀ b ∈ (stageRows selected split k n a).support,
      component (n + 1) b = component n a := by
  apply compose_support_in _ _
    (fun b => component (n + 1) b = component n a)
    (fun b => component (n + 1) b = component n a)
  · exact insertionRows_support_in (selected n)
      (fun a b => component (n + 1) b = component n a) (hsel n) a
  · intro b hb
    apply iterateRows_support_in _ (fun c => component (n + 1) c = component n a)
      _ (k n) b hb
    intro c hc d hd
    exact (hsplit n c d hd).trans hc

theorem prefixRows_support_component {Comp : Type*}
    (component : ∀ n, A n → Comp)
    (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (hsel : ∀ n a b, selected n a = some b → component (n + 1) b = component n a)
    (hsplit : ∀ n a b, b ∈ (split n a).support →
      component (n + 1) b = component (n + 1) a)
    (n : ℕ) (a : A 0) :
    ∀ b ∈ (prefixRows selected split k n a).support, component n b = component 0 a := by
  induction n with
  | zero =>
    intro b hb
    have hba : b = a := Finset.mem_singleton.1 (Finsupp.support_single_subset hb)
    rw [hba]
  | succ n ih =>
    apply compose_support_in _ _ (fun b => component n b = component 0 a)
      (fun b => component (n + 1) b = component 0 a) ih
    intro b hb c hc
    exact (stageRows_support_component component selected split k hsel hsplit n b c hc).trans hb

variable {Y : ℕ → Type*} [∀ n, AddCommGroup (Y n)] [∀ n, Module K (Y n)]

/-- The coefficient recursion represents the genuine finite inverse section
of the supplied exact stage equivalences. -/
theorem eval_prefixRows
    (selected : ∀ n, A n → Option (A (n + 1)))
    (split : ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (tower : ExtractionTower K (fun n => A n → K) Y)
    (hsection : ∀ n (f : A (n + 1) → K) a,
      tower.sectionMap n f a = SparseRows.eval (stageRows selected split k n a) f)
    (n : ℕ) (f : A n → K) (a : A 0) :
    SparseRows.eval (prefixRows selected split k n a) f = tower.prefixSection n f a := by
  induction n with
  | zero => simp [prefixRows, SparseRows.eval_single, ExtractionTower.prefixSection]
  | succ n ih =>
    rw [prefixRows, SparseRows.eval_compose]
    have heq : (fun b => SparseRows.eval (stageRows selected split k n b) f) =
        tower.sectionMap n f := funext (fun b => (hsection n f b).symm)
    rw [heq, ih]
    rfl

variable {Ω B C : Type*} [MeasurableSpace Ω] [Countable B]
  [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]

/-- Only rows in the original coordinate's component need to be adapted
to its history. Rows outside that component are masked to zero, which does
not change the actual composition because the current support cannot reach them. -/
theorem measurable_compose_coeff_on_support
    (row : Ω → B →₀ K) (next : Ω → B → C →₀ K) (P : B → Prop)
    (hrow : ∀ b, Measurable (fun ω => row ω b))
    (hlocal : ∀ ω b, b ∈ (row ω).support → P b)
    (hnext : ∀ b, P b → ∀ c, Measurable (fun ω => next ω b c)) (c : C) :
    Measurable (fun ω => SparseRows.compose (row ω) (next ω) c) := by
  classical
  let masked : Ω → B → C →₀ K := fun ω b => if P b then next ω b else 0
  have hm : ∀ b c, Measurable (fun ω => masked ω b c) := by
    intro b c
    by_cases hb : P b
    · simpa only [masked, ite_eq_left hb] using hnext b hb c
    · simpa only [masked, ite_eq_right hb, Finsupp.zero_apply] using
        (measurable_const : Measurable (fun _ : Ω => (0 : K)))
  have heq (ω : Ω) : SparseRows.compose (row ω) (next ω) =
      SparseRows.compose (row ω) (masked ω) := by
    apply Finset.sum_congr rfl
    intro b hb
    simp only [masked, ite_eq_left (hlocal ω b hb)]
  have h := AdaptedRows.measurable_compose_coeff row masked hrow hm c
  simpa only [← heq] using h

/-- Repeated splitting remains adapted to the original row's component.
No common history across different components is assumed. -/
theorem iterateRows_coeff_measurable {Comp : Type*}
    (component : B → Comp) (history : Comp → MeasurableSpace Ω)
    (rows : Ω → B → B →₀ K)
    (hlocal : ∀ ω b c, c ∈ (rows ω b).support → component c = component b)
    (hrows : ∀ b c, Measurable[history (component b)] (fun ω => rows ω b c))
    (n : ℕ) (b : B) :
    ∀ c, Measurable[history (component b)] (fun ω => SparseRows.iterateRows (rows ω) n b c) := by
  induction n with
  | zero => intro c; exact measurable_const
  | succ n ih =>
    intro c
    let : MeasurableSpace Ω := history (component b)
    apply measurable_compose_coeff_on_support
      (fun ω => SparseRows.iterateRows (rows ω) n b) rows (fun d => component d = component b)
      ih
    · intro ω d hd
      exact iterateRows_support_in (rows ω) (fun d => component d = component b)
        (fun d hd e he => (hlocal ω d e he).trans hd) n b rfl d hd
    · intro d hd e
      exact (hrows d e).mono (le_of_eq (congrArg history hd)) le_rfl

variable [∀ n, Countable (A n)]

theorem stageRows_coeff_measurable {Comp : Type*}
    (component : ∀ n, A n → Comp) (history : Comp → MeasurableSpace Ω)
    (selected : Ω → ∀ n, A n → Option (A (n + 1)))
    (split : Ω → ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (hselLocal : ∀ ω n a b, selected ω n a = some b →
      component (n + 1) b = component n a)
    (hsplitLocal : ∀ ω n a b, b ∈ (split ω n a).support →
      component (n + 1) b = component (n + 1) a)
    (n : ℕ)
    (hsel : ∀ a b, Measurable[history (component n a)]
      (fun ω => SparseRows.insertionRows (K := K) (selected ω n) a b))
    (hsplit : ∀ a b, Measurable[history (component (n + 1) a)]
      (fun ω => split ω n a b)) (a : A n) :
    ∀ b, Measurable[history (component n a)] (fun ω => stageRows (selected ω) (split ω) k n a b) := by
  intro b
  let : MeasurableSpace Ω := history (component n a)
  apply measurable_compose_coeff_on_support
    (fun ω => SparseRows.insertionRows (K := K) (selected ω n) a)
    (fun ω => SparseRows.iterateRows (split ω n) (k n))
    (fun c => component (n + 1) c = component n a) (hsel a)
  · intro ω c hc
    exact insertionRows_support_in (selected ω n)
      (fun a c => component (n + 1) c = component n a) (hselLocal ω n) a c hc
  · intro c hc d
    have h := iterateRows_coeff_measurable (component (n + 1)) history
      (fun ω => split ω n) (fun ω => hsplitLocal ω n) hsplit (k n) c d
    exact h.mono (le_of_eq (congrArg history hc)) le_rfl

/-- The coefficientwise adaptation of every true prefix row follows by
induction from the primitive insertion and split coefficients, preserving
the original coordinate's own component history. -/
theorem prefixRows_coeff_measurable {Comp : Type*}
    (component : ∀ n, A n → Comp) (history : Comp → ℕ → MeasurableSpace Ω)
    (hmono : ∀ c n, history c n ≤ history c (n + 1))
    (selected : Ω → ∀ n, A n → Option (A (n + 1)))
    (split : Ω → ∀ n, A (n + 1) → A (n + 1) →₀ K) (k : ℕ → ℕ)
    (hselLocal : ∀ ω n a b, selected ω n a = some b →
      component (n + 1) b = component n a)
    (hsplitLocal : ∀ ω n a b, b ∈ (split ω n a).support →
      component (n + 1) b = component (n + 1) a)
    (hsel : ∀ n a b, Measurable[history (component n a) (n + 1)]
      (fun ω => SparseRows.insertionRows (K := K) (selected ω n) a b))
    (hsplit : ∀ n a b, Measurable[history (component (n + 1) a) (n + 1)]
      (fun ω => split ω n a b)) (n : ℕ) (a : A 0) :
    ∀ b, Measurable[history (component 0 a) n]
      (fun ω => prefixRows (selected ω) (split ω) k n a b) := by
  induction n with
  | zero => intro b; exact measurable_const
  | succ n ih =>
    intro b
    let : MeasurableSpace Ω := history (component 0 a) (n + 1)
    apply measurable_compose_coeff_on_support
      (fun ω => prefixRows (selected ω) (split ω) k n a)
      (fun ω => stageRows (selected ω) (split ω) k n)
      (fun c => component n c = component 0 a)
    · intro c
      exact (ih c).mono (hmono (component 0 a) n) le_rfl
    · intro ω c hc
      exact prefixRows_support_component component (selected ω) (split ω) k
        (hselLocal ω) (hsplitLocal ω) n a c hc
    · intro c hc d
      have h := stageRows_coeff_measurable component (fun c => history c (n + 1))
        selected split k hselLocal hsplitLocal n (hsel n) (hsplit n) c d
      exact h.mono (le_of_eq (congrArg (fun c => history c (n + 1)) hc)) le_rfl

section ConcreteProbability

variable {G Comp : Type*} [Group G]
  [Fintype K] [Nontrivial K] [LinearOrder K]

/-- History of the two fresh streams consumed at each earlier stage,
pulled back to the actual (possibly conull-restricted) marker model. -/
abbrev markerHistory (geo : MarkerGeometry G) (marker : Ω → G → K)
    (g : G) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (geo.pastRead g (2 * n) ∘ marker) inferInstance

theorem markerHistory_mono (geo : MarkerGeometry G) (marker : Ω → G → K)
    (g : G) (n : ℕ) :
    markerHistory geo marker g n ≤ markerHistory geo marker g (n + 1) := by
  simpa only [markerHistory, ← MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono (g := marker)
      (geo.pastSigma_mono (K := K) g (show 2 * n ≤ 2 * (n + 1) by omega)))

theorem fresh_le_markerHistory (geo : MarkerGeometry G) (marker : Ω → G → K)
    (g : G) {r n : ℕ} (hr : r < 2 * n) :
    MeasurableSpace.comap (geo.freshRead g r ∘ marker) inferInstance ≤
      markerHistory geo marker g n := by
  simpa only [markerHistory, ← MeasurableSpace.comap_comp] using
    (MeasurableSpace.comap_mono (g := marker)
      (geo.freshSigma_le_pastSigma (K := K) g hr))

/-- The actual sparse inverse tower is injective almost surely. Its rows,
true supports, cardinality bounds, support-fiber adaptation, and row-death
implication are all derived here. The fresh packet inequality is the proved
product-marker theorem, not a hypothesis.

The remaining construction interfaces are primitive: stage-section rows,
component locality, measurable insertion/split coefficients in their actual
fresh streams, and equality of the actual selector with its finite packet
event. These must be instantiated by the coset-chart construction. -/
theorem ae_extract_injective_of_packet_rows
    (geo : MarkerGeometry G) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (marker : Ω → G → K)
    (hm : MeasurePreserving marker μ (MarkerGeometry.markerLaw (G := G) K))
    (component : ∀ n, A n → Comp) (base : Comp → G)
    (selected : Ω → ∀ n, A n → Option (A (n + 1)))
    (split : Ω → ∀ n, A (n + 1) → A (n + 1) →₀ K)
    (k : ℕ → ℕ) (C₀ : ℕ)
    (hC : ∀ ω n a, (split ω n a).support.card ≤ C₀)
    (hselLocal : ∀ ω n a b, selected ω n a = some b →
      component (n + 1) b = component n a)
    (hsplitLocal : ∀ ω n a b, b ∈ (split ω n a).support →
      component (n + 1) b = component (n + 1) a)
    (hselMeas : ∀ n a b, Measurable[
      MeasurableSpace.comap (geo.freshRead (base (component n a)) (2 * n) ∘ marker)
        inferInstance]
      (fun ω => SparseRows.insertionRows (K := K) (selected ω n) a b))
    (hsplitMeas : ∀ n a b, Measurable[
      MeasurableSpace.comap (geo.freshRead (base (component (n + 1) a)) (2 * n + 1)
        ∘ marker) inferInstance]
      (fun ω => split ω n a b))
    (L H : ℕ → ℕ) (hL : ∀ n, 0 < L n) (hH : ∀ n, 0 < H n)
    (hsize : ∀ n, 2 * rowBound C₀ k n ≤ L n)
    (sites : ∀ n, A n → (Fin (L n) × Fin (H n)) ↪ geo.D)
    (packetIndex : ∀ n, A n → Fin (L n))
    (hselectedEvent : ∀ n b,
      {ω | selected ω n b ≠ none} =
        marker ⁻¹' geo.packetSelected (base (component n b)) (2 * n)
          (sites n b) (packetIndex n b))
    (tower : Ω → ExtractionTower K (fun n => A n → K) Y)
    (hsection : ∀ ω n (f : A (n + 1) → K) a,
      (tower ω).sectionMap n f a =
        SparseRows.eval (stageRows (selected ω) (split ω) k n a) f) :
    ∀ᵐ ω ∂μ, Function.Injective (tower ω).extract := by
  let history : Comp → ℕ → MeasurableSpace Ω :=
    fun c n => markerHistory geo marker (base c) n
  have hcoeff (n : ℕ) (a : A 0) : ∀ b,
      Measurable[history (component 0 a) n]
        (fun ω => prefixRows (selected ω) (split ω) k n a b) := by
    apply prefixRows_coeff_measurable component history
      (fun c n => markerHistory_mono geo marker (base c) n)
      selected split k hselLocal hsplitLocal
    · intro n a b
      exact (hselMeas n a b).mono
        (fresh_le_markerHistory geo marker _ (by omega)) le_rfl
    · intro n a b
      exact (hsplitMeas n a b).mono
        (fresh_le_markerHistory geo marker _ (by omega)) le_rfl
  apply ae_extract_injective_of_contraction μ tower
    (fun a : A 0 => LinearMap.proj a) (fun x y h => funext h)
    (c := (2 : ℝ≥0∞)⁻¹) (by norm_num)
  intro a n
  let row : Ω → A n →₀ K := fun ω => prefixRows (selected ω) (split ω) k n a
  let support : Ω → Finset (A n) := fun ω => (row ω).support
  let : Nonempty (Fin (L n)) := ⟨⟨0, hL n⟩⟩
  let : Nonempty (Fin (H n)) := ⟨⟨0, hH n⟩⟩
  have hs (s : Finset (A n)) :
      MeasurableSet[history (component 0 a) n] {ω | support ω = s} := by
    let : MeasurableSpace Ω := history (component 0 a) n
    exact AdaptedRows.support_fiber_measurable row (hcoeff n a) s
  have hamb : history (component 0 a) n ≤ (inferInstance : MeasurableSpace Ω) :=
    ((geo.measurable_pastRead (base (component 0 a)) (2 * n)).comp hm.measurable).comap_le
  apply survival_step_of_adaptive_selection μ support
    (fun b => {ω | selected ω n b ≠ none}) _ _
    (fun s => hamb _ (hs s))
    (R := rowBound C₀ k n) (p := (L n : ℝ≥0∞)⁻¹)
  · intro ω
    exact prefixRows_card_le (selected ω) (split ω) k C₀ (hC ω) n a
  · intro s b hb
    by_cases hcomp : component n b = component 0 a
    · rw [hselectedEvent n b, hcomp]
      simpa only [Fintype.card_fin] using
        geo.row_support_packet_bound_pullback (base (component 0 a)) (2 * n)
          marker hm row (hcoeff n a) s (sites n b) (packetIndex n b)
    · have hemp : {ω | support ω = s} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro ω hω
        change support ω = s at hω
        apply hcomp
        exact prefixRows_support_component component (selected ω) (split ω) k
          (hselLocal ω) (hsplitLocal ω) n a b (by
            change b ∈ support ω
            rw [hω]
            exact hb)
      simp only [hemp, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · intro ω hω
    obtain ⟨f, hf⟩ := (SparseRows.support_nonempty_iff (row ω)).1 hω
    refine ⟨f, ?_⟩
    simpa only [row, eval_prefixRows (selected ω) (split ω) k (tower ω)
      (hsection ω), LinearMap.proj_apply] using hf
  · intro ω hω
    obtain ⟨f, hf⟩ := hω
    have hnext : prefixRows (selected ω) (split ω) k (n + 1) a ≠ 0 := by
      intro hz
      apply hf
      change (tower ω).prefixSection (n + 1) f a = 0
      rw [← eval_prefixRows (selected ω) (split ω) k (tower ω) (hsection ω), hz]
      exact SparseRows.eval_zero f
    exact prefixRows_survival_requires_selection (selected ω) (split ω) k n a hnext
  · exact selection_ratio_le_half (hL n) (hsize n)

end ConcreteProbability

end SparseTower
end BernoulliIso
