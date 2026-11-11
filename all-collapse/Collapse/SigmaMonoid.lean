module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Basic.Denumerable

/-!
# Monoids with countable sums and the absorption lemma

Sums are indexed by
arbitrary countable types, the empty type included, so the monoid has a zero.
-/

@[expose] public section

universe u

namespace Collapse

/-- A monoid with countable sums: every family indexed by a countable type has a sum; the sum
of a one-element family is its element (M1); sums are invariant under bijections of index
types (M2); and sums over a `Sigma` type may be computed in two stages (M3). -/
class SigmaMonoid (M : Type u) where
  /-- The sum of a countable family. -/
  sum : {ι : Type} → [Countable ι] → (ι → M) → M
  sum_unique : ∀ a : M, sum (fun _ : Unit => a) = a
  sum_equiv : ∀ {ι ι' : Type} [Countable ι] [Countable ι'] (e : ι' ≃ ι) (w : ι → M),
    sum (fun i => w (e i)) = sum w
  sum_sigma : ∀ {ι : Type} {κ : ι → Type} [Countable ι] [∀ i, Countable (κ i)]
    (w : (i : ι) → κ i → M), sum (fun p : Σ i, κ i => w p.1 p.2) = sum (fun i => sum (w i))

namespace SigmaMonoid

variable {M : Type u} [SigmaMonoid M]

/-- `∞ · a`: the sum of countably infinitely many copies of `a`. -/
def infty (a : M) : M := sum (fun _ : ℕ => a)

/-- Congruence for `sum`. -/
theorem sum_congr' {ι : Type} [Countable ι] {w w' : ι → M} (h : ∀ i, w i = w' i) :
    sum w = sum w' := congrArg _ (funext h)

theorem sum_unique' {ι : Type} [Countable ι] [Unique ι] (w : ι → M) : sum w = w default := by
  rw [← sum_equiv (Equiv.ofUnique Unit ι) w]
  exact (sum_unique (w (Equiv.ofUnique Unit ι ()))).trans (congrArg w (Subsingleton.elim _ _))

theorem sum_empty' {ι : Type} [Countable ι] [IsEmpty ι] (w : ι → M) :
    sum w = sum (fun i : Empty => i.elim) := by
  rw [← sum_equiv (Equiv.equivOfIsEmpty Empty ι) w]
  exact congrArg _ (funext fun i => i.elim)

theorem sum_elim' {ι κ : Type} [Countable ι] [Countable κ] (u : ι → M) (v : κ → M) :
    sum (Sum.elim u v) = sum (fun b : Bool => bif b then sum v else sum u) := by
  have : ∀ b : Bool, Countable (bif b then κ else ι) := fun b => by cases b <;> assumption
  rw [← sum_equiv (Equiv.sumEquivSigmaBool ι κ).symm]
  refine (sum_sigma (κ := fun b => bif b then κ else ι)
    (fun b x => Sum.elim u v ((Equiv.sumEquivSigmaBool ι κ).symm ⟨b, x⟩))).trans ?_
  exact congrArg _ (funext fun b => by cases b <;> rfl)

theorem sm_zero_add (a : M) :
    sum (fun i : Bool => bif i then a else sum (fun i : Empty => i.elim)) = a := by
  have h := sum_elim' (fun i : Empty => i.elim) (fun _ : Unit => a)
  rw [sum_unique a, ← sum_equiv (Equiv.emptySum Empty Unit).symm] at h
  rw [← h]; exact sum_unique a

theorem sm_add_zero (a : M) :
    sum (fun i : Bool => bif i then sum (fun i : Empty => i.elim) else a) = a := by
  have h := sum_elim' (fun _ : Unit => a) (fun i : Empty => i.elim)
  rw [sum_unique a, ← sum_equiv (Equiv.sumEmpty Unit Empty).symm] at h
  rw [← h]; exact sum_unique a

theorem sm_add_comm (a b : M) :
    sum (fun i : Bool => bif i then b else a) = sum (fun i : Bool => bif i then a else b) := by
  rw [← sum_equiv (⟨not, not, Bool.not_not, Bool.not_not⟩ : Bool ≃ Bool)
    (fun i : Bool => bif i then a else b)]
  exact congrArg _ (funext fun i => by cases i <;> rfl)

theorem sm_add_assoc (a b c : M) :
    sum (fun i : Bool => bif i then c else sum (fun i : Bool => bif i then b else a)) =
    sum (fun i : Bool => bif i then sum (fun i : Bool => bif i then c else b) else a) := by
  have h1 := sum_elim' (Sum.elim (fun _ : Unit => a) (fun _ : Unit => b)) (fun _ : Unit => c)
  have h2 := sum_elim' (fun _ : Unit => a) (Sum.elim (fun _ : Unit => b) (fun _ : Unit => c))
  rw [sum_elim' (fun _ : Unit => a) (fun _ : Unit => b), sum_unique, sum_unique,
    sum_unique] at h1
  rw [sum_elim' (fun _ : Unit => b) (fun _ : Unit => c), sum_unique, sum_unique,
    sum_unique] at h2
  rw [← h1, ← h2, ← sum_equiv (Equiv.sumAssoc Unit Unit Unit)]
  exact congrArg _ (funext fun x => by rcases x with (x | x) | x <;> rfl)

theorem sm_nsmul_succ (n : ℕ) (a : M) :
    sum (fun _ : Fin (n + 1) => a) = sum (fun i : Bool => bif i then a else
      sum (fun _ : Fin n => a)) := by
  have h := sum_elim' (fun _ : Fin n => a) (fun _ : Fin 1 => a)
  rw [sum_unique' (fun _ : Fin 1 => a)] at h
  rw [← h, ← sum_equiv (finSumFinEquiv (m := n) (n := 1))]
  exact congrArg _ (funext fun x => by rcases x with x | x <;> rfl)

/-- The finite sums: `0` is the empty sum, `a + b` the sum over `Bool`, and `n • a` the sum of
`n` copies. -/
instance (priority := 100) toAddCommMonoid : AddCommMonoid M where
  zero := sum (fun i : Empty => i.elim)
  add a b := sum (fun i : Bool => bif i then b else a)
  nsmul n a := sum (fun _ : Fin n => a)
  add_assoc a b c := sm_add_assoc a b c
  zero_add a := sm_zero_add a
  add_zero a := sm_add_zero a
  add_comm a b := sm_add_comm a b
  nsmul_zero _ := sum_empty' _
  nsmul_succ n a := sm_nsmul_succ n a

theorem zero_def : (0 : M) = sum (fun i : Empty => i.elim) := rfl

theorem add_def (a b : M) : a + b = sum (fun i : Bool => bif i then b else a) := rfl

theorem nsmul_def (n : ℕ) (a : M) : n • a = sum (fun _ : Fin n => a) := rfl

theorem sum_sum_comm' {ι κ : Type} [Countable ι] [Countable κ] (w : ι → κ → M) :
    sum (fun i => sum (fun k => w i k)) = sum (fun k => sum (fun i => w i k)) := by
  have h := sum_equiv ((Equiv.sigmaEquivProd κ ι).trans ((Equiv.prodComm κ ι).trans
    (Equiv.sigmaEquivProd ι κ).symm)) (fun p : Σ _ : ι, κ => w p.1 p.2)
  rw [← sum_sigma (fun i k => w i k), ← sum_sigma (fun k i => w i k), ← h]
  rfl

theorem sum_of_isEmpty {ι : Type} [Countable ι] [IsEmpty ι] (w : ι → M) : sum w = 0 :=
  sum_empty' w

theorem sum_of_unique {ι : Type} [Countable ι] [Unique ι] (w : ι → M) : sum w = w default :=
  sum_unique' w

theorem sum_add {ι : Type} [Countable ι] (u w : ι → M) :
    sum (fun i => u i + w i) = sum u + sum w := by
  refine (sum_sum_comm' (fun i (b : Bool) => bif b then w i else u i)).trans ?_
  rw [add_def]; exact congrArg _ (funext fun b => by cases b <;> rfl)

theorem sum_nsmul {ι : Type} [Countable ι] (n : ℕ) (w : ι → M) :
    sum (fun i => n • w i) = n • sum w :=
  sum_sum_comm' (fun i (_ : Fin n) => w i)

theorem sum_sum_comm {ι κ : Type} [Countable ι] [Countable κ] (w : ι → κ → M) :
    sum (fun i => sum (fun k => w i k)) = sum (fun k => sum (fun i => w i k)) :=
  sum_sum_comm' w

theorem sum_elim {ι κ : Type} [Countable ι] [Countable κ] (u : ι → M) (v : κ → M) :
    sum (Sum.elim u v) = sum u + sum v := sum_elim' u v

theorem sum_nat_succ (w : ℕ → M) : sum w = w 0 + sum (fun k => w (k + 1)) := by
  rw [← sum_equiv (⟨Sum.elim (fun _ => 0) (· + 1), fun n => Nat.casesOn n (Sum.inl ()) Sum.inr,
    by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩ : Unit ⊕ ℕ ≃ ℕ) w]
  rw [← sum_unique (w 0), ← sum_elim]
  exact congrArg _ (funext fun x => by rcases x with _ | _ <;> rfl)

theorem sum_const_of_infinite {ι : Type} [Countable ι] [Infinite ι] (a : M) :
    sum (fun _ : ι => a) = infty a := by
  obtain ⟨inst⟩ := nonempty_denumerable ι
  exact sum_equiv (@Denumerable.eqv ι inst) (fun _ => a)

theorem sum_nsmul_const (n : ℕ → ℕ) (hn : ∀ k, 1 ≤ n k) (a : M) :
    sum (fun k => n k • a) = infty a := by
  have : Infinite (Σ k, Fin (n k)) := Infinite.of_injective
    (fun k => (⟨k, ⟨0, hn k⟩⟩ : Σ k, Fin (n k))) (fun x y h => congrArg Sigma.fst h)
  exact (sum_sigma (fun k (_ : Fin (n k)) => a)).symm.trans (sum_const_of_infinite a)

theorem infty_nsmul (n : ℕ) (hn : 1 ≤ n) (a : M) : infty (n • a) = infty a :=
  sum_nsmul_const (fun _ => n) (fun _ => hn) a

theorem infty_add (a b : M) : infty (a + b) = infty a + infty b :=
  sum_add (fun _ : ℕ => a) (fun _ => b)

theorem infty_add_nsmul (n : ℕ) (a : M) : infty a + n • a = infty a := by
  show sum (fun _ : ℕ => a) + sum (fun _ : Fin n => a) = sum (fun _ : ℕ => a)
  rw [← sum_elim, show Sum.elim (fun _ : ℕ => a) (fun _ : Fin n => a) = fun _ => a from
    funext fun x => by cases x <;> rfl]
  exact sum_const_of_infinite a

theorem infty_add_self (a : M) : infty a + a = infty a := by
  have h := infty_add_nsmul 1 a
  rwa [one_nsmul] at h

theorem infty_infty (a : M) : infty (infty a) = infty a := by
  have : Infinite (Σ _ : ℕ, ℕ) := Infinite.of_injective (fun k => (⟨k, 0⟩ : Σ _ : ℕ, ℕ))
    (fun x y h => congrArg Sigma.fst h)
  exact (sum_sigma (fun (_ : ℕ) (_ : ℕ) => a)).symm.trans (sum_const_of_infinite a)

theorem nsmul_comm_aux (m n : ℕ) (x : M) : m • n • x = n • m • x := by
  rw [← mul_nsmul', Nat.mul_comm, mul_nsmul']

/-- **Absorption**. Here `r k` is the index of level `k` in level
`k + 1`, so (S1) reads `M k = r k • M (k + 1)`. -/
theorem absorption (Mk : ℕ → M) (r : ℕ → ℕ) (hr : ∀ k, 2 ≤ r k) {d e : ℕ} (hd : 1 ≤ d)
    (hde : d < e) (G : ℕ → M)
    (S1 : ∀ k, Mk k = r k • Mk (k + 1))
    (S2 : ∀ n, Mk n = sum (fun k : ℕ => (r (n + k) - 1) • Mk (n + k + 1)))
    (S3 : ∀ k, d • Mk k = e • Mk k + G k)
    (n a : ℕ) (ha : 1 ≤ a) : a • Mk n = infty (Mk 0) := by
  obtain ⟨Δ, rfl⟩ : ∃ Δ, e = d + Δ := ⟨e - d, by omega⟩
  have hΔ : 1 ≤ Δ := by omega
  have tower : ∀ n m, ∃ J, m + 1 ≤ J ∧ Mk n = J • Mk (n + m) := by
    intro n m
    induction m with
    | zero => exact ⟨1, le_refl _, (one_nsmul (Mk n)).symm⟩
    | succ m ih =>
      obtain ⟨J, hJ, h⟩ := ih
      refine ⟨J * r (n + m), by have := Nat.mul_le_mul hJ (hr (n + m)); omega, ?_⟩
      rw [← Nat.add_assoc, h, S1 (n + m), mul_nsmul']
  choose J hJ using tower
  have iter : ∀ (X Y : M) (D : ℕ), d • X = d • X + D • X + Y →
      ∀ t : ℕ, d • X = d • X + (t * D) • X + t • Y := by
    intro X Y D h t
    induction t with
    | zero => simp
    | succ t ih =>
      calc d • X = d • X + (t * D) • X + t • Y := ih
        _ = (d • X + D • X + Y) + (t * D) • X + t • Y := by rw [← h]
        _ = d • X + ((t + 1) * D) • X + (t + 1) • Y := by
          rw [Nat.add_mul, Nat.one_mul, add_nsmul, add_nsmul, one_nsmul]
          simp only [add_assoc, add_comm, add_left_comm]
  have step1 : ∀ n, d • Mk n = infty (Mk n) := by
    intro n
    have hX : ∀ k, Mk n = J n (k + 1) • Mk (n + k + 1) := fun k => (hJ n (k + 1)).2
    have hc : ∀ k, 1 ≤ r (n + k) - 1 := fun k => by have := hr (n + k); omega
    have h1 : ∀ k, d • Mk (n + k + 1) =
        d • Mk (n + k + 1) + Δ • Mk n + J n (k + 1) • G (n + k + 1) := by
      intro k
      have base : d • Mk (n + k + 1) =
          d • Mk (n + k + 1) + Δ • Mk (n + k + 1) + G (n + k + 1) := by
        rw [← add_nsmul]; exact S3 _
      have := iter _ _ _ base (J n (k + 1))
      rwa [mul_nsmul, ← hX k] at this
    have h2 : ∀ k, (d + Δ) • Mk n + J n (k + 1) • G (n + k + 1) = d • Mk n := by
      intro k
      rw [hX k, nsmul_comm_aux (d + Δ), nsmul_comm_aux d, ← nsmul_add, ← S3]
    have hI : ∀ m : ℕ → ℕ, (∀ k, 1 ≤ m k) → sum (fun k => m k • Mk n) = infty (Mk n) :=
      fun m hm => sum_nsmul_const m hm _
    have hA : sum (fun k => (r (n + k) - 1) • d • Mk (n + k + 1)) = d • Mk n := by
      conv_rhs => rw [S2 n]
      rw [← sum_nsmul]
      exact sum_congr' fun k => nsmul_comm_aux _ _ _
    have eA : d • Mk n = d • Mk n + infty (Mk n) +
        sum (fun k => (r (n + k) - 1) • J n (k + 1) • G (n + k + 1)) := by
      calc d • Mk n = sum (fun k => (r (n + k) - 1) • d • Mk (n + k + 1)) := hA.symm
        _ = sum (fun k => (r (n + k) - 1) • d • Mk (n + k + 1) +
              ((r (n + k) - 1) * Δ) • Mk n +
              (r (n + k) - 1) • J n (k + 1) • G (n + k + 1)) := by
            refine sum_congr' fun k => ?_
            conv_lhs => rw [h1 k]
            rw [nsmul_add, nsmul_add, mul_nsmul']
        _ = _ := by
            rw [sum_add, sum_add, hI (fun k => (r (n + k) - 1) * Δ)
              (fun k => Nat.mul_le_mul (hc k) hΔ), hA]
    have eB : d • Mk n = infty (Mk n) +
        sum (fun k => (r (n + k) - 1) • J n (k + 1) • G (n + k + 1)) := by
      conv_lhs => rw [eA]
      rw [add_comm (d • Mk n), infty_add_nsmul]
    rw [eB]
    calc infty (Mk n) + sum (fun k => (r (n + k) - 1) • J n (k + 1) • G (n + k + 1))
        = sum (fun k => ((r (n + k) - 1) * (d + Δ)) • Mk n) +
          sum (fun k => (r (n + k) - 1) • J n (k + 1) • G (n + k + 1)) := by
          rw [hI (fun k => (r (n + k) - 1) * (d + Δ))
            (fun k => Nat.mul_le_mul (hc k) (by omega : 1 ≤ d + Δ))]
      _ = sum (fun k => ((r (n + k) - 1) * d) • Mk n) := by
          rw [← sum_add]
          exact sum_congr' fun k => by rw [mul_nsmul', mul_nsmul', ← nsmul_add, h2 k]
      _ = infty (Mk n) := hI _ (fun k => Nat.mul_le_mul (hc k) hd)
  have step2 : ∀ n a, 1 ≤ a → a • Mk n = infty (Mk n) := by
    intro n a ha
    obtain ⟨hJ1, hJ2⟩ := hJ n d
    have hle : d ≤ a * J n d := by have := Nat.mul_le_mul ha hJ1; omega
    rw [hJ2, infty_nsmul (J n d) (by omega), ← mul_nsmul', ← Nat.add_sub_of_le hle, add_nsmul,
      step1, infty_add_nsmul]
  rw [step2 n a ha, (hJ 0 n).2, Nat.zero_add, infty_nsmul (J 0 n) (by have := (hJ 0 n).1; omega)]

/-- The algebra of the ergodic case: if `u = ∞ · u` and `a` is a
summand of `u`, then `u + a = u`. -/
theorem add_eq_of_infty {u a c : M} (hu : u = infty u) (hac : u = a + c) : u + a = u := by
  have h1 : infty u = infty a + infty c := by rw [hac, infty_add]
  calc u + a = infty u + a := by rw [← hu]
    _ = infty a + infty c := by rw [h1, add_right_comm, infty_add_self]
    _ = u := by rw [← h1, ← hu]

end SigmaMonoid

end Collapse
