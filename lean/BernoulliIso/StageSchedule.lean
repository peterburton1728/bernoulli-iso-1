module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.Order.Ring.Nat

/-!
An explicit schedule; no choice of an indefinitely large subgroup is hidden
in the tower. If the current true row bound is R, add R+1 lamp sites.
The resulting quotient has 2^(R+1) cosets, at least twice R.
-/

@[expose] public section

namespace BernoulliIso.StageSchedule

def state (C₀ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let p := state C₀ n
    let a' := p.1 + (p.2 + 1)
    (a', p.2 * C₀ ^ (2 ^ a'))

def level (C₀ n : ℕ) : ℕ := (state C₀ n).1
def bound (C₀ n : ℕ) : ℕ := (state C₀ n).2
def repetitions (C₀ n : ℕ) : ℕ := 2 ^ level C₀ (n + 1)
def packets (C₀ n : ℕ) : ℕ := 2 ^ (bound C₀ n + 1)
def discarded (C₀ n : ℕ) : ℕ := packets C₀ n - 1

@[simp] theorem level_zero (C₀ : ℕ) : level C₀ 0 = 0 := rfl
@[simp] theorem bound_zero (C₀ : ℕ) : bound C₀ 0 = 1 := rfl

theorem level_succ (C₀ n : ℕ) :
    level C₀ (n + 1) = level C₀ n + (bound C₀ n + 1) := rfl

theorem bound_succ (C₀ n : ℕ) :
    bound C₀ (n + 1) = bound C₀ n * C₀ ^ repetitions C₀ n := rfl

theorem level_step (C₀ n : ℕ) : level C₀ n ≤ level C₀ (n + 1) := by
  rw [level_succ]
  exact Nat.le_add_right _ _

theorem packets_pos (C₀ n : ℕ) : 0 < packets C₀ n :=
  Nat.pow_pos (by decide)

theorem discarded_succ (C₀ n : ℕ) : discarded C₀ n + 1 = packets C₀ n :=
  Nat.sub_add_cancel (packets_pos C₀ n)

theorem twice_bound_le_packets (C₀ n : ℕ) : 2 * bound C₀ n ≤ packets C₀ n := by
  have h : bound C₀ n ≤ 2 ^ bound C₀ n := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    2 * bound C₀ n ≤ 2 * 2 ^ bound C₀ n := Nat.mul_le_mul_left 2 h
    _ = packets C₀ n := by rw [packets, pow_succ, Nat.mul_comm]

end BernoulliIso.StageSchedule
