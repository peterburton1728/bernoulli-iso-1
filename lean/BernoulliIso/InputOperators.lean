module

public import BernoulliIso.AlgebraicInput
public import BernoulliIso.GroupRingAction

/-! The common rectangle interface instantiated on the actual coset spaces. -/

@[expose] public section
noncomputable section

namespace BernoulliIso.AlgebraicInput

variable {K N I V G : Type*} [Field K] [Finite K]
  [Group N] [Countable N] [Fintype I] [Fintype V] [Nonempty I] [Nonempty V]
  [Group G]

variable (s : AlgebraicInput K N I V) (H : Subgroup G) (ι : N →* G)
  (commutes : ∀ h ∈ H, ∀ n, Commute h (ι n))

/-- The abstract module splitting now acts on genuine configurations. -/
def concreteSplit : SplitData K (V → G ⧸ H → K) (I → G ⧸ H → K) := by
  classical
  exact CosetOperators.splitData H ι commutes (Matrix.diagonal s.p) s.U s.T
    s.PP s.UP s.PT s.UT

/-- The residual compact subgroup is defined by the actual rectangle. -/
abbrev residual := (s.concreteSplit H ι commutes).Q.range

def concreteEquiv : (s.concreteSplit H ι commutes).P.range ≃ₗ[K]
    ((I → G ⧸ H → K) × s.residual H ι commutes) :=
  (s.concreteSplit H ι commutes).linearEquiv

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_P : Continuous (s.concreteSplit H ι commutes).P :=
  CosetOperators.continuous_matrix H ι commutes _

theorem continuous_U : Continuous (s.concreteSplit H ι commutes).U :=
  CosetOperators.continuous_matrix H ι commutes _

theorem continuous_T : Continuous (s.concreteSplit H ι commutes).T :=
  CosetOperators.continuous_matrix H ι commutes _

theorem continuous_Q : Continuous (s.concreteSplit H ι commutes).Q :=
  (s.continuous_P H ι commutes).sub
    ((s.continuous_T H ι commutes).comp (s.continuous_U H ι commutes))

theorem continuous_concreteEquiv : Continuous (s.concreteEquiv H ι commutes) := by
  exact ((s.continuous_U H ι commutes).comp continuous_subtype_val).prodMk
    (((s.continuous_Q H ι commutes).comp continuous_subtype_val).subtype_mk _)

theorem continuous_concreteEquiv_symm :
    Continuous (s.concreteEquiv H ι commutes).symm := by
  exact (((s.continuous_T H ι commutes).comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end Topology

end BernoulliIso.AlgebraicInput
