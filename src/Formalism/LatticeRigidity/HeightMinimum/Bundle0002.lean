import Formalism.LatticeRigidity.StatementD
import Mathlib

-- bundled from Formalism.LatticeRigidity.HeightMinimum.OneLeProdOfInt
section
namespace Formalism.SA.P

open NumberField

section

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E)

end

lemma place_bound (a1 b1 c U U' O G α β : ℝ) (hc : 0 < c)
    (ha : c < a1 ^ 2) (hb : c < b1 ^ 2) (hU0 : 0 ≤ U) (hU'0 : 0 ≤ U')
    (hU : U ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c)) (hU' : U' ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c))
    (hO0 : 0 ≤ O) (hO : O ≤ a1 / (a1 ^ 2 - c) + U * U' * b1 / (b1 ^ 2 - c))
    (hG : 1 ≤ G) (hα : G * O = U' * α) (hβ : G * O = U * β) :
    α * β ≤ 4 * G ^ 2 * (a1 ^ 2 / (a1 ^ 2 - c)) * (b1 ^ 2 / (b1 ^ 2 - c)) / c := by
  have hk1 : 0 < a1 ^ 2 - c := by linarith
  have hk2 : 0 < b1 ^ 2 - c := by linarith
  have hUU : U = U' := (pow_left_inj₀ hU0 hU'0 two_ne_zero).mp (hU.trans hU'.symm)
  subst hUU
  have hr : 0 < U ^ 2 := by rw [hU]; positivity
  have hUpos : 0 < U := by
    rcases hU0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hr; norm_num at hr
  have hO2 : O * (a1 ^ 2 - c) ≤ a1 + b1 := by
    have e : a1 / (a1 ^ 2 - c) + U * U * b1 / (b1 ^ 2 - c) = (a1 + b1) / (a1 ^ 2 - c) := by
      rw [← sq, hU]; field_simp
    rw [e, le_div_iff₀ hk1] at hO
    exact hO
  have hαe : α = G * O / U := by field_simp; linarith
  have hβe : β = G * O / U := by field_simp; linarith
  have hab : α * β = G ^ 2 * O ^ 2 * (a1 ^ 2 - c) / (b1 ^ 2 - c) := by
    rw [hαe, hβe, div_mul_div_comm, ← sq U, hU]
    field_simp
  rw [hab, div_le_div_iff₀ hk2 hc]
  have hkey : c * (a1 + b1) ^ 2 ≤ 4 * a1 ^ 2 * b1 ^ 2 := by nlinarith [sq_nonneg (a1 - b1)]
  have hOk : (O * (a1 ^ 2 - c)) ^ 2 ≤ (a1 + b1) ^ 2 := by
    have : 0 ≤ O * (a1 ^ 2 - c) := by positivity
    exact pow_le_pow_left₀ this hO2 2
  have hG2 : 0 < G ^ 2 := by positivity
  have rhs : 4 * G ^ 2 * (a1 ^ 2 / (a1 ^ 2 - c)) * (b1 ^ 2 / (b1 ^ 2 - c)) * (b1 ^ 2 - c) =
      4 * G ^ 2 * a1 ^ 2 * b1 ^ 2 / (a1 ^ 2 - c) := by
    field_simp
  rw [rhs, le_div_iff₀ hk1]
  calc G ^ 2 * O ^ 2 * (a1 ^ 2 - c) * c * (a1 ^ 2 - c)
      = G ^ 2 * (c * (O * (a1 ^ 2 - c)) ^ 2) := by ring
    _ ≤ G ^ 2 * (4 * a1 ^ 2 * b1 ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left hOk hc.le) hkey) hG2.le
    _ = 4 * G ^ 2 * a1 ^ 2 * b1 ^ 2 := by ring

end Formalism.SA.P
end

-- bundled from Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
section
namespace Formalism.SA.P

open Matrix Polynomial
open scoped ComplexOrder

section TracePow

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem finite_eig (f : Module.End K V) : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := by
  first
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.iSupIndep_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt
      (Module.End.independent_maxGenEigenspace f)
  | exact (Module.End.independent_maxGenEigenspace f).finite_ne_bot
  | exact (Module.End.iSupIndep_maxGenEigenspace f).finite_ne_bot

theorem trace_pow_restrict_maxGen (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ,
      (((f.restrict h1) ^ m) z : V) = (f ^ m) z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      first
      | rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      | rw [pow_succ', LinearMap.mul_apply, pow_succ', LinearMap.mul_apply, ← ih]
      rfl
  have hg : (f ^ j).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) =
      (f.restrict h1) ^ j :=
    LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)
  rw [hg]
  have hxy : IsNilpotent (f.restrict h1 -
      algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
    convert Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1
    refine LinearMap.ext fun z => Subtype.ext ?_
    first
    | rfl
    | simp [LinearMap.restrict_apply]
    | simp
  generalize f.restrict h1 = x at hxy ⊢
  have hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) :=
    (Algebra.commutes μ x).symm
  have hnil : IsNilpotent
      (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) := by
    rw [← hc.geom_sum₂_mul]
    have hcomm : Commute (∑ i ∈ Finset.range j, x ^ i *
        (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i))
        (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      refine Commute.sub_right ?_ ?_
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
        | exact Commute.sum_left fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
        | exact Commute.sum_left fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
    first
    | exact hcomm.isNilpotent_mul_left hxy
    | exact hcomm.isNilpotent_mul_right hxy
    | exact hcomm.symm.isNilpotent_mul_left hxy
    | exact hcomm.symm.isNilpotent_mul_right hxy
  have h0 : LinearMap.trace K _ (x ^ j -
      (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0 := by
    first
    | exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    | exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))),
    Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]

theorem trace_pow_eq_sum (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  classical
  have htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤ := by
    refine eq_top_iff.mpr ?_
    first
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top (f := f)]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.maxGenEigenspace μ = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ)
        μ (by simpa using hμ) le_rfl
  have hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K)) := by
    first
    | exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective
    | exact (Module.End.iSupIndep_maxGenEigenspace f).comp Subtype.val_injective
  have hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm
  have htr := LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j)
    (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))
  exact htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))

end TracePow

section Lattice

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Lattice

end Formalism.SA.P
end

