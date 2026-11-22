import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebra
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1
    rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n
    rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]
  simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmQuadraticPhaseEquivariantEmbeddingsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmQuadraticPhase_equivariant_embeddings : ∀ D : D7, galPh1 D := by
  first | exact @GlobalTheory.QuadPhase.galPh1_all | exact GlobalTheory.QuadPhase.galPh1_all | (intros; apply GlobalTheory.QuadPhase.galPh1_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DupNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  by rw [sub_eq_add_neg]; exact i_add ha (by rwa [norm_neg])

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem i_one : ‖(1 : K)‖ ≤ 1 := by simp

theorem b_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg

theorem delta_eq (W : WeierstrassCurve K) (x : K) :
    W.Δ = (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) +
      (12 * x ^ 3 - W.b₂ * x ^ 2 - 10 * W.b₄ * x + (W.b₂ * W.b₄ - 27 * W.b₆)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem max_norm_eq (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) (x : K) :
    max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ =
      max 1 ‖x‖ ^ 4 := by
  obtain ⟨b2, b4, b6, b8⟩ := b_le W h1 h2 h3 h4 h6
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have hp : ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    have hq : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    rw [max_eq_left hx, one_pow]
    refine le_antisymm (max_le hp hq) ?_
    rw [← hΔ, delta_eq W x]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_) <;> rw [norm_mul] <;>
      refine mul_le_of_le_one_left (norm_nonneg _) ?_ <;> repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
  · have hR1 : 1 ≤ ‖x‖ := hx.le
    have bd : ∀ {c : K}, ‖c‖ ≤ 1 → ∀ {k m : ℕ}, k ≤ m → ‖c * x ^ k‖ ≤ ‖x‖ ^ m := by
      intro c hc k m hkm
      rw [norm_mul, norm_pow]
      calc ‖c‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ m :=
            mul_le_mul hc (pow_le_pow_right₀ hR1 hkm) (by positivity) zero_le_one
        _ = ‖x‖ ^ m := one_mul _
    have hφ : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ =
        x ^ 4 + -(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0) := by ring
    have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0 := by ring
    have hr : ‖W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0‖ ≤ ‖x‖ ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (bd b4 le_rfl) (bd (i_mul (i_ofNat 2) b6) (by norm_num)))) (bd b8 (by norm_num)))
    have hs : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0‖ ≤ ‖x‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le (bd (i_ofNat 4) le_rfl) (bd b2 (by norm_num))))
          (bd (i_mul (i_ofNat 2) b4) (by norm_num)))) (bd b6 (by norm_num)))
    have h24 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have h34 : ‖x‖ ^ 3 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have hne : ‖x ^ 4‖ ≠ ‖-(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0)‖ := by
      rw [norm_neg, norm_pow]; exact (hr.trans_lt h24).ne'
    rw [hφ, hψ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow,
      max_eq_left (hr.trans h24.le), max_eq_left (hs.trans h34.le), max_eq_right hR1]

theorem max_norm_eq_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]),
    ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 →
      ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖
        ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 :=
  fun _ _ W h1 h2 h3 h4 h6 hΔ x => max_norm_eq W h1 h2 h3 h4 h6 hΔ x

end GlobalTheory.DupNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAdeleIso

theorem intAE_mul_mem (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mem_intAE_iff_comm (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y ∈
      Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem r hr =>
      obtain ⟨a, ha, x, rfl⟩ := hr
      have e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
          (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
  · intro hw
    let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    have key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D := by
      intro z hz
      induction hz using Subring.closure_induction with
      | mem r hr =>
        rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
        · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
        · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | one =>
        rw [map_one]
        exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb => rw [map_mul]; exact intAE_mul_mem D ha hb
    have := key _ hw
    rwa [show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

theorem exists_finiteAdele_equiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  intro D
  obtain ⟨ι, h1, h2, -, h4⟩ :=
    GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E
  refine ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι,
    fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩

end GlobalTheory.HostAdeleIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := GlobalTheory.T.modularFunctionFractionField_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField Ω ε T
  have hgerm := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hj := GlobalTheory.T.lv_jT_one_and_jT_smul_eq
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).1, sl_mul := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).1, an_sl := GlobalTheory.T.modularFunctionFractionField_an_sl_germ Ω ε T, an_mero := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).2,
            an_exp := fun f => (GlobalTheory.T.modularFunctionFractionField_expansion_converges Ω ε T f).2,
            level := GlobalTheory.T.fractionField_exists_gamma_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant Ω ε T a ha, bdd := GlobalTheory.T.modularFunctionFractionField_bounded_denominators Ω ε T, sat := GlobalTheory.T.modularFunctionFractionField_saturation Ω ε T,
            mem_q := GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecompositionStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  first | exact @GlobalTheory.ThetaTranslDecomp.exists_decomp | exact GlobalTheory.ThetaTranslDecomp.exists_decomp | (intros; apply GlobalTheory.ThetaTranslDecomp.exists_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem adicCompletion_exists_approx_lt (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (y c : P.adicCompletion L) (hc : c ≠ 0) :
    ∃ k : L, Valued.v (y - algebraMap L (P.adicCompletion L) k) < Valued.v c := by
  have ho : IsOpen {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    have h0 := (Valued.isOpen_ball (P.adicCompletion L)
      ((Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).restrict c)).preimage
        (continuous_sub_left y)
    simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] using h0
  have hy : y ∈ {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    show Valued.v (y - y) < Valued.v c
    rw [sub_self, map_zero]
    exact (Valuation.pos_iff _).2 hc
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L)
    (v := P)).exists_mem_open ho ⟨y, hy⟩
  exact ⟨k, hk⟩

private lemma valued_v_algebraMap_adicCompletion_foundation (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (k : L) :
    Valued.v (algebraMap L (P.adicCompletion L) k) = P.valuation L k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := P) k

theorem adicCompletion_exists_unit_approx (L : Type) [Field L] [NumberField L] (N : ℕ) (hN : 0 < N)
    (P : HeightOneSpectrum (𝓞 L)) (y : P.adicCompletion L) (hy : y ≠ 0) :
    ∃ k : Lˣ, Valued.v y = P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ P.valuation L (N : L) * P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hN1 : P.valuation L (N : L) ≤ 1 := by
    simpa using P.valuation_le_one (K := L) (N : 𝓞 L)
  have he1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set c := y * algebraMap L (P.adicCompletion L) ((N : L) * π) with hcdef
  have hc : c ≠ 0 := mul_ne_zero hy ((map_ne_zero _).2 (mul_ne_zero hN0 hπ0))
  obtain ⟨k₀, hk₀⟩ := adicCompletion_exists_approx_lt L P y c hc
  have hvc : Valued.v c = Valued.v y * (P.valuation L (N : L) * WithZero.exp (-1 : ℤ)) := by
    rw [hcdef, map_mul, valued_v_algebraMap_adicCompletion_foundation, map_mul, hπ]
  have hlt : Valued.v (y - algebraMap L _ k₀) < Valued.v y := by
    refine hk₀.trans_le ?_
    rw [hvc]
    exact mul_le_of_le_one_right' (mul_le_one' hN1 he1)
  have hyk : P.valuation L k₀ = Valued.v y := by
    rw [← valued_v_algebraMap_adicCompletion_foundation]
    apply Valuation.map_eq_of_sub_lt
    rwa [Valuation.map_sub_swap]
  have hk0 : k₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hyk
    exact hy ((Valuation.zero_iff _).1 hyk.symm)
  refine ⟨Units.mk0 k₀ hk0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, hyk]
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_right' he1
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_left' hN1

theorem finiteIdele_exists_local_approx :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  intro L _ _ N hN x
  obtain ⟨hx0, hx1⟩ := FiniteAdeleRing.isUnit_iff.1 x.isUnit
  choose k hk using fun P => adicCompletion_exists_unit_approx L N hN P _ (hx0 P)
  have hN0 : (N : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa using hN0)
  have hfin := (Filter.eventually_cofinite.1 hx1).union h2
  refine ⟨hfin.toFinset, k, fun P _ => hk P, fun P hP => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hP
  obtain ⟨hP1, hP2⟩ := hP
  simp only [Set.mem_ofPred_eq, not_not] at hP1 hP2
  exact ⟨hP1, fun hmem => hP2 (Ideal.dvd_span_singleton.2 hmem)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeDualSumWeylLatticesLeStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_dual_sum_weyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | exact GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_dualFr_sumLat_delK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeSumWeylAndDualWeylLatticesLeStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | exact GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCoverStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  first | exact @GlobalTheory.CoshSqInt.memLp_two_of_decay | exact GlobalTheory.CoshSqInt.memLp_two_of_decay | (intros; apply GlobalTheory.CoshSqInt.memLp_two_of_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosureStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_all_levels_closure : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.ThetaLevels.levels_closed | exact GlobalTheory.ThetaLevels.levels_closed | (intros; apply GlobalTheory.ThetaLevels.levels_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumImageIntertwinerSelfDualPairStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  first | exact @GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | exact GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual | (intros; apply GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual <;> assumption)
end

