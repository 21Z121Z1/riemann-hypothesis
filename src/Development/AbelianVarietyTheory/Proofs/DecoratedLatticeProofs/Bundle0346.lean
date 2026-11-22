import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ENNReal NNReal

namespace GlobalTheory.MixedAbsGrowth

theorem map_infPart_nsmul {D : D7} {m r : ℕ} (n : ℕ) (u : Mx D m r) (hu : u.map (infPart D) = 0) :
    (n • u).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hu i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h, mul_zero]

theorem map_infPart_actO {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : u.map (infPart D) = 0) : (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ x
  rwa [inv_inv, inv_inv] at this

theorem mixed_abs_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h (w : WO S₀ T), (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 (om (g, h) f) x w‖ₑ) ≤ ENNReal.ofReal (C * (height S g * height T h) ^ A) := by
  intro D ψ S T χS χT om hW S₀ ρ d v f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K₀, hK₀, -, m, hm⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple hUo
  obtain ⟨k, hk⟩ := GlobalTheory.T.mixedCoordinate_tsum_le_of_theta_level_multiple D ψ hW.std θ hθ S S₀ T ρ d v
  obtain ⟨C, hC⟩ := hk K₀ hK₀
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hW θ hθ k
  obtain ⟨c, hc⟩ := hA f hf
  refine ⟨(C : ℝ) * (m : ℝ) ^ k * max c 0, A + k, fun g h w => ?_⟩
  obtain ⟨n, hn0, hnm, hnU⟩ := hm g h
  have hF := hW.om_pres (g, h) f hf
  have hlev : ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) (om (g, h) f) = om (g, h) f := by
    intro u hu hinf
    have h1 := hU _ (hnU u hu hinf) (map_infPart_actO _ _ _ (map_infPart_nsmul n u hinf))
    have h2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (n • u)) f hf
    rw [h1, actO_actO_inv] at h2
    exact h2.symm
  have h1 := hC n hn0 (om (g, h) f) hF hlev w
  have h2 : supSob ψ θ k (om (g, h) f) ≤ ENNReal.ofReal (c * (height S g * height T h) ^ A) := hc g h
  set H : ℝ := height S g * height T h with hH
  have H0 : 0 ≤ H := mul_nonneg (height_pos S g).le (height_pos T h).le
  refine h1.trans ?_
  have e1 : ((C : ℝ≥0∞) * (n : ℝ≥0∞) ^ k) = ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ k) := by
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow (Nat.cast_nonneg n),
      ENNReal.ofReal_natCast]
  rw [e1]
  refine (mul_le_mul' le_rfl (h2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg H0 A))))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : (n : ℝ) ^ k ≤ ((m : ℝ) * H) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg n) hnm k
  have hc0 : 0 ≤ max c 0 := le_max_right c 0
  calc (C : ℝ) * (n : ℝ) ^ k * (max c 0 * H ^ A) ≤ (C : ℝ) * ((m : ℝ) * H) ^ k * (max c 0 * H ^ A) := by
        gcongr
    _ = (C : ℝ) * (m : ℝ) ^ k * max c 0 * H ^ (A + k) := by rw [mul_pow, pow_add]; ring

end GlobalTheory.MixedAbsGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.KJReal

variable {D : D7}

theorem detPlus_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus 1 1 a b = b.det ^ n * a.det ^ m := by
  unfold GlobalTheory.WeilParts.detPlus
  have e2 : (1 + 1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = (2 : ℂ) • 1 := by
    rw [two_smul]
  rw [Matrix.transpose_one, Matrix.one_kronecker_one, sub_self, smul_zero, add_zero, e2, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

theorem exp_identity (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (e mS mT : ℤ) (nS nT : ℕ) (hS : (nS : ℤ) = mS + mS)
    (hT : (nT : ℤ) = mT + mT) :
    (a ^ (e - mT))⁻¹ * b ^ (e - mS) * (b ^ nS * a⁻¹ ^ nT) = a ^ (-e - mT) * b ^ (e + mS) := by
  rw [inv_pow, ← zpow_natCast b, ← zpow_natCast a, ← zpow_neg a, ← zpow_neg a]
  calc (a ^ (-(e - mT)) * b ^ (e - mS) * (b ^ (nS : ℤ) * a ^ (-(nT : ℤ))))
      = a ^ (-(e - mT)) * a ^ (-(nT : ℤ)) * (b ^ (e - mS) * b ^ (nS : ℤ)) := by ring
    _ = a ^ (-(e - mT) + -(nT : ℤ)) * b ^ (e - mS + (nS : ℤ)) := by rw [← zpow_add₀ ha, ← zpow_add₀ hb]
    _ = a ^ (-e - mT) * b ^ (e + mS) := by
      congr 2
      · rw [hT]; ring
      · rw [hS]; ring

end GlobalTheory.KJReal

namespace GlobalTheory.KJReal

end GlobalTheory.KJReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneLeMulOfOneLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumLoc

variable {D : D7}

theorem intAE_eq_hat :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem mul_mem {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  rw [intAE_eq_hat] at hx hy ⊢
  exact GlobalTheory.AdIdem.mul_mem_hat _ _ hx hy

theorem idem_mul_sum {es : Formalism.L2.DIV.Pl D.host.E → AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hes : ∀ Q ∈ S, Formalism.L2.NTheta.IsIdemAt (es Q) Q) (hc : (∑ Q ∈ S, es Q) * cA D (∑ Q ∈ S, es Q) = 0)
    {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) : es P * ∑ Q ∈ S, es Q = es P := by
  have h1 : ∀ i ∈ S, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ S, ∀ j ∈ S, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es S h1 hc
  rw [Finset.mul_sum, Finset.sum_eq_single P
    (fun Q hQ hQP => GlobalTheory.PlaceDatum.idemAt_mul (hes P hP) (hes Q hQ) (hcross P hP Q hQ) (hcross Q hQ P hP) hQP)
    (fun h => absurd hP h), h1 P hP]

end GlobalTheory.IdemSumLoc

namespace GlobalTheory.IdemSumLoc

end GlobalTheory.IdemSumLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedChainLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in

theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, (finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, (infPart D).map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedIntegralLinearPropertiesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularised_integral_linear_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χS χ : (AE D)ˣ →* Circle) (omh : WRep S W), IsInfFam θ → IsWeilDatumO ψ S W χS χ omh → ∀ mW : Measure (GA D W), EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), (∀ φ', IsThetaFunO ψ S W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → (∀ f f', IsThetaFunO ψ S W f → IsThetaFunO ψ S W f' → ∀ g, regRes omh mW θ τ d₀ b' zH P (f + f') g = regRes omh mW θ τ d₀ b' zH P f g + regRes omh mW θ τ d₀ b' zH P f' g) ∧ ∀ (c : ℂ) f, IsThetaFunO ψ S W f → ∀ g, regRes omh mW θ τ d₀ b' zH P (c • f) g = c * regRes omh mW θ τ d₀ b' zH P f g := by
  first | exact @GlobalTheory.Core.Rk.regRes_linear | exact GlobalTheory.Core.Rk.regRes_linear | (intros; apply GlobalTheory.Core.Rk.regRes_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem sum_support_comb {Y Z G : Type*} [AddCommMonoid G] [Module ℂ G] (n : ℕ) (a : Fin n → Y →₀ ℂ)
    (b : Fin n → Y → Z →₀ ℂ) (R : Z → G) :
    ∑ z ∈ (∑ i, ∑ y ∈ (a i).support, a i y • b i y).support, (∑ i, ∑ y ∈ (a i).support, a i y • b i y) z • R z =
      ∑ i, ∑ y ∈ (a i).support, a i y • ∑ z ∈ (b i y).support, b i y z • R z := by
  change Finsupp.sum _ (fun z r => r • R z) = _
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem twoX_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is →
    (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  intro D c 𝒯 t hBi hCen hLS hc ht hreal hker hrd
  intro j hj C hC y
  have hj0 : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  obtain ⟨χ, hχ⟩ := hrd j (by omega)
  have step1 : ∃ (n : ℕ) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank)
      (P' : Fin n → PolF D (c.X (j + 1 + 1)).rank (c.X (j + 1)).rank), ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
        (t s).two j (fun α => (t s).rd j α ψ y) C β = ∑ i, ∑ γ,
          ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
    by_cases hex : ∃ (s : 𝒯) (_ : (t s).Ch j) (γ : (t s).Ch (j + 1)) (_ : (t s).Ch (j + 1 + 1)), True
    · obtain ⟨s₀, α₀, γ₀, β₀, -⟩ := hex
      obtain ⟨n, P, P', hF⟩ := GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform D hBi hCen hLS c.ψ c.θ hc.inf (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))
        (c.x j) (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x j (by omega)) (hc.x (j + 1) (by omega)) (hc.x (j + 1 + 1) (by omega))
        ((t s₀).ker j α₀ γ₀) ((t s₀).ker (j + 1) γ₀ β₀) ((ht s₀).ker j hj0 α₀ γ₀) ((ht s₀).ker (j + 1) hj1 γ₀ β₀) χ C hC.1 hC.2
      refine ⟨n, P, P', fun s ψ hψ β => ?_⟩
      have hrdψ := fun α => hχ s ψ hψ α y
      have e1 : ∀ α γ, biLift ((t s).kom j) ((t s).kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ((t s).rd j α ψ y)
          (biComb c.ψ _ _ _ ((t s).dd j α γ) ((t s).dd (j + 1) γ β) C) =
          ∑ i, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := fun α γ =>
        hF ((t s).ker j α γ) ((t s).ker (j + 1) γ β) ((ht s).ker j hj0 α γ) ((ht s).ker (j + 1) hj1 γ β) rfl rfl
          (fun a ha b hb f hf => hreal j hj0 s s₀ a ha b hb f hf)
          (fun a ha b hb f hf => hreal (j + 1) hj1 s s₀ a ha b hb f hf) _ (hrdψ α).1 (hrdψ α).2
      have e2 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
          ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
        intro i γ
        have h := (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
          ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 ((t s).Ch j) Finset.univ (fun _ => 1)
          (fun α => ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y))
          (fun α _ => (hLS c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
            ((ht s).ker j hj0 α γ) (P i)).2.1 _ (hrdψ α).1)
        simpa using h
      simp only [Tup.two, e1, e2]
      rw [Finset.sum_comm]
      calc _ = ∑ γ, ∑ i, ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) :=
            Finset.sum_congr rfl fun γ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    · push Not at hex
      refine ⟨0, Fin.elim0, Fin.elim0, fun s ψ _ β => ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun γ _ => ?_
      exact ((hex s α γ β).elim)
  obtain ⟨n, P, P', hstep⟩ := step1
  choose a ha using fun i : Fin n => hker j hj0 y (P i)
  choose b hb using fun (i : Fin n) (y' : c.Fr (j + 1)) => hker (j + 1) hj1 y' (P' i)
  obtain ⟨χ', hχ'⟩ := hrd (j + 1) (by omega)
  refine ⟨∑ i, ∑ y' ∈ (a i).support, a i y' • b i y', fun s ψ hψ β => ?_⟩
  rw [hstep s ψ hψ β, sum_support_comb]
  have hKψ := (ht s).stabK j hj0 ψ hψ
  have e3 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
        (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
      ∑ y' ∈ (a i).support, ((t s).cK j * a i y') • ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1))
        (P' i) ((t s).rd (j + 1) γ ((t s).K j ψ) y') := by
    intro i γ
    rw [ha i s ψ hψ γ, Finset.smul_sum]
    simp only [smul_smul]
    exact (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
      ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 _ _ _ _ (fun y' _ => (hχ' s _ hKψ γ y').1)
  simp only [e3]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.smul_sum, hb i y' s _ hKψ β, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem kerX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro j hj y P
  have hj1 : j + 1 ≤ D.R.m := hj
  obtain ⟨hpos, hab⟩ := hρ.rk j hj
  obtain ⟨hB, ν, hν1, hνL, hmain⟩ := GlobalTheory.T.thetaLifts_all_charts_eq_classSum D c ρ hc hρ j hj1 hab
  obtain ⟨m', y', s, hinv, havg⟩ := @GlobalTheory.KJAvg.avg_span D.what₂.Tau _ (ρ.N j) (ρ.N (j + 1)) hab hpos (ρ.lam j) (ρ.n j)
    (GinfC (c.X j)) _ _ _ _ hB ν hν1 hνL (fun k τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ) (hρ.uni j _) (ρ.fr j y).1
    (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P)
  have hz : ∀ i, ∀ τ, IsUnit ((fun τ => ρ.sc j τ • y' i τ) τ).det := by
    intro i τ
    simp only [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit (hρ.sc j τ))).mul (hinv i τ)
  let z : Fin m' → FrN D (ρ.N (j + 1)) := fun i => ⟨fun τ => ρ.sc j τ • y' i τ, hz i⟩
  let y'' : Fin m' → c.Fr (j + 1) := fun i => (ρ.fr (j + 1)).symm (z i)
  let cst : ℂ := ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)
  have key := hmain 1 (fun _ => y) (fun _ => P) m' y' y'' (fun i => cst * s i)
    (by intro i τ; simp only [y'', Equiv.apply_symm_apply]; rfl)
    (by
      intro F hF Λ
      rw [Fin.sum_univ_one, havg F hF Λ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  refine ⟨∑ i, Finsupp.single (y'' i) (cst * s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ), ?_⟩
  intro s' ψ hψ γ
  obtain ⟨⟨A, hA'⟩, _⟩ := hA s'
  have h1 := key (t s') A (ht s') hA' ψ hψ γ
  rw [Fin.sum_univ_one] at h1
  rw [h1]
  congr 1
  change _ = Finsupp.sum _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
  rw [← Finsupp.sum_finset_sum_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y') (zero_smul ℂ _)]

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_uniformiserIdele_value_unramifiedChar : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.SplitUnifIdele.value_eq_val | exact GlobalTheory.SplitUnifIdele.value_eq_val | (intros; apply GlobalTheory.SplitUnifIdele.value_eq_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageWittIndexLtAndPlacesTwoSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.WittTwo

theorem wittIndex_lt_and_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D c j s hj hs
  refine ⟨?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hpar : GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.ParallelSig s.V (sigYD D.R j).1 (sigYD D.R j).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.parallelSig_of_sigOK hs.sigOK (fun τ => hs.sig τ)
  obtain ⟨W, hW, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex (s.V : HSpace D.host.E)).1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) s.V τ (hpar τ) W (fun x hx y hy => by
    have := hW hy
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this x hx)
  have h3 := D.R.three_m_lt_t
  simp only [sigYD] at h1
  omega

end GlobalTheory.ChainOnto.WittTwo
end

