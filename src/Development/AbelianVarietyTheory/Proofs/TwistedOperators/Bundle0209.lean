import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z, compFin D.host.F D.host.E (PP.under (𝓞 D.host.F)) (e + cA D e) = 1 := by
  first | exact @GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | exact GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one | (intros; apply GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  first | exact @GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | exact GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | (intros; apply GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocal
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem charpoly_eq_sharp (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (γ : GRat σ J) :
    γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  have h : (γ.1.1.map (σ : E →+* E))ᵀ * J * γ.1.1 = J := γ.2
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).2 (Ne.isUnit hJ)
  obtain ⟨U, hU⟩ := hJu
  have hg : IsUnit γ.1.1 := γ.1.isUnit
  have hgd : IsUnit γ.1.1.det := (Matrix.isUnit_iff_isUnit_det _).1 hg
  have hJd : IsUnit J.det := Ne.isUnit hJ
  set g := γ.1.1 with hgdef
  have h2 : (g.map (σ : E →+* E))ᵀ = J * g⁻¹ * J⁻¹ := by
    have : (g.map (σ : E →+* E))ᵀ * J = J * g⁻¹ := by
      conv_rhs => rw [← h]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    rw [← this, Matrix.mul_nonsing_inv_cancel_right _ _ hJd]
  set c : E := (-1) ^ n * Ring.inverse g.det with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (inv_ne_zero hgd.ne_zero)
  have hdeg : g.charpoly.natDegree = n := by simp
  have h3 : g.charpoly.map (σ : E →+* E) = C c * reflect n g.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose, h2, ← hU, Matrix.charpoly_units_conj,
      Matrix.charpoly_inv _ hg, ← Matrix.reverse_charpoly, Polynomial.reverse, hdeg, hc]
    simp
  have h4 : σ (g.charpoly.eval 0) = c := by
    have e : σ (g.charpoly.eval 0) = (g.charpoly.map (σ : E →+* E)).coeff 0 := by
      rw [coeff_map, coeff_zero_eq_eval_zero]; rfl
    have m : g.charpoly.coeff n = 1 := by
      have := (Matrix.charpoly_monic g).coeff_natDegree
      rwa [hdeg] at this
    rw [e, h3, coeff_C_mul, coeff_reflect, revAt_zero, m, mul_one]
  unfold sharp
  rw [h4, h3, reflect_C_mul, reflect_reflect, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1, one_mul]

end GlobalTheory.TrEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermConvergesOfLintegralUnfoldingEqStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classTerm_converges_of_lintegral_unfolding_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  first | exact @GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq | exact GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq | (intros; apply GlobalTheory.ClassTerm.hasClassInt_of_lintegral_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevkLoc

theorem smul_mem_of_isAA {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (h : IsAA Λ ΛT) (c : D.host.E)
    (hc : ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c * x) : ∀ x ∈ Λ, c • x ∈ ΛT := by
  intro x hx
  have hx' := (h x).1 hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hc a ha
    rw [smul_smul, ← hb]
    have : ((b : D.host.E)) • t = b • t := (algebraMap_smul D.host.E b t)
    rw [this]
    exact ΛT.smul_mem b ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact ΛT.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact ΛT.neg_mem hx

theorem smul_mem_ideal_smul {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (P : Ideal (𝓞 D.host.E)) (c : D.host.E)
    (h : ∀ x ∈ Λ, c • x ∈ ΛT) : ∀ x ∈ P • Λ, c • x ∈ P • ΛT := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun p hp y hy => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul hp (h y hy)
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

theorem congr_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT →
    ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) →
    ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  intro D k Λ ΛT P hP hAA m hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity D
  choose b hb using fun i => hc i (a i) (ha i)
  have hb1 : ∑ i, b i = 1 := by
    have : ((∑ i, b i : 𝓞 D.host.E) : D.host.E) = ((1 : 𝓞 D.host.E) : D.host.E) := by
      push_cast
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact hb i
    exact RingOfIntegers.ext this
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hb1]
    exact Ideal.sum_mem _ fun i _ => hcon i
  refine ⟨b i, hi, fun u hu => ?_⟩
  have hA : ∀ t ∈ ΛT, a i • t ∈ Λ := fun t ht =>
    (hAA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, t, ht, rfl⟩)
  have hC : ∀ x ∈ P • Λ, c i • x ∈ P • ΛT :=
    smul_mem_ideal_smul P (c i) (smul_mem_of_isAA hAA (c i) (hc i))
  have hu' := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D ΛT Λ (a i) hA u hu
  have h1 := hm _ hu'
  have h2 := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D (P • Λ) (P • ΛT) (c i) hC _ h1
  convert h2 using 1
  rw [Matrix.mulVec_smul, ← smul_sub, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hb i]

end GlobalTheory.LevkLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioInertEqZetaSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_localTwistedLFactor_ratio_inert_eq_zetaSum : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  first | exact @GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert | exact GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert | (intros; apply GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioSplitEqZetaSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_localTwistedLFactor_ratio_split_eq_zetaSum : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → (B w).map star = (B w).map (·⁻¹) → m w * m w' = 1 → ‖(m w : ℂ)‖ = 1 → quadSign D v = 1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) := by
  first | exact @GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc | exact GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc | (intros; apply GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPartMemCompletedSelfDualLatticeIffSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitRowLat

variable {D : D7}

theorem smul_mem_latHat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    ∀ a ∈ intAE D, ∀ y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
      (fun i => a * y i) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  intro a ha y hy
  change y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hy
  change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        Λ.smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem latHat_selfDual (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
        hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hsum : ∀ w x : Fin V.rank → D.host.E,
      (∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b)) =
        ∑ i, ∑ j, star (x i) * HSpace.gram V i j * w j := by
    intro w x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply]
    change w b * HSpace.gram V a b * star (x a) = _
    ring
  have hL : ∀ w : Fin V.rank → D.host.E,
      (∀ x ∈ Λ, ∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b) ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ w ∈ Λ := by
    intro w
    rw [hΛ.2 w]
    refine forall₂_congr fun x _ => ?_
    rw [FractionalIdeal.mem_one_iff, hsum]
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank Λ (GlobalTheory.Member.cF D)
    (HSpace.gram V)ᵀ 1 hΛ.1.fg hΛ.1.span_eq_top hcc hG hdet one_ne_zero hL
  rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one] at key
  simp only [GlobalTheory.LatDual.hR_eq_hermA]
  constructor
  · intro hy z hz
    change z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_latHat V Λ _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

theorem mem_iff (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z : Fin V.rank → AE D,
        (fun i => finPart D (z i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) →
          finPart D (GlobalTheory.SplitDualLat.form V x z) ∈ intAE D := by
  rw [latHat_selfDual V Λ hΛ]
  constructor
  · intro h z hz
    rw [← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA, GlobalTheory.SplitDualLat.finPart_form]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using GlobalTheory.SplitDualLat.finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← GlobalTheory.SplitDualLat.finPart_form, ← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)

theorem isInt_iff_le_one {v : FinPl D} (x : Fv D.host.F v) :
    GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x ↔ Valued.v x ≤ 1 := by
  rw [GlobalTheory.SplitHecke.isInt_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem conj_mem_latHat_iff : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  intro D V Λ β hΛ hβ v φ e he y
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he
  have hcol := GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D V Λ β hΛ hβ v φ e he
  have hmapQ : V.gram.map (rdQ φ) = V.gram.map fun a => rdA φ (incA D a) := by
    ext i j
    simp only [Matrix.map_apply, hQ]
  rw [mem_iff V Λ hΛ, hmapQ]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => rdA φ (s ((frCo φ β).1 k j))) = (frCo φ β).1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hcol fun k => s ((frCo φ β).1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; simp
      · rw [Pi.single_eq_of_ne hi]; simp)
    rw [GlobalTheory.SplitDualLat.form_mul, GlobalTheory.SplitDualLat.cA_cA, he.1.1, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h1,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, dotProduct_single, mul_one] at h2
    exact (isInt_iff_le_one _).1 h2
  · intro h z hz
    have h1 := smul_mem_latHat V Λ _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hcol z).1 h1
    have h3 := GlobalTheory.SplitDualLat.form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, GlobalTheory.SplitDualLat.cA_cA] at h3
    have h4 : (fun k => rdA φ (z k)) = (frCo φ β).1 *ᵥ (((frCo φ β)⁻¹).1 *ᵥ fun k => rdA φ (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      GlobalTheory.SplitHecke.isInt_iff]
    exact sum_mem fun i _ => mul_mem (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h i)))
      (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h2 i)))

end GlobalTheory.SplitRowLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamificationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  first | exact @GlobalTheory.ConjSplitChars.conj_chars_res | exact GlobalTheory.ConjSplitChars.conj_chars_res | (intros; apply GlobalTheory.ConjSplitChars.conj_chars_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffFockGaussianFormOfLinearMapFamilyStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  first | exact @GlobalTheory.FockFamily.fockForm_family_contDiff | exact GlobalTheory.FockFamily.fockForm_family_contDiff | (intros; apply GlobalTheory.FockFamily.fockForm_family_contDiff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocksStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  first | exact @GlobalTheory.FockFamily.contDiff_blockB_blockD | exact GlobalTheory.FockFamily.contDiff_blockB_blockD | (intros; apply GlobalTheory.FockFamily.contDiff_blockB_blockD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanSquareNormWeilRepSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilNormCont

theorem continuous_meanSquareNorm_weilRep_sub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsCovolOne (ratL T S) μ 𝓕 → ∀ f₁ f₂ : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₂ → Continuous fun p : GA D S × GA D T => nrm2 μ 𝓕 (om p f₁ - f₂) := by
  intro D ψ S T χS χT om μ 𝓕 hom hμ f₁ f₂ h₁ h₂
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b, hb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₂ h₂ {1} isCompact_singleton
  have hb' : ∀ w, ‖f₂ w‖ ≤ b := fun w => by simpa using hb 1 rfl w
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom f₁ h₁ K hK
  unfold nrm2
  refine continuousAt_of_dominated (bound := fun _ => (c + b) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    exact ((((hom.om_pres p f₁ h₁).cont.sub h₂.cont).norm.pow 2).measurable).aestronglyMeasurable
  · filter_upwards [hK0] with p hp
    refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hc p hp w) (hb' w))) 2
  · refine Filter.Eventually.of_forall fun w => ?_
    exact (((hom.om_cont f₁ h₁ w).sub continuous_const).norm.pow 2).continuousAt

end GlobalTheory.WeilNormCont
end

