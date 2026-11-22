import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0785
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0774
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0796
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0798
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLatticeSumsBoundedProduct
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem fold_parseval : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  intro D ρ p m ψ hψ b₀ hb Φ φ B₁ B₂ hΦ hφ h1 h2
  haveI := m.hμ.1
  have hfd : IsAddFundamentalDomain (ratMx D ρ p) m.𝓕 m.μ := m.hμ.2.1
  have hfin : m.μ m.𝓕 = 1 := m.hμ.2.2
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : Countable (ratMx D ρ p) := by
    unfold GlobalTheory.MixModel.ratMx
    exact (AddMonoidHom.rangeRestrict_surjective _).countable
  haveI : MeasurableConstVAdd (ratMx D ρ p) (Mx D ρ p) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : SFinite m.μ := by
    have hs := hfd.sum_restrict
    open scoped Pointwise in
    haveI : ∀ g : ratMx D ρ p, IsFiniteMeasure (m.μ.restrict (g +ᵥ m.𝓕)) := fun g =>
      ⟨by rw [Measure.restrict_apply_univ, measure_vadd, hfin]; exact ENNReal.one_lt_top⟩
    rw [← hs]
    infer_instance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hfin]; exact ENNReal.one_lt_top⟩
  have hds : ∀ (Ψ : Mx D ρ p → ℂ) (B : ℝ),
      (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Ψ (rt ξ + y)‖) ∧
        ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Ψ (rt ξ + y)‖ ≤ B) →
      ∀ x y, ‖dsum ψ b₀ Ψ x y‖ ≤ B := by
    intro Ψ B hB x y
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).1
    · simpa [norm_mul, chv_norm ψ hψ] using (hB y).2
  have hB₁ : 0 ≤ B₁ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h1 0).2
  have hB₂ : 0 ≤ B₂ := (tsum_nonneg (fun _ => norm_nonneg _)).trans (h2 0).2
  have hm : StronglyMeasurable (Ap ψ b₀ Φ φ) :=
    (dsum_stronglyMeasurable ψ hψ b₀ Φ hΦ (fun y => (h1 y).1)).mul
      (Complex.continuous_conj.comp_stronglyMeasurable
        (dsum_stronglyMeasurable ψ hψ b₀ φ hφ (fun y => (h2 y).1)))
  have hint : Integrable (Ap ψ b₀ Φ φ) ((m.μ.restrict m.𝓕).prod (m.μ.restrict m.𝓕)) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (B₁ * B₂) (ae_of_all _ (fun v => ?_))
    rw [Ap, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hds Φ B₁ h1 _ _) (hds φ B₂ h2 _ _) (norm_nonneg _) hB₁
  have hP : StronglyMeasurable (fun y => Φ y * conj (φ y)) :=
    hΦ.mul (Complex.continuous_conj.comp_stronglyMeasurable hφ)
  have hsum : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
      ≤ ENNReal.ofReal (B₁ * B₂) := by
    intro y
    calc ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y) * conj (φ (rt ξ + y))‖ₑ
        ≤ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E,
            ‖Φ (rt ξ + y)‖ₑ * ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := by
          refine ENNReal.tsum_le_tsum (fun ξ => ?_)
          rw [enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj, ofReal_norm]
          gcongr
          exact ENNReal.le_tsum (f := fun η => ‖φ (rt η + y)‖ₑ) ξ
      _ = (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (rt ξ + y)‖ₑ) *
            ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (rt η + y)‖ₑ := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal B₁ * ENNReal.ofReal B₂ := by
          gcongr
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h1 y).1]
            exact ENNReal.ofReal_le_ofReal (h1 y).2
          · simp only [← ofReal_norm]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (h2 y).1]
            exact ENNReal.ofReal_le_ofReal (h2 y).2
      _ = ENNReal.ofReal (B₁ * B₂) := (ENNReal.ofReal_mul hB₁).symm
  have hPint : Integrable (fun y => Φ y * conj (φ y)) m.μ := by
    refine ⟨hP.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [hfd.lintegral_eq_tsum'']
    beta_reduce
    rw [← lintegral_tsum (f := fun (g : ratMx D ρ p) (x : Mx D ρ p) => ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ)
      (fun g => ((hP.measurable.comp (measurable_const_vadd g)).enorm).aemeasurable)]
    calc ∫⁻ x in m.𝓕, ∑' g : ratMx D ρ p, ‖Φ (g +ᵥ x) * conj (φ (g +ᵥ x))‖ₑ ∂m.μ
        ≤ ∫⁻ _ in m.𝓕, ENNReal.ofReal (B₁ * B₂) ∂m.μ := by
          refine lintegral_mono (fun x => ?_)
          refine (ENNReal.tsum_le_tsum_comp_of_surjective
            (AddMonoidHom.rangeRestrict_surjective
              (Formalism.L2.Theta.incA D).toAddMonoidHom.mapMatrix) _).trans ?_
          exact hsum x
      _ < ⊤ := by
          rw [lintegral_const, Measure.restrict_apply_univ, hfin, mul_one]
          exact ENNReal.ofReal_lt_top
  rw [← Measure.prod_restrict, integral_prod _ hint, integral_fold m _ hPint]
  refine integral_congr_ae (ae_of_all _ (fun y => ?_))
  exact GlobalTheory.T.heisenberg_character_orthogonality m ψ hψ b₀ hb (fun η => Φ (rt η + y)) (fun η => φ (rt η + y)) (h1 y).1 (h2 y).1

end GlobalTheory.CompanionTheory.FJE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawa
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, iw₁, lev⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ hcm n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, iw₂, good⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact F E σ hcm n J hJ r X Y hW
  obtain ⟨K, hK, iw, -⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ hcm n J hJ r X Y hW
    K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ lev good
  exact ⟨K, hK, iw⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuity
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_mixS_joint {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hω : IsWeilDatumO ψ S T χS χT om) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w₀ : WO S₀ T) :
    Continuous fun u : GA D S × Mx D T.rank ρ => d.mixS T ψ μ 𝓕 (om (u.1, 1) f) u.2 w₀ := by
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have cX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  refine GlobalTheory.Core.Rk.IP.continuous_covolOne_integral hμ
    (fun (u : GA D S × Mx D T.rank ρ) a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T u.2)
      (heisO ψ S T (d.ext0 T w₀) (om (u.1, 1) f))) 0) ?_
    (fun u => d.integrandS_periodic (hω.om_pres _ _ hf) u.2 w₀)
  simp only [HypDec.integrandS_eq]
  have c1 : Continuous fun p : (GA D S × Mx D T.rank ρ) × Mx D T.rank ρ => d.extY T p.2 := cY.comp continuous_snd
  have c2 : Continuous fun p : (GA D S × Mx D T.rank ρ) × Mx D T.rank ρ => d.extX T p.1.2 :=
    cX.comp (continuous_snd.comp continuous_fst)
  exact (hω.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH c1 c2)).mul
    ((GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hω f hf).comp
      (((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk ((c1.add c2).add continuous_const)))

set_option maxHeartbeats 1000000 in

theorem weilCont : WeilCont := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ u : G D n × Mx D V.rank n, (ω u.1 Φ).1 u.2 =
      (dblDec A).mixS V ψ₀ μ 𝓕 (omh (κ.symm u.1, 1) f) u.2 0 := by
    intro u
    have h := hT (κ.symm u.1) f hf Φ hfΦ.symm
    have e : κ (κ.symm u.1) = u.1 := κ.apply_symm_apply u.1
    rw [e] at h
    exact congrFun h u.2
  have hc := continuous_mixS_joint ψ₀ (dblDec A) hW hμ hf 0
  have hk := (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  have hc' : Continuous fun u : G D n × Mx D V.rank n => (dblDec A).mixS V ψ₀ μ 𝓕 (omh (κ.symm u.1, 1) f) u.2 0 :=
    hc.comp (f := fun u : G D n × Mx D V.rank n => (κ.symm u.1, u.2)) ((hk.comp continuous_fst).prodMk continuous_snd)
  exact hc'.congr fun u => (key u).symm

end GlobalTheory.CompanionTheory.ThTot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.WeilLaw

theorem weil_parabolic_law : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)),
    IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n),
    ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n ψ χ θ V μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by
    rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.CompanionTheory.WeilLaw
end

