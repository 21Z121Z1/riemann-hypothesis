import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.HalfPeriodStandardCM
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0229
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((TaylorLogMetric.embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_natCast_coprime {p : ℕ} [Fact p.Prime] {n : ℕ} (h : Nat.Coprime n p) : ‖(n : ℂ_[p])‖ = 1 := by
  have e : (n : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := (map_natCast _ n).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem atLin_X {σ κ : Type} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) F = Formalism.L2.Th1.G.linSub c F := rfl

theorem tauEmb_eq {D : D7} {p : ℕ} [Fact p.Prime] {lm : TaylorLogMetric.Qbar →+* ℂ_[p]} {ι : ℂ ≃+* ℂ_[p]}
    (hι : Formalism.L2.KerInert.IotaExt lm ι) (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.tauEmb D lm τ x = ι (TaylorLogMetric.embT D τ x) := by
  have h := embT_mem D τ x
  show TaylorLogMetric.lamC lm (TaylorLogMetric.embT D τ x) = _
  rw [TaylorLogMetric.lamC, dif_pos h]
  exact (hι ⟨_, h⟩).symm

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem analytic_U (B : Base D cc δ) (t : TaylorLogMetric.VC D N N') {G : TaylorLogMetric.VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (TaylorLogMetric.U D B.tor t G) Set.univ := by
  have hadd : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => z + t) Set.univ := fun z _ => by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => G (z + t)) Set.univ :=
    hG.comp hadd (fun _ _ => Set.mem_univ _)
  let ℓ : TaylorLogMetric.VC D N N' →ₗ[ℂ] ℂ := (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N').flip t
  have h2 : AnalyticOnNhd ℂ (fun z : TaylorLogMetric.VC D N N' => ℓ z) Set.univ :=
    (LinearMap.toContinuousLinearMap ℓ).analyticOnNhd _
  have h3 : ∀ z : TaylorLogMetric.VC D N N', TaylorLogMetric.Hf D B.tor z t = ℓ z := fun z => by
    show _ = formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' z t
    rw [formV_apply]; rfl
  intro z hz
  have h4 : AnalyticAt ℂ (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) z := by
    have := h2 z hz
    fun_prop
  have h5 := (h1 z hz).mul h4
  have e : TaylorLogMetric.U D B.tor t G = (fun z => G (z + t)) * (fun z : TaylorLogMetric.VC D N N' => Complex.exp (-(Real.pi : ℂ) * ℓ z -
      (Real.pi : ℂ) * TaylorLogMetric.Hf D B.tor t t / 2)) := by
    funext z
    simp only [TaylorLogMetric.U, h3, Pi.mul_apply]
  rw [e]
  exact h5

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

namespace GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem term_jets (hIn : GlobalTheory.ThLoc.Inputs) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {X : Fields} (s : Seam D X) (hs : s.Ok)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁') {p : ℕ} [Fact p.Prime] (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁')
    (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : Formalism.L2.KerInert.IotaExt lm ι)
    (hpd : p ≠ D.host.d) (h3 : p = 3 → D.host.d % 3 = 2)
    (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t)
    {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (hy : ∀ j, y j ∈ TaylorLogMetric.YYl D L L') :
    JetsIntegral (TaylorLogMetric.atLin (fun k j => TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j)
      (TaylorLogMetric.pSer D lm (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')))) := by
  obtain ⟨s₁, hs₁, e1, e2⟩ := id hE
  obtain ⟨s₂, hs₂, e3, e4⟩ := id hE'
  have hS : Nat.Coprime (s₁ * s₂) p := Nat.Coprime.mul_left hs₁ hs₂
  obtain ⟨M, hM0, hMc, hMm⟩ := (Formalism.L2.KerInert.pairing_fact D cc δ p N N' L L₁ L' L₁' hE hE').2 t ht
  have hLat := GlobalTheory.T.normalisedThetaFamily_normalised_all_places D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L₁ L₁' hA₁ p ι

  have hθ := hLat.mem_th.1
  have hEan : AnalyticOnNhd ℂ (B.eNat χ N N' L₁ L₁') Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) Set.univ :=
      (LinearMap.toContinuousLinearMap (s.flatV N N').symm.toLinearMap).analyticOnNhd _
    have h2 := hθ.comp h1 (fun _ _ => Set.mem_univ _)
    have e : (B.eNat χ N N' L₁ L₁') = (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) ∘ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) := by
      funext w
      simp
    rw [e]
    exact h2
  have hGan := analytic_U B t hEan
  have hCo : TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')) TaylorLogMetric.Qbar :=
    hIn.algT D cc δ B χ hcc hδ hχ N N' L₁ L₁' hA₁ t ⟨M, hM0, hMm⟩

  have hU : (fun z => TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁') (s.flatV N N' z)) =
      Formalism.L2.Th1.H.opU (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) ((s.flatV N N').symm t)
        (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) := by
    funext z
    rw [KS.opU_pb (s.flatV N N') _ _ (KS.form_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))), LinearEquiv.apply_symm_apply]
    simp only [Formalism.L2.Th1.H.opU, formV_apply]
    rfl

  let v : Fin n → DVar X.Tau N N' → ℂ := fun j =>
    (s.flatV N N').symm (TaylorLogMetric.embV D B.tor (((s₁ * s₂ : ℕ) : D.host.E) • y j))
  let A : Fin n → Fin n → ℂ_[p] := fun j x => if j = x then (((s₁ * s₂ : ℕ) : ℂ_[p]))⁻¹ else 0
  have hn1 : ‖(((s₁ * s₂ : ℕ) : ℂ_[p]))‖ = 1 := norm_natCast_coprime hS
  have hn0 : (((s₁ * s₂ : ℕ) : ℂ_[p])) ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hv : ∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) (s.laF B.tor L₁ L₁') (v j) := by
    intro j ω hω
    show s.flatV N N' (ω • v j) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
    rw [map_smul, LinearEquiv.apply_symm_apply]
    refine AddSubgroup.subset_closure ⟨ω, ?_, _, Formalism.L2.KerInert.ie_yy_scale s₁ s₂ e2 e3 (hy j), rfl⟩
    show ω ∈ TaylorLogMetric.lamOf D cc δ
    rw [← hlat]
    exact hω
  have hA : ∀ j x, ‖A j x‖ ≤ 1 := by
    intro j x
    by_cases h : j = x
    · simp only [A, if_pos h, norm_inv, hn1, inv_one, le_refl]
    · simp only [A, if_neg h, norm_zero, zero_le_one]
  have hfr : (fun (i : DVar X.Tau N N') x => (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : Fin n) =>
      TaylorLogMetric.tauEmb D lm k.1 (y j k.2.1 k.2.2)) (s.iT i.1, i.2) x) = frameM (ι : ℂ →+* ℂ_[p]) v A := by
    funext i x
    have e : v x i = ((s₁ * s₂ : ℕ) : ℂ) * TaylorLogMetric.embT D (s.iT i.1) (y x i.2.1 i.2.2) := by
      show TaylorLogMetric.embT D (s.iT i.1) ((((s₁ * s₂ : ℕ) : D.host.E) • y x) i.2.1 i.2.2) = _
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast]
    simp only [frameM, A, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [tauEmb_eq hι, e]
    simp only [RingHom.coe_coe, map_mul, map_natCast]
    field_simp
  have key := GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hlat (DVar X.Tau N N')
    (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L₁ L₁')
    (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) p ι hLat hpd h3 Unit (fun _ => 1)
    (fun _ => (s.flatV N N').symm t) M (fun _ => by simp) hM0
    (fun h => by
      have := Nat.Coprime.eq_one_of_dvd hMc.symm h
      exact (Fact.out : p.Prime).one_lt.ne' this)
    (fun _ => by
      show s.flatV N N' ((M : ℂ) • (s.flatV N N').symm t) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
      rw [map_smul, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
      exact hMm)
    (Fin n) v hv (Fin n) A hA
  rw [GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor D X s N N' p lm ι hι _ hGan hCo (Fin n), hfr, hU]
  simpa [thetaLin] using key

end GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d

theorem GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → TaylorLogMetric.JetsInt D lm (TaylorLogMetric.YYl D L L') F := by
  intro hIn D cc δ hcc hδ B χ hχ X s hs N N' L L' hA p _ lm hpd h3 F hF
  obtain ⟨ι, hι⟩ := hIn.lamExt p lm
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by
    rw [hL]
    exact B.lat
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL1, rfl⟩ := hF
  refine (GlobalTheory.T.latticeJetsIntegral_iff_integralFrames D N N' p lm _ _).1.2 fun n y hy => ?_
  have e : ∀ (c : D.what₂.Tau × Fin N' × Fin N → Fin n → ℂ_[p]) (G : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j)
        (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) * G k) =
      ∑ k, MvPowerSeries.C (r k) * TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) (G k) := by
    intro c G
    rw [GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.atLin_X, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, Formalism.L2.Th1.G.linSubHom_apply]
    rfl
  rw [e]
  exact GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jets_comb r _ hr fun k =>
    GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.term_jets hIn hcc hδ B χ hχ s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat (hL1 k).1 (hL1 k).2.1 (hL1 k).2.2 lm ι hι hpd h3
      (t k) (ht k) y hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegrees_small_against_typePrimes : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  first | exact @GlobalTheory.AtG.KernelSizes.sizeAt_of_params | exact GlobalTheory.AtG.KernelSizes.sizeAt_of_params | (intros; apply GlobalTheory.AtG.KernelSizes.sizeAt_of_params <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLatticesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_theta_unitary_lattice_equivariant : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N N' → DatLoc D cc SS cl N N' Ξ → ∀ (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) = TaylorLogMetric.pull D B.tor e e' (kerTh B χ SS cl N N' Ξ) := by
  first | exact @GlobalTheory.TwU.KerMove.kerTh_move | exact GlobalTheory.TwU.KerMove.kerTh_move | (intros; apply GlobalTheory.TwU.KerMove.kerTh_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftInertEigenvaluesIffThetaImageEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.InertLift

variable {D : D7}

theorem hkF_comb (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = ∑ d ∈ c.support, c d • hkF V P (Finsupp.single d 1) F := by
  funext h
  simp only [hkF, Finset.sum_apply, Pi.smul_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem hkF_nonlab (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) {d : List ℤ}
    (hd : ¬ IsLab V P d) (F : Bridge.Gf V → W) : hkF V P (Finsupp.single d 1) F = 0 := by
  funext h
  simp [hkF, rep, hd]

open Classical in

def tyOf (n : ℕ) (e : List ℤ) : List ℕ :=
  if h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y then h.choose else []

theorem labIn_tyOf {n : ℕ} {e : List ℤ} (h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y) :
    Formalism.L2.Col.InertTypeOk n (tyOf n e) ∧ e = GlobalTheory.Hk3.labIn n (tyOf n e) := by
  have hs : tyOf n e = h.choose := by
    simp only [tyOf]
    rw [dif_pos h]
  rw [hs]
  exact h.choose_spec

open Classical in

def valC (Lb : List ℤ → Prop) (n : ℕ) (a : List ℕ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  ∑ e ∈ c.support, c e * (if Lb e then a (tyOf n e) else 0)

open Classical in

theorem comb_apply {M X : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X] (e : M →ₗ[ℂ] X)
    (he : Function.Injective e) (h : (List ℤ →₀ ℂ) → Module.End ℂ M) (Tt : (List ℤ →₀ ℂ) → X → X)
    (hh : ∀ c x, e (h c x) = Tt c (e x))
    (hT : ∀ c F, Tt c F = ∑ d ∈ c.support, c d • Tt (Finsupp.single d 1) F)
    (Lb : List ℤ → Prop) (hT0 : ∀ d, ¬ Lb d → ∀ F, Tt (Finsupp.single d 1) F = 0) (n : ℕ) (a : List ℕ → ℂ) (u : M)
    (hlab : ∀ d, Lb d → ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ d = GlobalTheory.Hk3.labIn n y)
    (heig : ∀ y, Formalism.L2.Col.InertTypeOk n y → h (Finsupp.single (GlobalTheory.Hk3.labIn n y) 1) u = a y • u) (c : List ℤ →₀ ℂ) :
    h c u = valC Lb n a c • u := by
  have hone : ∀ d, h (Finsupp.single d 1) u = (if Lb d then a (tyOf n d) else 0) • u := by
    intro d
    by_cases hd : Lb d
    · obtain ⟨h1, h2⟩ := labIn_tyOf (hlab d hd)
      have := heig _ h1
      rw [← h2] at this
      rw [if_pos hd, this]
    · rw [if_neg hd, zero_smul]
      apply he
      rw [hh, hT0 d hd, map_zero]
  apply he
  rw [hh, hT, valC, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul, ← hone d, map_smul, hh]

theorem evC_congr (V : HSp D) (P : Pl D.host.E) {a b : List ℤ → ℂ} (hab : ∀ d, IsLab V P d → a d = b d) (c : List ℤ →₀ ℂ) :
    evC V P a c = evC V P b c := by
  classical
  simp only [evC, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : IsLab V P d
  · rw [if_pos hd, if_pos hd, hab d hd]
  · rw [if_neg hd, if_neg hd]

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tied_label (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m)
    (Q : A3.okI A3.A.μ0) (y : List ℕ) (hy : Formalism.L2.Col.InertTypeOk (Vc D j).rank y) :
    ∀ h, IsOpsV R.toRealDat j A3.A.μ0 h → ∀ f : (A3.A.fam.L j A3.A.μ0).S.Forms,
      R.jV j A3.A.μ0 ((A3.liftI j A3.A.μ0).opAll (Sum.inr (Q, y)) f) =
      h (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 f) := by
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hOk := h3.2.2.1
  have hin : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 →
      Good R.toRealDat A3.A.μ0 (R.plI k.1.1) ∧ conjPl (R.plI k.1.1) = R.plI k.1.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
    ⟨(hOk A3.A.μ0 k.1.1 k.1.2).1, (hOk A3.A.μ0 k.1.1 k.1.2).2,
      ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
  exact (hC.inert.hL j A3.A.μ0).elim fun Comparison₂ =>
    (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) hin Comparison₂ (Q, y) hy).2.2.2

theorem one_side (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hSch : SchurAll R.toRealDat) (hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) (j : Fin D.R.m)
    (c : Pl D.host.E → List ℤ → ℂ) (s : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms)
    (hx : ∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x)
    (hm : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c) (h0 : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
    (Q : A3.okI A3.A.μ0) :
    (∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → ∀ cW,
      MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) cW →
      D.what₂.embLL (s (Sum.inr (Q, y))) = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW) ∧
    (∀ d, IsLab (Wc D j) (R.plI Q.1) d → ∀ cV, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV (Finsupp.single d 1) →
      c (R.plI Q.1) d =
        valC (IsLab (Vc D j) (R.plI Q.1)) (Vc D j).rank (fun y => D.what₂.embLL (s (Sum.inr (Q, y)))) cV) := by
  classical
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hSF := h3.2.1
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hVall := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models).2 j A3.A.μ0
  have hWall := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 core hSch hIrr R.SF hSF j
  obtain ⟨hV, hVo, -⟩ := hVall
  obtain ⟨hW, hWo, -, -, -, -, hWev, -⟩ := hWall
  have hwW : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ Wcc R.toRealDat R.SF j c := hm
  have heig : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y →
      hV (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (s (Sum.inr (Q, y))) • R.jV j A3.A.μ0 x := fun y hy =>
    (tied_label R F hC hEx j Q y hy hV hVo x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) (hx (Sum.inr (Q, y)))).trans (LinearMap.map_smulₛₗ (R.jV j A3.A.μ0) _ x))
  have hlab : ∀ d, IsLab (Vc D j) (R.plI Q.1) d →
      ∃ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y ∧ d = GlobalTheory.Hk3.labIn (Vc D j).rank y := by
    intro d hd
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (R.plI Q.1) d).1 hd
    obtain ⟨y, ya, yb, yc, yd⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff _ d).1 ⟨h1, h2, h3 hcj⟩
    exact ⟨y, ⟨yb, yc, ya⟩, yd⟩
  have hthe : ∀ cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      R.thG j A3.A.μ0 (hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x)) =
        hW (R.plI Q.1) cW (R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x)) := fun cV cW hM =>
    (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 core hSch hIrr R.SF hSF j A3.A.μ0 (R.plI Q.1) hg cV cW hM hV hVo).1 hW hWo
      (R.jV j A3.A.μ0 x)
  have hchain : ∀ (v : ℂ) cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x) = v • R.jV j A3.A.μ0 x →
      v = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW := fun v cV cW hM hv =>
    smul_left_injective ℂ h0 (((R.thG j A3.A.μ0).map_smul v _).symm.trans
      ((congrArg (R.thG j A3.A.μ0) hv.symm).trans ((hthe cV cW hM).trans (hWev c _ hg cW _ hwW))))
  refine ⟨fun y hy cW hM => hchain _ _ cW hM (heig y hy), fun d hd cV hM => ?_⟩
  have h2 : evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) (Finsupp.single d 1) = c (R.plI Q.1) d := by
    simp [evC, hd]
  refine h2.symm.trans (hchain _ cV _ hM ?_).symm
  exact comb_apply (R.HV j A3.A.μ0).e (core.models.HV j A3.A.μ0).1 (hV (R.plI Q.1)) (hkF (Vc D j) (R.plI Q.1))
    (fun c y => hVo _ hg c y) (hkF_comb (Vc D j) (R.plI Q.1)) (IsLab (Vc D j) (R.plI Q.1))
    (fun d hd F => hkF_nonlab (Vc D j) (R.plI Q.1) hd F) (Vc D j).rank _ _ hlab heig cV

end Main

end GlobalTheory.Hk3.InertLift

open GlobalTheory.Hk3.InertLift in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.lift_inert_iff : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ (j : Fin D.R.m) (c c' : Pl D.host.E → List ℤ → ℂ) (s s' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = s' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) ↔ ∀ d, IsLab (Wc D j) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ hIrr j c c' s s' x x' hx hm h0 hx' hm' h0' Q
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hTwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hInt core hSch A3.A.μ0 _ hg hcj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC A3.A.μ0 _ hg hcj)
  obtain ⟨a1, a2⟩ := one_side R F hC hEx hSch hIrr j c s x hx hm h0 Q
  obtain ⟨b1, b2⟩ := one_side R F hC hEx hSch hIrr j c' s' x' hx' hm' h0' Q
  constructor
  · intro hs d hd
    obtain ⟨cV, hM⟩ := (hTwo.2 j).2 (Finsupp.single d 1)
    rw [a2 d hd cV hM, b2 d hd cV hM]
    simp only [hs]
  · intro hcc y
    have hval : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y)) := by
      intro y hy
      obtain ⟨cW, hM⟩ := (hTwo.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1)
      apply D.what₂.embLL.injective
      rw [a1 y hy cW hM, b1 y hy cW hM]
      exact evC_congr _ _ hcc cW
    have hx0 : x ≠ 0 := fun e => h0 ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hx0' : x' ≠ 0 := fun e => h0' ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.B.rankL j
    have e1 : A3.heckeLI j A3.A.μ0 (Q, y) x = s (Sum.inr (Q, y)) • x := hx (Sum.inr (Q, y))
    have e2 : A3.heckeLI j A3.A.μ0 (Q, y) x' = s' (Sum.inr (Q, y)) • x' := hx' (Sum.inr (Q, y))
    rcases hJ.L j A3.A.μ0 Q y with hz | ⟨y', hy', he⟩
    · have z1 : s (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun hz x).trans (zero_smul _ x).symm))
      have z2 : s' (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun hz x').trans (zero_smul _ x').symm))
      rw [z1, z2]
    · have f1 : A3.heckeLI j A3.A.μ0 (Q, y') x = s (Sum.inr (Q, y')) • x := hx (Sum.inr (Q, y'))
      have f2 : A3.heckeLI j A3.A.μ0 (Q, y') x' = s' (Sum.inr (Q, y')) • x' := hx' (Sum.inr (Q, y'))
      have g1 : s (Sum.inr (Q, y)) = s (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun he x).trans f1))
      have g2 : s' (Sum.inr (Q, y)) = s' (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun he x').trans f2))
      rw [g1, g2]
      exact hval y' (hrk ▸ hy')

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_point_theta_exhaustion : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalPin.main | exact GlobalTheory.PtLocalPin.main | (intros; apply GlobalTheory.PtLocalPin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcreteStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  first | exact @GlobalTheory.AtG.ramCols_true | exact GlobalTheory.AtG.ramCols_true | (intros; apply GlobalTheory.AtG.ramCols_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_completion_iso_tame : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  first | exact @GlobalTheory.typeVec_blockChar_fixedPlace | exact GlobalTheory.typeVec_blockChar_fixedPlace | (intros; apply GlobalTheory.typeVec_blockChar_fixedPlace <;> assumption)
end

