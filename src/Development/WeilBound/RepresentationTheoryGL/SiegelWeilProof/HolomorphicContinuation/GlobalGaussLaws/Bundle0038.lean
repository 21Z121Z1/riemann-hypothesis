import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0037
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaAutomorphicOfConvergence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableRho
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

def rr (m n : ℕ) : ℝ := ((Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 : ℕ) : ℝ)

theorem integrable_rho : Integrable (fun u : Fin m → Fin n → ℂ => (1 + ‖u‖) ^ (-rr m n)) := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  apply integrable_one_add_norm
  unfold rr; push_cast; linarith

set_option synthInstance.maxHeartbeats 400000 in

theorem hloc_away {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] {Ψ : Mx D m n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    (K : Set (Fin m → Fin n → ℂ)) (hK : IsCompact K) :
    ∫⁻ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ∂μ ≠ ∞ := by
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) 1 one_pos
  have hmem := hΨ.2 (gs 1) ⟨S, funext hS⟩
  have hI := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ μ ⟨_, hmem⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hgc : Continuous fun u : Fin m → Fin n → ℂ => ‖gs (n := n) 1 u‖ :=
    continuous_norm.comp (S.continuous.congr fun u => hS u)
  obtain ⟨u0, -, hu0⟩ := hK.exists_isMinOn hne hgc.continuousOn
  have hδ : 0 < ‖gs (n := n) 1 u0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hle : ∀ z, K.indicator 1 (piF θ τ fr z) * ‖Ψ z‖ₑ ≤
      ENNReal.ofReal (‖gs (n := n) 1 u0‖)⁻¹ * ‖tens θ τ fr (gs 1) Ψ z‖ₑ := by
    intro z
    by_cases hz : piF θ τ fr z ∈ K
    · rw [Set.indicator_of_mem hz, Pi.one_apply, one_mul]
      have h1 : tens θ τ fr (gs 1) Ψ z = gs (n := n) 1 (piF θ τ fr z) * Ψ z := rfl
      rw [h1, enorm_mul, ← mul_assoc]
      conv_lhs => rw [← one_mul ‖Ψ z‖ₑ]
      gcongr
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_inv_mul, one_le_div hδ]
      exact hu0 hz
    · rw [Set.indicator_of_notMem hz, zero_mul]; exact zero_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.hasFiniteIntegral.ne

set_option synthInstance.maxHeartbeats 800000 in

theorem hint_int {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure]
    {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (x : Mx D V.rank n) :
    Integrable (fun z => (1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖) μ := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hΨc := cont_of_away hθ hΨ
  have hπ := continuous_piF (n := n) hθ τ fr
  obtain ⟨c, hc⟩ := Fib.fib_meas μ (piF θ τ fr) hπ (sIns τ fr) (piF_sIns hθ τ hdet) (fun z => ‖Ψ z‖ₑ)
    hΨc.enorm.measurable (fun z u => by simp only [away_add hθ hΨ]) (hloc_away hθ μ hΨ)
  have hρc : Continuous fun u : Fin V.rank → Fin n → ℂ => (1 + ‖u‖) ^ (-rr V.rank n) :=
    (continuous_const.add continuous_norm).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg u)).ne'
  refine ⟨((hρc.comp hπ).mul (continuous_Bw hθ hψ hΨ x).norm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have e1 : ∀ z, ‖(1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n) * ‖Bw ψ V θ τ fr Ψ x z‖‖ₑ =
      ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ := by
    intro z
    rw [enorm_mul, norm_Bw hψ, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (Ψ z), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      enorm_norm, ofReal_norm_eq_enorm]
  simp_rw [e1]
  have e2 : ∫⁻ z, ENNReal.ofReal ((1 + ‖piF θ τ fr z‖) ^ (-rr V.rank n)) * ‖Ψ z‖ₑ ∂μ =
      ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)) ∂((μ.withDensity fun z => ‖Ψ z‖ₑ).map (piF θ τ fr)) := by
    rw [lintegral_map (f := fun u : Fin V.rank → Fin n → ℂ => ENNReal.ofReal ((1 + ‖u‖) ^ (-rr V.rank n)))
      (ENNReal.measurable_ofReal.comp hρc.measurable) hπ.measurable]
    have e := lintegral_withDensity_eq_lintegral_mul μ hΨc.enorm.measurable
      ((ENNReal.measurable_ofReal.comp hρc.measurable).comp hπ.measurable)
    simp only [Function.comp_def] at e
    rw [e]
    congr 1; ext z; simp [mul_comm]
  rw [e2, hc, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hI := (integrable_rho (m := V.rank) (n := n)).hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  congr 1; ext u
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

theorem alg_id (Z R : ℂ) (hZ : Z ≠ 0) (hR : R ≠ 0) (k j : ℤ) (p q m : ℕ) (hm : p + q = m) (hj : k - m = j + j) :
    (Z / R) ^ k * R ^ (m : ℤ) = (Z * (Z / R ^ 2)) ^ (k - j) * ((Z / R ^ 2) ^ (-(p : ℤ)) * (Z / R ^ 2) ^ (-(q : ℤ))) := by
  have hk : k = (m : ℤ) + j + j := by omega
  have hkj : k - j = (m : ℤ) + j := by omega
  have hpq : -(p : ℤ) + -(q : ℤ) = -(m : ℤ) := by omega
  rw [← zpow_add₀ (div_ne_zero hZ (pow_ne_zero 2 hR)), hpq, hkj, hk]
  have hR2 : (R ^ 2 : ℂ) = R * R := by ring
  rw [hR2]
  simp only [div_eq_mul_inv, mul_zpow, _root_.inv_zpow, zpow_add₀ hZ, zpow_add₀ hR, _root_.zpow_neg, zpow_natCast, inv_inv, mul_inv]
  have h1 : Z ^ m ≠ 0 := pow_ne_zero _ hZ
  have h2 : R ^ m ≠ 0 := pow_ne_zero _ hR
  have h3 : Z ^ j ≠ 0 := zpow_ne_zero _ hZ
  have h4 : R ^ j ≠ 0 := zpow_ne_zero _ hR
  field_simp
  ring_nf
  rw [inv_pow]
  field_simp

end PositivityTheory.Rg.Sw.Glob.LocLawH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoI
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  delta PositivityTheory.Rg.Sw.Glob.phiS
  rw [dif_pos h]

theorem tens_add_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (a : ℂ)
    (f g : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) :
    tens θ τ fr (a • f + g) Ψ = a • tens θ τ fr f Ψ + tens θ τ fr g Ψ := by
  funext x
  delta PositivityTheory.Rg.Sw.Glob.tens
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (a * f (fr⁻¹ * compAt θ τ x) + g (fr⁻¹ * compAt θ τ x)) * Ψ x = _
  ring

theorem tensor_gaussian_vacuum_injective {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (l : D.what₂.Tau → ℝ) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr g (psi0 θ V n l s τ)) : f = g := by
  have hdet : IsUnit fr.det := hfr.1
  suffices hU : ∀ U : Matrix (Fin V.rank) (Fin n) ℂ, f U = g U from funext hU
  intro U
  have hx := congrFun h (xL θ τ (fr * U))
  have hc : compAt θ τ (xL θ τ (fr * U)) = fr * U := by
    have h1 := congrFun (compAt_xL hθ τ (fr * U)) τ
    simpa [dirAt_self] using h1
  have hp : psi0 θ V n l s τ (xL θ τ (fr * U)) = 1 := by
    show gAway V l s τ (fun τ' => compAt θ τ' (xL θ τ (fr * U))) *
      g0 D V.rank n (fun i j => finPart D (xL θ τ (fr * U) i j)) = 1
    rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ, gaussian_at_zero_eq_one, one_mul]
  have hinv : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul fr hdet, Matrix.one_mul]
  change f (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) =
    g (fr⁻¹ * compAt θ τ (xL θ τ (fr * U))) * psi0 θ V n l s τ (xL θ τ (fr * U)) at hx
  rw [hc, hp, hinv, mul_one, mul_one] at hx
  exact hx

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntegralCompWeil
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GCommH

variable {D : D7} {n : ℕ}

theorem gComm {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle}
    (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (Φ Φh : schwartzA θ V.rank n) (h : GA D V) (hΦh : ∀ x, Φh.1 x = Φ.1 (mt V h ⬝ x)) (g : G D n) (x : Mx D V.rank n) :
    (ω g Φh).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hs0, hsk, _, _, hκ, hW, hT⟩ := GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hs0 θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have hlaw := fun F (hF : IsThetaFunO ψ₀ (dblSp A) V F) => (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ F hF).1
  have hf1 : IsThetaFunO ψ₀ (dblSp A) V (omh (1, h⁻¹) f) := hW.om_pres _ f hf
  have hΦh' : Φh.1 = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) f) := by
    funext y
    rw [hΦh, hlaw f hf h⁻¹ y, inv_inv, hfΦ]
    rfl
  have key : ∀ g0 : GA D (dblSp A), (ω (κ g0) Φh).1 x = (ω (κ g0) Φ).1 (mt V h ⬝ x) := by
    intro g0
    have hc : omh (g0, 1) (omh (1, h⁻¹) f) = omh (1, h⁻¹) (omh (g0, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        one_mul, mul_one, one_mul, mul_one]
    have hg1 : IsThetaFunO ψ₀ (dblSp A) V (omh (g0, 1) f) := hW.om_pres _ f hf
    calc (ω (κ g0) Φh).1 x = sch ψ₀ A V μ 𝓕 (omh (g0, 1) (omh (1, h⁻¹) f)) x := congrFun (hT g0 _ hf1 Φh hΦh') x
      _ = sch ψ₀ A V μ 𝓕 (omh (1, h⁻¹) (omh (g0, 1) f)) x := by rw [hc]
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h⁻¹⁻¹ ⬝ x) := hlaw _ hg1 h⁻¹ x
      _ = sch ψ₀ A V μ 𝓕 (omh (g0, 1) f) (mt V h ⬝ x) := by rw [inv_inv]
      _ = (ω (κ g0) Φ).1 (mt V h ⬝ x) := (congrFun (hT g0 f hf Φ hfΦ.symm) _).symm
  have e : κ (κ.symm g) = g := κ.apply_symm_apply g
  have k := key (κ.symm g)
  rw [e] at k
  exact k

end PositivityTheory.Rg.Sw.Glob.GCommH
end
end

