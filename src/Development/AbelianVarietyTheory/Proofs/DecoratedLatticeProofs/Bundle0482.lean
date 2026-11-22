import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreTheta
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem det_uni {ρ : ℕ} {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) : Matrix.GeneralLinearGroup.det u = 1 := by
  have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular bt, Units.val_one]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

theorem halfMod_uni {ρ : ℕ} (n : ℕ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n u = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_uni hu, map_one, NNReal.coe_one, Real.one_rpow]

theorem om_mul_left {S T : HSp D} (om : Om S T) (a b : GA D S) (f : WO S T → ℂ) :
    om (a * b, 1) f = om (a, 1) (om (b, 1) f) := by
  have h : ((a * b, 1) : GA D S × GA D T) = (a, 1) * (b, 1) := by simp
  rw [h, map_mul, Module.End.mul_apply]

section Source

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {χW : (AE D)ˣ →* Circle}
  {om : Om V W} {om' : Om V₀ W} {μ : Measure (Mx D W.rank ρ)} {𝓕 : Set (Mx D W.rank ρ)} {f : WO V W → ℂ}

theorem mixS_levi_uni (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) {u : GL (Fin ρ) (AE D)}
    (hu : u ∈ UX D ρ) (x : Mx D W.rank ρ) :
    d.mixS W ψ μ 𝓕 (om (d.levi u, 1) f) x = d.mixS W ψ μ 𝓕 f (x ⬝ u.1) := by
  rw [hF.levi, det_uni hu, halfMod_uni _ hu, map_one, inv_one]
  simp

theorem mixS_nB_zero (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) (b : Mx D ρ V₀.rank)
    (x : Mx D W.rank ρ) : d.mixS W ψ μ 𝓕 (om (d.nB b, 1) f) x 0 = d.mixS W ψ μ 𝓕 f x (x ⬝ b) := by
  rw [hF.unip]
  simp only [heisO, zero_add, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

theorem mixS_nC (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) (c : skewA D ρ) (x : Mx D W.rank ρ)
    (w : WO V₀ W) : d.mixS W ψ μ 𝓕 (om (d.nC c, 1) f) x w = ψ (d.qS W c x) * d.mixS W ψ μ 𝓕 f x w := by
  rw [hF.centre]
  rfl

end Source

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem blocks_flag {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ V₀.rank)
    (c : skewA D ρ) :
    mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 ∧
    d.pX ⬝ (mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0) = u.1 ⬝ b ∧
    d.pX ⬝ (mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jY) = u.1 ⬝ (c.1 - half D • (b ⬝ plus V₀ b)) := by
  have hp : d.pX ⬝ mt V (d.levi u * (d.nB b * d.nC c)) =
      u.1 ⬝ (d.pX + c.1 ⬝ d.pY + b ⬝ d.p0 - (half D • (b ⬝ plus V₀ b)) ⬝ d.pY) := by
    rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  · rw [← Matrix.mul_assoc, hp]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero, sub_zero]
  · rw [← Matrix.mul_assoc, hp]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero]

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

set_option maxHeartbeats 2000000 in

theorem rat_coords {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ V₀.rank)
    (c : skewA D ρ) (hγ : d.levi u * (d.nB b * d.nC c) ∈ GQ V) :
    u.1 ∈ ratMx D ρ ρ ∧ u.1 ⬝ b ∈ ratMx D ρ V₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
  set γ := d.levi u * (d.nB b * d.nC c) with hγdef
  obtain ⟨hX, h0, hY⟩ := blocks_flag d u b c
  rw [← hγdef] at hX h0 hY
  have hM : mt V γ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V γ).1 hγ
  have hMi : mt V γ⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V γ⁻¹).1 (inv_mem hγ)
  have hpX : d.pX ∈ ratMx D ρ V.rank := rat_mem _
  have hjX : d.jX ∈ ratMx D V.rank ρ := rat_mem _
  have hj0 : d.j0 ∈ ratMx D V.rank V₀.rank := rat_mem _
  have hjY : d.jY ∈ ratMx D V.rank ρ := rat_mem _
  have hu : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V γ ⬝ d.jX) = u.1 := by rw [hX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hpX (ratMx_mul hM hjX)
  have hui : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e1 : mt V γ⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
      calc mt V γ⁻¹ ⬝ d.jX = mt V γ⁻¹ ⬝ (d.jX ⬝ u.1) ⬝ (u⁻¹).1 := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have e : d.pX ⬝ (mt V γ⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [e1, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hpX (ratMx_mul hMi hjX)
  have hub : u.1 ⬝ b ∈ ratMx D ρ V₀.rank := by rw [← h0]; exact ratMx_mul hpX (ratMx_mul hM hj0)
  have hb : b ∈ ratMx D ρ V₀.rank := by
    have e : (u⁻¹).1 ⬝ (u.1 ⬝ b) = b := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hui hub
  have hc : c.1 ∈ ratMx D ρ ρ := by
    have e : c.1 = (u⁻¹).1 ⬝ (d.pX ⬝ (mt V γ ⬝ d.jY)) + half D • (b ⬝ plus V₀ b) := by
      have h2 : (u⁻¹).1 ⬝ (u.1 ⬝ (c.1 - half D • (b ⬝ plus V₀ b))) = c.1 - half D • (b ⬝ plus V₀ b) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      rw [hY, h2, sub_add_cancel]
    have hplus : plus V₀ b ∈ ratMx D V₀.rank ρ := by
      show giA V₀ ⬝ adj b ∈ ratMx D V₀.rank ρ
      exact ratMx_mul (rat_mem (V₀.gram⁻¹)) (ratMx_adj hb)
    rw [e]
    refine add_mem (ratMx_mul hui (ratMx_mul hpX (ratMx_mul hM hjY))) ?_
    show incA D (1 / 2) • (b ⬝ plus V₀ b) ∈ ratMx D ρ ρ
    exact ratMx_smul (1 / 2) (ratMx_mul hb hplus)
  exact ⟨hu, hub, hc⟩

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem continuous_periodic_integral {X : Type} [TopologicalSpace X] {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕) (G : X → Mx D m n → ℂ)
    (hG : Continuous (Function.uncurry G)) (hper : ∀ p, ∀ γ ∈ ratMx D m n, ∀ a, G p (γ + a) = G p a) :
    Continuous fun p => ∫ a in 𝓕, G p a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hint : ∀ p, IntegrableOn (G p) 𝓕 μ := fun p => covolOne_integrableOn h (G p) (hG.uncurry_left p) (hper p)
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev : ∀ᶠ p in nhds p₀, ∀ k ∈ K, ‖G p k - G p₀ k‖ < ε / 2 :=
    hK.eventually_forall_of_forall_eventually fun k hk => by
      have hca : ContinuousAt (fun q : X × Mx D m n => ‖Function.uncurry G q - G p₀ q.2‖) (p₀, k) :=
        (hG.sub ((hG.uncurry_left p₀).comp continuous_snd)).norm.continuousAt
      have h1 : ‖Function.uncurry G (p₀, k) - G p₀ (p₀, k).2‖ < ε / 2 := by
        rw [Function.uncurry_apply_pair, sub_self, norm_zero]; exact half_pos hε
      exact hca.eventually_lt continuousAt_const h1
  filter_upwards [hev] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  have hb : ∀ a ∈ 𝓕, ‖G p a - G p₀ a‖ ≤ ε / 2 := fun a _ => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hper p γ hγ a, ← hper p₀ γ hγ a]
    exact (hp _ ha).le
  have h1 : μ 𝓕 = 1 := h.2.2
  calc ‖∫ a in 𝓕, (G p a - G p₀ a) ∂μ‖ ≤ ε / 2 * _ :=
        norm_setIntegral_le_of_norm_le_const (by rw [h1]; exact ENNReal.one_lt_top) hb
    _ < ε := by simp [Measure.real, h1]; linarith

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

theorem term_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) b (u : UX D ρ) c, term ψ d W vS (om (d.nC c * (d.nB b * d.levi u.1), 1) Ψ) x = ψ (d.qS W c (rat x)) * d.mixS W ψ vS.μ vS.𝓕 Ψ (rat x ⬝ u.1.1) (rat x ⬝ b)) ∧ (∀ γ ∈ GQ V, γ ∈ flagN d → ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, (rat x' : Mx D W.rank ρ) = rat x ⬝ blockX d γ → term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ δ ∈ GQ W, ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, mt W δ ⬝ (rat x' : Mx D W.rank ρ) = rat x → term ψ d W vS (om (1, δ) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ x, Continuous fun p : GA D V × GA D W => term ψ d W vS (om p Ψ) x) ∧ HasSum (term ψ d W vS Ψ) (Ψ 0) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hMS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ d χV χW om om' hW hW' vS.μ vS.𝓕 vS.covol
  have hMV := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 V V₀ W ρ d vS.μ vS.𝓕 vS.covol
  have thP : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hW.om_pres
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x b u c
    simp only [term]
    rw [om_mul_left, om_mul_left, mixS_nC d (hMS _ (thP _ _ (thP _ _ hΨ))), mixS_nB_zero d (hMS _ (thP _ _ hΨ)),
      mixS_levi_uni d (hMS _ hΨ) u.2]
  · intro γ hγQ hγN x x' hx'
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D V V₀ ρ d).1 γ).1 hγN
    obtain ⟨hru, hrub, hrc⟩ := rat_coords d u b c hγQ
    have hblk : blockX d (d.levi u * (d.nB b * d.nC c)) = u.1 := by
      rw [blockX, (blocks_flag d u b c).1, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [hblk] at hx'
    simp only [term]
    rw [om_mul_left, om_mul_left, mixS_levi_uni d (hMS _ (thP _ _ (thP _ _ hΨ))) hu, mixS_nB_zero d (hMS _ (thP _ _ hΨ)),
      mixS_nC d (hMS _ hΨ), hx']
    have hxu : rat x ⬝ u.1 ∈ ratMx D W.rank ρ := ratMx_mul (rat_mem x) hru
    have hq : ψ (d.qS W c (rat x ⬝ u.1)) = 1 :=
      (((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.2 ψ hstd).2.1 _ hxu c hrc
    obtain ⟨β, hβ⟩ := ratMx_mul (rat_mem x) hrub
    have hθ := (hMV Ψ hΨ (rat x ⬝ u.1)).quasi β 0
    rw [add_zero, GlobalTheory.MixModel.symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at hθ
    have hβ' : ratW W V₀ β = rat x ⬝ u.1 ⬝ b := by rw [ratW_eq, Matrix.mul_assoc]; exact hβ
    rw [hβ'] at hθ
    rw [hq, one_mul, hθ]
  · intro δ hδ x x' hx
    simp only [term]
    rw [(hMS _ hΨ).target δ (rat x)]
    have e : mt W δ⁻¹ ⬝ rat x = rat x' := by rw [← hx, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    rw [e]
    exact hW'.om_aut 1 (one_mem _) δ hδ _ (hMV Ψ hΨ _)
  · intro x
    have hψc : Continuous ψ := hstd.1.1
    have hJ := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ V W χV χW om hW Ψ hΨ
    have hY : Continuous (d.extY W) := continuous_id.matrix_mul continuous_const
    have hterm : (fun p => term ψ d W vS (om p Ψ) x) = fun p => ∫ a in vS.𝓕,
        ψ (symplOH V W (d.extY W a) (d.extX W (rat x))) * om p Ψ (d.extY W a + d.extX W (rat x) + d.ext0 W 0) ∂vS.μ := by
      funext p
      simp only [term, HypDec.mixS]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => d.integrandS_eq _ _ _ _)
    rw [hterm]
    refine continuous_periodic_integral vS.covol
      (fun p a => ψ (symplOH V W (d.extY W a) (d.extX W (rat x))) * om p Ψ (d.extY W a + d.extX W (rat x) + d.ext0 W 0))
      ?_ ?_
    · refine (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_snd) continuous_const)).mul ?_
      exact hJ.comp (continuous_fst.prodMk (((hY.comp continuous_snd).add continuous_const).add continuous_const))
    · intro p γ hγ a
      have h := d.integrandS_periodic (thP p Ψ hΨ) (rat x) 0 γ hγ a
      rwa [d.integrandS_eq, d.integrandS_eq] at h
  · have h := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd V V₀ W ρ d vS Ψ hΨ).2.2.2.2 0
    rw [map_zero] at h
    exact h

end GlobalTheory.Unf.TermLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  intro D S A L o ζ M M' LA LL μ T v a₀ hζ hLL hM hTr hSp hμ hline hn hT
  obtain ⟨Λ', hΛ', hmem⟩ := GlobalTheory.T.exists_selfDual_lineLatticeTrace_at_place D S A L o ζ M' μ T v hζ hμ hline hn hT
  obtain ⟨γ, hγ, hmove⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D L v _ Λ' (GlobalTheory.FinPl.TamePlaces.tame D v)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D L LL v hLL) hΛ'
  obtain ⟨c, hc, hc', hγc⟩ := GlobalTheory.T.exists_normOneIdele_of_supported_rankOneUnitary D L v γ hζ.1 hγ
  obtain ⟨a, ha, hma⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A v (cA D c) hc'
  refine ⟨a, c, ha, hc, ?_⟩
  intro y hy
  have hAy : ∀ i, (o.pA *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hBy : ∀ i, (o.pB *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hcBy : ∀ i, (c • (o.pB *ᵥ y)) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hBy i)
  have hcc : c * cA D c = 1 := hc.1
  have key : c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y) =
      o.jA *ᵥ (Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y)) + o.jB *ᵥ (c • (o.pB *ᵥ y)) := by
    rw [o.mt_emb, GlobalTheory.FinPlLoc.mt_mul, hma, GlobalTheory.FinPlLoc.mt_one]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul, smul_add, smul_smul, hcc, one_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hz : ∀ i, (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) i ∈ idAt D (· = v) := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  have hpA : o.pA *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pA o.jA, Matrix.mulVec_mulVec _ o.pA o.jB, o.pA_jA, o.pA_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have hpB : o.pB *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = c • (o.pB *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pB o.jA, Matrix.mulVec_mulVec _ o.pB o.jB, o.pB_jA, o.pB_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
  rw [hM y, hSp _ hz, hpA, hpB, ← hTr _ hAy, ← hmem _ hcBy, hmove _ hBy, hγc, Matrix.smul_mulVec,
    Matrix.one_mulVec]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeModel_standardLattice_values_are_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) E₂ (stdHom S T) 1 f₀ T' → ∀ Φ, IsSBHalf E₂ (stdHom S T) Φ → IsThetaFunO ψ S T (T' Φ) := by
  first | exact @GlobalTheory.LocMod.StdTheta.theta_placeModel_std | exact GlobalTheory.LocMod.StdTheta.theta_placeModel_std | (intros; apply GlobalTheory.LocMod.StdTheta.theta_placeModel_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimitiveCharacterMatchesLinesDownFlagStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_character_matches_lines_down_flag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → PrimAt ψ d L v → PrimAt ψ d L' v → NormOneAt v c → ∀ i j : Fin ρ, j.1 = i.1 + 1 → (∀ a ∈ idAt D (· = v), (colMul d.jX j a ∈ latV S L (· = v) ↔ colMul d.jX j (c * a) ∈ latV S L' (· = v))) → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.match_down_flag | exact GlobalTheory.Core.Mi.LatMatch.match_down_flag | (intros; apply GlobalTheory.Core.Mi.LatMatch.match_down_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.ChainTw.VolScale

theorem scale {D : D7} (V : HSp D)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (K₁ K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν₁ ν₀ : Measure (GA D V)) :
    K₁ ≤ K₀ → K₀ ≤ UA D.sp.cm V.gram → K₁.relIndex K₀ ≠ 0 → MeasurableSet {g : GA D V | Lev.finE V g ∈ K₁} →
    Lev.IsMeasLevW V K₁ good ν₁ → Lev.IsMeasLevW V K₀ good ν₀ → ν₁ = (K₁.relIndex K₀ : ℝ≥0∞) • ν₀ := by
  intro hle hUA hne hmeas h₁ h₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨hH₁, ⟨θ, hθ⟩, k1⟩ := h₁
  obtain ⟨⟨A, hA⟩, k1⟩ := k1 θ hθ
  obtain ⟨⟨m, hm⟩, k1⟩ := k1 A hA
  obtain ⟨hH₀, -, k0⟩ := h₀
  obtain ⟨-, k0⟩ := k0 θ hθ
  obtain ⟨-, k0⟩ := k0 A hA
  have k0 := k0 m hm
  haveI := hH₁
  haveI := hH₀
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.RealMeasOne.infMat_toInf]
  have hset : ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), {g : GA D V | Lev.finE V g ∈ K} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E =
      {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K
    rw [hpre]
    rfl
  have v1 : ν₁ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₁ (hset K₁)).trans (k1 m hm (fun ρ => B ρ) hB)
  have v0 : ν₀ ({g : GA D V | Lev.finE V g ∈ K₀} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) = ∏ ρ, m ρ (B ρ) :=
    (congrArg ν₀ (hset K₀)).trans (k0 (fun ρ => B ρ) hB)
  have hI := GlobalTheory.T.relIndex_mul_measure_adelicLevelSet D V ν₀ K₁ K₀ E hle hUA hne hmeas hE
  rw [v0] at hI
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  set x := ν₀ ({g : GA D V | Lev.finE V g ∈ K₁} ∩ GlobalTheory.AutMult.toInf V ⁻¹' E) with hx
  have hx0 : x ≠ 0 := fun h => h0 (by rw [← hI, h, mul_zero])
  have hxt : x ≠ ⊤ := fun h => ht (by rw [← hI, h]; exact ENNReal.mul_top (by exact_mod_cast hne))
  have e : ν₁ = ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) • ν₀ := Measure.isMulLeftInvariant_eq_smul ν₁ ν₀
  have e' := v1
  rw [e, Measure.smul_apply, smul_eq_mul, ← hI] at e'
  have hc : ((Measure.haarScalarFactor ν₁ ν₀ : NNReal) : ENNReal) = (K₁.relIndex K₀ : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hx0 hxt).1 e'
  rw [e, hc]

theorem vol_step {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L₁ L₀ : LevDat D.host.E ℂ V.rank)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure) (ν₁ ν₀ : Measure (GA D V)) (N : ℝ)
    (hle : lev D.sp.cm V.gram β L₁ ≤ lev D.sp.cm V.gram β L₀)
    (hN : (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℕ) : ℝ) = N) (hN0 : 0 < N)
    (hmeas : MeasurableSet {g : GA D V | Lev.finE V g ∈ lev D.sp.cm V.gram β L₁})
    (h₁ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₁) good ν₁) (h₀ : Lev.IsMeasLevW V (lev D.sp.cm V.gram β L₀) good ν₀) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₀ * N ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν₁ := by
  have hne : (lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero] at hN; linarith
  have e := scale V good hgood _ _ ν₁ ν₀ hle lev_le_UA hne hmeas h₁ h₀
  refine ⟨?_, ?_⟩
  · rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ
    have e2 : GlobalTheory.AutomorphicL2Unitary.autMeasure V (((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • ν₀) =
        ((lev D.sp.cm V.gram β L₁).relIndex (lev D.sp.cm V.gram β L₀) : ℝ≥0∞) • GlobalTheory.AutomorphicL2Unitary.autMeasure V ν₀ :=
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul _
    rw [e2, measureReal_ennreal_smul_apply, ← hN, ENNReal.toReal_natCast, mul_comm]
  · haveI := h₁.1
    exact GlobalTheory.RallisIP.Model.vol_pos ν₁

theorem idxQ_pos {D : D7} (PP : Pl D.host.E) (j : ℕ) : 0 < idxQ PP j := by
  have hq : (0 : ℝ) < (Ideal.absNorm PP.asIdeal : ℝ) := by
    have := HeightOneSpectrum.one_lt_absNorm PP
    exact_mod_cast (Nat.zero_lt_one.trans this)
  unfold idxQ
  exact div_pos (mul_pos (pow_pos hq _) (RModel.zinv_pos PP _ _)) (mul_pos (RModel.zinv_pos PP _ _) (RModel.zinv_pos PP _ _))

theorem rVol_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR t
  have hQ0 : (twR R A.μ0).Q = ∅ := RModel.Q_base R hG.core.lev
  have hprod : ∀ j, 0 < ∏ PP ∈ R.Q t, idxQ PP j := fun j => Finset.prod_pos fun PP _ => idxQ_pos PP j
  refine ⟨fun j hj => ?_, ?_⟩
  · have hS := (hC hR t).2.1 j hj
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.1 j hj
    rw [hQ0] at hL0
    obtain ⟨good, hgood, hW⟩ := GlobalTheory.RealMeasOne.models_good R hG.core.models j hj
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) j (stY R t j) (hC hR t).1 hj.le hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stY R t j).V.rank D.R.r D.R.t j hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datYt A.μ0 j R.triv := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) hS).1
    exact vol_step (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.datYt A.μ0 j R.triv) good hgood (R.νY t j) (R.νY A.μ0 j) _
      hle hN (hprod j) hmeas (hW t) (hW A.μ0)
  · have hS := (hC hR t).2.2.1
    obtain ⟨hr0, hL0, -⟩ := (hC hR A.μ0).2.2.1
    rw [hQ0] at hL0
    obtain ⟨hle, hN⟩ := GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices D (comR R t) (twR R t) D.R.m (stX R t) (hC hR t).1 le_rfl hS hr0 R.chi (R.xiR A.μ0)
    have e : Lev.datY (stX R t).V.rank D.R.r D.R.t D.R.m hr0 (twR R t).Pg ∅ (LevelP.triv _ _ _) R.chi (R.xiR A.μ0) Lev.Frm.B =
        R.datXt A.μ0 := hL0.symm
    rw [e] at hle hN
    have hmeas := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 D.R.m le_rfl (stX R t) hS).1
    have h := vol_step D.sp.X' R.βX (R.datXt t) (R.datXt A.μ0) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m)
      (fun _ _ hm => hm.1) (R.νX t) (R.νX A.μ0) _ hle hN (hprod D.R.m) hmeas (hG.core.models.νX t).1 (hG.core.models.νX A.μ0).1
    exact ⟨h.1, h.2⟩

end GlobalTheory.ChainTw.VolScale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  first | exact @GlobalTheory.TwLevRed.blockTri_iff_mem_lev | exact GlobalTheory.TwLevRed.blockTri_iff_mem_lev | (intros; apply GlobalTheory.TwLevRed.blockTri_iff_mem_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  first | exact @GlobalTheory.LocRed.red_entry_movedFrame | exact GlobalTheory.LocRed.red_entry_movedFrame | (intros; apply GlobalTheory.LocRed.red_entry_movedFrame <;> assumption)
end

