import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Lbc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import GroundTheory.AutomorphicForms.MeasuresModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermFormula
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary in

theorem isCuspidal_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        GlobalTheory.CuspRep.IsCuspidal (fun x => ψ (ι x * g₀)) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW K _ S l d h ι hι _ hS hk hl ψ hψ g₀ _
  intro r' hr0 hr1 _ _ μ 𝓕 hμ h𝓕 g
  let k : Fin r := ⟨l + r' - 1, by omega⟩
  have hkv : k.val + 1 = l + r' := by simp only [k]; omega
  have hkS : k ∉ S := hS k (by simp only [k]; omega) (by simp only [k]; omega)
  have hSS : S ⊂ insert k S := Finset.ssubset_insert hkS
  set U := GlobalTheory.StdPar.unip σ J X (insert k S) with hU
  set U₀ := GlobalTheory.StdPar.unip σ J X S with hU₀
  have hle : U₀ ≤ U := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hσ n J hJ r X Y hW _ S (Finset.subset_insert _ _)
  haveI : LocallyCompactSpace U₀ := (GlobalTheory.StdPar.isClosed_unip S hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace U := (GlobalTheory.StdPar.isClosed_unip _ hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have cS := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW S
  have cS' := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW (insert k S)
  have esub : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → (ratPts σ J ⊓ U).subgroupOf N = (ratPts σ J).subgroupOf N := by
    intro N hN
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hN x.2⟩⟩
  have cinf : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → Cocompact (ratPts σ J) N → Cocompact (ratPts σ J ⊓ U) N := by
    intro N hN hc
    unfold Cocompact
    rw [esub hN]
    exact hc
  have hfΓ : LeftInv (ratPts σ J ⊓ U) ψ := fun γ hγ g => by
    obtain ⟨m, hm, hmL, ν, hν, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hσ n J hJ r X Y hW S (insert k S) (Finset.subset_insert _ _) γ hγ.1 hγ.2
    rw [e, mul_assoc, hψ.1.leftM m hm hmL, hψ.1.leftN ν hν]
  have hnorm : ∀ p ∈ U, ∀ u ∈ U₀, p * u * p⁻¹ ∈ U₀ := by
    intro p hp u hu
    by_cases hS0 : S = ∅
    · subst hS0
      rw [hU₀, GlobalTheory.StdPar.unip_empty, Subgroup.mem_bot] at hu ⊢
      simp [hu]
    obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
      S.max'_mem _, fun k hk => S.le_max' k hk⟩
    have hσσ := sigma_sigma hσ
    have eS := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ hσ n J hJ r X Y hW S mS hmS hmS'
    have hCS : IsIsoCols σ J (GlobalTheory.StdPar.initCols X mS) := isIsoCols_of_isWittFrame hW hσσ hJ mS.2
    rw [hU₀, eS] at hu ⊢
    exact conj_mem_unipFlag hJ hσσ hCS _ (GlobalTheory.ConstTrans.unip_le_parFlag F E σ hσ n J hJ r X Y hW (insert k S) S mS
      (Finset.subset_insert _ _) hmS hmS' hp) hu
  obtain ⟨π, hπc, hπm, hπs, hπk, hπr⟩ := GlobalTheory.T.exists_blockProjection_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv
  have hrat := GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints F E σ hσ n J hJ r X Y hW l d h ι hι
  have hιc := GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries F E σ hσ n J hJ r X Y hW l d h ι hι
  have hsN := GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv

  have h0 : constTermOn (ratPts σ J ⊓ U) U ψ (ι g * g₀) = 0 := by
    obtain ⟨μN, 𝓕N, h1, h2, h3⟩ := exists_mass_one cS'
    rw [constTermOn_eq_of_measure_eq_one ((esub le_rfl).symm ▸ h2) h3 hfΓ]
    exact (hψ.2 _ hSS μN 𝓕N h1 h2 h3 (ι g * g₀)).symm
  have key := GlobalTheory.T.cocompact_normal_subgroup_descent_invariants (GAd σ J) (ratPts σ J ⊓ U) U U₀ hle hnorm (cinf le_rfl cS') (cinf hle cS)
    (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (GlobalTheory.CuspRep.ratN E d r') (fun x => ι (GlobalTheory.CuspRep.unip x)) π
    (hιc.comp (continuous_unip E d r')) (fun v w => by rw [GlobalTheory.CuspRep.unip_add, map_mul]) hsN hπc hπm hπs hπk
    (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      refine ⟨?_, hsN _⟩
      have := GlobalTheory.CuspRep.unip_algebraMap (a := d) (r := r') x
      exact this ▸ hrat _)
    (fun a ha => hπr a ha.1) ψ hfΓ hψ.1.cont (fun m hm g => hψ.1.leftN m hm g) μ 𝓕 hμ h𝓕 (ι g * g₀)
  rw [h0, smul_zero] at key
  simpa only [map_mul, mul_assoc] using key

end GlobalTheory.BlockForms.CuspConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DarbouxMeasure

theorem transport_covol_one : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  intro D S T κ _ e he ν 𝓕 hc
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F)
      (Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
  obtain ⟨hH, hF, h1⟩ := hc
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Formalism.IndefR.Datum.WO S T ≃ₜ ((κ → AF D.host.F) × (κ → AF D.host.F)) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  let m := h.toMeasurableEquiv
  refine ⟨Measure.map m ν, m '' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e.toAddEquiv hc1 hc2
  · let r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ ≃ ratL T S :=
      { toFun := fun p => ⟨e.symm p, (he (e.symm p)).2 (by simpa using p.2)⟩
        invFun := fun γ => ⟨e γ, (he γ).1 γ.2⟩
        left_inv := fun p => by ext1; simp
        right_inv := fun γ => by ext1; simp }
    refine hF.image_of_equiv m.toEquiv (m.measurePreserving_symm ν).quasiMeasurePreserving r ?_
    intro g x
    change e (e.symm (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + x) = (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + e x
    rw [map_add, LinearEquiv.apply_symm_apply]
  · rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ m.injective, h1]
  · intro g
    rw [m.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ m.injective]
    rfl

end GlobalTheory.DarbouxMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

section General

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

theorem finrank_eq_two_mul_nPl : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

theorem rkK_mul_muDef [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG)
    (hr : Formalism.HN.rkK L ≠ 0) :
    (Formalism.HN.rkK L : ℝ) * (Formalism.HN.muDef b X L / 2) = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  obtain ⟨-, hrk, hht⟩ := Formalism.HN.plLat K V ι b X hX L hL
  have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (Formalism.HN.rkK L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have e₁ : Formalism.HN.ht b X L = (2 : ℝ) ^ (Formalism.HN.nPl K * Formalism.HN.rkK L) *
      |(NumberField.discr K : ℝ)| ^ (-(Formalism.HN.rkK L : ℝ) / 2) *
      Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := rfl
  have hC : 0 < Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    rw [e₁] at hht
    exact pos_of_mul_pos_right hht (by positivity)
  have hlog : Real.log (Formalism.HN.ht b X L) = ((Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L) * Real.log 2 +
      (-(Formalism.HN.rkK L : ℝ) / 2) * Real.log |(NumberField.discr K : ℝ)| +
      Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) := by
    rw [e₁, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_rpow hd]
    push_cast; ring
  have hrk' : (Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) : ℝ) =
      2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L := by
    have : Formalism.F.rk (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L) = Module.finrank ℚ K * Formalism.HN.rkK L := hrk
    rw [this, finrank_eq_two_mul_nPl]; push_cast; ring
  have hmu : Formalism.HN.muDef b X L = 2 * (-Real.log (Formalism.F.covol (Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) L)) /
      (2 * (Formalism.HN.nPl K : ℝ) * Formalism.HN.rkK L)) - Real.log 2 +
      Real.log |(NumberField.discr K : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) := by
    rw [Formalism.HN.muDef, Formalism.HN.slope, Formalism.F.slope, Formalism.F.deg, hrk', Formalism.HN.logDisc, finrank_eq_two_mul_nPl]
    push_cast; ring
  rw [hmu, hlog]
  field_simp
  ring

theorem pgeoDeg_eq_deg {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (hinv : h.IsConjInv) {N : (K →+* ℂ) → V → ℝ} (hN : ∀ σ x, h.nrm σ x = N σ x)
    (hg : AllWt.HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) : ReciprocityTheory.GeometryOfNumbersTheory.deg h L = AllWt.deg N L := by
  by_cases h0 : L = ⊥
  · subst h0
    have hv : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (⊥ : Submodule (𝓞 K) V) (Fin.elim0 : Fin 0 → V) :=
      ⟨fun i => i.elim0, linearIndependent_empty_type, by simp⟩
    rw [AllWt.deg_bot, ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hL hv]
    simp [ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily, ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram]
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hG⟩ := hg.some
  haveI : FiniteDimensional K V := Module.Basis.finiteDimensional_of_finite b
  have hr : Formalism.HN.rkK L ≠ 0 := by
    intro hr
    apply h0
    rw [Formalism.HN.rkK, Submodule.finrank_eq_zero] at hr
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
    rw [hr, Submodule.mem_bot] at hx'
    rw [hx']
    exact zero_mem _
  rw [GlobalTheory.T.hermitian_lattice_degree_eq_neg_log_frame_height K V h hinv (Fin n) b X (fun v => (hG v).1) (fun v x => ((hG v).2 x).trans (hN _ x).symm) L hL,
    AllWt.deg, AllWt.slope, AllWt.slope_sq_eq hG hL, rkK_mul_muDef b X (fun v => (hG v).1) hL hr]

end General

theorem isTotallyComplex_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) : IsTotallyComplex c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem Ready.degM_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k j hj
  haveI : IsTotallyComplex c.F := isTotallyComplex_coeff c
  have hM : (h.data f₁ f₂ th k).M j = (GlobalTheory.AllWt.latOn U Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0)).map
      ((h.equivV f₁ f₂ th k hj).toLinearMap.restrictScalars (𝓞 c.F)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(h.equivV f₁ f₂ th k hj).symm y, ?_, (h.equivV f₁ f₂ th k hj).apply_symm_apply y⟩
      refine (h.equivV_mem f₁ f₂ th k hj _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨g, hg, rfl⟩
      exact (h.equivV_mem f₁ f₂ th k hj g).2 hg
  rw [HilbertSamuel.Data.degM, hM, ← FibIndep.deg_map_of_isometry
    (HermTools.comap ((h.data f₁ f₂ th k).nm j) (h.equivV f₁ f₂ th k hj).toLinearMap
      (h.equivV f₁ f₂ th k hj).injective) _ (h.equivV f₁ f₂ th k hj).toLinearMap (fun _ _ _ => rfl)
    (h.good j hj).2.1]
  exact pgeoDeg_eq_deg _ (HermTools.isConjInv_comap ((h.data f₁ f₂ th k).conjInv j) _ _)
    (fun σ x => h.nrm_equivV f₁ f₂ th k hj σ x) (h.good j hj).1 (h.good j hj).2.1

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityGlueingUnderTransition
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem part_compl_eq_zero {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {ρ : AlgChart p σ 1 → CxPts p σ → ℝ} {K : Set (CxPts p σ)} (hK : MeasurableSet K)
    (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y ≤ 0) : part ρ Kᶜ = 0 := by
  have key : part ρ ≤ (part ρ).restrict K := iSup_le fun c => by
    have e : ChartGlue.chartMeas c.e (fun y => ENNReal.ofReal (ρ c y)) Kᶜ = 0 := by
      rw [ChartGlue.chartMeas_apply _ _ hK.compl]
      refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
        (c.e.open_source.measurableSet.inter hK.compl) Set.inter_subset_left) ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1]
      exact ENNReal.ofReal_eq_zero.2 (h c y hy.1 hy.2)
    rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ 1 =>
      ChartGlue.chartMeas c.e fun y => ENNReal.ofReal (ρ c y)) c)
  refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
  rw [Measure.restrict_apply hK.compl, Set.compl_inter_self, measure_empty]

theorem integral_re_dbar_eq_zero {n : ℕ} {F : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (u : ReciprocityTheory.L2DbarEstimates.V n) :
    Integrable (fun v => (dbar F v u).re) ∧ ∫ v, (dbar F v u).re = 0 := by
  have hint : ∀ w : ReciprocityTheory.L2DbarEstimates.V n, Integrable (fun y => fderiv ℝ F y w) := fun w =>
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => dbar F v u) := by
    simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  refine ⟨Complex.reCLM.integrable_comp hD, ?_⟩
  have h0 : ∫ v, dbar F v u = 0 := by
    simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n F hF hc]
    simp
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

theorem total_dbar_eq_zero_of_compact_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → ∀ (c₀ : AlgChart p σ 1) (K : Set (CxPts p σ)), IsCompact K → K ⊆ c₀.e.source → (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → m c y = 0) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ m h1 h2 c₀ K hK hKs h3
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  have hD : IsDens ρ := GlobalTheory.T.dbar_density_of_transition k X p σ m h1 h2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet

  have hz : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∉ K → ρ c y = 0 := fun c y hy hyK => by
    have hW := ChartGlue.isOpen_over c.e hK.isClosed.isOpen_compl
    have he : (fun v => m c (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun _ => 0 := by
      filter_upwards [hW.mem_nhds (ChartGlue.mem_over c.e hy hyK)] with v hv
      exact h3 c _ (c.e.map_target hv.1) hv.2
    simp only [hρ]
    rw [dbar_congr he, dbar_apply]
    simp

  set A : Set (ReciprocityTheory.L2DbarEstimates.V 1) := c₀.e '' K with hAdef
  have hA : IsCompact A := hK.image_of_continuousOn (c₀.e.continuousOn.mono hKs)
  have hAt : A ⊆ c₀.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c₀.e.map_source (hKs hy)
  set F : ReciprocityTheory.L2DbarEstimates.V 1 → ℂ := c₀.e.target.indicator fun v => m c₀ (c₀.e.symm v) with hFdef
  have hF0 : ∀ v ∉ A, F v = 0 := fun v hv => by
    by_cases ht : v ∈ c₀.e.target
    · rw [hFdef, Set.indicator_of_mem ht]
      refine h3 c₀ _ (c₀.e.map_target ht) fun hk => hv ⟨_, hk, c₀.e.right_inv ht⟩
    · rw [hFdef, Set.indicator_of_notMem ht]
  have hFt : ∀ v ∈ c₀.e.target, F =ᶠ[𝓝 v] fun v => m c₀ (c₀.e.symm v) := fun v hv => by
    filter_upwards [c₀.e.open_target.mem_nhds hv] with w hw
    rw [hFdef, Set.indicator_of_mem hw]
  have hFA : ∀ v ∉ A, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFC : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ c₀.e.target
    · have := h1 c₀ _ (c₀.e.map_target ht)
      rw [c₀.e.right_inv ht] at this
      exact this.congr_of_eventuallyEq (hFt v ht)
    · exact contDiffAt_const.congr_of_eventuallyEq (hFA v fun h => ht (hAt h))
  have hFs : HasCompactSupport F := HasCompactSupport.intro hA hF0
  obtain ⟨hHi, hH0⟩ := integral_re_dbar_eq_zero hFC hFs (EuclideanSpace.single 0 1)
  set H : ReciprocityTheory.L2DbarEstimates.V 1 → ℝ := fun v => (dbar F v (EuclideanSpace.single 0 1)).re with hHdef
  have hHA : ∀ v ∉ A, H v = 0 := fun v hv => by
    simp only [hHdef]
    rw [dbar_congr (hFA v hv), dbar_apply]
    simp
  have hHt : ∀ v ∈ A, H v = ρ c₀ (c₀.e.symm v) := fun v hv => by
    simp only [hHdef, hρ]
    rw [dbar_congr (hFt v (hAt hv)), c₀.e.right_inv (hAt hv)]

  have hl : ∀ τ : ℝ → ℝ, τ 0 = 0 → ∫⁻ v, ENNReal.ofReal (τ (H v)) =
      ∫⁻ v in A, ENNReal.ofReal (τ (ρ c₀ (c₀.e.symm v))) := fun τ h0 => by
    rw [← lintegral_indicator hA.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A
    · rw [Set.indicator_of_mem hv, hHt v hv]
    · rw [Set.indicator_of_notMem hv, hHA v hv, h0, ENNReal.ofReal_zero]
  have hp : part ρ Set.univ = ∫⁻ v, ENNReal.ofReal (H v) := by
    rw [hl (fun t => t) rfl, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => (hz c y hy hyK).le, add_zero,
      hD.part_apply c₀ hKm hKs]
  have hn : part (fun c y => -ρ c y) Set.univ = ∫⁻ v, ENNReal.ofReal (-H v) := by
    rw [hl (fun t => -t) neg_zero, ← measure_add_measure_compl hKm,
      part_compl_eq_zero hKm fun c y hy hyK => by rw [hz c y hy hyK, neg_zero], add_zero,
      hD.neg.part_apply c₀ hKm hKs]
  rw [total, hp, hn, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi]
  exact hH0

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometryStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_isometric_of_isometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (H : h.IsCInf) (H' : h'.IsCInf) (φ : E ≅ E'), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  first | exact @GlobalTheory.CurveDens.det_isometric_of_isIsometry | exact GlobalTheory.CurveDens.det_isometric_of_isIsometry | (intros; apply GlobalTheory.CurveDens.det_isometric_of_isIsometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharNorm
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.FunExt GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LBCNu

open MeasureTheory

theorem distribHaarChar_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (z : k'ˣ) :
    distribHaarChar k (Units.map (Algebra.norm k : k' →* k) z) = distribHaarChar k' z := by
  let b := Module.finBasis k k'
  let e : k' ≃ₗ[k] (Fin (Module.finrank k k') → k) := b.equivFun
  let e' : k' ≃ₜ+ (Fin (Module.finrank k k') → k) :=
    { e.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  let M : k' ≃ₗ[k] k' := LinearEquiv.ofLinear (LinearMap.mulLeft k (z : k')) (LinearMap.mulLeft k ((z⁻¹ : k'ˣ) : k'))
    (by ext x; simp) (by ext x; simp)
  let Lz : (Fin (Module.finrank k k') → k) ≃ₗ[k] (Fin (Module.finrank k k') → k) := (e.symm.trans M).trans e
  have h1 : distribHaarChar (Fin (Module.finrank k k') → k) Lz = distribHaarChar k' z :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e' z Lz (fun x => by
      show e ((z : k') * x) = e (M (e.symm (e x)))
      simp [M])
  rw [← h1, GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, LinearEquiv.coe_det, Lz, Algebra.norm_apply]
  symm
  show LinearMap.det (e.toLinearMap ∘ₗ M.toLinearMap ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj]
  rfl

open GlobalTheory.SmGL GlobalTheory.SplitWeil in

theorem absPow_comp_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (t : ℂ) :
    (absPow k t).comp (Units.map (Algebra.norm k : k' →* k)) = absPow k' t := by
  ext z
  simp only [MonoidHom.comp_apply, val_absPow, nabs, distribHaarChar_norm]

end GlobalTheory.LBCNu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspForm_operator_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (o : Op E a) (φ : Sm E a), IsCuspForm φ → IsCuspForm (act o φ) := by
  first | exact @GlobalTheory.CuspStabFin.isCuspForm_act | exact GlobalTheory.CuspStabFin.isCuspForm_act | (intros; apply GlobalTheory.CuspStabFin.isCuspForm_act <;> assumption)
end

