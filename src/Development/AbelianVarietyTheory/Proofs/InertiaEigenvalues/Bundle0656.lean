import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecondKindMatrixMooreDetNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisDvdTauPowLPowAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_dvd_tauPow_lPow_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BSP.HeightSprime.main | exact GlobalTheory.BSP.HeightSprime.main | (intros; apply GlobalTheory.BSP.HeightSprime.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlaces
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaEigenvalues.DimAtQD

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc),
    EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 :=
  fun _ _ D i _ w hw C =>
    by
      classical
      haveI := (D.nbr i w hw).Kw.2
      haveI := C.LL.2
      exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied (D.nd.l i) _ (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.nbr i w hw).Kw C.LL _

end GlobalTheory.InertiaEigenvalues.DimAtQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionFormulaConcretePeriodRingsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], BlochKatoDim (P.PD K) ↥LL.1 := by
  first | exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | exact GlobalTheory.BlochKatoTied.blochKatoDim_of_tied | (intros; apply GlobalTheory.BlochKatoTied.blochKatoDim_of_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoAnn

section Abstract

variable {k Z Z' : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup Z'] [Module k Z']
  [FiniteDimensional k Z] [FiniteDimensional k Z']

def rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) : Submodule k Z' :=
  (W.map β).dualCoannihilator

theorem mem_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (b : Z') :
    b ∈ rorth β W ↔ ∀ a ∈ W, β a b = 0 := by
  unfold rorth
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem finrank_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (hW : LinearMap.ker β ≤ W) :
    finrank k (rorth β W) + finrank k W = finrank k Z' + finrank k (LinearMap.ker β) := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (W.map β)
  have h2 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
  have h3 : LinearMap.range (β.domRestrict W) = W.map β := by
    rw [LinearMap.range_domRestrict]
  have h4 : LinearMap.ker (β.domRestrict W) = (LinearMap.ker β).comap W.subtype := by
    rw [LinearMap.ker_domRestrict]
  have h5 : finrank k ((LinearMap.ker β).comap W.subtype) = finrank k (LinearMap.ker β) :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  rw [h3, h4, h5] at h2
  unfold rorth
  linarith

theorem rorth_top (β : Z →ₗ[k] Z' →ₗ[k] k) : rorth β ⊤ = LinearMap.ker β.flip := by
  ext b
  rw [mem_rorth, LinearMap.mem_ker]
  constructor
  · intro h
    ext a
    exact h a trivial
  · intro h a _
    have := LinearMap.congr_fun h a
    simpa using this

theorem exact_ann (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (W' : Submodule k Z')
    (hW : LinearMap.ker β ≤ W) (hW' : LinearMap.ker β.flip ≤ W')
    (hort : ∀ a ∈ W, ∀ b ∈ W', β a b = 0)
    (hdim : finrank k W + finrank k W' = finrank k Z + finrank k (LinearMap.ker β.flip)) :
    rorth β W = W' ∧ rorth β.flip W' = W := by
  have hT := finrank_rorth β ⊤ (le_top)
  rw [rorth_top, finrank_top] at hT
  have hA := finrank_rorth β W hW
  have hB := finrank_rorth β.flip W' hW'
  have l1 : W' ≤ rorth β W := fun b hb => (mem_rorth β W b).2 fun a ha => hort a ha b hb
  have l2 : W ≤ rorth β.flip W' := fun a ha => (mem_rorth β.flip W' a).2 fun b hb => by
    rw [LinearMap.flip_apply]; exact hort a ha b hb
  constructor
  · exact (Submodule.eq_of_le_of_finrank_eq l1 (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_eq l2 (by omega)).symm

end Abstract

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

section Concrete

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL]

theorem galoisCoboundaries_le_continuousCocycles (A : GRep G Qp LL O) : B1 A.ρ ≤ continuousCocycles A.ρ := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, fun g h => ?_⟩
  · have : (cob A.ρ x : G → A.V) = fun g => A.ρ g x + (-x) := by
      funext g
      simp [cob, sub_eq_add_neg]
    rw [this]
    exact (A.cont x).add continuous_const
  · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub]
    abel

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  intro c hc
  refine ⟨galoisCoboundaries_le_continuousCocycles A hc, ?_⟩
  obtain ⟨x, rfl⟩ := hc
  refine ⟨x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  simp [cob, actVB, sub_tmul]

theorem blochKatoFiniteCocycles_le_continuousCocycles (A : GRep G Qp LL O) : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ := fun _ h => h.1

theorem finite_continuous_cocycles_localGaloisRep (A : GRep G Qp LL O) (h : Module.Finite LL (H1V A.ρ)) :
    FiniteDimensional LL (continuousCocycles A.ρ) := by
  haveI : FiniteDimensional LL (B1 A.ρ) := LinearMap.finiteDimensional_range (cob A.ρ)
  have hK : FiniteDimensional LL ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).symm
  show Module.Finite LL (continuousCocycles A.ρ)
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ
  · rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.finite_def.1 h
  · rw [top_inf_eq, Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.1 hK

theorem finrank_H1V (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (H1V A.ρ) + finrank LL (B1 A.ρ) = finrank LL (continuousCocycles A.ρ) := by
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq] at e
  exact e

theorem finrank_H1fV (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (FiniteCohomology PD A.ρ) + finrank LL (B1 A.ρ) =
      finrank LL ((finiteCocycles PD A.ρ).comap (continuousCocycles A.ρ).subtype) := by
  have eW := (Submodule.comapSubtypeEquivOfLe (blochKatoFiniteCocycles_le_continuousCocycles PD A))
  haveI : FiniteDimensional LL (finiteCocycles PD A.ρ) := Module.Finite.equiv eW
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (finiteCocycles PD A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (B1_le_Z1f PD A)).finrank_eq] at e
  rw [eW.finrank_eq]
  exact e

end Concrete

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

theorem bkA_exact_annihilators : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ K : FinExt l, bkACore (P.PD K) := by
  intro hTD hEC l _ P AI hT K
  intro LL _ _ _ O _ _ hO A A' m hdr hdual
  have hdual' : IsDual1 (P.PD K) A'.ρ A.ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hdrd, hfd⟩ := GlobalTheory.T.de_rham_filtration_duality l P AI hT K
  have hdr' : IsDR (P.PD K) A'.ρ := hdrd LL O hO A A' m hdr hdual
  have hfil := hfd LL O hO A A' m hdr hdual
  obtain ⟨hH1fin, hH1⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A A' m hdual
  obtain ⟨hH1fin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A' A m.flip hdual'
  obtain ⟨-, hf⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A hdr
  obtain ⟨-, hf'⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A' hdr'
  have hort := GlobalTheory.T.cup_product_finite_classes_coboundary l P AI hT K LL O hO A A' m hdr hdual
  obtain ⟨β, hβ, hl, hr⟩ := GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K LL O hO A A' m hdual
  haveI := finite_continuous_cocycles_localGaloisRep A hH1fin
  haveI := finite_continuous_cocycles_localGaloisRep A' hH1fin'
  have hkl : LinearMap.ker β = (B1 A.ρ).comap (continuousCocycles A.ρ).subtype := by
    ext a
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hl a]
    constructor
    · intro h b
      rw [h]
      rfl
    · intro h
      ext b
      exact h b
  have hkr : LinearMap.ker β.flip = (B1 A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hr b]
    constructor
    · intro h a
      have := LinearMap.congr_fun h a
      simpa using this
    · intro h
      ext a
      simpa using h a
  have hW : LinearMap.ker β ≤ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype := by
    rw [hkl]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A)
  have hW' : LinearMap.ker β.flip ≤ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    rw [hkr]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A')
  have horth : ∀ a ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype,
      ∀ b ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype, β a b = 0 := by
    intro a ha b hb
    rw [hβ]
    exact hort a.1 ha b.1 hb
  have eZ := finrank_H1V A
  have eW := finrank_H1fV (P.PD K) A
  have eW' := finrank_H1fV (P.PD K) A'
  have eKl : finrank LL (LinearMap.ker β) = finrank LL (B1 A.ρ) := by
    rw [hkl]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq
  have eKr : finrank LL (LinearMap.ker β.flip) = finrank LL (B1 A'.ρ) := by
    rw [hkr]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A')).finrank_eq
  have hdV := hdual.2.2.2
  unfold IsDR at hdr hdr'
  rw [← hdV] at hdr'
  have hdim : finrank LL ((finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype) +
      finrank LL ((finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype) =
      finrank LL (continuousCocycles A.ρ) + finrank LL (LinearMap.ker β.flip) := by
    rw [eKr]
    zify at eZ eW eW' hH1 hfil hdr hdr' ⊢
    linarith
  obtain ⟨h1, h2⟩ := exact_ann β _ _ hW hW' horth hdim
  constructor
  · intro a ha
    change (⟨a, ha⟩ : continuousCocycles A.ρ) ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype ↔ _
    rw [← h2, mem_rorth]
    constructor
    · intro h b hb
      have := h ⟨b, hb.1⟩ hb
      rw [LinearMap.flip_apply, hβ] at this
      exact this
    · intro h b hb
      rw [LinearMap.flip_apply, hβ]
      exact h b.1 hb
  · intro b hb
    change (⟨b, hb⟩ : continuousCocycles A'.ρ) ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype ↔ _
    rw [← h1, mem_rorth]
    constructor
    · intro h a ha
      have := h ⟨a, ha.1⟩ ha
      rw [hβ] at this
      exact this
    · intro h a ha
      rw [hβ]
      exact h a.1 ha

end GlobalTheory.BlochKatoAnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality l P K hInt
  exact ⟨hA, GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExactStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bloch_kato_right_exact : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  first | exact @GlobalTheory.BKRightExact.bkARightExact_of_tied | exact GlobalTheory.BKRightExact.bkARightExact_of_tied | (intros; apply GlobalTheory.BKRightExact.bkARightExact_of_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMatrix_frobenius_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.rel_frob | exact GlobalTheory.BSP.Height.rel_frob | (intros; apply GlobalTheory.BSP.Height.rel_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbeddingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_character_jump_one_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.HWL.charRep_crys_jump_one | exact GlobalTheory.HWL.charRep_crys_jump_one | (intros; apply GlobalTheory.HWL.charRep_crys_jump_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlacesStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p8_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  first | exact @GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | exact GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | (intros; apply GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermFrameIndependent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

theorem ratMul_ratMul {m : ℕ} {a c : ℕ} (c₁ : Matrix (Fin a) (Fin m) D.host.E) (c₂ : Matrix (Fin m) (Fin m) D.host.E)
    (u : Mx D m c) : ratMul c₁ (ratMul c₂ u) = ratMul (c₁ * c₂) u := by
  unfold ratMul
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem covolOne_integral_ratMul {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (c c' : Matrix (Fin m) (Fin m) D.host.E) (h1 : c' * c = 1)
    (h2 : c * c' = 1) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (ratMul c a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hl : ∀ a : Mx D m n, ratMul c' (ratMul c a) = a := fun a => by
    rw [ratMul_ratMul, h1, ratMul_one]
  have hr : ∀ a : Mx D m n, ratMul c (ratMul c' a) = a := fun a => by
    rw [ratMul_ratMul, h2, ratMul_one]
  have mem : ∀ (d : Matrix (Fin m) (Fin m) D.host.E) (g : GlobalTheory.MixModel.ratMx D m n),
      ratMul d (g : Mx D m n) ∈ GlobalTheory.MixModel.ratMx D m n := fun d g =>
    GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem d) g.2
  let A : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => ratMul c a
      invFun := fun a => ratMul c' a
      left_inv := hl
      right_inv := hr
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  let L : Mx D m n ≃ₜ+ Mx D m n :=
    { A with
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let e : Mx D m n ≃ᵐ Mx D m n := L.toHomeomorph.toMeasurableEquiv
  haveI := hμ.1
  have hH : (μ.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving e μ (μ.map e) := e.measurable.measurePreserving μ
  let r : GlobalTheory.MixModel.ratMx D m n ≃ GlobalTheory.MixModel.ratMx D m n :=
    { toFun := fun g => ⟨ratMul c' (g : Mx D m n), mem c' g⟩
      invFun := fun g => ⟨ratMul c (g : Mx D m n), mem c g⟩
      left_inv := fun g => Subtype.ext (hr _)
      right_inv := fun g => Subtype.ext (hl _) }
  have hcov : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) (μ.map e) (e '' 𝓕) := by
    refine ⟨hH, ?_, ?_⟩
    · refine hμ.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show ratMul c (ratMul c' (g : Mx D m n) + a) = (g : Mx D m n) + ratMul c a
      unfold ratMul
      rw [Matrix.mul_add]
      congr 1
      exact hr _
    · rw [e.map_apply, e.preimage_image]; exact hμ.2.2
  have h := GlobalTheory.MixModel.covolOne_integral_eq hμ hcov φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

theorem exists_frame_change {W : HSp D} {Y : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hC : IsLagFrame W Y C) (hC' : IsLagFrame W Y C') :
    ∃ c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E,
      C'.1 = C.1 * c ∧ C'.2 = C.2 * c ∧ c * c' = 1 ∧ c' * c = 1 := by
  have mem : ∀ {C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E},
      IsLagFrame W Y C → ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 :=
    fun h j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  let v : ∀ C, IsLagFrame W Y C → Fin W.rank → Y.1 := fun C h j => ⟨_, mem h j⟩
  have sp : ∀ C (h : IsLagFrame W Y C), ⊤ ≤ Submodule.span D.host.E (Set.range (v C h)) := by
    intro C h
    refine le_of_eq (Submodule.map_injective_of_injective Y.1.injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h
  have li : ∀ C (h : IsLagFrame W Y C), LinearIndependent D.host.E (v C h) := fun C h =>
    linearIndependent_of_top_le_span_of_card_eq_finrank (sp C h) (by rw [Fintype.card_fin, Y.2.1])
  let b := Module.Basis.mk (li C hC) (sp C hC)
  let b' := Module.Basis.mk (li C' hC') (sp C' hC')
  have hb : ∀ j, (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C.1 a j), (fun a => C.2 a j)) :=
    fun j => by simp [b, v]
  have hb' : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C'.1 a j), (fun a => C'.2 a j)) :=
    fun j => by simp [b', v]
  have key : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
      ∑ i, b.toMatrix b' i j • (b i : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) := fun j => by
    have := congrArg Subtype.val (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Module.Basis.toMatrix_apply]
    exact this.symm
  refine ⟨b.toMatrix b', b'.toMatrix b, ?_, ?_, Module.Basis.toMatrix_mul_toMatrix_flip b b', Module.Basis.toMatrix_mul_toMatrix_flip b' b⟩
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.1 a) (key j)
    simp only [hb, hb', Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.2 a) (key j)
    simp only [hb, hb', Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lagTerm_frame_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  intro D ψ V W μ 𝓕 hμ hψ f₁ f₂ h₁ h₂ Y C C' hC hC'
  obtain ⟨c, c', e1, e2, hcc, hc'c⟩ := exists_frame_change hC hC'
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  unfold lagTerm
  rw [e1, e2]
  simp only [← ratMul_ratMul]
  refine (covolOne_integral_ratMul (m := W.rank) (n := V.rank) hμ c c' hc'c hcc
    (fun u => f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) ?_).symm
  rintro _ ⟨γ, rfl⟩ a
  exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC h₁ h₂ γ a

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecondKindMatrixMooreDetNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondKind_matrix_moore_det_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h → ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) → (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) → ∃ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧ (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) ∧ (∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1) ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 := by
  first | exact @GlobalTheory.SecondKind.exists_secondKind | exact GlobalTheory.SecondKind.exists_secondKind | (intros; apply GlobalTheory.SecondKind.exists_secondKind <;> assumption)
end

