import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0200
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfChar
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.ContCharUnitsOL

theorem norm_algHom_apply (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (x : ↥K.1) : ‖((τ₀ x : ↥LL.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have h1 : minpoly ℚ_[l] ((τ₀ x : ↥LL.1) : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq ((LL.1).val.comp τ₀) ((Subtype.val_injective).comp τ₀.toRingHom.injective) x
  have h2 : minpoly ℚ_[l] (x : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq (K.1).val Subtype.val_injective x
  show spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem continuous_algHom (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Continuous (fun x : ↥K.1 => τ₀ x) := by
  refine AddMonoidHomClass.continuous_of_bound τ₀ 1 (fun x => ?_)
  show ‖((τ₀ x : ↥LL.1) : Om l)‖ ≤ 1 * ‖(x : Om l)‖
  rw [norm_algHom_apply, one_mul]

theorem norm_le_one (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) (g : ↥(GK K)) :
    ‖(((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  obtain ⟨B, hB⟩ := (isCompact_univ (X := ↥(GK K))).exists_bound_of_continuousOn hc.continuousOn
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
  have hpow : (((c (g ^ n) : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) = ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) ^ n := by
    simp [map_pow]
  have := hB (g ^ n) (Set.mem_univ _)
  rw [hpow, norm_pow] at this
  linarith

end GlobalTheory.ContCharUnitsOL

namespace GlobalTheory.ContCharUnitsOL

theorem exists_unit_char (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) :
    ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ,
      Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧
      ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) *
        τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  let ι : ↥(K0 K) →+* ↥K.1 := algebraMap ↥(K0 K) ↥K.1
  have hι : ∀ x : ↥(K0 K), ((ι x : ↥K.1) : Om l) = (x : Om l) := fun x => rfl
  let v : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
  let w : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι ((c g : (↥(K0 K))ˣ) : ↥(K0 K)))
  have hw : ∀ g, w g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι]
    exact norm_le_one l K c hc g
  have hv : ∀ g, v g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι, ← map_inv]
    exact norm_le_one l K c hc g⁻¹
  have hvw : ∀ g, v g * w g = 1 := fun g => by
    show τ₀ (ι _) * τ₀ (ι _) = 1
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hwv : ∀ g, w g * v g = 1 := fun g => by rw [mul_comm]; exact hvw g
  let χf : ↥(GK K) → (↥(OL LL))ˣ := fun g =>
    ⟨⟨v g, hv g⟩, ⟨w g, hw g⟩, Subtype.ext (hvw g), Subtype.ext (hwv g)⟩
  let χ : ↥(GK K) →* (↥(OL LL))ˣ :=
    { toFun := χf
      map_one' := by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c 1)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) = 1
        rw [map_one, inv_one, Units.val_one, map_one, map_one]
      map_mul' := fun g h => by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c (g * h))⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) =
          τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) * τ₀ (ι (((c h)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
        rw [map_mul, mul_inv, Units.val_mul, map_mul, map_mul] }
  refine ⟨χ, ?_, fun g => hvw g⟩
  show Continuous v
  have hne : ∀ g, (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) ≠ 0 := fun g h => by
    have : ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 0 := Subtype.ext h
    exact (c g).ne_zero this
  have h1 : Continuous (fun g : ↥(GK K) => ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) := by
    refine continuous_induced_rng.2 ?_
    have : (fun g : ↥(GK K) => ((ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)) : ↥K.1) : Om l)) =
        fun g => ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))⁻¹ := by
      funext g; rw [hι, Units.val_inv_eq_inv_val]; rfl
    rw [Function.comp_def, this]
    exact hc.inv₀ hne
  exact (continuous_algHom l K LL τ₀).comp h1

end GlobalTheory.ContCharUnitsOL

theorem GlobalTheory.ContCharUnitsOL.main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  intro l _ K LL τ₀ c hc
  exact GlobalTheory.ContCharUnitsOL.exists_unit_char l K LL τ₀ c hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpVec

theorem exists_letter_of_jump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  intro D HW l _ K s LL h T hC i ζ τ hPt a hJ
  obtain ⟨-, hemb, ι, hComp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt
  have hC3 := (GlobalTheory.NL.CompD.component D HW l K s LL h T hC i ζ τ ι hComp hemb).2.2.1
  have hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a :=
    lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ
  obtain ⟨w, hwa, hwa1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd, hdw⟩ := hC3 w hwa.1
  refine ⟨d, hd, ?_, ?_⟩
  · have : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
        w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hwa hdw
  · intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hdis := GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ
    have hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ := Submodule.sub_mem _ hwa.1 hy.1
    have hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ' := by
      have : w - y = z - (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by
        rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hz hdw
    have h0 : w - y = 0 := Submodule.disjoint_def.1 hdis _ hD hS
    have : w = y := sub_eq_zero.1 h0
    exact hwa1 (this ▸ hy)

end GlobalTheory.NL.JumpVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_adicCompletion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  first | exact @GlobalTheory.BSP.exists_delta_completion | exact GlobalTheory.BSP.exists_delta_completion | (intros; apply GlobalTheory.BSP.exists_delta_completion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairingStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  first | exact @GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | exact GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | (intros; apply GlobalTheory.Pass.LocDual.exists_dualLat_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  first | exact @GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | exact GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet | (intros; apply GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhatStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  first | exact @GlobalTheory.BK.coordE_mxInv | exact GlobalTheory.BK.coordE_mxInv | (intros; apply GlobalTheory.BK.coordE_mxInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.FrobSysCoef.main | exact GlobalTheory.FrobSysCoef.main | (intros; apply GlobalTheory.FrobSysCoef.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  first | exact @GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | exact GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet | (intros; apply GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnityStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  first | exact @GlobalTheory.BKLim.exists_isZ_not_root | exact GlobalTheory.BKLim.exists_isZ_not_root | (intros; apply GlobalTheory.BKLim.exists_isZ_not_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvalues
section
noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Polynomial

theorem blockPol_map_ringHom {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem map_mem_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {w : Matrix (Fin n) (Fin n) A}
    (hw : w ∈ Submodule.span A (Set.range σ)) :
    w.map (toFr A) ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A)) := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact Submodule.subset_span ⟨h, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (c • y).map (toFr A) = toFr A c • y.map (toFr A) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem exists_denom_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {m : Matrix (Fin n) (Fin n) (FractionRing A)}
    (hm : m ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A))) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A (Set.range σ), w.map (toFr A) = toFr A d • m := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    exact ⟨1, one_ne_zero, σ h, Submodule.subset_span ⟨h, rfl⟩, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      add_mem (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    have h2 := congrFun (congrFun e' i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, map_add,
      map_mul] at h1 h2 ⊢
    rw [h1, h2]; ring
  | smul c y _ hy =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap A (FractionRing A) q ≠ 0 := by simpa using hq0
    refine ⟨d * q, mul_ne_zero hd hq0, p • w, Submodule.smul_mem _ _ hw, ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
    rw [h1]
    simp only [toFr]
    field_simp

theorem exists_correction_distinct_eigenvalues {Γ X A : Type} [Group Γ] [Finite X] [CommRing A]
    [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A) (hz : z ≠ 0)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y)
    (hirr : ∀ x, AbsIrrDistinct (overK (rep x))) (hin : InRing T rep eB) (hid : eB * eB = eB)
    (hrk : ∀ x, ((eB x).map (toFr A)).rank = t)
    (hπ : ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable) :
    ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x,
      (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet
        (AlgebraicClosure (FractionRing A))).ncard = t := by
  classical
  have hidx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  have hidK : ∀ x, (eB x).map (toFr A) * (eB x).map (toFr A) = (eB x).map (toFr A) := fun x => by
    rw [← Matrix.map_mul, hidx]
  choose a b hba hab hpol using fun x => GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image ((eB x).map (toFr A)) (hidK x) (hrk x)
  have hbe : ∀ x, b x * (eB x).map (toFr A) = b x := fun x => by
    rw [← hab, ← Matrix.mul_assoc, hba, Matrix.one_mul]
  have hea : ∀ x, (eB x).map (toFr A) * a x = a x := fun x => by
    rw [← hab, Matrix.mul_assoc, hba, Matrix.mul_one]
  have hpolA : ∀ x (M : Matrix (Fin n) (Fin n) A),
      (blockPol (eB x) (eB x * M * eB x)).map (toFr A) = (b x * M.map (toFr A) * a x).charpoly := by
    intro x M
    rw [blockPol_map_ringHom, Matrix.map_mul, Matrix.map_mul, hpol]
  let φ : (X → Matrix (Fin n) (Fin n) A) →ₗ[A] (X → Matrix (Fin t) (Fin t) (FractionRing A)) :=
    { toFun := fun s x => b x * (z • s x).map (toFr A) * a x
      map_add' := fun s s' => by
        funext x
        simp only [Pi.add_apply, smul_add, Matrix.map_add _ (map_add (toFr A)), Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun c s => by
        funext x
        have : (z • c • s x).map (toFr A) = c • (z • s x).map (toFr A) := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
          rw [Algebra.smul_def, mul_left_comm]
        simp only [this, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply] }
  have hφ : ∀ s x, φ s x = b x * (z • s x).map (toFr A) * a x := fun _ _ => rfl
  obtain ⟨_, ⟨s, hs, rfl⟩, hsx⟩ := GlobalTheory.T.exists_mem_submodule_all_charpoly_separable (O := A) (K := FractionRing A) t
    ((spanRingCornerIdealModule T rep π eB).map φ) (fun x => b x * (mat (rep x) g0).map (toFr A) * a x) (by
      intro x
      by_cases hx : x = π
      · left
        subst hx
        rwa [hpolA] at hπ
      · right
        have hmem : a x * b x ∈ Submodule.span (FractionRing A)
            (Set.range fun g => (mat (rep x) g).map (toFr A)) := by
          rw [hab]
          exact map_mem_span_frac _ (eval_mem_span hin x)
        obtain ⟨m, hm, hms⟩ := GlobalTheory.T.exists_mem_span_corner_charpoly_separable (mapM (toFr A) ((Units.coeHom _).comp (rep x)))
          (a x) (b x) (hirr x) (hba x) hmem
        obtain ⟨d, hd, w, hw, hwm⟩ := exists_denom_span_frac (mat (rep x)) hm
        obtain ⟨w', hw', rfl⟩ := exists_inRing_eval (T := T) x hw
        obtain ⟨f, hf, hfx⟩ := hsep x π hx
        have hj : f - algebraMap A (X → A) (f π) ∈ T := T.sub_mem hf (T.algebraMap_mem _)
        have hjx : f x - f π ≠ 0 := sub_ne_zero.2 hfx
        have hc : toFr A (z * (f x - f π) * d) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
            (mul_ne_zero (mul_ne_zero hz hjx) hd)
        refine ⟨_, ⟨fun y => (f - algebraMap A (X → A) (f π)) y • (eB y * w' y * eB y),
          Submodule.subset_span ⟨_, hj, by simp, w', hw', rfl⟩, rfl⟩,
          (toFr A (z * (f x - f π) * d))⁻¹, inv_ne_zero hc, ?_⟩
        have h1 : (z • ((f - algebraMap A (X → A) (f π)) x • (eB x * w' x * eB x))).map (toFr A) =
            toFr A (z * (f x - f π) * d) •
              ((eB x).map (toFr A) * m * (eB x).map (toFr A)) := by
          have h2 : ∀ (c : A) (M : Matrix (Fin n) (Fin n) A),
              (c • M).map (toFr A) = toFr A c • M.map (toFr A) := fun c M => by
            ext i j; simp
          rw [h2, h2, Matrix.map_mul, Matrix.map_mul, hwm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, mul_assoc]
          simp
        rw [hφ, h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc, one_smul,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbe, Matrix.mul_assoc _ _ (a x), hea]
        exact hms)
  have hs' := (mem_spanRingCornerIdealModule_iff T rep π eB s).1 hs
  refine ⟨s, hs', fun x => ?_⟩
  have hc := InMatrixCongruenceModule.corner hid hs' x
  have h1 : eB x * mat (rep x) g0 * eB x + z • s x = eB x * (mat (rep x) g0 + z • s x) * eB x := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hc.1, hc.2]
  have h2 := hsx x
  rw [hφ, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add (toFr A))] at h2
  rw [h1, hpolA, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree h2 (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

end GlobalTheory.SpanRing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaMulGaloisCompositumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_mul_galois_compositum : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 → ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) → ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧ (i : GQ l)⁻¹ * h ∈ GK K'' := by
  first | exact @GlobalTheory.InertiaLift.lift | exact GlobalTheory.InertiaLift.lift | (intros; apply GlobalTheory.InertiaLift.lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralInversePowerSeriesOfUnitConstantCoStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1 := by
  first | exact @GlobalTheory.powerSeries_inv_coeff_norm_le_one | exact GlobalTheory.powerSeries_inv_coeff_norm_le_one | (intros; apply GlobalTheory.powerSeries_inv_coeff_norm_le_one <;> assumption)
end

