import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevel
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem teich_pow_sub_one_eq_ED_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ε c hε hc
  have hd : ED K t ϖ = toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) := by
    rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨⟨ξ, hξ, hμ⟩, -, hθδ, -⟩ := (GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  set G : Ainf l := ∑ i ∈ Finset.range c, WittVector.teichmuller l ε ^ i with hG
  set w : Ainf l := (v : Ainf l) * (muOf δ * G) with hwdef
  have hkey : WittVector.teichmuller l ε ^ c - 1 = ϖ.ev a (eis l a e) * w := by
    have h1 : WittVector.teichmuller l ε ^ c - 1 = muOf ε * G := by
      rw [muOf, hG, mul_comm, geom_sum_mul]
    rw [h1, hμ, ← hv, hwdef]
    ring
  have hθG : ((Per.θ l G : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
    rw [hG, map_sum]
    simp only [map_pow, WittVector.fontaineTheta_teichmuller, hε.1, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have hθw : ((Per.θ l w : Per.OC l) : ℂ_[l]) ≠ 0 := by
    have h1 : ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
      (v.isUnit.map (Per.θ l)).ne_zero (Subtype.ext (h.trans rfl))
    have h2 : ((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h => hθδ (Subtype.ext (h.trans rfl))
    have h3 : (c : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc
    have h4 : ((Per.θ l w : Per.OC l) : ℂ_[l]) =
        ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) * (((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) *
          ((Per.θ l G : Per.OC l) : ℂ_[l])) := by
      rw [hwdef, map_mul, map_mul]
      rfl
    rw [h4, hθG]
    exact mul_ne_zero h1 (mul_ne_zero h2 h3)
  have hwu : IsUnit (ainfToBdRp l w) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
    change Per.θD l (GlobalTheory.MemLoc.aDp l w) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact hθw)
  refine ⟨toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O), ?_, ?_⟩
  · have h2 : toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O) =
        (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O) (ainfToBdRp l w) := by
      simp [toOD]
    rw [h2]
    exact hwu.map _
  · have h3 : ((1 : O) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ε : OA l O) ^ c - 1 =
        ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) * ((1 : O) ⊗ₜ[ℤ_[l]] w) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hkey,
        Algebra.TensorProduct.one_def, TensorProduct.tmul_sub]
    rw [hd, ← map_mul, ← h3, map_sub, map_pow, map_one]

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisActionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDeRhamCoordMul_galois_action : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  first | exact @GlobalTheory.HodgeAt.PhiS_act | exact GlobalTheory.HodgeAt.PhiS_act | (intros; apply GlobalTheory.HodgeAt.PhiS_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := GlobalTheory.T.exists_integralLatticeBasisLocal l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.exists_integral_retraction_finiteExtension_ql l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := GlobalTheory.T.characterSetMapCoefficientField_properties (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (GlobalTheory.T.latticeHomBaseChange_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (GlobalTheory.T.inertiaThroughCharacters_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (GlobalTheory.T.hodgeJumps_mem_latticeCoefficientExtension l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, GlobalTheory.T.liftable_descends_from_larger_coefficientField l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.LocInputs

open TensorProduct in

theorem _root_.GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler :
    _root_.Formalism.GaloisCohomology.LocalTateDualityK → _root_.Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : _root_.Formalism.BasicNotions.D7) (HW : _root_.Formalism.BasicNotions.HWOf D.loc) (F : _root_.Formalism.BasicNotions.FonOf D.loc D.locA HW),
        ∃ _J : _root_.Formalism.MainNotions.LocalSituation.Ties D.loc D.locA HW F, _root_.Formalism.MainNotions.LocalSituation.admitted D HW F := by
  intro hduality heuler D HW F
  refine ⟨⟨fun l _ => (_root_.GlobalTheory.ThetaTie.nonempty_thetaL D l).some⟩, ?_⟩
  refine ⟨?_, hduality, _root_.GlobalTheory.TateTop.tate_h2_of_local_duality hduality D, heuler,
    _root_.GlobalTheory.TateFilQuot.tate_fil_quot D, _root_.GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories D,
    _root_.GlobalTheory.Per.FontaineAll.fontaine_bounds D, _root_.GlobalTheory.TateDualFil.main D, ?_⟩
  · refine _root_.GlobalTheory.FundSeq.surjective_half_of_onto (fun l _ => ?_) D
    obtain ⟨C⟩ := _root_.GlobalTheory.MemLoc.nonempty_core l
    exact _root_.GlobalTheory.FundSeq.ontoAt_of_core C
      (_root_.GlobalTheory.MemLoc.one_sub_phi_onto l C) (_root_.GlobalTheory.MemLoc.FundOnto.fundOnto l C)
  · intro l _ K s LL h
    exact ⟨_root_.GlobalTheory.Cyc.FontW.main D HW F l K s LL h,
      _root_.GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.LocInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectivStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWittEmbeddingTwisted_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  first | exact @GlobalTheory.CrysPrism.emb_algebraMap_injective | exact GlobalTheory.CrysPrism.emb_algebraMap_injective | (intros; apply GlobalTheory.CrysPrism.emb_algebraMap_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachImageDeRhamPlusComponentLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_image_deRham_plus_component_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → ∃ Ψ : ↥(W.N T) → T.V ⊗[ℚ_[l]] (D.loc l).R.BdR, (∀ x, Ψ x ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0) ∧ (∀ z ∈ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0, ∃ (m : ℕ) (b : Fin m → (D.loc l).R.BdR) (x : Fin m → ↥(W.N T)), (∀ j, b j ∈ ((D.loc l).PD K).Fil 0) ∧ z - ∑ j, mulVR T (b j) (Ψ (x j)) ∈ compKer T ι) ∧ ∀ (x : ↥(W.N T)) (a : ℕ), (∀ r : ℤ, r < -(a : ℤ) → ex C h T i ζ x r = 0) → ∃ c : ℤ, ∀ M : ℕ, mulVR T (tS (D.loc l) s ^ a) (Ψ x) - ∑ r ∈ Finset.range M, mulVR T (tS (D.loc l) s ^ r) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T i ζ x ((r : ℤ) - (a : ℤ)))) ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) ((M : ℤ) - c) := by
  first | exact @GlobalTheory.NL.PerS.image | exact GlobalTheory.NL.PerS.image | (intros; apply GlobalTheory.NL.PerS.image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_cokernel_killed_by_power : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  first | exact @GlobalTheory.NL.CokerFin.coker_killed | exact GlobalTheory.NL.CokerFin.coker_killed | (intros; apply GlobalTheory.NL.CokerFin.coker_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  first | exact @GlobalTheory.FrobCong.sigma_eq_pow_add | exact GlobalTheory.FrobCong.sigma_eq_pow_add | (intros; apply GlobalTheory.FrobCong.sigma_eq_pow_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormulaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zg_formula_alt : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : ((HW l).W K s LL h).DD T), z ∈ aN ((HW l).W K s LL h) T letπ → ∀ hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T, ∃ zz : ↥((HW l).W K s LL h).GKs → ((HW l).W K s LL h).DD T, (∀ g, zz g ∈ aN ((HW l).W K s LL h) T letπ) ∧ (∀ g, ((HW l).W K s LL h).γ T (zz g) - zz g = ((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥((HW l).W K s LL h).GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥((HW l).W K s LL h).GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = ((F l).E K s LL h).tie.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) := by
  first | exact @GlobalTheory.NL.ZgAll.zg_formula | exact GlobalTheory.NL.ZgAll.zg_formula | (intros; apply GlobalTheory.NL.ZgAll.zg_formula <;> assumption)
end

