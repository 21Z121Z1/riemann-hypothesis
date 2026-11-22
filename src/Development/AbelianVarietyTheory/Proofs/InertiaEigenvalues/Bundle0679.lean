import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteHeightBreuilKisinLatticeSemistable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WHeight

open GlobalTheory.BSP.HeightEx in

theorem exists_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (b : ℕ) (A A' : Matrix (Fin d) (Fin d) (bk.S)), IsUnit (Y.map (inclW l)) ∧ IsUnit Z ∧ (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) ∧ A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Y.map WittVector.frobenius = Y * A.map bk.ev := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (GlobalTheory.BSP.HeightEx.inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet
  have hY'u := GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.semistableSeed_module_lAdic_closed l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.semistable_periods_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.semistablePeriod_span_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨Y, _, b, _, A', hYu, GlobalTheory.T.semistable_disc_period_basis_isUnit l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, hA', hA⟩

end GlobalTheory.BKLim.WHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LocalRepsFin

theorem exists_isCosetRep_finIdem : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  intro D V β L v f hf α hα
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hG : ∀ g, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g → g ∈ GfC V := fun g hg =>
    GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 hg
  let S : Subgroup (GA D V) := GlobalTheory.IdemSupport.suppGroup V (algebraMap _ (Formalism.L2.Theta.AE D) ε)
  have hS : ∀ g, g ∈ S ↔ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g := fun _ => Iff.rfl
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps (GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := S)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ levG V β L ∧ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) k} =
      (levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end GlobalTheory.LocalRepsFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  first | exact @GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | exact GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | (intros; apply GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedFCrystalOfStratifiedPhiModule
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCrys

theorem exists_semiBC {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] : ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B P) (u : M →ₛₗ[f] P), SemiBC u := by
  letI := f.toAlgebra
  let u : M →ₛₗ[algebraMap A B] (B ⊗[A] M) :=
    { toFun := fun x => 1 ⊗ₜ x
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun a x => by rw [algebraMap_smul, TensorProduct.tmul_smul] }
  exact ⟨B ⊗[A] M, inferInstance, inferInstance, u,
    (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B M (B ⊗[A] M) u (TensorProduct.mk A B M 1) fun _ => rfl).2
      (TensorProduct.isBaseChange A M B)⟩

theorem bijective_of_semiBC {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (u : M →ₗ[A] N) (h : SemiBC u) : Function.Bijective u := by
  obtain ⟨w, hw, -⟩ := h M LinearMap.id
  have h2 : u.comp w = LinearMap.id := h.hom_ext fun x => congrArg u (hw x)
  exact ⟨Function.LeftInverse.injective (g := w) hw, fun y => ⟨w y, LinearMap.congr_fun h2 y⟩⟩

def fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) :
    N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N where
  toFun x := LocalizedModule.mk (Ψ x) ⟨t ^ a, (Submonoid.mem_powers_iff _ _).2 ⟨a, rfl⟩⟩
  map_add' x y := by
    rw [map_add, LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
  map_smul' c x := by
    rw [Ψ.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]

theorem isFrac_fracMap {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {φ : A →+* A} (t : A) (a : ℕ)
    (Ψ : N →ₛₗ[φ] N) (x : N) : IsFrac t (fracMap t a Ψ x) (Ψ x) a := rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}

theorem eval_ext {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N) {x y : N}
    (h : ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), V.v a g x = V.v a g y) : x = y := by
  obtain ⟨C, c, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  exact (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V c f hc).1 (h C c f)

theorem v_id_bijective {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : Function.Bijective (V.v (Hom.id B) f) :=
  bijective_of_semiBC (A := B.A) (V.v (Hom.id B) f) (V.bc (Hom.id B) f)

theorem semiBC_fracMap {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (t : B.A) (ht : t ∈ B.I) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) : SemiBC (fracMap t S.a Ψ) := by
  obtain ⟨P, _, _, u, hu⟩ := exists_semiBC B.D.φ N
  obtain ⟨L, hL, -⟩ := hu N Ψ
  obtain ⟨n, h1, h2⟩ := GlobalTheory.T.linearizedFrobenius_invertible_up_to_pow l K bk d S B N V t ht Ψ hΨ P u hu L hL
  exact GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded B.A B.D.φ t N P u hu L n S.a h1 h2 _ fun x => by
    rw [hL]; exact isFrac_fracMap _ _ _ _

variable (S) in

theorem exists_crys : ∃ (M : FCrys l ↥(OL K)) (V : ∀ B, Eval S B (M.M B)),
    (∀ (B B' Q : Obj l ↥(OL K)) (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B),
      (V B').v a g (M.tr k x) = (V B).v (a.comp k) g x) ∧
    ∀ (B : Obj l ↥(OL K)) (t : ↥B.I), ∃ Ψ : M.M B →ₛₗ[B.D.φ] M.M B, IsPsi (V B) t Ψ ∧
      ∀ x, IsFrac (t : B.A) (M.Φ B t x) (Ψ x) S.a := by
  choose N acg mod hV using GlobalTheory.T.exists_stratifiedPhiModuleValue l K bk d S
  have V : ∀ B, Eval S B (N B) := fun B => (hV B).some
  choose tr trbc htr using fun (B B' : Obj l ↥(OL K)) (k : Hom B B') =>
    GlobalTheory.T.exists_stratifiedValue_transition_baseChange l K bk d S B B' (N B) (N B') (V B) (V B') k
  choose Ψ hΨ using fun (B : Obj l ↥(OL K)) (t : ↥B.I) =>
    GlobalTheory.T.exists_frobenius_on_stratifiedValue l K bk d S B (N B) (V B) t t.2
  let M : FCrys l ↥(OL K) :=
    { M := N
      acg := acg
      mod := mod
      fin := fun B => (V B).fin
      proj := fun B => (V B).proj
      tr := fun k => tr _ _ k
      tr_bc := fun k => trbc _ _ k
      tr_id := fun B x => eval_ext (V B) fun Q a g => htr _ _ _ Q a g x
      tr_comp := fun {B B' B''} k' k x => eval_ext (V B'') fun Q a g =>
        (htr _ _ (k'.comp k) Q a g x).trans
          ((htr _ _ k' Q a g _).trans (htr _ _ k Q (a.comp k') g x)).symm
      Φ := fun B t => fracMap (t : B.A) S.a (Ψ B t)
      Φ_bc := fun B t => semiBC_fracMap (V B) t t.2 _ (hΨ B t)
      Φ_nat := fun {B B'} k t t' x m i n j h1 h2 =>
        GlobalTheory.T.isLocalizedFraction_semilinear_transition B.A B'.A k.f (N B) (N B') (tr _ _ k) t t' S.a _ _ _ m _ n i j
          (isFrac_fracMap _ _ _ _) h1 (isFrac_fracMap _ _ _ _) h2
          (GlobalTheory.T.stratifiedValue_frobenius_comm_transition l K bk d S B B' (N B) (N B') (V B) (V B') k (tr _ _ k) (htr _ _ k) t t' _ _
            (hΨ B t) (hΨ B' t') x) }
  exact ⟨M, V, fun B B' Q k a g x => htr _ _ k Q a g x, fun B t => ⟨Ψ B t, hΨ B t, fun _ => rfl⟩⟩

theorem map_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (j i : Fin d) :
    f ((Pi.single j 1 : Fin d → A) i) = (Pi.single j 1 : Fin d → B) i := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem sum_single {A : Type} [CommRing A] (c : Fin d → A) :
    ∑ i, c i • (Pi.single i 1 : Fin d → A) = c := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_basis {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) : ∃ e : Module.Basis (Fin d) B.A N, ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1 := by
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  let q : N ≃ₗ[B.A] (Fin d → B.A) := LinearEquiv.ofBijective w (v_id_bijective V f)
  refine ⟨(Pi.basisFun _ _).map q.symm, fun j => ?_⟩
  change q _ = _
  simp

theorem eq_sum_of_coord {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (e : Fin d → N) (he : ∀ j, V.v (Hom.id B) f (e j) = Pi.single j 1) (x : N)
    (c : Fin d → B.A) (h : V.v (Hom.id B) f x = c) : x = ∑ i, c i • e i := by
  apply (v_id_bijective V f).1
  let w : N →ₗ[B.A] (Fin d → B.A) := V.v (Hom.id B) f
  have he' : ∀ j, w (e j) = Pi.single j 1 := he
  change _ = w _
  rw [h, map_sum]
  simp only [map_smul, he']
  exact (sum_single c).symm

theorem coord_psi {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N] (V : Eval S B N)
    (f : Hom bk.prism B) (t : B.A) (ht : t = BK.hf f bk.E) (Ψ : N →ₛₗ[B.D.φ] N) (hΨ : IsPsi V t Ψ) (x : N)
    (j : Fin d) (hx : V.v (Hom.id B) f x = Pi.single j 1) :
    V.v (Hom.id B) f (Ψ x) = fun i => BK.hf f (S.A i j) := by
  have h1 := hΨ (Hom.id B) f x
  rw [hx, funext (map_single B.D.φ j), Matrix.mulVec_single_one] at h1
  subst ht
  ext i
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f).2 S.a)).1 (congrFun h1 i)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) :
    ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  obtain ⟨M, V, htr, hΦ⟩ := exists_crys S
  obtain ⟨e, he⟩ := exists_basis (V bk.prism) (Hom.id _)
  have he' : ∀ {B : Obj l ↥(OL K)} (g : Hom bk.prism B) j, (V bk.prism).v g g (e j) = Pi.single j 1 :=
    fun g j => by
      ext i
      have := (V bk.prism).v_nat g (Hom.id _) (Hom.id _) (e j) i
      rw [he, map_single] at this
      exact this
  refine ⟨M, e, ⟨fun {B} f g j => ?_, fun j => ?_⟩⟩
  · have h1 : ∀ (g : Hom bk.prism B) x, (V B).v (Hom.id B) f (M.tr g x) = (V bk.prism).v g f x :=
      fun g x => htr _ _ B g (Hom.id B) f x
    refine eq_sum_of_coord (V B) f (fun i => M.tr f (e i)) (fun i => (h1 f _).trans (he' f i)) _
      (fun i => S.ε f g i j) ?_
    rw [h1, (V _).v_ε g f g, he', Matrix.mulVec_single_one]
    rfl
  · have h0 : ∀ x, BK.hf (Hom.id bk.prism) x = bk.toP x := fun _ => rfl
    have ht : bk.toP bk.E ∈ bk.prism.I := by
      rw [(GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk bk.prism (Hom.id _)).1, h0]
      exact Ideal.mem_span_singleton_self _
    have hh := hΦ bk.prism ⟨bk.toP bk.E, ht⟩
    obtain ⟨Ψ, hΨ, h⟩ := hh
    have h1 := coord_psi (V _) (Hom.id _) _ (h0 _).symm Ψ hΨ _ j (he j)
    have h2 := eq_sum_of_coord (V _) (Hom.id _) e he _ _ h1
    simp only [h0] at h2
    exact Eq.mp (congrArg (fun m => IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, ht⟩ (e j)) m S.a) h2)
      (h (e j))

end GlobalTheory.BSP.StratCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZero
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  first | (exact @GlobalTheory.LogFlatLam.exists_lam) | (exact GlobalTheory.LogFlatLam.exists_lam) | (intros; apply GlobalTheory.LogFlatLam.exists_lam  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrism
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  apply GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRepStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  first | exact @GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | exact GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | (intros; apply GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)), ht.Rel (BK.hf f X) f g ε → x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε → BK.hf g bk.E ^ (ht.a + s.N) • (ht.A.map (BK.hf f) * x.map B.D.φ) = BK.hf f bk.E ^ (ht.a + s.N) • (x * ht.A.map (BK.hf g)) := by
  first | exact @GlobalTheory.BSP.Height.phi_eq_of_rel_pow | exact GlobalTheory.BSP.Height.phi_eq_of_rel_pow | (intros; apply GlobalTheory.BSP.Height.phi_eq_of_rel_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalLemmaLattice_degreeOne : FLAt 1 := by
  first | exact @GlobalTheory.PMon.FLOne.flAt_one | exact GlobalTheory.PMon.FLOne.flAt_one | (intros; apply GlobalTheory.PMon.FLOne.flAt_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryMemLatticeInvLOfMonodromyEqZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_coboundary_mem_lattice_inv_l_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.BKGal.coboundary_mem_lattice_of_mon_eq_zero | exact GlobalTheory.BKGal.coboundary_mem_lattice_of_mon_eq_zero | (intros; apply GlobalTheory.BKGal.coboundary_mem_lattice_of_mon_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPairStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1f_class_of_wach_pair : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  first | exact @GlobalTheory.NL.ExtClassKs.main | exact GlobalTheory.NL.ExtClassKs.main | (intros; apply GlobalTheory.NL.ExtClassKs.main <;> assumption)
end

