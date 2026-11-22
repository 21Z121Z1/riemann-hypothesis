import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExt
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpRestrict

open GlobalTheory.DRFil

theorem jump_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  intro l _ P AI T K K' LL hle V _ _ _ _ _ ρ hc τ' a hj
  have := K.2
  have := K'.2
  have := LL.2
  set τ := τ'.comp (IntermediateField.inclusion hle) with hτ
  have hF := isField_dR T
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) hF ρ (filSpans T K LL ρ (crys T K LL ρ hc).1) τ
  set e' := idem (K := ↥K'.1) P.R.BdR (LL := ↥LL.1) τ' with he'
  set e := idem (K := ↥K.1) P.R.BdR (LL := ↥LL.1) τ with he
  have hee : e' * e = e' := by
    obtain ⟨n, x, c, hc1, hc2⟩ := idem_repr (K := ↥K.1) P.R.BdR τ
    rw [he, hc1]
    have := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ' n x (fun i => IntermediateField.inclusion hle (c i))
    exact (this.trans (by rw [← hc2]; rfl)).trans (one_smul _ _)
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ'
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V e' (d i)) k := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r hr i => ?_, fun n y hy => ?_⟩
    · exact sm_idem_mem_DdRE (P.PD K') _ τ' (GlobalTheory.Per.TiedRestrict.ddR_le hle ρ (hA.mem i).1.1)
    · refine sm_idem_mem_FilV (P.PD K') τ' ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (hA.mem i).2
    · have h1 := hA.indep (fun i => r i * e') (by
        rw [← hr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_mul])
      calc e' * r i = (e' * e) * r i := by rw [hee]
        _ = e * (r i * e') := by ring
        _ = 0 := h1 i
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']
        exact hr i
      · have h2 : sm ℚ_[l] P.R.BdR ↥LL.1 V e' y =
            sm ℚ_[l] P.R.BdR ↥LL.1 V e' (sm ℚ_[l] P.R.BdR ↥LL.1 V e y) := by
          rw [← sm_mul, hee]
        rw [h2, hy', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_comm]
  rw [hA'.isJumpV_iff] at hj
  exact hA.isJumpV_iff a |>.2 hj

end GlobalTheory.Per.JumpRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol GlobalTheory.DeRhamSymbolBasis

theorem colHT_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI J K LL m r' u k hu g hg
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply, colHT, Matrix.of_apply]
  set M := (r' g : Matrix (Fin m) (Fin m) ↥LL.1) with hM
  set t : P.R.BdR := ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) with ht
  set q : ℚ_[l] := ((P.χQ (g : GQ l) ^ k i : ℚ_[l]ˣ) : ℚ_[l]) with hq
  have key : ∀ x, t * u i x ∈ (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i x))
  have hmem : ∀ x, algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x) ∈
      (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
    exact om_mul_mem _ (act_mem _ (key x))
  have h1 := congrFun (hg i) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, embF_apply] at h1
  have h2 : t * u i j = ∑ x, algebraMap (Om l) P.R.BdR ((M j x : ↥LL.1) : Om l) *
      (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) := by
    conv_lhs => rw [← h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, shift_act]
  have h3 : ∀ x, J.θ (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) =
      (q : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR,
      J.θ_mul _ (om_mem _) _ (act_mem _ (key x)), J.θ_Om, J.θ_act _ _ (key x),
      GlobalTheory.MemLoc.TiedTheta.actC_eq]
  have hunit : (q : ℂ_[l]) * ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    have e : q * (((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
      rw [hq, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    have e2 := congrArg (fun z : ℚ_[l] => (z : ℂ_[l])) e
    rw [map_mul, UniformSpace.Completion.coe_mul, map_one, UniformSpace.Completion.coe_one] at e2
    exact e2
  rw [h2, theta_comb J _ _ hmem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h3]
  linear_combination (-((((M j x : ↥LL.1) : Om l) : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)))) * hunit

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem colHT_isUnit_det {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ)
    (hu : ∀ i j, u i j ∈ (P.PD K).Fil (k i))
    (hspan : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i)
    (hli : LinearIndependent P.R.BdR u) : IsUnit (colHT J u k).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  set s : Fin m → Fin m → P.R.BdR := fun i j => ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j with hs
  have hs0 : ∀ i j, s i j ∈ (P.PD (botExt l)).Fil 0 := fun i j =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i j))
  choose γ hγ0 hγ using J.θ_onto
  set z : Fin m → P.R.BdR := fun j => ∑ i, γ (c i) * s i j with hz
  have hz0 : ∀ j, z j ∈ (P.PD (botExt l)).Fil 0 := fun j => by
    have := Submodule.sum_mem ((P.PD (botExt l)).Fil 0) (t := Finset.univ)
      (f := fun i => γ (c i) * s i j) fun i _ => by
        simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)
    exact this
  have hz1 : ∀ j, z j ∈ (P.PD K).Fil 1 := fun j => by
    rw [mem_iff K]
    refine (J.θ_ker _ (hz0 j)).1 ?_
    have h1 := congrFun hc j
    simp only [Matrix.mulVec, dotProduct, colHT, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hz, GlobalTheory.DeRhamSymbolBasis.theta_sum J _ _ fun i => by
      simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [J.θ_mul _ (hγ0 (c i)) _ (hs0 i j), hγ, mul_comm]
  obtain ⟨f, hf, hfz⟩ := hspan 1 z hz1
  have hz' : z = ∑ i, (γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) • u i := by
    funext j
    simp only [hz, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiff := Fintype.linearIndependent_iff.1 hli
    (fun i => f i - γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hfz, ← hz', sub_self])
  funext i
  have hfi : f i = γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) := sub_eq_zero.1 (hdiff i)
  have hγi : γ (c i) = f i * ((tU P ^ (k i) : P.R.BdRˣ) : P.R.BdR) := by
    rw [hfi, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  have hmem : γ (c i) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_iff K _ _).1 (hf i)) (zpow_mem J (k i))
    rw [sub_add_cancel] at this
    rwa [hγi]
  rw [Pi.zero_apply, ← hγ (c i)]
  exact (J.θ_ker _ (hγ0 (c i))).2 hmem

end GlobalTheory.HTBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section General

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] [NeZero a]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_Ehat_pow_mul (w : ZMod a → ι → AhatE O K l e) :
    ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * w τ i := by
  classical
  choose r z hz using fun p : ZMod a × ι => IsLocalization.Away.surj (Ehat O K l e) (w p.1 p.2)
  refine ⟨Finset.univ.sup r, fun τ i => Ehat O K l e ^ (Finset.univ.sup r - r (τ, i)) * z (τ, i),
    fun τ i => ?_⟩
  have hle : r (τ, i) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
  rw [map_mul, map_pow, ← hz (τ, i), mul_left_comm, ← pow_add, Nat.sub_add_cancel hle, mul_comm]

end General

theorem hsum_mul_Ehat_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P n s m
  exact exists_Ehat_pow_mul (GlobalTheory.BKGal.JumpDR.hsum P s fun k => (m k).1)

end GlobalTheory.BKGal.JumpDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisibleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_membership_divisible : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e), ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} → ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  first | exact @GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | exact GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | (intros; apply GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmHerrLocal

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F :=
  fun D HW F => Formalism.MainNotions.HerrComplexNaturality.herr_class_maps_of_naturality D HW F
    (Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_a_and_natural D HW F))
    (GlobalTheory.HerrExtUnit.main D HW F)

end GlobalTheory.AdmHerrLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerMore
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.EtaPassage

theorem main : ∀ D : D7, KillingConditions.CommutingEndomorphismCondition D → TwistedPlaces.adm1 D := by
  intro D h i hi hl
  obtain ⟨α, hc, h1, h0⟩ := h i hi hl
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : ℤ) ≠ 0 := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos.ne'
  have hP := Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) α _ hA hc h1 h0
  rw [← Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.etaLoc_eq] at hP
  simp only [padicValInt.of_nat] at hP
  have hR := (Rat.cast_le (K := ℝ)).2 hP
  push_cast at hR
  exact hR

end GlobalTheory.EtaPassage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | exact GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | (intros; apply GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelation
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.QuadN

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.Cut.CocN.main D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact GlobalTheory.Cut.Quad.eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (GlobalTheory.Cut.Quad.length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.QuadN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_inertia_of_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  first | exact @GlobalTheory.InertiaConj.inertia_conj_mem | exact GlobalTheory.InertiaConj.inertia_conj_mem | (intros; apply GlobalTheory.InertiaConj.inertia_conj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLessStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixing_kummer_root_moves_less : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  first | exact @GlobalTheory.NearRoot.near_root | exact GlobalTheory.NearRoot.near_root | (intros; apply GlobalTheory.NearRoot.near_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InerQl

theorem root_eq_of_near {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m)
    {ζ η : Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  first
  | exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)

theorem IK_fixes_Kur {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) {g : ↥(GK K)} (hg : g ∈ IK K)
    {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : (g : GQ l) c = c := by
  let Fx : Subgroup ↥(GK K) :=
    { carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun {a b} ha hb c hc => by
        show (a : GQ l) ((b : GQ l) c) = c
        rw [hb c hc, ha c hc]
      inv_mem' := fun {a} ha c hc => by
        show ((a : GQ l)⁻¹) c = c
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← ha c hc]
        exact AlgEquiv.symm_apply_apply _ _ }
  have hle : IK K ≤ Fx := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ c hc
    unfold MaximalUnramifiedExtension at hc
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, hlm, hxm⟩ := hx
      have hxn : ‖x‖ ≤ 1 := by
        have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le
      exact root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)
    | algebraMap x => exact (σ : GQ l).commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  exact hle hg c hc

theorem IK_mem_Iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl K' h hN hF hS g hg c
  show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c
  rw [Pl.PD_actB]
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  exact Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)

end GlobalTheory.InerQl
end

