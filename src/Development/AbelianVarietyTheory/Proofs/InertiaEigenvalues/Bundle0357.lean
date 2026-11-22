import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMem
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem inclR_pow_mul_smul_eq_sum {l : ℕ} [Fact l.Prime] {LL : FinExt l} {M : Type} [AddCommGroup M]
    [Module (RW LL) M] {ι : Type} [Fintype ι] [DecidableEq ι]
    (bO : Module.Basis ι ℤ_[l] ↥(OL LL)) (x : Ainf l) (k : ℕ) (z : RA LL) (y : M) :
    inclR LL (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x : RA LL) ^ k * z) • y =
      ∑ α, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (x ^ k * TensorProduct.equivFinsuppOfBasisLeft bO z α) : RW LL) •
        ((bO α ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL) • y) := by
  have hz : z = ∑ α, bO α ⊗ₜ[ℤ_[l]] TensorProduct.equivFinsuppOfBasisLeft bO z α := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft bO).symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  conv_lhs => rw [hz]
  rw [Finset.mul_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, ← mul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

theorem coords_sum_one_tmul_smul {R O W T ι κ : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W]
    [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι]
    [DecidableEq ι] [Fintype κ] (b : Module.Basis ι R T) (w : κ → W) (Y : κ → (O ⊗[R] W) ⊗[O] T)
    (i : ι) :
    GlobalTheory.WeakTop.coords W O b (∑ α, ((1 : O) ⊗ₜ[R] w α) • Y α) i =
      ∑ α, w α * GlobalTheory.WeakTop.coords W O b (Y α) i := by
  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun α _ => GlobalTheory.WeakTop.coords_one_tmul_smul b _ _ i

theorem exists_pow_wittCoords_inclR_smul_mem_nhds {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
    {K LL : FinExt l} {m : ℕ} (bO : Module.Basis (Fin m) ℤ_[l] ↥(OL LL)) {T : Lt K LL} {d : ℕ}
    (b : LatB T d) (y : TW (RW LL) T) (V : Set (Fin d → WCb l))
    (hV : letI := wTop l; V ∈ 𝓝 (0 : Fin d → WCb l)) :
    ∃ k : ℕ, ∀ z : RA LL, letI := zlMod T; haveI := zlTower T;
      GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b (inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]]
        (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y) ∈ V := by
  letI := zlMod T
  haveI := zlTower T
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  set x : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1 with hx
  let Y : Fin m → TW (RW LL) T := fun α => ((bO α ⊗ₜ[ℤ_[l]] (1 : WCb l) : RW LL)) • y
  let F : (Fin m → WCb l) → (Fin d → WCb l) := fun w i =>
    ∑ α, w α * GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b (Y α) i
  have hF : Continuous F := continuous_pi fun i =>
    continuous_finset_sum _ fun α _ => (continuous_apply α).mul continuous_const
  have hF0 : F 0 = 0 := by funext i; simp [F]
  have hFV : F ⁻¹' V ∈ 𝓝 (0 : Fin m → WCb l) := hF.tendsto 0 (hF0 ▸ hV)
  rw [nhds_pi] at hFV
  obtain ⟨I, -, t, ht, hIt⟩ := Filter.mem_pi.1 hFV
  have hV0 : (⋂ α, t α) ∈ 𝓝 (0 : WCb l) := Filter.iInter_mem.2 ht
  obtain ⟨k, hk⟩ := GlobalTheory.T.teichmullerRootPow_ideals_tendsto_zero_weakTop AI s (⋂ α, t α) hV0
  refine ⟨k, fun z => ?_⟩
  have key : GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b
      (inclR LL (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x : RA LL) ^ k * z) • y) =
      F (fun α => inclW l (x ^ k * TensorProduct.equivFinsuppOfBasisLeft bO z α)) := by
    exact (congrArg (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
      (inclR_pow_mul_smul_eq_sum (M := TW (RW LL) T) bO x k z y)).trans
      (funext fun i => coords_sum_one_tmul_smul b _ _ i)
  rw [key]
  exact hIt fun α _ => Set.mem_iInter.1 (hk _) α

theorem exists_pow_inclR_smul_mem : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL, inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U := by
  intro l _ P AI s K LL T d b y
  letI := zlMod T
  haveI := zlTower T
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  intro U hU
  obtain ⟨-, -, -, -, hfree, hfin, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hU' : U ∈ Filter.comap (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
      (𝓝 (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b 0)) := by
    have := hU
    rw [nhds_induced] at this
    exact this
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU'
  rw [map_zero] at hV
  obtain ⟨k, hk⟩ := exists_pow_wittCoords_inclR_smul_mem_nhds AI s (Module.finBasis ℤ_[l] ↥(OL LL)) b y V hV
  exact ⟨k, fun z => hVU (Set.mem_preimage.2 (hk z))⟩

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem coeC (z : Om l) : (z : ℂ_[l]) = algebraMap (Om l) ℂ_[l] z := rfl

theorem norm_l_C : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]

theorem norm_l_Om : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.norm_extends l (l : Om l), coeC, map_natCast, norm_l_C]

theorem norm_OC_le (x : OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_pi_lt {K : FinExt l} (bk : BK K) : ‖((Per.θ l (bk.ev X) : OC l) : ℂ_[l])‖ < 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  set φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom) with hφ
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  have hπ1 : ‖π‖ ≤ 1 := norm_OC_le _
  have h0 : bk.Ep.eval₂ φ π = 0 := by
    have h1 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    have h2 := congrArg (PadicComplexInt l).toSubring.subtype h1
    rw [BK.E, ← Polynomial.eval₂_C_X_eq_coe, Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      Polynomial.hom_eval₂, map_zero] at h2
    have hc : (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (bk.ev.comp C)) = φ :=
      RingHom.ext fun w => by simp [hφ, bk.ev_C]
    rw [hc] at h2
    exact h2
  have hcoef : ∀ i < bk.Ep.natDegree, ‖φ (bk.Ep.coeff i)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨c, hc⟩ := bk.dvd_coeff i hi
    rw [hc, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le (Per.θ l (wA l bk.a c)))
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree, map_one, one_mul] at h0
  have h3 : π ^ bk.Ep.natDegree = -∑ i ∈ Finset.range bk.Ep.natDegree, φ (bk.Ep.coeff i) * π ^ i := by
    linear_combination h0
  have h4 : ‖π‖ ^ bk.Ep.natDegree ≤ ‖(l : ℂ_[l])‖ := by
    rw [← norm_pow, h3, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ1)).trans
      (hcoef i (Finset.mem_range.1 hi))
  rw [norm_l_C] at h4
  by_contra h5
  push_neg at h5
  have h6 := one_le_pow₀ (n := bk.Ep.natDegree) h5
  have h7 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem step {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ (w : Wq l bk.a) (y' : Om l), y' ∈ K.1 ∧ y' ∈ MaximalUnramifiedExtension l ∧ ‖y'‖ ≤ 1 ∧
      (y : ℂ_[l]) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) + (l : ℂ_[l]) * (y' : ℂ_[l]) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let r : ↥(OL K) := ⟨⟨y, hyK⟩, mem_OL_of_norm_le K _ hy1⟩
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (bk.str r)
  have hθ : (y : ℂ_[l]) = ((Per.θ l (bk.ev f) : OC l) : ℂ_[l]) := by
    rw [bk.θ_ev r f hf, coe_intToOC]
  set z : Fq l bk.a := (constantCoeff f).coeff 0 with hz
  obtain ⟨u, hu⟩ : (l : Wq l bk.a) ∣ constantCoeff f - WittVector.teichmuller l z := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply, hz]
  set f' : bk.S := PowerSeries.mk fun p => coeff (p + 1) f
  have hfe : f = X * f' + C (constantCoeff f) := eq_X_mul_shift_add_const f
  have hc : constantCoeff f = WittVector.teichmuller l z + (l : Wq l bk.a) * u := by rw [← hu]; ring
  set Ψ : bk.S →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp bk.ev) with hΨ
  have hΨC : ∀ w, Ψ (C w) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun w => by simp [hΨ, bk.ev_C]
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  set t : ℂ_[l] := ((Per.θ l (wA l bk.a (WittVector.teichmuller l z)) : OC l) : ℂ_[l]) with ht
  set A : ℂ_[l] := ((Per.θ l (wA l bk.a u) : OC l) : ℂ_[l]) with hA
  set B : ℂ_[l] := ((Per.θ l (bk.ev f') : OC l) : ℂ_[l]) with hB
  have hdec : (y : ℂ_[l]) = t + (l : ℂ_[l]) * A + π * B := by
    have e1 : (y : ℂ_[l]) = Ψ f := hθ
    have e2 : Ψ X = π := rfl
    have e3 : Ψ f' = B := rfl
    rw [e1, hfe, hc]
    simp only [map_add, map_mul, map_natCast, hΨC, e2, e3]
    rw [ht, hA]
    ring

  set rt : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (C (WittVector.teichmuller l z))) with hrt
  have htK : t = (((rt : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← bk.θ_ev rt (C (WittVector.teichmuller l z)) (by rw [hrt, RingEquiv.apply_symm_apply]), bk.ev_C]
  set yt : Om l := ((rt : ↥K.1) : Om l) with hyt
  have hytK : yt ∈ K.1 := (rt : ↥K.1).2
  have hteich : (WittVector.teichmuller l z) ^ (l ^ bk.a) = WittVector.teichmuller l z := by
    rw [← map_pow, Fq.pow_card]
  have hyt_pow : yt ^ (l ^ bk.a) = yt := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_pow, ← coeC, ← htK, ht, ← SubmonoidClass.coe_pow, ← map_pow, ← map_pow, hteich]
  have hytU : yt ∈ MaximalUnramifiedExtension l := by
    by_cases h0 : yt = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ bk.a := one_lt_pow_l l bk.a
      refine IntermediateField.subset_adjoin ℚ_[l] _ ⟨l ^ bk.a - 1, by omega, fun h => ?_, ?_⟩
      · exact hl.out.not_dvd_one ((Nat.dvd_sub_iff_right hq.le (dvd_pow_self l (NeZero.ne bk.a))).1 h)
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, hyt_pow, one_mul]

  have hdK : y - yt ∈ K.1 := sub_mem hyK hytK
  have hdU : y - yt ∈ MaximalUnramifiedExtension l := sub_mem hyU hytU
  have hdC : ((y - yt : Om l) : ℂ_[l]) = (l : ℂ_[l]) * A + π * B := by
    rw [coeC, map_sub, ← coeC, ← coeC, hdec, ← htK]
    ring
  have hd1 : ‖y - yt‖ < 1 := by
    rw [← PadicComplex.norm_extends, hdC]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul, norm_l_C]
      exact (mul_le_of_le_one_right (by positivity) (norm_OC_le _)).trans_lt (inv_lt_one_of_one_lt₀ hl1)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le _)).trans_lt (norm_pi_lt bk)
  have hd2 : ‖y - yt‖ ≤ (l : ℝ)⁻¹ := by
    by_cases h0 : y - yt = 0
    · rw [h0, norm_zero]; positivity
    obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hdU h0
    rw [hk] at hd1 ⊢
    have hk0 : k < 0 := by
      by_contra hk0
      push_neg at hk0
      exact absurd hd1 (not_lt.2 (one_le_zpow₀ hl1.le hk0))
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le (by omega)
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine ⟨WittVector.teichmuller l z, (y - yt) / (l : Om l), div_mem hdK (natCast_mem _ l),
    div_mem hdU (natCast_mem _ l), ?_, ?_⟩
  · rw [norm_div, norm_l_Om, div_inv_eq_mul]
    calc ‖y - yt‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · have hlC : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    rw [coeC ((y - yt) / (l : Om l)), map_div₀, map_natCast, ← coeC, hdC, hdec]
    field_simp
    ring

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_of_int {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ w : Wq l bk.a, ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = (y : ℂ_[l]) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let N : Type := {y : Om l // y ∈ K.1 ∧ y ∈ MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}
  let Φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom)
  have hΦ : ∀ w, Φ w = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun _ => rfl
  have hΦ1 : ∀ w, ‖Φ w‖ ≤ 1 := fun w => norm_OC_le _
  have hs : ∀ v : N, ∃ p : Wq l bk.a × N,
      ((v.1 : Om l) : ℂ_[l]) = Φ p.1 + (l : ℂ_[l]) * ((p.2.1 : Om l) : ℂ_[l]) := by
    intro v
    obtain ⟨w, y', h1, h2, h3, h⟩ := step bk v.1 v.2.1 v.2.2.1 v.2.2.2
    exact ⟨(w, ⟨y', h1, h2, h3⟩), h⟩
  choose g hg using hs
  let ys : ℕ → N := fun k => Nat.rec (motive := fun _ => N) ⟨y, hyK, hyU, hy1⟩ (fun _ v => (g v).2) k
  have hys : ∀ k, ys (k + 1) = (g (ys k)).2 := fun _ => rfl
  let s : ℕ → Wq l bk.a := fun k => ∑ i ∈ Finset.range k, (l : Wq l bk.a) ^ i * (g (ys i)).1
  have hinv : ∀ k, (y : ℂ_[l]) = Φ (s k) + (l : ℂ_[l]) ^ k * (((ys k).1 : Om l) : ℂ_[l]) := by
    intro k
    induction k with
    | zero => simp [s, ys]
    | succ k ih =>
      have h := hg (ys k)
      rw [← hys] at h
      simp only [s, Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast]
      linear_combination ih + (l : ℂ_[l]) ^ k * h
  have hcau : ∀ m n, m ≤ n → (l : Wq l bk.a) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : s (n + 1) - s m = (s n - s m) + (l : Wq l bk.a) ^ n * (g (ys n)).1 := by
        simp only [s, Finset.sum_range_succ]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : Wq l bk.a)}) s fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hcau m n hmn)
  refine ⟨L, ?_⟩
  rw [← hΦ]
  have hbd : ∀ n : ℕ, ‖(y : ℂ_[l]) - Φ L‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    intro n
    have h := hL n
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨v, hv⟩ := h
    have e : (y : ℂ_[l]) - Φ L = (l : ℂ_[l]) ^ n * (Φ v + (((ys n).1 : Om l) : ℂ_[l])) := by
      have := congrArg Φ hv
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination hinv n + this
    rw [e, norm_mul, norm_pow, norm_l_C]
    refine mul_le_of_le_one_right (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hΦ1 v) ?_))
    rw [PadicComplex.norm_extends]
    exact (ys n).2.2.2
  by_contra hne
  have hpos : 0 < ‖(y : ℂ_[l]) - Φ L‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  exact absurd (hbd n) (not_le.2 hn)

theorem exists_pow_mul_eq_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 →
    x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a),
      ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  intro l _ K bk x hxK hxU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hl1
  have h1 : ‖(l : Om l) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_l_Om, inv_pow]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hn.le
  obtain ⟨w, hw⟩ := exists_of_int bk _ (mul_mem (pow_mem (natCast_mem _ l) n) hxK)
    (mul_mem (pow_mem (natCast_mem _ l) n) hxU) h1
  exact ⟨n, w, hw⟩

end GlobalTheory.UnrWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tau_component_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  first | exact @GlobalTheory.TauFrame.exists_tau_frame | exact GlobalTheory.TauFrame.exists_tau_frame | (intros; apply GlobalTheory.TauFrame.exists_tau_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceMemMaximalIdealPowOfDifferentExponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), ramificationIndex F M * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | exact GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | (intros; apply GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_unramifiedIntegers_coords_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  first | exact @GlobalTheory.PrismSplit.existsUnique_coords | exact GlobalTheory.PrismSplit.existsUnique_coords | (intros; apply GlobalTheory.PrismSplit.existsUnique_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachInclusionPowerSeriesIntoOneTmulAinfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachInclusion_powerSeries_into_one_tmul_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∃ io : PowerSeries (WK K) →+* Ainf l, (∀ x, I.io (letEmb Γ.emb x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] io x) ∧ io PowerSeries.X = WittVector.teichmuller l (AI.εroot s) - 1 ∧ ∀ w : WK K, Formalism.Per.θ l (io (PowerSeries.C w)) = intToOC (unr K) w := by
  first | exact @GlobalTheory.PrismS.IoDescent.main | exact GlobalTheory.PrismS.IoDescent.main | (intros; apply GlobalTheory.PrismS.IoDescent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpStarOfLowTermsRemoved
section
noncomputable section

namespace GlobalTheory.ExpImage.LowTerms

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem oB_mem_zero {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) : oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem tD_pow_mem_zero (j : ℕ) : tD P ^ j ∈ FilB P 0 :=
  FilB_anti (by simp) (FilB_pow (tD_mem (P := P)) j)

theorem act_term (g : GQ l) (c : ℚ_[l]) {x : Om l} (hx : g x = x) (j : ℕ) :
    P.actQdR g (qB P c * (oB P x * tD P ^ j)) =
      qB P (c * (P.χQ g : ℚ_[l]) ^ j) * (oB P x * tD P ^ j) := by
  rw [map_mul, map_mul, map_pow, act_tD, P.actQdR_Om, hx, AlgEquiv.commutes, map_mul, map_pow,
    mul_pow]
  ring

theorem Ks_le_Kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun _ hx => Exists.intro s hx) _

theorem expStar_of_sum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  intro LT l _ AI T K s hs e g hg w hw b hb hH hN
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  obtain ⟨hn, -, hker⟩ := GlobalTheory.Cyc.cyc_basic l _ hχ
  obtain ⟨-, -, hint, hlog⟩ := GlobalTheory.PadicLogUnits.logZl_hom l
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set u : ℚ_[l] := ((LT l).χQ g : ℚ_[l]) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hL : logZl l u ≠ 0 := by
    rw [← norm_pos_iff, hlog s hs.1 hs.2 u hg.2.le, hg.2]
    exact zpow_pos hl _
  have hLc : ((logChi LT g : ℤ_[l]) : ℚ_[l]) = logZl l u :=
    congrArg Subtype.val (dif_pos (hint _ (hn g)))
  have hne : ∀ j ∈ Finset.range e, u ^ ((j : ℤ) - e) - 1 ≠ 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← norm_pos_iff, GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l s hs u hg.2 _ (by omega)]
    exact zpow_pos hl _
  set c : ℕ → ℚ_[l] := fun j => (u ^ ((j : ℤ) - e) - 1)⁻¹ with hc
  set S : (LT l).R.BdR :=
    ∑ j ∈ Finset.range e, qB (LT l) (c j) * (oB (LT l) (w j) * tD (LT l) ^ j) with hS
  have hS0 : S ∈ FilB (LT l) 0 :=
    Submodule.sum_mem _ fun j _ =>
      qB_mul_mem _ (FilB_zero_mul (oB_mem_zero T _) (tD_pow_mem_zero j))
  have hSH : ∀ h ∈ Hinf K, (LT l).actQdR h S = S := by
    intro h hh
    have h1 : (LT l).χQ h = 1 := (hker K h (Hinf_le_fix hh)).2.1 hh
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_term h _ (hh ⟨w j, Ks_le_Kinf K s (hw j)⟩), h1]
    simp
  have hSg : qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g S - S =
      ∑ j ∈ Finset.range e, oB (LT l) (w j) * tD (LT l) ^ j := by
    rw [hS, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [act_term g _ (hg.1 ⟨w j, hw j⟩), ← mul_assoc, ← map_mul, ← sub_mul, ← map_sub]
    have : (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (c j * u ^ j) - c j = 1 := by
      have h2 : u ^ ((j : ℤ) - e) = u ^ (-(e : ℤ)) * u ^ j := by
        rw [sub_eq_neg_add, zpow_add₀ hu0, zpow_natCast]
      have h3 : (u ^ ((j : ℤ) - e) - 1) * c j = 1 := mul_inv_cancel₀ (hne j hj)
      rw [Units.val_zpow_eq_zpow_val, ← hu]
      rw [h2] at h3
      linear_combination h3
    rw [this, map_one, one_mul]
  refine GlobalTheory.T.integral_cocycle_of_generator_and_fixing LT l AI T K s hs e g hg _
    (mul_mem (IntermediateField.algebraMap_mem _ _) (hw e)) (b + S) (add_mem hb hS0)
    (fun h hh => ?_) ?_
  · have := hH h hh
    rwa [map_add, hSH h hh, add_sub_add_right_eq_sub]
  · have h4 : qB (LT l) (logZl l u) * oB (LT l) (algebraMap ℚ_[l] (Om l) (logZl l u)⁻¹) = 1 := by
      rw [← IsScalarTower.algebraMap_apply, ← map_mul, mul_inv_cancel₀ hL, map_one]
    convert hN using 1
    rw [hLc, Finset.sum_range_succ, ← hSg, map_add, map_mul]
    linear_combination (oB (LT l) (w e) * tD (LT l) ^ e) * h4

end GlobalTheory.ExpImage.LowTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1ReductionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_reduction : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  first | exact @GlobalTheory.CocycleModPow.finite_H1Q_lpow | exact GlobalTheory.CocycleModPow.finite_H1Q_lpow | (intros; apply GlobalTheory.CocycleModPow.finite_H1Q_lpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one : ∀ (G : Type) [Group G] [Fintype G] , {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  first | exact @GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | exact GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one | (intros; apply GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one <;> assumption)
end

