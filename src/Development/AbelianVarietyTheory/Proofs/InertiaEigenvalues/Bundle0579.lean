import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frame_coord_cancel {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ}
    (b : Module.Basis (Fin d) B N) {t p q : B} (ht : t ∈ nonZeroDivisors B) {m : N} {k r s : ℕ}
    {v w : Fin d → B} (h1 : t ^ r • (p • m - t ^ k • ∑ i, v i • b i) = 0)
    (h2 : t ^ s • (q • m - t ^ k • ∑ i, w i • b i) = 0) (i : Fin d) : p * w i = q * v i := by
  have e1 := congrArg (fun x => b.equivFun x i) h1
  have e2 := congrArg (fun x => b.equivFun x i) h2
  simp only [← b.equivFun_symm_apply, map_smul, map_sub, LinearEquiv.apply_symm_apply, map_zero,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
  have f1 := (mem_nonZeroDivisors_iff.1 (pow_mem ht r)).1 _ e1
  have f2 := (mem_nonZeroDivisors_iff.1 (pow_mem ht s)).1 _ e2
  rw [← sub_eq_zero]
  apply (mem_nonZeroDivisors_iff.1 (pow_mem ht k)).1
  linear_combination q * f1 - p * f2

theorem frame_sum_single {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (v : Fin d → N)
    (j : Fin d) : ∑ i, (Pi.single j 1 : Fin d → B) i • v i = v j := by
  simp [Pi.single_apply]

theorem frame_sum_mulVec {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (φ : B →+* B)
    (A ε : Matrix (Fin d) (Fin d) B) (v c : Fin d → N) (h : ∀ x, v x = ∑ i, ε i x • c i) (j : Fin d) :
    ∑ i, A.mulVec (fun x => φ ((Pi.single j 1 : Fin d → B) x)) i • v i = ∑ i, (ε * A) i j • c i := by
  have h2 : (fun x => φ ((Pi.single j 1 : Fin d → B) x)) = Pi.single j 1 := by
    ext x
    by_cases hx : x = j <;> simp [hx]
  simp only [h2, Matrix.mulVec_single_one, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, mul_comm]
  rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem frame_matrix_φ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ)
    (A : Matrix (Fin d) (Fin d) bk.S)
    (hΦ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
      (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a)
    {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (c : Module.Basis (Fin d) B.A (M.M B))
    (hc : ∀ i, c i = M.tr f (e i)) (ε : Matrix (Fin d) (Fin d) B.A)
    (htr : ∀ j, M.tr g (e j) = ∑ i, ε i j • M.tr f (e i)) :
    BK.hf g bk.E ^ a • (A.map (BK.hf f) * ε.map B.D.φ) = BK.hf f bk.E ^ a • (ε * A.map (BK.hf g)) := by
  obtain ⟨hI, ht⟩ := GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk B f
  let t : ↥B.I := ⟨BK.hf f bk.E, hI.ge (Ideal.mem_span_singleton_self _)⟩
  ext i j
  obtain ⟨m, k, hm⟩ := exists_isFrac (t : B.A) (M.Φ B t (M.tr g (e j)))
  obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B g t (Pi.single j 1) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k)
      (frame_sum_single (fun i => M.tr g (e i)) j).symm hm)
  obtain ⟨s, hs⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B f t (fun i => ε i j) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (htr j) hm)
  have h1 := frame_sum_mulVec B.D.φ (A.map (BK.hf g)) ε (fun i => M.tr g (e i)) c
    (fun x => (htr x).trans (Finset.sum_congr rfl fun i _ => congrArg (fun z => ε i x • z) (hc i).symm)) j
  rw [h1] at hr
  simp only [← hc] at hs
  exact frame_coord_cancel c ht hr hs i

theorem exists_frame_matrices (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :
    ∃ ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A,
      (∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, ε f g i j • M.tr f (e i)) ∧
      (∀ {B} (f : Hom bk.prism B), ε f f = 1) ∧
      (∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h) ∧
      (∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)) := by
  have hb : ∀ {B : Obj l ↥(OL K)} (f : Hom bk.prism B), ∃ c : Module.Basis (Fin d) B.A (M.M B),
      ∀ i, c i = M.tr f (e i) := fun f => GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  choose c hc using @hb
  have htr : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d),
      M.tr g (e j) = ∑ i, (c f).toMatrix (c g) i j • M.tr f (e i) := fun f g j => by
    rw [← hc, ← (c f).sum_toMatrix_smul_self (c g) j]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  have huniq : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d) (v : Fin d → B.A),
      M.tr g (e j) = ∑ i, v i • M.tr f (e i) → ∀ i, (c f).toMatrix (c g) i j = v i := fun f g j v h i => by
    change (c f).repr (c g j) i = v i
    rw [hc, h]
    simp only [← hc]
    rw [← (c f).equivFun_symm_apply, ← (c f).equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun f g => (c f).toMatrix (c g), htr, fun f => (c f).toMatrix_self,
    fun f g h => (c f).toMatrix_mul_toMatrix (c g) (c h), fun k f g => ?_⟩
  ext i j
  refine (huniq (k.comp f) (k.comp g) j (fun i => k.f ((c f).toMatrix (c g) i j)) ?_ i).symm
  refine (M.tr_comp k g (e j)).trans ((congrArg (M.tr k) (htr f g j)).trans ?_)
  refine (map_sum (M.tr k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact ((M.tr k).map_smulₛₗ _ _).trans
    (congrArg (fun z => k.f ((c f).toMatrix (c g) i j) • z) (M.tr_comp k f (e i)).symm)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)) :
    ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  have : IsLocalRing bk.prism.A := inferInstanceAs (IsLocalRing (Wq l bk.a)⟦X⟧)
  have := M.fin bk.prism
  have := M.proj bk.prism
  have : Module.Free bk.prism.A (M.M bk.prism) := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, ⟨e⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :=
    ⟨_, ⟨Module.finBasis bk.prism.A (M.M bk.prism)⟩⟩
  obtain ⟨a, b, A, A', hA, hΦ⟩ := GlobalTheory.T.exists_frobenius_matrix_fCrystal_breuilKisin l K bk d M e
  obtain ⟨ε, htr, h1, h2, h3⟩ := exists_frame_matrices M e
  refine ⟨d, ⟨a, b, A, A', hA, ε, h1, h2, h3, fun f g => ?_⟩, e, htr, hΦ⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  exact frame_matrix_φ M e a A hΦ f g c hc (ε f g) (htr f g)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProof
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
theorem GlobalTheory.PMon.exI_of_ser_core (hser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y) (hcore : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Formalism.Per.Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0) : ExI := by
  intro l _ P AI T h hh μ hμ hne
  obtain ⟨S, θ, hS, hker, hq, hb⟩ := hser l P AI T
  let μ' : Fin h → ℂ_[l] := fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩
  have hμ' : μ' ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    exact hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))
  obtain ⟨y, hy, hz, hind⟩ := hcore l h μ' hh hμ'
  choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)
  choose hm hev using hev
  choose hq0 hq using hq
  refine ⟨b, hplus, hφ, ?_, fun a => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have : c = 0 := by
      refine hind c fun j _ => ?_
      have e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x) := fun x => by
        simp only [ev, AlgHom.coe_pow]
      have h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0 := by
        apply Subtype.ext
        have := congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc
        simp only [map_sum, map_smul, map_zero] at this
        simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, e, ZeroMemClass.coe_zero]
        simpa only [Algebra.smul_def] using this
      have h2 := congrArg θ h1
      rw [map_sum, map_zero] at h2
      simpa only [map_mul, hq, hev] using h2
    exact fun i => congrFun this i
  · have h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0 := by
      rw [map_sum]
      simpa only [map_mul, hev] using hz a
    have := (hker _).1 h2
    simpa only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul] using this

theorem GlobalTheory.PMon.exI_main : ExI := GlobalTheory.PMon.exI_of_ser_core GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGenerated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem adI_pow_eq_map_of_map_I {B C : Obj l R} (h : Hom B C) (hI : B.I.map h.f = C.I) (m : ℕ) :
    adI C ^ m = (adI B ^ m).map h.f := by
  rw [Ideal.map_pow]
  congr 1
  simp only [adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem isLoc_of_locP (hrig : ∀ (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I)
    {B : Obj l R} {s d : B.A} (L : LocP B s d) : IsLoc s L.inl := by
  have hJ : ∀ m, adI L.Q ^ m = (adI B ^ m).map L.inl.f :=
    adI_pow_eq_map_of_map_I L.inl (hrig _ _ _)
  refine ⟨fun m => ?_, fun Q a ha => ?_⟩
  · letI := (qmap L.inl m).toAlgebra
    have hmap : ∀ b : B.A, algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (L.inl.f b) := fun b => rfl
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, k, rfl⟩
      change IsUnit (algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ s ^ k))
      rw [map_pow, hmap]
      exact (L.unit.map _).pow k
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨k, b, hkb⟩ := L.surj c m
      refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ c * algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m)
        (Ideal.Quotient.mk _ s ^ k) = algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b)
      rw [map_pow, hmap, hmap, ← map_pow, ← map_mul, Ideal.Quotient.eq, hJ, mul_comm]
      exact hkb
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hmap, hmap, Ideal.Quotient.eq, hJ, ← map_sub] at hxy
      obtain ⟨k, hk⟩ := L.ker (a - b) m hxy
      refine ⟨⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ b
      rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
      exact hk
  · obtain ⟨c, hc, -⟩ := L.univ Q a ha
    exact ⟨c, hc⟩

theorem exists_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d →
    ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  intro l _ R _ B s d hg
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_completedLocalizationPrism l R B s d hg
  exact ⟨L.Q, L.inl, isLoc_of_locP (GlobalTheory.T.prism_hom_map_ideal_eq l R) L, L.I_eq⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelVectorMemOEOfFrobeniusStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  first | exact @GlobalTheory.BSP.exists_ker_vector_mem_OE | exact GlobalTheory.BSP.exists_ker_vector_mem_OE | (intros; apply GlobalTheory.BSP.exists_ker_vector_mem_OE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubinTate_character_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  first | exact @GlobalTheory.LTChar.main | exact GlobalTheory.LTChar.main | (intros; apply GlobalTheory.LTChar.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_frobVector_residue_zero : ExII := by
  first | exact @GlobalTheory.PMonII.exII | exact GlobalTheory.PMonII.exII | (intros; apply GlobalTheory.PMonII.exII <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.CoeffIdeal

theorem principal_of_saturated {S k : Type} [CommRing S] [IsNoetherianRing S] [CommRing k]
    [IsPrincipalIdealRing k] (π : S →+* k) (hπ : Function.Surjective π) (p : S)
    (hker : ∀ x, π x = 0 → p ∣ x) (hp : Ideal.span {p} ≤ Ideal.jacobson ⊥) (P : Ideal S)
    (hP : ∀ x, p * x ∈ P → x ∈ P) : ∃ g, P = Ideal.span {g} := by
  obtain ⟨g', hg'⟩ := (IsPrincipalIdealRing.principal (P.map π)).principal
  have h0 : g' ∈ P.map π := by rw [hg']; exact Submodule.mem_span_singleton_self _
  obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 h0
  refine ⟨g, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hg)⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian P) hp fun x hx => ?_
  have h1 : π x ∈ P.map π := Ideal.mem_map_of_mem π hx
  rw [hg'] at h1
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨c, rfl⟩ := hπ c'
  obtain ⟨y, hy⟩ := hker (x - c * g) (by rw [map_sub, map_mul, ← hc', smul_eq_mul, sub_self])
  have hyP : y ∈ P := hP y (hy ▸ P.sub_mem hx (P.mul_mem_left c hg))
  have e : x = c * g + p • y := by rw [smul_eq_mul, ← hy]; ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self g))
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self p) hyP)

theorem c_frob_mem {S A : Type} [CommRing S] [IsNoetherianRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (hI : I ≤ Ideal.jacobson ⊥) (φ : S →+* S) (Φ : A →+* A)
    (hφ : ∀ a, s (φ a) = Φ (s a)) (hφI : I.map φ ≤ I) (x : A) (N : Ideal S) (hN : ∀ i, φ (TB.c i x) ∈ N)
    (j : ι) : TB.c j (Φ x) ∈ N := by
  have hH : IsHausdorff I (S ⧸ N) := IsHausdorff.of_le_jacobson _ _ hI
  refine Ideal.Quotient.eq_zero_iff_mem.1 (hH.haus _ fun n => ?_)
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by simpa using hi
  have h1 := Ideal.mem_map_of_mem Φ (TB.approx x n _ hF)
  have e : Φ.comp s = s.comp φ := RingHom.ext fun a => (hφ a).symm
  rw [Ideal.map_map, e, ← Ideal.map_map, Ideal.map_pow] at h1
  have h2 := TB.c_mem_of_mem_map _ _ (Ideal.map_mono (Ideal.pow_right_mono hφI n) h1) j
  rw [map_sub, map_sub, map_sum, map_sum] at h2
  have h3 : ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i)) ∈ N :=
    N.sum_mem fun i _ => by
      rw [map_mul, ← hφ, TB.c_mul]
      exact N.mul_mem_right _ (hN i)
  have h4 : Ideal.Quotient.mk N (TB.c j (Φ x)) =
      (TB.c j (Φ x) - ∑ i ∈ (TB.fin x n).toFinset, TB.c j (Φ (s (TB.c i x) * TB.b i))) • (1 : S ⧸ N) := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simpa using h3
  rw [SModEq.zero, h4]
  exact Submodule.smul_mem_smul h2 Submodule.mem_top

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

theorem prime_l : Prime (l : (Wq l a)⟦X⟧) := by
  have key : ∀ x : (Wq l a)⟦X⟧, (l : (Wq l a)⟦X⟧) ∣ x →
      PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l a)) x = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [map_mul, map_natCast, l_eq_zero, zero_mul]
  refine ⟨l_ne_zero l a, fun h => ?_, fun x y h => ?_⟩
  · have := key 1 h.dvd
    rw [map_one] at this
    exact one_ne_zero this
  · have := key _ h
    rw [map_mul] at this
    exact (mul_eq_zero.1 this).imp (dvd_of_map_eq_zero l a x) (dvd_of_map_eq_zero l a y)

theorem ne_zero_of_isPer {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := h
  rw [map_zero, eq_comm, Units.mul_right_eq_zero, sub_eq_zero] at h
  have h1 : ε = 1 := by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simpa using this
  exact hδ1 (by rw [h1, map_one, map_one])

end GlobalTheory.BSP.CoeffIdeal

open GlobalTheory.BSP.CoeffIdeal in

theorem GlobalTheory.BSP.pow_l_mem_span_coeff : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (M : ℕ), ∃ r : ℕ, (l : bk.S) ^ r ∈ Ideal.span (Set.range fun i => TB.c i (τ ^ M)) := by
  intro l _ K bk τ hτ ι TB M
  set I : Ideal bk.S := Ideal.span (Set.range fun i => TB.c i (τ ^ M)) with hI
  have hJ : bk.J ≤ Ideal.jacobson ⊥ := by
    have := bk.complete
    exact IsAdicComplete.le_jacobson_bot _
  have hpr := prime_l l bk.a
  let P : Ideal bk.S :=
    { carrier := {x | ∃ r : ℕ, (l : bk.S) ^ r * x ∈ I}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨t, ht⟩
        refine ⟨r + t, ?_⟩
        have := I.add_mem (I.mul_mem_left ((l : bk.S) ^ t) hr) (I.mul_mem_left ((l : bk.S) ^ r) ht)
        convert this using 1
        ring
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        refine ⟨r, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact I.mul_mem_left c hr }
  have hsat : ∀ x, (l : bk.S) * x ∈ P → x ∈ P := by
    rintro x ⟨r, hr⟩
    exact ⟨r + 1, by rwa [pow_succ, mul_assoc]⟩
  have hIP : I ≤ P := fun x hx => ⟨0, by simpa using hx⟩
  obtain ⟨g, hg⟩ := principal_of_saturated
    (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)))
    (PowerSeries.map_surjective _ (WittVector.constantCoeff_surjective l)) (l : bk.S)
    (dvd_of_map_eq_zero l bk.a) (le_sup_left.trans hJ) P hsat
  have hgP : g ∈ P := by rw [hg]; exact Ideal.mem_span_singleton_self g
  have hdvd : ∀ i, g ∣ TB.c i (τ ^ M) := fun i => by
    rw [← Ideal.mem_span_singleton, ← hg]
    exact hIP (Ideal.subset_span ⟨i, rfl⟩)
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact pow_ne_zero M (ne_zero_of_isPer l bk hτ) (TB.eq_zero_of_c _ fun i => zero_dvd_iff.1 (hdvd i))
  have hlg : ¬ (l : bk.S) ∣ g := by
    rintro ⟨y, hy⟩
    have h1 : y ∈ P := hsat y (hy ▸ hgP)
    rw [hg, Ideal.mem_span_singleton] at h1
    obtain ⟨z, hz⟩ := h1
    refine hpr.not_unit (IsUnit.of_mul_eq_one z (mul_left_cancel₀ hg0 ?_))
    rw [mul_one]
    conv_rhs => rw [hy, hz]
    ring
  have hφJ : bk.J.map (frobS l bk.a) ≤ bk.J := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    obtain ⟨b, hb⟩ := frobS_eq l bk.a bk.E
    rw [hb, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Fact.out : l.Prime).pos)
  have hE : ∀ j, frobS l bk.a g ∣ bk.E ^ M * TB.c j (τ ^ M) := fun j => by
    have := c_frob_mem TB hJ (frobS l bk.a) WittVector.frobenius bk.ev_frob hφJ (τ ^ M)
      (Ideal.span {frobS l bk.a g}) (fun i => Ideal.mem_span_singleton.2 (map_dvd _ (hdvd i))) j
    rwa [map_pow, hτ.1, mul_pow, ← map_pow, TB.c_mul, Ideal.mem_span_singleton] at this
  have hEI : ∀ x ∈ I, frobS l bk.a g ∣ bk.E ^ M * x := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hE i
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left c
  obtain ⟨r, hr⟩ := hgP
  have hlφ : ¬ (l : bk.S) ∣ frobS l bk.a g := by
    obtain ⟨b, hb⟩ := frobS_eq l bk.a g
    rw [hb]
    intro h
    exact hlg (hpr.dvd_of_dvd_pow ((dvd_add_left (dvd_mul_right _ b)).1 h))
  have hfin : frobS l bk.a g ∣ bk.E ^ M * g := by
    obtain ⟨z, hz⟩ := hEI _ hr
    obtain ⟨w, hw⟩ : (l : bk.S) ^ r ∣ z :=
      hpr.pow_dvd_of_dvd_mul_left r hlφ ⟨bk.E ^ M * g, by rw [← hz]; ring⟩
    refine ⟨w, mul_left_cancel₀ (pow_ne_zero r hpr.ne_zero) ?_⟩
    rw [mul_left_comm, hz, hw]
    ring
  have hu := GlobalTheory.T.isUnit_of_frobenius_dvd_eisenstein_pow_mul l K bk g hlg M hfin
  exact ⟨r, (I.mul_unit_mem_iff_mem hu).1 hr⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulusStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveRoot_in_rayClassField_natModulus : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) → ∃ ζ : H, IsPrimitiveRoot ζ n := by
  first | exact @GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | exact GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay | (intros; apply GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => GlobalTheory.T.coker_finite_length_of_primitive_divisor O K l e a ι κ P Q F hyp ?_, fun hyp => GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_H1_dual_pair : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  first | exact @GlobalTheory.EulerCharH1.finite_and_finrank_H1V | exact GlobalTheory.EulerCharH1.finite_and_finrank_H1V | (intros; apply GlobalTheory.EulerCharH1.finite_and_finrank_H1V <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteFieldStatement
section
open Matrix Formalism.IndefR.Datum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_flat_character_datum_finiteField : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  first | exact @GlobalTheory.fourier_flatDatum_finite | exact GlobalTheory.fourier_flatDatum_finite | (intros; apply GlobalTheory.fourier_flatDatum_finite <;> assumption)
end

