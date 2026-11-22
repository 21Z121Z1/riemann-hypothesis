import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfLocalizationAway
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_away {A C A' C' : Type} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    (h : A →+* C) (k : A →+* A') (k' : C →+* C') (h' : A' →+* C') (e : k'.comp h = h'.comp k) (x : A)
    (H : letI := h.toAlgebra; IsLocalization.Away x C)
    (H' : letI := h'.toAlgebra; IsLocalization.Away (k x) C') :
    CategoryTheory.IsPushout (CommRingCat.ofHom h) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  letI : Algebra A C := h.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra C C' := k'.toAlgebra
  letI : Algebra A' C' := h'.toAlgebra
  letI : Algebra A C' := (h'.comp k).toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun e a).symm
  haveI : IsLocalization (Submonoid.powers x) C := H
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers x)) C' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact H'
  haveI : Algebra.IsPushout A A' C C' :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers x) C A' C'
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := C) (S := A') (S' := C')).2
    (Algebra.IsPushout.symm inferInstance)

theorem IsLoc.isUnit_of_complete {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} {s : B.A} {h : Hom B C}
    (H : IsLoc s h) : IsUnit (h.f s) := by
  have hu : IsUnit (qmap h 1 (Ideal.Quotient.mk (adI B ^ 1) s)) := by
    letI := (qmap h 1).toAlgebra
    haveI := H.away 1
    exact IsLocalization.Away.algebraMap_isUnit _
  rw [qmap_mk] at hu
  haveI := C.complete
  have hj : adI C ^ 1 ≤ (⊥ : Ideal C.A).jacobson := by
    rw [pow_one]
    exact IsAdicComplete.le_jacobson_bot _
  haveI := isLocalHom_of_le_jacobson_bot _ hj
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hu

theorem stable_of_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (s : B.A) (h : Hom B C),
    (∃ t ∈ B.I, ∀ x ∈ B.I, ∃ k : ℕ, s ^ k * x ∈ Ideal.span {t}) → IsLoc s h → Stable h := by
  rintro l _ R _ B C s h ⟨t, ht, hst⟩ H
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · letI := (qmap h m).toAlgebra
    haveI := H.away m
    exact IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (adI B ^ m) s))
  ·
    have hgen : GenAway B' (k.f s) (k.f t) := by
      refine ⟨k.f_I t ht, fun x hx => ?_⟩
      rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R B B' k] at hx
      have hx' : x ∈ Ideal.span (k.f '' B.I) := hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ n : ℕ, k.f s ^ n * x ∈ Ideal.span {k.f t}) ?_ ?_ ?_ ?_ hx'
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨n, hn⟩ := hst y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
        refine ⟨n, Ideal.mem_span_singleton'.2 ⟨k.f c, ?_⟩⟩
        simpa only [map_mul, map_pow] using congrArg k.f hc
      · exact ⟨0, by simp⟩
      · rintro a b _ _ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
        refine ⟨n₁ + n₂, ?_⟩
        have hab : k.f s ^ (n₁ + n₂) * (a + b) =
            k.f s ^ n₂ * (k.f s ^ n₁ * a) + k.f s ^ n₁ * (k.f s ^ n₂ * b) := by ring
        rw [hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
      · rintro a b _ ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hn
    obtain ⟨C', h', hloc', -⟩ := GlobalTheory.T.exists_isPrismLocalizationAway_of_generated l R B' (k.f s) (k.f t) hgen
    obtain ⟨k', hk'⟩ := H.univ C' (h'.comp k)
      (show IsUnit (h'.f (k.f s)) from IsLoc.isUnit_of_complete hloc')
    refine ⟨C', k', h', hk', fun m => ?_⟩
    refine isPushout_of_away (qmap h m) (qmap k m) (qmap k' m) (qmap h' m) ?_
      (Ideal.Quotient.mk _ s) (H.away m) ?_
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, qmap_mk]
      exact congrArg (fun g : Hom B C' => Ideal.Quotient.mk (adI C' ^ m) (g.f a)) hk'
    · rw [qmap_mk]
      exact hloc'.away m

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiscBasisCrystallineLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem height_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_radius_pos_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturatedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_saturated' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) → IsUnit Y := by
  first | exact @GlobalTheory.SatInvUnit.isUnit_of_saturated | exact GlobalTheory.SatInvUnit.isUnit_of_saturated | (intros; apply GlobalTheory.SatInvUnit.isUnit_of_saturated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittaker
section
open NumberField Matrix GlobalTheory.CuspRep

noncomputable section

open MeasureTheory GroundTheory.Automorphic.FourierWhittaker

namespace GlobalTheory.CuspGeneric.WhitEq

theorem avg_eq_setIntegral {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [m : MeasurableSpace G] [hB : BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (D : Set G)
    (hD : IsAddFundamentalDomain Γ D μ) (h1 : μ D = 1) (Φ : G → ℂ)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    avg Γ Φ = ∫ x in D, Φ x ∂μ := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  have hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 :=
    ⟨(μ, D), inferInstance, hD, h1⟩
  unfold avg
  rw [dif_pos hex]
  obtain ⟨hH, hD', h1'⟩ := hex.choose_spec
  set ν := hex.choose.1
  set D' := hex.choose.2
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc0 : Measure.addHaarScalarFactor ν μ ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hν, h0, zero_smul]
    have hpos : 0 < ν Set.univ := IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩
    rw [this] at hpos
    simp at hpos
  have hac : μ ≪ ν := by
    rw [hν]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have hDμ : IsAddFundamentalDomain Γ D' μ := hD'.mono hac
  have hμD' : μ D' = 1 := by rw [hDμ.measure_eq hD, h1]
  have hc1 : Measure.addHaarScalarFactor ν μ = 1 := by
    have := h1'
    rw [hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hνμ : ν = μ := by rw [hν, hc1, one_smul]
  rw [hνμ]
  exact hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x

def colIx {a k : ℕ} (hk : k < a) : UnipotentBlockColumnIndex a k k ≃ Fin k where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show k = (j : ℕ)
      simp only at h2 h3
      omega
  right_inv i := rfl

theorem blkU_eq_colGL {R : Type} [CommRing R] {a k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) = colGL (n := a) k (fun i => x ((colIx hk).symm i)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j
  rw [uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]
  by_cases hij : (i : ℕ) < k ∧ (j : ℕ) = k
  · have hne : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := by rw [Fin.lt_def]; omega
    rw [Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]
    · rw [if_neg hne, if_neg hne, dif_pos hlt, colX_apply, dif_pos hij.2, Matrix.single_apply_same, zero_add]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        show (j : ℕ) = k
        exact hij.2
    · intro t _ ht
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [add_zero]
      split_ifs with h1 h2
      · rfl
      · rw [colX_apply, dif_neg]
        intro h3
        exact hij ⟨by rw [← h3]; exact h2, h3⟩
      · rfl
    · intro t _
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      apply hij
      have := t.2
      rw [← h1, ← h2]
      omega

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem dot_eLast {k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) x = pair (lastVec k) (fun i => x ((colIx hk).symm i)) := by
  unfold dot pair
  refine Fintype.sum_equiv (colIx hk) _ _ fun t => ?_
  dsimp only
  rw [Equiv.symm_apply_apply]
  rfl

theorem colT_eq_stepCoeff {k : ℕ} (hk : k < a) (f : GA E a → ℂ)
    (hf : ∀ (ξ : Fin k → E) g, f (ratGL E a (colGL k ξ) * g) = f g) (g : GA E a) :
    colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) k f g = stepCoeff k f g := by
  set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)
  have hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ) := fun y => rfl
  set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef
  have hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x := by
    rintro _ ⟨c, rfl⟩ x
    have e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e1]
    have hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g) := by
      change f (posU _ _ * g) = _
      rw [posU_add, mul_assoc]
      change f (blkU _ * _) = _
      rw [← ratGL_blkU, blkU_eq_colGL hk, hf]
      rfl
    have hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) =
        algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
    simp only [Φ]
    rw [hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg,
      GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice
  have hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k) :=
    avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k))
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ
  change avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _
  rw [hA]
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [Φ, hEx, hψ]
  rw [blkU_eq_colGL hk, dot_eLast hk, mul_comm]

theorem whit_partialCoeff (F : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) :
    ∀ m, m + 1 ≤ a → whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) m (partialCoeff F (m + 1)) =
      partialCoeff F 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hk : m + 1 < a := by omega
    rw [whit_succ]
    have hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) =
        partialCoeff F (m + 1) := by
      funext g
      rw [colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g),
        partialCoeff_of_lt F hk]
    rw [hcol]
    exact ih (by omega)

theorem whit_eq_whittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F →
    (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) →
    GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  intro E _ _ a F ha hc hl
  have h := whit_partialCoeff F hl (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha, partialCoeff_self] at h
  rw [h]
  funext g
  exact (whittaker_eq_partialCoeff hc ha g).symm

end GlobalTheory.CuspGeneric.WhitEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilTStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jB_single_mem_filT' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  first | exact @GlobalTheory.BKGal.XiPole.jB_single_mem_filT | exact GlobalTheory.BKGal.XiPole.jB_single_mem_filT | (intros; apply GlobalTheory.BKGal.XiPole.jB_single_mem_filT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kisinInfGalois_acts_through_descentDatum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (Δ : Descent P), IsCrisCmp I jB → IsGalDesc (sQ l) I Δ → ∀ (g : Gl l) (γ : TameGal K l e a), Covers K t ϖ (sQ l g) γ → ∀ σ σ' : P.MMl, σ'.1 = Δ.act γ σ.1 → actB (sQ l) T g (jB (toBcris t ϖ P σ)) = jB (toBcris t ϖ P σ') := by
  first | exact @GlobalTheory.TameAct.main | exact GlobalTheory.TameAct.main | (intros; apply GlobalTheory.TameAct.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  first | exact @GlobalTheory.DeRhamIdent.main | exact GlobalTheory.DeRhamIdent.main | (intros; apply GlobalTheory.DeRhamIdent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProofStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCountDualLifting_proof : StepLocDual := by
  first | exact @GlobalTheory.Pass.LocDual.main | exact GlobalTheory.Pass.LocDual.main | (intros; apply GlobalTheory.Pass.LocDual.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotent
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequence
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

theorem GlobalTheory.PZ.ltData_read_OC : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ (hπ : Irreducible π) (hF : IsLubinTateSeries π (ltSeries K π)) (v : ℕ → OC l), v 0 = 0 ∧ v 1 ≠ 0 ∧
      (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) ∧
      ∀ g : ↥(GK K), ∃ a : ↥(OL K), (a : ↥K.1) = (χ g : ↥K.1) ∧ ∀ n,
        HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF a).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  intro l _ K χ π z h
  haveI : Finite (IsLocalRing.ResidueField ↥(OL K)) :=
    Nat.finite_of_card_ne_zero (by rw [GlobalTheory.AinfK.card_res K]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have hrel := h.2.2.2.1
  obtain ⟨hπ, hF, v, hv, -, h0, h1, hg⟩ := GlobalTheory.PZ.ltData_tilt_hyps l K χ π z h
  refine ⟨hπ, hF, v, h0, h1, fun n => ?_, fun g => ?_⟩
  · apply Subtype.ext
    have e := congrArg (algebraMap (Om l) ℂ_[l]) (hrel n)
    rw [map_add, map_mul, map_pow, ← hv, ← hv] at e
    have hq : resCard K = l ^ fK K := rfl
    rw [← hq]
    exact e
  · obtain ⟨a, ha, -⟩ := h.2.2.2.2 g
    exact ⟨a, ha, hg g a ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubinTateTwistTotalWeightZero_proof : TwistStep := by
  first | exact @GlobalTheory.PMon.twistStep | exact GlobalTheory.PMon.twistStep | (intros; apply GlobalTheory.PMon.twistStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeedCoeffRecurrenceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seed_coeff_recurrence_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  first | exact @GlobalTheory.BSP.seed_coeff_recurrence | exact GlobalTheory.BSP.seed_coeff_recurrence | (intros; apply GlobalTheory.BSP.seed_coeff_recurrence <;> assumption)
end

