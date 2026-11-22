import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecay

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmooth
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SmChart

open MvPolynomial

noncomputable def subst {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) O :=
  Fin.cases (C ϖ) (fun j => X j) i

@[simp] theorem subst_zero {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : subst ϖ n 0 = C ϖ := rfl
@[simp] theorem subst_succ {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (j : Fin n) : subst ϖ n j.succ = X j := rfl

theorem prod_lt_one {O : Type} [CommRing O] (n : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (X i : MvPolynomial (Fin (n + 1)) O)) = X 0 := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by simpa using h)
    · rintro rfl; simp
  rw [this, Finset.prod_singleton]

noncomputable abbrev gen {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {X 0 - C ϖ}

theorem subst_vanish {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ a ∈ gen ϖ n, (aeval (subst ϖ n)).toRingHom a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, aeval_C, subst_zero,
    algebraMap_eq, sub_self, mul_zero]

noncomputable def quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (aeval (subst ϖ n)).toRingHom (subst_vanish ϖ n)

noncomputable def quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) :=
  (Ideal.Quotient.mk _).comp (rename Fin.succ).toRingHom

theorem quotMap_mk {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (a : MvPolynomial (Fin (n + 1)) O) :
    quotMap ϖ n (Ideal.Quotient.mk _ a) = aeval (subst ϖ n) a := rfl

theorem quotMap_quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (quotInv ϖ n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    simp [quotInv, quotMap_mk]

theorem quotInv_quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotInv ϖ n).comp (quotMap ϖ n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, quotMap_mk, aeval_X, subst_zero, RingHom.id_apply]
      simp only [quotInv, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_C]
      rw [Ideal.Quotient.eq]
      rw [← neg_sub]; exact neg_mem (Ideal.subset_span rfl)
    · simp [quotInv, quotMap_mk]

theorem quotMap_bijective {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Function.Bijective (quotMap ϖ n) :=
  ⟨Function.LeftInverse.injective (g := quotInv ϖ n) (fun a => congr($(quotInv_quotMap ϖ n) a)),
    Function.RightInverse.surjective (g := quotInv ϖ n) (fun a => congr($(quotMap_quotInv ϖ n) a))⟩

theorem quotMap_algebraMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (algebraMap O _) = C := by
  refine RingHom.ext fun c => ?_
  change quotMap ϖ n (Ideal.Quotient.mk _ (C c)) = C c
  rw [quotMap_mk, aeval_C, algebraMap_eq]

end GlobalTheory.SmChart

open GlobalTheory.SmChart in

theorem GlobalTheory.SSG.chartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) →
    GlobalTheory.SSG.ChartAt ϖ p x := by
  intro O _ ϖ X p V x hx hsm
  set f := V.ι ≫ p with hf
  let x' : V.toScheme := ⟨x, hx⟩
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x')
  have hW : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hφ : (f.appLE ⊤ W e).hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hW e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hφ
  obtain ⟨s, hs, hfs⟩ := hφ
  have hs' := iSup_basicOpen_of_span_eq_top W (s : Set Γ(V.toScheme, W)) hs
  have hmem : x' ∈ (⨆ i ∈ (s : Set Γ(V.toScheme, W)), V.toScheme.basicOpen i) := hs'.symm ▸ hxW
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x' ∈ V.toScheme.basicOpen r := by simpa using hmem
  have hW' : IsAffineOpen (V.toScheme.basicOpen r) := hW.basicOpen r
  have e' : V.toScheme.basicOpen r ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  haveI : IsLocalization.Away r Γ(V.toScheme, V.toScheme.basicOpen r) := hW.isLocalization_basicOpen r
  have hst : (f.appLE ⊤ _ e').hom.IsStandardSmooth := by
    rw [← f.appLE_map e (homOfLE (V.toScheme.basicOpen_le r)).op]
    exact hfs r hr _
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  let c : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hc : Function.Bijective c := (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let k := V.ι.appIso (V.toScheme.basicOpen r)
  have hk : Function.Bijective k.inv.hom := k.symm.commRingCatIsoToRingEquiv.bijective
  have hU : IsAffineOpen (V.ι ''ᵁ V.toScheme.basicOpen r) := hW'.image_of_isOpenImmersion V.ι
  have hxU : x ∈ V.ι ''ᵁ V.toScheme.basicOpen r := ⟨x', hxr, rfl⟩
  have hcomp : p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top ≫ k.hom = f.appLE ⊤ _ e' := by
    have h1 := Scheme.Hom.appLE_comp_appLE V.ι p ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) (V.toScheme.basicOpen r)
      le_top (V.ι.preimage_image_eq _).ge
    have h2 : k.hom = V.ι.appLE _ _ (V.ι.preimage_image_eq _).ge := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]; rfl
    rw [h2]; exact h1
  refine ⟨_, hU, hxU, n + 1, 1, le_rfl, by omega, ?_⟩
  rw [prod_lt_one]
  refine ⟨k.inv.hom.comp (g.comp ((MvPolynomial.map c).comp (quotMap ϖ n))), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (quotMap_bijective ϖ n))
          (RingHom.Etale.of_bijective ⟨MvPolynomial.map_injective _ hc.1, MvPolynomial.map_surjective _ hc.2⟩))
        hg) (RingHom.Etale.of_bijective hk)
  · refine RingHom.ext fun a => ?_
    change k.inv.hom (g (MvPolynomial.map c (quotMap ϖ n (algebraMap O _ a)))) =
      (p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top).hom (c a)
    rw [show quotMap ϖ n (algebraMap O _ a) = MvPolynomial.C a from congr($(quotMap_algebraMap ϖ n) a),
      MvPolynomial.map_C, show g (MvPolynomial.C (c a)) = (f.appLE ⊤ _ e').hom (c a) from congr($hgC (c a)),
      ← hcomp]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassPStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | exact GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOnStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinConstantTermPart_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.aPart_differentiableOn | exact GlobalTheory.HeckeTwo.aPart_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.aPart_differentiableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnit
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoUnit

theorem phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]
  ring

theorem abs_mul_inv_sq {l : ℝ} (hl : l ≠ 0) :
    ((|l| : ℝ) : ℂ) * (l : ℂ)⁻¹ ^ 2 = ((|l| : ℝ) : ℂ)⁻¹ := by
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hl
  have h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [inv_pow, h2]; field_simp

theorem hTrans_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (ν y : ℝ) :
    hTrans σ ν (l * y) = ((|l| : ℝ) : ℂ) ^ (-1 - 2 * σ) * hTrans σ (l * ν) y := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l
  unfold hTrans
  rw [← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]
  have habs : |l⁻¹| = |l|⁻¹ := abs_inv l
  have hpos : 0 < |l| := abs_pos.2 hl
  have e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) =
      |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) := by
    rw [key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [e1]
  have e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) =
      ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t
    rw [show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring,
      phi_smul σ hl]
    push_cast; ring_nf
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    abs_mul_inv_sq hl]
  congr 1
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem prod_abs_unit_cpow {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ε : (𝓞 F)ˣ) (s : ℂ) :
    ∏ τ : Emb F, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = 1 := by
  have hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s =
      ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
  rw [hprod]
  have h := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)
  rw [← Complex.ofReal_prod] at h
  have hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
    have := Units.norm F ε
    exact_mod_cast this
  rw [← h, hn, Complex.ofReal_one, Complex.one_cpow]

theorem fTerm_unit_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F)
    (ε : (𝓞 F)ˣ) :
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  have hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0 := fun τ h => by
    have hu : ((ε : 𝓞 F) : F) ≠ 0 := by
      intro h0; have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact hu ((map_eq_zero τ).1 h)
  unfold fTerm
  have e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) =
      ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ b * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ (((ε : 𝓞 F) : F) * ν)) (τ b * (z τ).im)) := by
    intro τ
    rw [map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]
    rw [show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem fTerm_unit_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) :=
  fun _ _ _ _ σ z b ν ε => fTerm_unit_mul σ z b ν ε

end GlobalTheory.HeckeTwoUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigma
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoAB

open MeasureTheory GlobalTheory.HeckeTwoC

def wt (y t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * I

def L (y t : ℝ) : ℝ := Real.log |y| + lg (t / y)

theorem wt_eq {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t = (y : ℂ) * (((t / y : ℝ) : ℂ) + I) := by
  unfold wt
  have : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  push_cast
  field_simp

theorem norm_wt {y : ℝ} (hy : y ≠ 0) (t : ℝ) : ‖wt y t‖ = Real.exp (L y t) := by
  rw [wt_eq hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, L, Real.exp_add,
    Real.exp_log (abs_pos.2 hy), ← norm_tI_eq]

theorem wt_ne {y : ℝ} (hy : y ≠ 0) (t : ℝ) : wt y t ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp [wt] at this; exact hy this

def F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b * Complex.exp ((L y t : ℂ) * (-2 * σ)) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def F' (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) : ℂ :=
  (wt y t)⁻¹ ^ a * ((starRingEnd ℂ) (wt y t))⁻¹ ^ b *
    (Complex.exp ((L y t : ℂ) * (-2 * σ)) * ((L y t : ℂ) * (-2))) *
    Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_eq (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (fun σ => hTransAB a b σ ν y) = fun σ => ∫ t, F a b ν y σ t := by
  funext σ
  unfold hTransAB F
  congr 1; funext t
  congr 2
  rw [show (t : ℂ) + (y : ℂ) * I = wt y t from rfl, norm_wt hy,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]

theorem norm_e (ν t : ℝ) : ‖Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem norm_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) := by
  unfold F
  rw [norm_mul, norm_mul, norm_mul, norm_e, norm_pow, norm_pow, norm_inv, norm_inv, Complex.norm_conj,
    norm_wt hy, Complex.norm_exp, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) (t : ℝ) :
    ‖F' a b ν y σ t‖ = Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|) := by
  have : F' a b ν y σ t = F a b ν y σ t * ((L y t : ℂ) * (-2)) := by unfold F F'; ring
  rw [this, norm_mul, norm_F a b ν hy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp; ring

theorem bound_exp {ε M c L0 D : ℝ} (hc : 1 + 2 * ε ≤ c) (hM : c ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.exp (-c * (L0 + D)) ≤ Real.exp (M * |L0|) * Real.exp (-(1 + ε) * D) * Real.exp (-(ε * D)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := le_abs_self L0
  have h2 := neg_abs_le L0
  have h3 := abs_nonneg L0
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : 0 ≤ |L0| + L0),
    mul_nonneg (by linarith : 0 ≤ M - c) h3, mul_nonneg (by linarith : 0 ≤ c - 1 - 2 * ε) hD]

theorem bound_F {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F a b ν y σ t‖ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F a b ν hy]
  have hD := lg_nonneg (t / y)
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have h2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) := h
    _ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _

theorem bound_F' {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F' a b ν y σ t‖ ≤
      2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F' a b ν hy]
  have hD : 0 ≤ lg (t / y) := lg_nonneg _
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have hL : |L y t| ≤ |Real.log (abs y)| + lg (t / y) := by
    unfold L; exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hD])
  have hE2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE2D : Real.exp (-(ε * lg (t / y))) * lg (t / y) ≤ 1 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg (t / y))
    have := Real.add_one_le_exp (ε * lg (t / y))
    rw [show (Real.exp (ε * lg (t / y)))⁻¹ * lg (t / y) * ε = (ε * lg (t / y)) / Real.exp (ε * lg (t / y)) by
      field_simp]
    rw [div_le_iff₀ hp]; linarith
  have heC : 0 ≤ Real.exp (M * |Real.log (abs y)|) := (Real.exp_pos _).le
  have hE1 : 0 ≤ Real.exp (-(1 + ε) * lg (t / y)) := (Real.exp_pos _).le
  have hE2p : 0 ≤ Real.exp (-(ε * lg (t / y))) := (Real.exp_pos _).le
  have hl0 := abs_nonneg (Real.log |y|)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t) * (2 * |L y t|)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) *
          (2 * (|Real.log (abs y)| + lg (t / y))) :=
        mul_le_mul h (by linarith) (by positivity) (by positivity)
    _ = 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) *
          (Real.exp (-(ε * lg (t / y))) * |Real.log (abs y)| + Real.exp (-(ε * lg (t / y))) * lg (t / y)) := by ring
    _ ≤ 2 * Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * (1 * |Real.log (abs y)| + 1 / ε) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hE2 hl0) hE2D) (by positivity)
    _ = _ := by ring

theorem integrable_bound {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : y ≠ 0) :
    Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg (t / y))) :=
  (integrable_expL hε).comp_div hy

theorem hasDerivAt_F (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) :
    HasDerivAt (fun s => F a b ν y s t) (F' a b ν y σ t) σ := by
  unfold F F'
  have h : HasDerivAt (fun s : ℂ => (L y t : ℂ) * (-2 * s)) ((L y t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (L y t : ℂ)).congr_deriv (by ring)
  exact (h.cexp.const_mul _).mul_const _

theorem continuous_L {y : ℝ} : Continuous (L y) := by
  unfold L
  exact continuous_const.add (continuous_lg.comp (continuous_id.div_const y))

theorem continuous_F (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F a b ν y σ) := by
  unfold F
  have hw : Continuous (wt y) := by unfold wt; fun_prop
  have h1 : Continuous fun t => (wt y t)⁻¹ := hw.inv₀ (wt_ne hy)
  have h2 : Continuous fun t => ((starRingEnd ℂ) (wt y t))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => (map_ne_zero _).2 (wt_ne hy t))
  have h3 : Continuous fun t => Complex.exp ((L y t : ℂ) * (-2 * σ)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)
  have h4 : Continuous fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by fun_prop
  exact (((h1.pow a).mul (h2.pow b)).mul h3).mul h4

theorem continuous_F' (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F' a b ν y σ) := by
  have : F' a b ν y σ = fun t => F a b ν y σ t * ((L y t : ℂ) * (-2)) := by funext t; unfold F F'; ring
  rw [this]
  exact (continuous_F a b ν hy σ).mul ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)

end GlobalTheory.HeckeTwoAB

namespace GlobalTheory.HeckeTwo

open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB

theorem hTransAB_differentiableOn : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 →
    DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  intro a b ν y hab hy
  rw [hTransAB_eq a b ν hy]
  intro σ₀ hσ₀
  have hre : -1 / 2 < σ₀.re := hσ₀
  set ε := (σ₀.re + 1 / 2) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hab' : (2 : ℝ) ≤ (a + b : ℝ) := by exact_mod_cast hab
  have hball : ∀ σ ∈ Metric.ball σ₀ ε, -1 / 2 + ε ≤ σ.re ∧ σ.re ≤ σ₀.re + ε := by
    intro σ hσ
    have h1 : |(σ - σ₀).re| ≤ ‖σ - σ₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖σ - σ₀‖ < ε := by simpa [dist_eq_norm] using hσ
    have h3 := abs_lt.1 (lt_of_le_of_lt h1 h2)
    simp only [sub_re] at h3
    constructor <;> linarith [h3.1, h3.2]
  set M := (a + b : ℝ) + 2 * (σ₀.re + ε) with hM_def
  have hc : ∀ σ ∈ Metric.ball σ₀ ε, 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re := by
    intro σ hσ; have := (hball σ hσ).1; linarith
  have hM : ∀ σ ∈ Metric.ball σ₀ ε, (a + b : ℝ) + 2 * σ.re ≤ M := by
    intro σ hσ; have := (hball σ hσ).2; rw [hM_def]; linarith
  have h0 := Metric.mem_ball_self hε (x := σ₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F a b ν y)
    (F' := F' a b ν y) (x₀ := σ₀)
    (bound := fun t => 2 * Real.exp (M * |Real.log (abs y)|) * (|Real.log (abs y)| + 1 / ε) *
      Real.exp (-(1 + ε) * lg (t / y)))
    (Metric.ball_mem_nhds σ₀ hε)
    (Filter.Eventually.of_forall fun σ => (continuous_F a b ν hy σ).aestronglyMeasurable)
    (((integrable_bound hε hy).const_mul (Real.exp (M * |Real.log (abs y)|))).mono'
      (continuous_F a b ν hy σ₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => bound_F hε a b ν hy (hc σ₀ h0) (hM σ₀ h0) t))
    (continuous_F' a b ν hy σ₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t σ hσ => bound_F' hε a b ν hy (hc σ hσ) (hM σ hσ) t)
    ((integrable_bound hε hy).const_mul _)
    (Filter.Eventually.of_forall fun t σ _ => hasDerivAt_F a b ν y σ t)
  exact key.2.differentiableAt.differentiableWithinAt

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOnStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.cConst_differentiableOn | exact GlobalTheory.HeckeTwo.cConst_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.cConst_differentiableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroZeroStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierConstantAtZero_zero : GlobalTheory.HeckeTwo.cConst 0 = 0 := by
  first | exact @GlobalTheory.HeckeTwo.cConst_zero | exact GlobalTheory.HeckeTwo.cConst_zero | (intros; apply GlobalTheory.HeckeTwo.cConst_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecayStatement
section
open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_rapid_decay | exact GlobalTheory.HeckeTwo.hTrans_rapid_decay | (intros; apply GlobalTheory.HeckeTwo.hTrans_rapid_decay <;> assumption)
end

