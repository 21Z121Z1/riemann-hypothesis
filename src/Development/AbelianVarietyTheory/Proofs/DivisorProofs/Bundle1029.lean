import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusLiftStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem frobLift_stalk (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U)
    (F₀ : Γ(Y, U) →+* Γ(Y, U)) (hp2 : (p : Γ(Y, U)) ^ 2 = 0) (hF₀ : ∀ z, ∃ w, F₀ z = z ^ p + p * w)
    (y : Y) (hy : y ∈ U) :
    ∃ F : Y.presheaf.stalk y →+* Y.presheaf.stalk y,
      (∀ b, F ((Y.presheaf.germ U y hy).hom b) = (Y.presheaf.germ U y hy).hom (F₀ b)) ∧
        ∀ z, ∃ w, F z = z ^ p + p * w := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact frobLift_localization p (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl F₀ hp2 hF₀

theorem stalk_ringHom_ext {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    {C : Type} [CommRing C] (f f' : Y.presheaf.stalk y →+* C)
    (h : ∀ b, f ((Y.presheaf.germ U y hy).hom b) = f' ((Y.presheaf.germ U y hy).hom b)) : f = f' := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.ringHom_ext (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (RingHom.ext h)

theorem exists_frobLift_stalk_of_etCoord :
    ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  intro p _ Y g U n t hU ht η hη
  obtain ⟨F₀, hF₀, hFt⟩ := frob_lift_etale_chart p _ ht
  have hp2 : (p : Γ(Y, U)) ^ 2 = 0 := by
    have h := map_natCast (cstOn g U) (p ^ 2)
    rw [ZMod.natCast_self, map_zero] at h
    rw [← Nat.cast_pow, ← h]
  obtain ⟨F, hFg, hF⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ η hη
  refine ⟨F, hF, fun l => ?_, fun y hy h z hz => ?_⟩
  · have := hFt l
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    rw [hFg, this, map_pow]
  · obtain ⟨F', hFg', hF'⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ y hy
    have hs : ∀ b, (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ U y hy).hom b) =
        (Y.presheaf.germ U η hη).hom b := fun b =>
      congrArg (fun k => k.hom b) (Y.presheaf.germ_stalkSpecializes hy h)
    have hc : F.comp (Y.presheaf.stalkSpecializes h).hom =
        (Y.presheaf.stalkSpecializes h).hom.comp F' := by
      apply stalk_ringHom_ext U hU y hy
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, hFg, hFg', hs]
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨w, hw⟩ := hF' a
    refine ⟨_, ⟨w, rfl⟩, ?_⟩
    have := congrArg (· a) hc
    simp only [RingHom.comp_apply] at this
    rw [this, hw, map_add, map_mul, map_pow, map_natCast]

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
  (P.valuedAdicCompletion_eq_valuation' _).symm.trans (unif_spec P)

theorem exists_unit_part (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ∃ u : Eˣ, P.valuation E (u : E) = 1 ∧ k = unif P ^ ordF P k * u := by
  refine ⟨(unif P ^ ordF P k)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
  have h0 : P.valuation E (k : E) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, val_unif,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg, ordF]
  conv_lhs => rw [← WithZero.exp_log h0, WithZero.log_exp, ← WithZero.exp_add]
  simp

theorem twVal_half (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1)
    (k : Eˣ) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal χ (1 / 2) P k =
      (((χ.locK P (unif P) : ℂˣ) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)) ^ ordF P k := by
  obtain ⟨u, hu, hk⟩ := exists_unit_part P k
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  generalize ordF P k = n at hk ⊢
  rw [hk, map_mul, h u hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  congr 1
  have hN : (0 : ℝ) ≤ (Nat.card (kP P) : ℕ) := Nat.cast_nonneg _
  rw [show Ideal.absNorm P.asIdeal = Nat.card (kP P) from rfl, ← Complex.ofReal_zpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hN, ← Real.rpow_intCast, ← Real.rpow_mul hN, Complex.ofReal_cpow hN]
  push_cast
  congr 1
  ring

end General

theorem locK_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ) (hu : UnramEverywhere D c)
    (P : Pl D.host.E) (u : D.host.Eˣ) (h : P.valuation D.host.E (u : D.host.E) = 1) : χ.locK P u = 1 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, hP, hQ⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have key : ∀ k : D.host.E, P.valuation D.host.E k = 1 → finPart D (locE D e k) ∈ intAE D := by
    intro k hk
    rw [h2]
    intro Q
    have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (ι (finPart D (incA D k)) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
    rw [h5, h4]
    change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
    by_cases hQP : Q = P
    · subst hQP
      rw [hP, one_mul, add_sub_cancel]
      exact ((Q.valuedAdicCompletion_eq_valuation' k).trans hk).le
    · rw [hQ Q hQP, zero_mul, add_zero, map_one]
  have hinv : (((locU he.1 u)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((u⁻¹ : D.host.Eˣ) : D.host.E) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [locU_val, locE_mul_locE he.1]
    simp [locE]
  have h6 := hu (locU he.1 u) (by
    rw [locU_val, locE, RingHom.map_add, RingHom.map_one, RingHom.map_mul, hinf, zero_mul, add_zero])
    (key _ h) (by
      rw [hinv]
      refine key _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one])
  have h7 := hc.2 P e he u (locU he.1 u) rfl
  rw [h6] at h7
  exact Units.ext h7.symm

theorem exists_galConj_eta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClassesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_rigidified_line_bundle_classes : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i)), (∀ i, IsOpenImmersion (f i)) → (∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) → (∀ y, ∃ i, y ∈ V i) → (∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0) → (∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k → GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) → ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  first | exact @GlobalTheory.PicGlue.exists_glue_rigidified | exact GlobalTheory.PicGlue.exists_glue_rigidified | (intros; apply GlobalTheory.PicGlue.exists_glue_rigidified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperplane
section
open Matrix

namespace GlobalTheory.HyperplaneSymmetricForm

theorem exists_hyperplane {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (hs : GlobalTheory.LKTrip.sigPosH hA = 1) :
    ∃ φ : (Fin n → ℂ) →ₗ[ℂ] ℂ, ∀ u, u ≠ 0 → φ u = 0 → (star u ⬝ᵥ A *ᵥ u).re < 0 := by
  obtain ⟨⟨i0, hi0⟩, huniq⟩ := Fintype.card_eq_one_iff.1 hs
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hAe : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hneg : ∀ i, i ≠ i0 → hA.eigenvalues i < 0 := by
    intro i hi
    rcases lt_trichotomy (hA.eigenvalues i) 0 with h | h | h
    · exact h
    · exact absurd h (hne i)
    · exact absurd (congrArg Subtype.val (huniq ⟨i, h⟩)) hi
  refine ⟨(LinearMap.proj i0).comp (star U).mulVecLin, fun u hu hφ => ?_⟩
  set c := star U *ᵥ u with hc
  have hφ' : c i0 = 0 := hφ
  have hc0 : c ≠ 0 := by
    intro h
    apply hu
    have : U *ᵥ c = u := by rw [hc, mulVec_mulVec, hUU, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : (star u ⬝ᵥ A *ᵥ u).re = ∑ i, hA.eigenvalues i * Complex.normSq (c i) := by
    have e1 : star u ⬝ᵥ A *ᵥ u = star c ⬝ᵥ (diagonal (fun i => (hA.eigenvalues i : ℂ)) *ᵥ c) := by
      conv_lhs => rw [hAe]
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
      simp [star_eq_conjTranspose]
    rw [e1, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mulVec_diagonal, Complex.normSq_apply]
    ring
  rw [hq]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc0
  have hj0 : j ≠ i0 := by rintro rfl; exact hj hφ'
  have : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · by_cases h : i = i0
      · rw [h, hφ']; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hneg i h).le (Complex.normSq_nonneg _)
    · exact mul_neg_of_neg_of_pos (hneg j hj0) (Complex.normSq_pos.2 hj)
  simpa using this

theorem form_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x z : Fin n → ℂ) :
    star x ⬝ᵥ A *ᵥ z = (starRingEnd ℂ) (star z ⬝ᵥ A *ᵥ x) := by
  have : star (star z ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ z := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hA.eq, ← dotProduct_mulVec]
  rw [← this]; rfl

theorem main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (hs : GlobalTheory.LKTrip.sigPosH hA = 1) (z : Fin n → ℂ) (hz : 0 < (star z ⬝ᵥ A *ᵥ z).re)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    (star z ⬝ᵥ A *ᵥ z).re * (star x ⬝ᵥ A *ᵥ x).re < 2 * ‖star z ⬝ᵥ A *ᵥ x‖ ^ 2 := by
  obtain ⟨φ, hφ⟩ := exists_hyperplane A hA hd hs
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have ha : φ z ≠ 0 := fun h => absurd (hφ z hz0 h) (not_lt.2 hz.le)
  have hzz := form_symm A hA z z
  have hxx := form_symm A hA x x
  have hxz := form_symm A hA x z
  set a := φ z with ha'
  set b := φ x with hb'
  have hu : φ (a • x - b • z) = 0 := by
    rw [map_sub, map_smul, map_smul, ← ha', ← hb', smul_eq_mul, smul_eq_mul]; ring
  have hexp : star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z) =
      (starRingEnd ℂ) a * a * (star x ⬝ᵥ A *ᵥ x) - (starRingEnd ℂ) a * b * (star x ⬝ᵥ A *ᵥ z)
       - (starRingEnd ℂ) b * a * (star z ⬝ᵥ A *ᵥ x) + (starRingEnd ℂ) b * b * (star z ⬝ᵥ A *ᵥ z) := by
    simp only [star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, RCLike.star_def]
    ring
  have hlin : star z ⬝ᵥ A *ᵥ (a • x - b • z) = a * (star z ⬝ᵥ A *ᵥ x) - b * (star z ⬝ᵥ A *ᵥ z) := by
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hxz] at hexp
  generalize star z ⬝ᵥ A *ᵥ x = h at *
  generalize star z ⬝ᵥ A *ᵥ z = P at *
  generalize star x ⬝ᵥ A *ᵥ x = Q at *
  have hP : P.im = 0 := Complex.conj_eq_iff_im.1 hzz.symm
  have hQ : Q.im = 0 := Complex.conj_eq_iff_im.1 hxx.symm
  have hapos : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  have key : P.re * (star (a • x - b • z) ⬝ᵥ A *ᵥ (a • x - b • z)).re =
      Complex.normSq a * (P.re * Q.re - Complex.normSq h) + Complex.normSq (a * h - b * P) := by
    rw [hexp]
    simp [Complex.normSq_apply, hP, hQ]
    ring
  rw [← Complex.normSq_eq_norm_sq]
  have hh := Complex.normSq_nonneg h
  have hr := Complex.normSq_nonneg (a * h - b * P)
  by_cases h0 : a • x - b • z = 0
  · rw [h0] at key hlin
    simp only [mulVec_zero, dotProduct_zero, Complex.zero_re, mul_zero] at key hlin
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, zero_smul, sub_zero] at h0
      exact hx ((smul_eq_zero.1 h0).resolve_left ha)
    have hP0 : P ≠ 0 := by rintro rfl; simp at hz
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hb hP0 (by linear_combination hlin)
    have hpos := Complex.normSq_pos.2 hh0
    have : P.re * Q.re - Complex.normSq h ≤ 0 := by
      by_contra hc
      have := mul_pos hapos (not_le.1 hc)
      linarith
    linarith
  · have h1 := mul_neg_of_pos_of_neg hz (hφ _ h0 hu)
    have : P.re * Q.re - Complex.normSq h < 0 := by
      by_contra hc
      have := mul_nonneg hapos.le (not_lt.1 hc)
      linarith
    linarith

end GlobalTheory.HyperplaneSymmetricForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentCutoffTendstoAdelicUnitary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.UnitaryCutoff

section Mix

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mix (e : R) (A : Matrix ι ι R) : Matrix ι ι R := e • A + (1 - e) • (1 : Matrix ι ι R)

theorem mix_mul_mul {e : R} (he : e * e = e) (A C B : Matrix ι ι R) :
    mix e A * C * mix e B = e • (A * C * B) + (1 - e) • C := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem mix_mul {e : R} (he : e * e = e) (A B : Matrix ι ι R) :
    mix e A * mix e B = e • (A * B) + (1 - e) • (1 : Matrix ι ι R) := by
  have := mix_mul_mul he A 1 B
  rwa [Matrix.mul_one, Matrix.mul_one] at this

theorem mix_transpose (e : R) (A : Matrix ι ι R) : (mix e A)ᵀ = mix e Aᵀ := by
  simp [mix, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem mix_map {S : Type} [CommRing S] [Algebra S R] (c : R →ₐ[S] R) {e : R} (hc : c e = e) (A : Matrix ι ι R) :
    (mix e A).map c = mix e (A.map c) := by
  ext i j
  simp only [mix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hc]

end Mix

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_mix_fin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      mix (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) M) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (GlobalTheory.LocalGlobalChar.tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem exists_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AE F E := fun S => algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
  have he : ∀ S, e S * e S = e S := fun S => by
    simp only [e]; rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hc : ∀ S, cA σ (e S) = e S := fun S => (cA σ).commutes _
  have hg : (g.1.1)ᵀ * J₀ * (g.1.1).map (cA σ) = J₀ := g.2
  have hs : ∀ S, e S • (1 : Matrix ι ι (AE F E)) + (1 - e S) • 1 = 1 := fun S => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL ι (AE F E) := fun S =>
    ⟨mix (e S) g.1.1, mix (e S) g.1.inv, by rw [mix_mul (he S), g.1.val_inv, hs],
      by rw [mix_mul (he S), g.1.inv_val, hs]⟩
  have hu : ∀ S, u S ∈ UG (cA σ) J₀ := fun S => by
    show (mix (e S) g.1.1)ᵀ * J₀ * (mix (e S) g.1.1).map (cA σ) = J₀
    rw [mix_transpose, mix_map (cA σ) (hc S), mix_mul_mul (he S), hg,
      ← add_smul, add_sub_cancel, one_smul]
  refine ⟨fun S => ⟨u S, hu S⟩, fun S => rfl, ?_⟩
  refine (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  refine Tendsto.prodMk_nhds (tendsto_mix_fin g.1.1) ?_
  exact (MulOpposite.continuous_op.tendsto _).comp (tendsto_mix_fin g.1.inv)

end GlobalTheory.UnitaryCutoff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulIsAdicIntegralInTensorBasis
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_int_smul_mem_adicCompletionIntegers_of_elt (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : v.adicCompletion ℚ) * a ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [mul_comm]
  simpa using h

theorem exists_int_smul_isIntB : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  intro M _ _ κ b v y
  choose d hd0 hd using exists_int_smul_mem_adicCompletionIntegers_of_elt v
  set c := (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y with hc
  refine ⟨∏ i ∈ c.support, d (c i), Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _, fun i => ?_⟩
  rw [map_zsmul, ← hc, Finsupp.smul_apply, zsmul_eq_mul]
  by_cases hi : i ∈ c.support
  · rw [← Finset.prod_erase_mul _ _ hi, Int.cast_mul, mul_assoc]
    exact mul_mem (intCast_mem _ _) (hd _)
  · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
    exact zero_mem _

end GlobalTheory.AdicSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntWitness
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus
open Formalism.L2.Host (atFin IsUnitAt)

namespace GlobalTheory.GaussModulus

theorem exists_int_witness {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (ha : a ≠ 0) (hE : ExpAt χ w a) :
    ∃ (y : 𝓞 E) (u : Eˣ), (u : E) = y ∧ y ∉ w.asIdeal ∧ y - 1 ∈ w.asIdeal ^ (a - 1) ∧ χ.locK w u ≠ 1 := by
  have hnot : ¬ χ.LevelLe w (a - 1) := fun h => by
    have := (hE (a - 1)).mp h
    omega
  have hlev : χ.LevelLe w a := (hE a).mpr le_rfl
  simp only [Formalism.L2.Host.HChar.LevelLe, not_forall] at hnot
  obtain ⟨x, hxu, hx1, hxχ⟩ := hnot
  have hxv : Valued.v (x : w.adicCompletion E) = 1 := hxu
  obtain ⟨y, hy⟩ := exists_int_approx w hxv.le a
  have hlt : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hyv' : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = 1 := by
    rw [← hxv]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hxv]
    exact lt_of_le_of_lt hy hlt
  have hyv : w.valuation E (y : E) = 1 := by rwa [← valued_algebraMap]
  have hy0 : (y : E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact zero_ne_one hyv
  refine ⟨y, Units.mk0 (y : E) hy0, rfl, ?_, ?_, ?_⟩
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
    exact hyv
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) ((algebraMap (𝓞 E) E) (y - 1)) =
        (algebraMap E (w.adicCompletion E) (y : E) - (x : w.adicCompletion E)) + ((x : w.adicCompletion E) - 1) := by
      simp
    rw [e]
    refine Valuation.map_add_le _ ?_ hx1
    rw [Valuation.map_sub_swap]
    refine hy.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · intro hχ
    apply hxχ
    set u : Eˣ := Units.mk0 (y : E) hy0 with hu
    have hau : ((atFin w u : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (y : E) := rfl
    have h1 : χ.loc w (x * (atFin w u)⁻¹) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v (((x * (atFin w u)⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hau, map_mul, map_inv₀, hxv, hyv', inv_one, one_mul]
      · rw [Units.val_mul, Units.val_inv_eq_inv_val, hau]
        have hne : algebraMap E (w.adicCompletion E) (y : E) ≠ 0 := by
          intro h; rw [h, map_zero] at hyv'; exact zero_ne_one hyv'
        rw [show (x : w.adicCompletion E) * (algebraMap E (w.adicCompletion E) (y : E))⁻¹ - 1 =
            ((x : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) *
              (algebraMap E (w.adicCompletion E) (y : E))⁻¹ by field_simp]
        rw [map_mul, map_inv₀, hyv', inv_one, mul_one]
        exact hy
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
    exact hχ

end GlobalTheory.GaussModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOne
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
end

