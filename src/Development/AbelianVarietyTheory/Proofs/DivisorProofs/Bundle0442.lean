import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechDR

theorem mOm_two_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x : Om R A 2) :
    (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x =
      GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) x := by
  set h := SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)
  let L : Om R A 2 →ₗ[A] Om R B 2 :=
    { toFun := h.mOm 2
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply]; exact algebraMap_smul B a _ }
  have e : L = GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti, hv, ← wedge_eq_ιMulti]
    change h.mOm 2 _ = _
    rw [h.mOm_wedge, h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), h.oneFormMap_eq_kaehlerDifferential_map (fun _ ↦ rfl), wedge_eq_ιMulti]
    congr 1
    ext i; fin_cases i <;> rfl
  exact LinearMap.congr_fun e x

theorem twoForm_exists_pow_smul_eq_zero_of_isLocalization {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by
  haveI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) 2
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c) B _).2 hb
  rw [mOm_two_eq_exteriorPowerMapOver, ← map_zero (GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B))] at hx
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := c) hx
  exact ⟨n, hn.trans (smul_zero _)⟩

theorem twoForm_exists_pow_smul_eq_zero_of_algHom {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : A)
    (hc : @IsLocalization.Away A _ c B _ f.toRingHom.toAlgebra) (x : Om R A 2)
    (hx : (SemiHom.of_algHom f).mOm 2 x = 0) : ∃ n : ℕ, c ^ n • x = 0 := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact twoForm_exists_pow_smul_eq_zero_of_isLocalization c x hx

theorem twoForm_sep_of_basis : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by
  intro R' _ X' s' C' _ G hcov T η hη
  obtain ⟨n, b, hb, hf⟩ := hcov T
  have key : ∀ i, ∃ m : ℕ, b i ^ m • η = 0 := by
    intro i
    let U : X'.affineOpens := T.unop
    let c : Γ(X', U.1) := b i
    let V : X'.affineOpens := ⟨X'.basicOpen c, U.2.basicOpen c⟩
    have hle : V ≤ U := X'.basicOpen_le c
    let u : T ⟶ Opposite.op V := (homOfLE hle).op
    have hu : IsUnit (mp (OAff s') u (b i)) := X'.toRingedSpace.isUnit_res_basicOpen c
    obtain ⟨t, v, w, hvw⟩ := hf i (Opposite.op V) u hu
    have h0 : pOm (OAff s') 2 u η = 0 := by rw [← hvw, pOm_comp, hη t v, map_zero]
    exact twoForm_exists_pow_smul_eq_zero_of_algHom (mp (OAff s') u) (b i)
      (U.2.isLocalization_basicOpen c) η h0
  choose m hm using key
  have hN : ∀ i, b i ^ (∑ j, m j) • η = 0 := fun i ↦ by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j))
      (Finset.mem_univ i))
    rw [hk, pow_add, mul_comm, mul_smul, hm i, smul_zero]
  have := Ideal.span_pow_eq_top _ hb (∑ j, m j)
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  rw [← one_smul ((OAff s').obj T) η, ← hr, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [Function.comp_apply, mul_smul, hN i, smul_zero]

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLastStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | exact GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | (intros; apply GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem mem_adjoin_both' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (ξ a b : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval ξ)) (hab : IsUnit (ξ * a - b))
    (hY : Y * (g - algebraMap O A ξ) = algebraMap O A a * g - algebraMap O A b) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g ξ Q hQ hQs
    have e : Y = (algebraMap O A a * g - algebraMap O A b) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C ξ * X - C b) ^ i * (X - C a) ^ (n - i)
    have hgY : g * (Y - algebraMap O A a) = algebraMap O A ξ * Y - algebraMap O A b := by
      linear_combination hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (Y - algebraMap O A a) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (Y - algebraMap O A a) ^ n = (Y - algebraMap O A a) ^ i * (Y - algebraMap O A a) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval a = (ξ * a - b) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval a) := by
      rw [hRe]; exact hab.pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y a R hR hRu
    have e : g = (algebraMap O A ξ * Y - algebraMap O A b) * v := by
      linear_combination (-g) * hYv + v * hgY
    rw [e]
    exact mul_mem (sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
      (Subalgebra.algebraMap_mem _ _)) hv

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

variable {K : UQ}

theorem isUnit_of_conj (K : UQ) (x y : K.O) (h : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hy : IsUnit y) : IsUnit x := by
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨w, hw⟩ := K.c_int (↑u⁻¹ : K.O)
  have h1 : K.c (algebraMap K.O K.E (u : K.O)) = algebraMap K.O K.E x := by rw [← h, K.c_c]
  have h2 : algebraMap K.O K.E (x * w) = 1 := by
    rw [map_mul, ← h1, ← hw, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← map_one (algebraMap K.O K.E)] at h2
  exact IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective K.O K.E h2)

theorem mobius_selfadj (B : InvAlg K) (x y ξ : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hξ : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1)
    (w : B.A) (hw : (B.g - algebraMap K.O B.A ξ) * w = 1)
    (hY : Y * (B.g - algebraMap K.O B.A ξ) =
      algebraMap K.O B.A y * B.g - algebraMap K.O B.A x * algebraMap K.O B.A ξ) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have hξA : algebraMap K.O B.A ξ * B.σ (algebraMap K.O B.A ξ) = 1 := by
    rw [σ_algebraMap, IsScalarTower.algebraMap_apply K.O K.E B.A ξ, ← map_mul, hξ, map_one]
  have h1 := congrArg B.σ hY
  rw [map_mul, map_sub, map_sub, map_mul, map_mul, sx, sy] at h1
  set G := B.g
  set Gs := B.σ B.g
  set ξA := algebraMap K.O B.A ξ
  set ξs := B.σ (algebraMap K.O B.A ξ)
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  have key : (B.σ Y - Y) * (G - ξA) = 0 := by
    linear_combination (-G * ξA) * h1 - hY - (xA * ξA - B.σ Y * ξA) * hu - (B.σ Y * G - yA * G) * hξA
  calc B.σ Y = B.σ Y * ((G - ξA) * w) := by rw [hw, mul_one]
    _ = Y * ((G - ξA) * w) + (B.σ Y - Y) * (G - ξA) * w := by ring
    _ = Y := by rw [key, hw]; ring

end GlobalTheory.UnitLemma.CayleyAny

namespace GlobalTheory.UnitLemma.CayleyAny

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_residually_unipotent_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K),
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ hu₁ hu₂ hsep s hs ⟨Q, hQ, hQr⟩
  have hinj := IsFractionRing.injective K.O K.E

  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  set yi : K.O := ↑hyu.unit⁻¹ with hyi
  have hyyi : y * yi = 1 := hyu.mul_val_inv
  set ξ : K.O := (s : K.O) * x * yi with hξd
  have hξu : IsUnit ξ := (s.isUnit.mul hxu).mul (hyu.unit⁻¹).isUnit
  have hξn : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1 := by
    obtain ⟨w, hw⟩ := K.c_int yi
    have e1 : algebraMap K.O K.E x * algebraMap K.O K.E w = 1 := by
      have := congrArg K.c (congrArg (algebraMap K.O K.E) hyyi)
      rw [map_mul, map_mul, hyx, hw, map_one, map_one] at this
      exact this
    have e2 : algebraMap K.O K.E y * algebraMap K.O K.E yi = 1 := by
      rw [← map_mul, hyyi, map_one]
    rw [hξd, map_mul, map_mul, map_mul, map_mul, hxy, hw]
    linear_combination (algebraMap K.O K.E x * algebraMap K.O K.E w * algebraMap K.O K.E y *
      algebraMap K.O K.E yi) * hs + (algebraMap K.O K.E y * algebraMap K.O K.E yi) * e1 + e2
  have hQξ : IsUnit (Q.eval ξ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    apply pow_ne_zero
    intro h0
    apply hm
    set r := IsLocalRing.residue K.O
    have hs0 : r (s : K.O) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
    have h3 : r (y * yi) = 1 := by rw [hyyi, map_one]
    rw [map_mul] at h3
    have h4 : r (s : K.O) * (r x - r y) = 0 := by
      rw [hξd, map_mul, map_mul] at h0
      linear_combination r y * h0 - (r (s : K.O) * r x) * h3
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact (mul_eq_zero.1 h4).resolve_left hs0
  have hab : IsUnit (ξ * y - x * ξ) := by
    rw [show ξ * y - x * ξ = -(ξ * (x - y)) by ring]
    exact (hξu.mul hxyu).neg
  obtain ⟨Q₁, Q₂, hQQ, e₁, e₂, a₁, a₂, hmQ⟩ := lift_factor B₁ B₂ hsep Q hQ
  have hQs₁ : IsUnit (Q₁.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_left hQξ
  have hQs₂ : IsUnit (Q₂.eval ξ) := by
    rw [hQQ, eval_mul] at hQξ; exact isUnit_of_mul_isUnit_right hQξ
  have hm₁ : Q₁.Monic := monic_of_injective hinj (e₁ ▸ LinearMap.charpoly_monic _)
  have hm₂ : Q₂.Monic := monic_of_injective hinj (e₂ ▸ LinearMap.charpoly_monic _)
  obtain ⟨w₁, -, hw₁⟩ := sub_inv_mem B₁.g ξ Q₁ a₁ hQs₁
  obtain ⟨w₂, -, hw₂⟩ := sub_inv_mem B₂.g ξ Q₂ a₂ hQs₂
  set Y₁ := (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * w₁ with hY₁d
  set Y₂ := (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * w₂ with hY₂d
  have hY₁ : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) =
      algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A x * algebraMap K.O B₁.A ξ) * hw₁
  have hY₂ : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) =
      algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A x * algebraMap K.O B₂.A ξ) * hw₂
  have hY₁' : Y₁ * (B₁.g - algebraMap K.O B₁.A ξ) = algebraMap K.O B₁.A y * B₁.g - algebraMap K.O B₁.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₁.A) x ξ]; exact hY₁
  have hY₂' : Y₂ * (B₂.g - algebraMap K.O B₂.A ξ) = algebraMap K.O B₂.A y * B₂.g - algebraMap K.O B₂.A (x * ξ) := by
    rw [map_mul (algebraMap K.O B₂.A) x ξ]; exact hY₂
  have adj₁ := mem_adjoin_both' B₁.g Y₁ ξ y (x * ξ) Q₁ hm₁ a₁ hQs₁ hab hY₁'
  have adj₂ := mem_adjoin_both' B₂.g Y₂ ξ y (x * ξ) Q₂ hm₂ a₂ hQs₂ hab hY₂'
  have aQ : aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) Q = 0 := by
    have f1 := aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    have f2 := aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q
    refine Prod.ext ?_ ?_
    · change AlgHom.fst K.O B₁.A B₂.A _ = 0
      rw [← f1]; change aeval B₁.g Q = 0
      rw [hQQ, map_mul, a₁, zero_mul]
    · change AlgHom.snd K.O B₁.A B₂.A _ = 0
      rw [← f2]; change aeval B₂.g Q = 0
      rw [hQQ, map_mul, a₂, mul_zero]
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * ((B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) ξ) =
      algebraMap K.O (B₁.A × B₂.A) y * (B₁.g, B₂.g) - algebraMap K.O (B₁.A × B₂.A) (x * ξ) :=
    Prod.ext hY₁' hY₂'
  have adjP := mem_adjoin_both' ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) ξ y (x * ξ) Q hmQ aQ hQξ hab hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := mobius_selfadj B₁ x y ξ Y₁ hu₁ hxy hξn w₁ hw₁ hY₁
  have sa₂ := mobius_selfadj B₂ x y ξ Y₂ hu₂ hxy hξn w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g ⟨Q₁, hm₁, a₁⟩
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g ⟨Q₂, hm₂, a₂⟩
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CayleyAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOne
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel Filter
open scoped Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), sc F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  obtain ⟨hfd, htr, hinv, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨L, hL, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (inter_mem h1 h2)
  obtain ⟨hsU, hsv⟩ := hs (show (s : F) ∈ GlobalTheory.SplitWeil.cball s from show valuation F (s : F) ≤ valuation F (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [GlobalTheory.SplitWeil.cball] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0), h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (GlobalTheory.WeilM.eq_one_of_forall_pow_near fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [sc, hz0, hχz, hn]

end GlobalTheory.KSp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDivLeOneCofiniteStatement
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_valuation_div_le_one_of_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  first | exact @GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | exact GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | (intros; apply GlobalTheory.LocGenVal.valuation_div_le_one_cofinite <;> assumption)
end

