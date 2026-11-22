import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l n M : ℕ) [Fact l.Prime] (hM : 0 < M) (hn : l ^ n ∣ M) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ i : ℕ, i.Coprime M ∧ s ζ = ζ ^ i ∧
      (i : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hcard : Nat.card (rootsOfUnity M Ω) = M := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω M
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  set c := modularCyclotomicCharacter Ω hcard s.toRingEquiv with hc
  have hsζ : s ζ = ζ ^ (c : ZMod M).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard s.toRingEquiv hζ.toRootsOfUnity.2
    simpa using h
  refine ⟨ζ, hζ, (c : ZMod M).val, ZMod.val_coe_unit_coprime c, hsζ, ?_⟩
  rw [cyclotomicCharacter.toZModPow]
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hcard' : Nat.card (rootsOfUnity (l ^ n) Ω) = l ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)
  set c' := modularCyclotomicCharacter Ω hcard' s.toRingEquiv
  have hζ' : IsPrimitiveRoot (ζ ^ (M / l ^ n)) (l ^ n) :=
    hζ.pow hM (Nat.div_mul_cancel hn).symm
  have h1 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c : ZMod M).val := by
    rw [map_pow, hsζ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : s (ζ ^ (M / l ^ n)) = (ζ ^ (M / l ^ n)) ^ (c' : ZMod (l ^ n)).val := by
    have h := modularCyclotomicCharacter.spec Ω hcard' s.toRingEquiv hζ'.toRootsOfUnity.2
    simpa using h
  have hfin : IsOfFinOrder (ζ ^ (M / l ^ n)) :=
    orderOf_pos_iff.1 (by rw [← hζ'.eq_orderOf]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h3 := hfin.pow_eq_pow_iff_modEq.1 (h1.symm.trans h2)
  rw [← hζ'.eq_orderOf] at h3
  rw [← ZMod.natCast_zmod_val (c' : ZMod (l ^ n))]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.exists_sl2_conj_diag_zmod (M i : ℕ) (hi : i.Coprime M) (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), (_root_.GlobalTheory.KZ.en γ 0 0 : ZMod M) = _root_.GlobalTheory.KZ.en δ 0 0 ∧
      (_root_.GlobalTheory.KZ.en γ 0 1 : ZMod M) = (i : ZMod M) * _root_.GlobalTheory.KZ.en δ 0 1 ∧
      (i : ZMod M) * _root_.GlobalTheory.KZ.en γ 1 0 = _root_.GlobalTheory.KZ.en δ 1 0 ∧
      (_root_.GlobalTheory.KZ.en γ 1 1 : ZMod M) = _root_.GlobalTheory.KZ.en δ 1 1 := by
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime i hi
  have hu : (u : ZMod M) = i := rfl
  have hγdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hγdet
  set m : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod M),
      ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M);
      (i : ZMod M) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M),
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M)] with hm_def
  have hm : m.det = 1 := by
    rw [hm_def, Matrix.det_fin_two_of]
    have h1 : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * (i : ZMod M) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (Int.cast : ℤ → ZMod M) hγdet
    push_cast at h2
    linear_combination h2 - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod M) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) * h1
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M ⟨m, hm⟩
  have he : ∀ a b, (((δ : Matrix (Fin 2) (Fin 2) ℤ) a b : ℤ) : ZMod M) = m a b := fun a b => by
    have h := congrArg (fun g : SL(2, ZMod M) => (g : Matrix (Fin 2) (Fin 2) (ZMod M)) a b) hδ
    simpa using h
  refine ⟨δ, ?_, ?_, ?_, ?_⟩ <;> simp only [_root_.GlobalTheory.KZ.en, he, hm_def]
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [← mul_assoc, ← hu, Units.mul_inv, one_mul]
  · simp
  · simp

theorem exists_conj_level_exponent :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M →
      l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧
      ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧
        (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧
        (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  intro Ω _ _ _ N l n M _ hM hN hl hn s γ hγ
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hn s
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_sl2_conj_diag_zmod M i hi γ
  have red : ∀ {K : ℕ}, K ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod K) = y := fun {K} hK x y h => by
    simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h
  have h10' : (((i : ℤ) * en γ 1 0 : ℤ) : ZMod M) = en δ 1 0 := by push_cast; exact h10
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a1, a2, a3⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ1
  have a4 := CongruenceSubgroup.Gamma0_mem.1 hγ0
  refine ⟨δ, Subgroup.mem_inf.2 ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨?_, ?_, ?_⟩,
    CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ζ, hζ, i, by rw [zpow_natCast, hs], ⟨h00, ?_, ?_, h11⟩, ?_⟩
  · exact (red hN h00).symm.trans a1
  · exact (red hN h11).symm.trans a2
  · refine (red hN h10').symm.trans ?_
    have : (en γ 1 0 : ZMod N) = 0 := a3
    rw [Int.cast_mul, this, mul_zero]
  · refine (red hl h10').symm.trans ?_
    have : (en γ 1 0 : ZMod l) = 0 := a4
    rw [Int.cast_mul, this, mul_zero]
  · simpa only [Int.cast_natCast] using h01
  · simpa only [Int.cast_natCast] using h10
  · simpa only [Int.cast_natCast] using hχ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHom
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNTwist

noncomputable def twistMap {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : HahnSeries ℚ Ω' where
  coeff r := χ r * s (h.coeff r)
  isPWO_support' := h.isPWO_support.mono (by
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro h0
    exact hr (by rw [h0, map_zero, mul_zero]))

lemma twistMap_coeff {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) (r : ℚ) : (twistMap s χ h).coeff r = χ r * s (h.coeff r) := rfl

lemma twistMap_support {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : (twistMap s χ h).support ⊆ h.support := by
  intro r hr
  simp only [HahnSeries.mem_support, twistMap_coeff, ne_eq] at hr ⊢
  intro h0
  exact hr (by rw [h0, map_zero, mul_zero])

noncomputable def twistHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h0 : χ 0 = 1) (hadd : ∀ r r', χ (r + r') = χ r * χ r') :
    HahnSeries ℚ Ω →+* HahnSeries ℚ Ω' where
  toFun := twistMap s χ
  map_one' := by
    ext r
    rw [twistMap_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs with hr
    · subst hr; simp [h0]
    · simp
  map_zero' := by
    ext r
    simp [twistMap_coeff]
  map_add' x y := by
    ext r
    simp [twistMap_coeff, mul_add]
  map_mul' x y := by
    ext a
    show (twistMap s χ (x * y)).coeff a = (twistMap s χ x * twistMap s χ y).coeff a
    rw [twistMap_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    have hsub : Finset.antidiagonal (twistMap s χ x).isPWO_support (twistMap s χ y).isPWO_support a ⊆
        Finset.antidiagonal x.isPWO_support y.isPWO_support a :=
      fun ij hij => (Finset.antidiagonal_mono_right (twistMap_support s χ y))
        ((Finset.antidiagonal_mono_left (twistMap_support s χ x)) hij)
    rw [Finset.sum_subset hsub (fun ij hbig hij => ?_)]
    · refine Finset.sum_congr rfl (fun ij hij => ?_)
      have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
      rw [twistMap_coeff, twistMap_coeff, map_mul, ← hsum, hadd]
      ring
    · have hs : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hbig).2.2
      by_cases h1 : (twistMap s χ x).coeff ij.1 = 0
      · rw [h1, zero_mul]
      · by_cases h2 : (twistMap s χ y).coeff ij.2 = 0
        · rw [h2, mul_zero]
        · exact absurd (Finset.mem_antidiagonal.mpr ⟨h1, h2, hs⟩) hij

end GlobalTheory.FNTwist

theorem GlobalTheory.FNTwist.exists_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  intro Ω Ω' _ _ s l χ hl h0 hadd
  have hinj : Function.Injective (AddMonoidHom.mulRight l) := by
    intro a b hab
    simpa [AddMonoidHom.coe_mulRight, hl.ne'] using hab
  have hmono : ∀ g g' : ℚ, AddMonoidHom.mulRight l g ≤ AddMonoidHom.mulRight l g' ↔ g ≤ g' := by
    intro g g'
    simp only [AddMonoidHom.coe_mulRight]
    exact mul_le_mul_iff_of_pos_right hl
  refine ⟨(HahnSeries.embDomainRingHom (AddMonoidHom.mulRight l) hinj hmono).comp
    (GlobalTheory.FNTwist.twistHom s χ h0 hadd), fun h r => ?_⟩
  rw [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
  have := HahnSeries.embDomain_coeff (f := ⟨⟨AddMonoidHom.mulRight l, hinj⟩, hmono _ _⟩)
    (x := GlobalTheory.FNTwist.twistHom s χ h0 hadd h) (a := r)
  rw [show χ r * s (h.coeff r) = (GlobalTheory.FNTwist.twistHom s χ h0 hadd h).coeff r from rfl]
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
section
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section
namespace GlobalTheory.RootHs
open Metric Complex

lemma mem_ball_big (u : ℂ) (R ε : ℝ) (hε : 0 < ε) (hu : 2 * ε ≤ u.im) (hR : u.re ^ 2 + u.im ^ 2 < R * u.im)
    (hRε : ε < R) : u ∈ ball ((R : ℂ) * I) (R - ε) := by
  have hRe : 0 ≤ R - ε := by linarith
  rw [Metric.mem_ball, Complex.dist_eq]
  have hsq : ‖u - (R : ℂ) * I‖ ^ 2 = u.re ^ 2 + (u.im - R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hlt : ‖u - (R : ℂ) * I‖ ^ 2 < (R - ε) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R) (by linarith : (0:ℝ) ≤ u.im - 2 * ε), sq_nonneg ε]
  nlinarith [norm_nonneg (u - (R : ℂ) * I)]

lemma closedBall_big_sub (R ε : ℝ) (hε : 0 < ε) : closedBall ((R : ℂ) * I) (R - ε) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h1 := Complex.abs_im_le_norm (z - (R : ℂ) * I)
  have h2 : (z - (R : ℂ) * I).im = z.im - R := by simp
  rw [h2] at h1
  show 0 < z.im
  have h3 := neg_abs_le (z.im - R)
  linarith

lemma exists_disc (z₀ z : ℂ) (h₀ : 0 < z₀.im) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), closedBall c r ⊆ Hs ∧ z₀ ∈ ball c r ∧ z ∈ ball c r := by
  set ε : ℝ := min z₀.im z.im / 2 with hεdef
  have hε : 0 < ε := half_pos (lt_min h₀ hz)
  have h2ε₀ : 2 * ε ≤ z₀.im := by rw [hεdef]; linarith [min_le_left z₀.im z.im]
  have h2ε : 2 * ε ≤ z.im := by rw [hεdef]; linarith [min_le_right z₀.im z.im]
  have ha : 0 ≤ (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im := div_nonneg (by positivity) h₀.le
  have hb : 0 ≤ (z.re ^ 2 + z.im ^ 2) / z.im := div_nonneg (by positivity) hz.le
  set R : ℝ := (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im + (z.re ^ 2 + z.im ^ 2) / z.im + ε + 1 with hRdef
  have hR₀ : z₀.re ^ 2 + z₀.im ^ 2 < R * z₀.im := (div_lt_iff₀ h₀).mp (by rw [hRdef]; linarith)
  have hR : z.re ^ 2 + z.im ^ 2 < R * z.im := (div_lt_iff₀ hz).mp (by rw [hRdef]; linarith)
  have hRε : ε < R := by rw [hRdef]; linarith
  exact ⟨(R : ℂ) * I, R - ε, closedBall_big_sub R ε hε, mem_ball_big z₀ R ε hε h2ε₀ hR₀ hRε,
    mem_ball_big z R ε hε h2ε hR hRε⟩

theorem discRoot : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    (∃ z₀ ∈ Hs, h z₀ ≠ 0) → ∀ (c : ℂ) (r : ℝ), Metric.closedBall c r ⊆ Hs →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧ ∀ z ∈ Metric.ball c r, g z ^ m = h z := by
  rintro h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz => ?_⟩
    rw [Metric.ball_eq_empty.mpr hr] at hz
    exact absurd hz (Set.notMem_empty z)
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hHsConn : IsPreconnected Hs := by
    show IsPreconnected {z : ℂ | 0 < z.im}
    exact (convex_halfSpace_im_gt (r := 0)).isPreconnected
  have han : AnalyticOnNhd ℂ h Hs := hh.analyticOnNhd hHsOpen
  refine GlobalTheory.KZ.RootDisc.exists_root_disc h m c r hm hr (han.mono hsub) ?_
  intro τ hτ
  have hτ' := hsub hτ
  have hfin : analyticOrderAt h τ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHsConn hτ' htop hz₀)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmer : meromorphicOrderAt h τ = ((n : ℤ) : WithTop ℤ) := by
    rw [(han τ hτ').meromorphicOrderAt_eq, ← hn]
    rfl
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.mp (hdiv τ hτ' n hmer)
  exact ⟨k, by rw [← hn, hk]⟩

theorem rootUnique : ∀ (U : Set ℂ) (g₁ g₂ : ℂ → ℂ) (m : ℕ) (z₀ : ℂ), 0 < m → IsOpen U → IsPreconnected U →
    DifferentiableOn ℂ g₁ U → DifferentiableOn ℂ g₂ U → (∀ z ∈ U, g₁ z ^ m = g₂ z ^ m) → z₀ ∈ U →
    g₁ z₀ = g₂ z₀ → g₁ z₀ ≠ 0 → Set.EqOn g₁ g₂ U := by
  intro U g₁ g₂ m z₀ hm hU hC hg₁ hg₂ hpow hz₀ heq hne
  have hc₁ : ContinuousAt g₁ z₀ := (hg₁.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hc₂ : ContinuousAt g₂ z₀ := (hg₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hq : ContinuousAt (fun z => g₂ z / g₁ z) z₀ := hc₂.div hc₁ hne
  have hq0 : g₂ z₀ / g₁ z₀ = 1 := by rw [← heq, div_self hne]
  set S : Finset ℂ := (Polynomial.nthRoots m (1 : ℂ)).toFinset.erase 1 with hSdef
  have hS : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  have hopen : (S : Set ℂ)ᶜ ∈ 𝓝 (g₂ z₀ / g₁ z₀) := by
    rw [hq0]
    exact hS.isOpen_compl.mem_nhds (by simp [hSdef])
  have hev : g₁ =ᶠ[𝓝 z₀] g₂ := by
    filter_upwards [hq.preimage_mem_nhds hopen, hc₁.eventually_ne hne, hU.mem_nhds hz₀] with z hzS hz1 hzU
    have hroot : g₂ z / g₁ z ∈ Polynomial.nthRoots m (1 : ℂ) := by
      rw [Polynomial.mem_nthRoots hm, div_pow, ← hpow z hzU, div_self (pow_ne_zero _ hz1)]
    have h1 : g₂ z / g₁ z = 1 := by
      by_contra hne1
      exact hzS (Finset.mem_erase.mpr ⟨hne1, Multiset.mem_toFinset.mpr hroot⟩)
    rw [div_eq_one_iff_eq hz1] at h1
    exact h1.symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hg₁.analyticOnNhd hU) (hg₂.analyticOnNhd hU) hC hz₀ hev

theorem rootHs : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  classical
  intro h m hm hh hdiv
  by_cases hz : ∃ z₀ ∈ Hs, h z₀ ≠ 0
  swap
  · simp only [not_exists, not_and, not_not] at hz
    refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz' => ?_⟩
    rw [hz z hz', zero_pow hm.ne']
  obtain ⟨z₀, hz₀, hne⟩ := hz
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hm
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hw₀, zero_pow hm.ne'])
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have key : ∀ z ∈ Hs, ∃ (c : ℂ) (r : ℝ), z₀ ∈ ball c r ∧ z ∈ ball c r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball c r) ∧ (∀ y ∈ ball c r, g y ^ m = h y) ∧ g z₀ = w₀ := by
    intro z hz
    obtain ⟨c, r, hsub, h0, h1⟩ := exists_disc z₀ z hz₀ hz
    obtain ⟨g, hgd, hgp⟩ := discRoot h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
    have hg0 : g z₀ ≠ 0 := by
      intro h0'
      apply hne
      rw [← hgp z₀ h0, h0', zero_pow hm.ne']
    refine ⟨c, r, h0, h1, fun y => (w₀ / g z₀) * g y, hgd.const_mul _, fun y hy => ?_, ?_⟩
    · rw [mul_pow, div_pow, hgp y hy, hw₀, hgp z₀ h0, div_self hne, one_mul]
    · exact div_mul_cancel₀ w₀ hg0
  choose c r h0 h1 g hgd hgp hgz using key
  have hloc : ∀ z₁ (hz₁ : z₁ ∈ Hs) z (hz : z ∈ Hs), z ∈ ball (c z₁ hz₁) (r z₁ hz₁) →
      g z hz z = g z₁ hz₁ z := by
    intro z₁ hz₁ z hz hzb
    have hU : IsOpen (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) := isOpen_ball.inter isOpen_ball
    have hC : IsPreconnected (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    refine rootUnique _ (g z hz) (g z₁ hz₁) m z₀ hm hU hC ((hgd z hz).mono Set.inter_subset_left)
      ((hgd z₁ hz₁).mono Set.inter_subset_right) (fun y hy => by rw [hgp z hz y hy.1, hgp z₁ hz₁ y hy.2])
      ⟨h0 z hz, h0 z₁ hz₁⟩ ((hgz z hz).trans (hgz z₁ hz₁).symm) (by rw [hgz z hz]; exact hw₀ne) ⟨h1 z hz, hzb⟩
  refine ⟨fun z => if h' : z ∈ Hs then g z h' z else 0, ?_, ?_⟩
  · intro z₁ hz₁
    have hev : (fun z => if h' : z ∈ Hs then g z h' z else 0) =ᶠ[𝓝 z₁] g z₁ hz₁ := by
      have hmem : ball (c z₁ hz₁) (r z₁ hz₁) ∩ Hs ∈ 𝓝 z₁ := (isOpen_ball.inter hHsOpen).mem_nhds ⟨h1 z₁ hz₁, hz₁⟩
      filter_upwards [hmem] with z hz
      show (if h' : z ∈ Hs then g z h' z else 0) = g z₁ hz₁ z
      rw [dif_pos hz.2]
      exact hloc z₁ hz₁ z hz.2 hz.1
    exact (((hgd z₁ hz₁).differentiableAt (isOpen_ball.mem_nhds (h1 z₁ hz₁))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    show (if h' : z ∈ Hs then g z h' z else 0) ^ m = h z
    rw [dif_pos hz]
    exact hgp z hz z (h1 z hz)

end GlobalTheory.RootHs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePointStatement
section
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatumStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  first | exact @GlobalTheory.BadShare.Cells.relevant_cells | exact GlobalTheory.BadShare.Cells.relevant_cells | (intros; apply GlobalTheory.BadShare.Cells.relevant_cells <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootBallOfAnalyticOrderDvdStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_ball_of_analyticOrder_dvd : ∀ (h : ℂ → ℂ) (m : ℕ) (c : ℂ) (R : ℝ), 0 < m → 0 < R → AnalyticOnNhd ℂ h (Metric.closedBall c R) → (∀ τ ∈ Metric.closedBall c R, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball c R) ∧ ∀ z ∈ Metric.ball c R, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.RootDisc.exists_root_disc | exact GlobalTheory.KZ.RootDisc.exists_root_disc | (intros; apply GlobalTheory.KZ.RootDisc.exists_root_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOneStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  first | exact @GlobalTheory.exists_root_of_unity_close_of_pow_close | exact GlobalTheory.exists_root_of_unity_close_of_pow_close | (intros; apply GlobalTheory.exists_root_of_unity_close_of_pow_close <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevelStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M → ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧ ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.KZ.exists_scalar_mod_level | exact GlobalTheory.KZ.exists_scalar_mod_level | (intros; apply GlobalTheory.KZ.exists_scalar_mod_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoIntSmulOfFixesJK
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.JStab

theorem eps_eOm_of_alg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  haveI : NeZero (x.den : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  obtain ⟨ζ, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 x.den_pos).ne')
  have hζ : IsPrimitiveRoot ζ x.den := (Polynomial.isRoot_cyclotomic_iff).1 hζ0
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_ne_zero' {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x ≠ 0 := by
  intro h0
  have := eps_eOm_of_alg ε x
  rw [h0, map_zero] at this
  exact Complex.exp_ne_zero _ this.symm

end GlobalTheory.KZ.ES.JStab
end
end

