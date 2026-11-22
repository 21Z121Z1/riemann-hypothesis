import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem isUnit_natCast_of_primes {W : Type} [CommRing W] (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (n : ℕ)
    (hn : n ≠ 0) : IsUnit (n : W) := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h0; exact absurd rfl h0
  | one => intro _; simp
  | prime p hp => intro _; exact h p hp
  | mul a b ha hb =>
    intro hab
    rw [Nat.cast_mul]
    exact (ha (left_ne_zero_of_mul hab)).mul (hb (right_ne_zero_of_mul hab))

theorem isUnit_map_of_ne_zero {K : Type} [Field K] [NumberField K] {W : Type} [CommRing W]
    (h : ∀ p : ℕ, p.Prime → IsUnit (p : W)) (f : 𝓞 K →+* W) {a : 𝓞 K} (ha : a ≠ 0) : IsUnit (f a) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hN : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  have e : f b * f a = (Ideal.absNorm (Ideal.span {a}) : W) := by rw [← map_mul, hb, map_natCast]
  exact isUnit_of_mul_isUnit_right (e ▸ isUnit_natCast_of_primes h _ hN)

theorem idlAlong_comap {X X' : Scheme.{0}} (k : X' ⟶ X) (I : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X') : idlAlong (I.comap k) ξ = idlAlong I (ξ ≫ k) := by
  unfold idlAlong
  rw [VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

theorem idlAlong_pow {X : Scheme.{0}} (I : X.IdealSheafData) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) : idlAlong (I ^ n) ξ = idlAlong I ξ ^ n := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, TraitOrder.idlAlong_eq_map _ ξ ⟨U, hU⟩ hle, ← Ideal.map_pow]
  congr 1

theorem blowOrd_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be ∧ idlAlong EX.idealSheaf χ = Ideal.span {ϖ ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hY hB W _ _ _ hW hp ϖ hϖ χ t mt P hr be hbe hmon
  obtain ⟨-, -, -, hjQ, -, hEX, -⟩ := hB
  have := c.fin
  have : NumberField c.F := {}

  let f : 𝓞 c.F →+* W := (Spec.preimage (χ ≫ Z.s)).hom
  let g : c.F →+* W := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f)
    fun y => isUnit_map_of_ne_zero hp f (nonZeroDivisors.ne_zero y.2)
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = f := IsLocalization.lift_comp _
  have hsq : χ ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, f, CommRingCat.ofHom_hom, Spec.map_preimage]
  let χ₀ : Sp W ⟶ gen Z := pullback.lift χ (spMap g) hsq
  have hχ : χ₀ ≫ genι Z = χ := pullback.lift_fst _ _ _

  have hI : idlAlong EX.idealSheaf χ = idlAlong BY.idealSheaf (χ₀ ≫ e.inv ≫ genι Y) ^ n := by
    calc idlAlong EX.idealSheaf χ = idlAlong EX.idealSheaf ((χ₀ ≫ e.inv) ≫ e.hom ≫ genι Z) := by
          rw [Category.assoc, e.inv_hom_id_assoc, hχ]
      _ = idlAlong (EX.idealSheaf.comap (e.hom ≫ genι Z)) (χ₀ ≫ e.inv) := (idlAlong_comap _ _ _).symm
      _ = idlAlong ((BY.idealSheaf ^ n).comap (genι Y)) (χ₀ ≫ e.inv) := by rw [hEX]
      _ = idlAlong (BY.idealSheaf ^ n) ((χ₀ ≫ e.inv) ≫ genι Y) := idlAlong_comap _ _ _
      _ = _ := by rw [idlAlong_pow, Category.assoc]

  have hZY : Z.jQ ≫ e.inv = Y.jQ := by rw [← hjQ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨t₀, n₁, n₂, -⟩ := cmpSt_of_sabExtNormalSt (sabExtNormalSt_of_homExtNormalSt homExtNormal) E H D l Xo c
    c.F (𝓞 c.F) (RingHom.id c.F) (algebraMap (𝓞 c.F) c.F) Y Z e.inv hZY
    (ModelRelCompare.normal_genericFibre Z (ModelRelCompare.isDedFrac_in_use c).1).1
  obtain ⟨a⟩ := TraitOrder.cancel hχ n₁ mt
  obtain ⟨b⟩ := TraitOrder.comp (h := χ₀ ≫ e.inv ≫ genι Y) rfl n₂ a

  have hr' : Set.range (jK W ≫ χ₀ ≫ e.inv ≫ genι Y) ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    have hz : (jK W ≫ χ₀) p ∈ Set.range Z.jQ := by
      rw [← Z.ab_gen]
      obtain ⟨q, hq⟩ := hr ⟨p, rfl⟩
      show (jK W ≫ χ₀ ≫ genι Z) p ∈ abLocus Z.t.G
      rw [hχ, ← hq]
      show genι Z (Z.jQ q) ∈ abLocus Z.t.G
      rw [← Set.mem_preimage, Z.ab_gen]
      exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hz
    refine ⟨q, ?_⟩
    show (Y.jQ ≫ genι Y) q = _
    rw [← hZY]
    simp only [Scheme.Hom.comp_apply] at hq ⊢
    rw [hq]
  obtain ⟨m₀, hm₀, hid⟩ := hY W hW ϖ hϖ _ t b P hr' be hbe hmon
  refine ⟨n * m₀, ?_, ?_⟩
  · push_cast
    rw [hm₀]
    simp only [InvFun.evalZ, InvFun.eval, comb]
    push_cast
    ring
  · rw [hI, hid, Ideal.span_singleton_pow, pow_mul']

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section Member

theorem finrank_int_eq_finrank_mul (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

theorem free_int_of_projective (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] : Module.Free ℤ Y := by
  have : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.trans (𝓞 E)
  exact Module.free_of_finite_type_torsion_free'

theorem mem_psdCone_int {E : Type} [Field E] [NumberField E] (bar : 𝓞 E → 𝓞 E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X) : B ∈ psdCone (id : ℤ → ℤ) X := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, h1, h2, h3⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  have : Module.Free ℤ X₁ := free_int_of_projective E
  exact ⟨X₁, _, _, inferInstance, r.restrictScalars ℤ, B₁, hr, ⟨h1.1, fun a y z => by simp⟩, h2, h3⟩

section ClassMin

open scoped Pointwise

variable {M n : ℕ} {C C' : (Fin n → ℤ) → (Fin n → ℤ) → ℝ}

theorem classMin_set_nonempty (M : ℕ) (C : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) (y : Fin n → ZMod (M + 1)) :
    {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x}.Nonempty := by
  obtain ⟨a, ha⟩ := redV_surjective M n y
  exact ⟨_, a, ha, rfl⟩

theorem classMin_set_bddBelow (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) :
    BddBelow {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} :=
  ⟨0, by rintro _ ⟨a, -, rfl⟩; exact hC a⟩

theorem classMin_nonneg (hC : ∀ a, 0 ≤ C a a) (y : Fin n → ZMod (M + 1)) : 0 ≤ classMin M C y :=
  le_csInf (classMin_set_nonempty M C y) (by rintro _ ⟨a, -, rfl⟩; exact hC a)

theorem classMin_smul {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ZMod (M + 1)) :
    classMin M (fun a b => t * C a b) y = t * classMin M C y := by
  unfold classMin
  have : {x | ∃ a : Fin n → ℤ, redV M a = y ∧ t * C a a = x} = t • {x | ∃ a : Fin n → ℤ, redV M a = y ∧ C a a = x} := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  rw [this, Real.sInf_smul_of_nonneg ht, smul_eq_mul]

theorem classMin_add_le (hC : ∀ a, 0 ≤ C a a) (hC' : ∀ a, 0 ≤ C' a a) (y : Fin n → ZMod (M + 1)) :
    classMin M C y + classMin M C' y ≤ classMin M (fun a b => C a b + C' a b) y := by
  refine le_csInf (classMin_set_nonempty M (fun a b => C a b + C' a b) y) ?_
  rintro _ ⟨a, ha, rfl⟩
  exact add_le_add (csInf_le (classMin_set_bddBelow hC y) ⟨a, ha, rfl⟩)
    (csInf_le (classMin_set_bddBelow hC' y) ⟨a, ha, rfl⟩)

theorem classMin_exists_nat {β : (Fin n → ℤ) → (Fin n → ℤ) → ℤ} (hβ : ∀ a, 0 ≤ β a a) (y : Fin n → ZMod (M + 1)) :
    ∃ k : ℕ, classMin M (fun a b => (β a b : ℝ)) y = k := by
  classical
  let T : Set ℕ := {k | ∃ a : Fin n → ℤ, redV M a = y ∧ β a a = k}
  have hT : T.Nonempty := by
    obtain ⟨a, ha⟩ := redV_surjective M n y
    exact ⟨(β a a).toNat, a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  obtain ⟨a₀, ha₀, e₀⟩ := Nat.sInf_mem hT
  refine ⟨sInf T, IsLeast.csInf_eq ⟨⟨a₀, ha₀, by simp only [e₀]; push_cast; rfl⟩, ?_⟩⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : sInf T ≤ (β a a).toNat := Nat.sInf_le ⟨a, ha, (Int.toNat_of_nonneg (hβ a)).symm⟩
  have h2 : ((β a a).toNat : ℤ) = β a a := Int.toNat_of_nonneg (hβ a)
  show ((sInf T : ℕ) : ℝ) ≤ (β a a : ℝ)
  rw [← h2]
  exact_mod_cast h1

end ClassMin

variable {X : Type} [AddCommGroup X] [Module.Finite ℤ X]

theorem fineMean_eval_eq (M : ℕ) {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (fineMean M).eval X (fun a b => B a b) =
      (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y := by
  rw [(fineMean M).eval_eq hs]
  show _ * _ - B (s 0) (s 0) = _
  simp

end Member

theorem baseFun_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ)
    (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q →
    (∀ B ∈ psdCone H.bar X, ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) =
      t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧
    (∀ B ∈ psdCone H.bar X, ∀ B' ∈ psdCone H.bar X, evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B +
      evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  intro E _ _ _ H g q φs 𝓜 X _ _ _ _ hφ hE hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have hd : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq_finrank_mul E X]
    exact (Nat.mul_le_mul_left _ hX).trans hE
  have hφX : IsPolFanOn id φs X := hφ X hd
  set d := Module.finrank ℤ X with hd_def
  let b := Module.finBasis ℤ X
  let s : (Fin d → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hs : Function.Surjective s := b.equivFun.symm.surjective
  set D := fineDen g 𝓜 with hD
  have key : ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, evalR (baseFun (𝓞 E) D φs 𝓜) B = D * (evalR φs B +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y) := by
    intro B
    rw [evalR, eval_baseFun]
    simp only [fineMean_eval_eq _ hs]
    rfl
  have keyZ : ∀ β : LinearMap.BilinForm ℤ X, (baseFun (𝓞 E) D φs 𝓜).evalZ β = D * (φs.evalZ β +
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (β (s a) (s b) : ℝ)) y) := by
    intro β
    rw [← evalR_toReal, key, evalR_toReal]
    simp only [toReal_apply]
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_⟩
  · have hB0 := nonneg_of_mem_psdCone hB
    rw [key, key, hφX.homog B (mem_psdCone_int _ hB) t ht]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    simp only [mul_left_comm _ t, ← Finset.mul_sum]
    ring
  · have h1 := hφX.superadd B (mem_psdCone_int _ hB) B' (mem_psdCone_int _ hB')
    have h2 : ∀ M ∈ 𝓜, (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B (s a) (s b)) y +
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => B' (s a) (s b)) y ≤
        (((M : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin M (fun a b => (B + B') (s a) (s b)) y := fun M _ => by
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (by positivity)
      simp only [LinearMap.add_apply]
      exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib] at h3
    rw [key, key, key, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · obtain ⟨n, hn⟩ := hφX.integral β (mem_balForms_int.2 hβ.1) hp
    have hdiv : ∀ M ∈ 𝓜, ∃ e : ℕ, D = (M + 1) ^ d * e := fun M hM =>
      (pow_dvd_pow (M + 1) hd).trans (Finset.dvd_prod_of_mem (fun M => (M + 1) ^ g) hM)
    choose! e he using hdiv
    choose k hk using fun M y => classMin_exists_nat (M := M) (β := fun a b => β (s a) (s b)) (fun a => hp (s a)) y
    refine ⟨D * n + ∑ M ∈ 𝓜, (e M : ℤ) * ∑ y, (k M y : ℤ), ?_⟩
    rw [keyZ, hn]
    simp only [hk]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM : (D : ℝ) = ((M : ℝ) + 1) ^ d * e M := by exact_mod_cast he M hM
    rw [hM]
    field_simp
  · have h1 := hφX.pos β (mem_balForms_int.2 hβ.1) hp h0
    rw [keyZ]
    refine mul_pos (by exact_mod_cast fineDen_pos g 𝓜) (add_pos_of_pos_of_nonneg h1 (Finset.sum_nonneg fun M _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => classMin_nonneg (fun a => ?_) y)))
    exact_mod_cast hp (s a)

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartCompatible
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem exists_smul_of_pt_eq {O k : Type} [CommRing O] [Field k] {N : ℕ} {c c' : O →+* k} {v w : Fin (N + 1) → k}
    {hv : Ideal.span (Set.range v) = ⊤} {hw : Ideal.span (Set.range w) = ⊤} (h : pt c v hv = pt c' w hw) :
    w ≠ 0 ∧ ∃ u : k, w = u • v := by
  have hc : c = c' := by
    have h1 := (pt_str c v hv).symm.trans ((congrArg (· ≫ PSpace.str O N) h).trans (pt_str c' w hw))
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hc
  obtain ⟨u, hu⟩ := (pt_eq_pt_iff c hv hw).1 h
  refine ⟨fun h0 => ?_, u, hu⟩
  rw [h0] at hw
  refine bot_ne_top (α := Ideal k) (Eq.trans ?_ hw)
  refine (Ideal.span_eq_bot.2 ?_).symm
  rintro _ ⟨i, rfl⟩
  rfl

theorem exists_coeff_of_mem_span_initial {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m n : ℕ} (h : n ≤ m)
    (c : Fin m → V) {v : V} (hv : v ∈ Submodule.span k (Set.range fun l : Fin n => c (Fin.castLE h l))) :
    ∃ cf : Fin m → k, (∀ j : Fin m, n ≤ (j : ℕ) → cf j = 0) ∧ v = ∑ j, cf j • c j := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    refine ⟨Pi.single (Fin.castLE h l) 1, fun j hj => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd l.2 (not_lt.2 hj)
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨r • a, fun j hj => by simp [ha j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem tie_glue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → SameFlag Z.ty (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) ((Z.fr a').bc φ') := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k _ a a' φ φ' e τ n hn i hi
  have hn' : n ≤ Dw.mult τ := by
    rw [T.ty] at hn
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hx : spMap (φ.comp (ρ a)) ≫ (aff (ι a)).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π := by
    rw [spMap_comp, Category.assoc, T.res a]
  have e' : spMap φ ≫ Z.chart a ≫ Z.π = spMap φ' ≫ Z.chart a' ≫ Z.π := by
    rw [← Category.assoc, e, Category.assoc]
  obtain ⟨h1, e1⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a (ι a) φ _ hx (stdEn τ n hn')
  obtain ⟨h2, e2⟩ := GlobalTheory.T.pre_model_chart_gluing E H Dw Xo p W Y i₀ Z L aff M crd ι ρ g T k a' (ι a) φ' _ (hx.trans e') (stdEn τ n hn')
  have e3 : spMap φ ≫ Z.chart a ≫ g (stdEn τ n hn') = spMap φ' ≫ Z.chart a' ≫ g (stdEn τ n hn') := by
    rw [← Category.assoc, e, Category.assoc]
  obtain ⟨h0, u, hu⟩ := exists_smul_of_pt_eq (e1.symm.trans (e3.trans e2))
  have hm := GlobalTheory.T.mem_span_of_plucker_proportional k M n
    (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ (Fin.castLE hn' l)))
    (fun l => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a').bc φ' τ (Fin.castLE hn' l))) u h0 hu ⟨i, hi⟩
  obtain ⟨cf, hcf, hs⟩ := exists_coeff_of_mem_span_initial hn'
    (fun j => crd (ι a) k (φ.comp (ρ a)) ((Z.fr a).bc φ τ j)) hm
  refine ⟨cf, hcf, (T.emb.comb_iff (ι a) (φ.comp (ρ a)) hx (fun j => ((T.frame a k φ).1 τ j).1)
    (e' ▸ ((T.frame a' k φ').1 τ i).1) cf).2 hs⟩

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_model_arc_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ q : (pullback Z.s (spMap bV) : Scheme.{0}), pullback.fst Z.s (spMap bV) q ∈ Set.range Z.j ↔ f q ∈ Set.range Y.j := by
  first | exact @GlobalTheory.GlobalLocalRange.fst_mem_range_j_iff | exact GlobalTheory.GlobalLocalRange.fst_mem_range_j_iff | (intros; apply GlobalTheory.GlobalLocalRange.fst_mem_range_j_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedLevelEqParahoricWithTupleCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtPara

theorem levelPara : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  intro D T L μ0 hL hPg i t hr ψ v hv
  obtain ⟨s, hsv, hsQ⟩ := GlobalTheory.T.exists_splitTwistPlace_over_productCharacter_ramified D T L μ0 hL i t v hv
  have hvg : s.v ∉ gPl D := hsv ▸ hv.1
  obtain ⟨hPgo, hQo⟩ := GlobalTheory.T.typeAndTwistPlaces_over_other_than_split D T L μ0 hL hPg t s hvg hsQ

  have hunr : (L.C.mu0 i).UnrAt s.w := by
    refine (L.C.isMu0 i).unr s.w fun k hk => hvg ⟨s.w, s.w_under, k, hk⟩
  have htame : (L.C.mu0 i * L.xiH t).TameAt s.w := by
    intro x hx hx1
    rw [HChar.loc_mul, (L.C.isMu0 i).tame s.w x hx hx1, hL.xi_tame t s.w x hx hx1, one_mul]
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.tame_heckeCharacter_split_place_local_component D.host.E s _ htame
  obtain ⟨hUA, hSt, hred, hloc⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, -, hφ0, hφa, hφe⟩ := hloc s
  have hoff : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ PP,
      (PP ∈ L.Pg ∨ (PP ∈ L.Q t ∧ PP ≠ s.w)) → redFn 1 PP (km D D.R.nV κ) = 1 := by
    intro κ hκ htr PP hPP
    obtain ⟨v', hov, hne⟩ : ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v :=
      hPP.elim (hPgo PP) (fun h => hQo PP h.1 h.2)
    exact hred κ hκ {s.v} v' PP htr hov (by simpa using hne)
  refine ⟨s, ξ, hsv, hξc, ⟨?_, ?_⟩⟩
  · intro κ htr
    have hkey : ∀ hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV,
        (redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) ↔ ∀ a b : Fin D.R.nV, D.R.r ≤ a.val → b.val < D.R.r →
          Valued.v (((s.loc D.R.nV κ : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) := fun hκ =>
      (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκ)).1
    constructor
    · intro hJ
      have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _ := hJ
      rw [mem_lev, mem_parLev] at hJ'
      obtain ⟨⟨-, hSt', -, hQ'⟩, -⟩ := hJ'
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 hSt'
      refine ⟨GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => GlobalTheory.HeckeStdFacts.proj_mem s (hκU a b), fun a b => ?_⟩, ?_⟩
      · rw [← map_inv]
        exact GlobalTheory.HeckeStdFacts.proj_mem s ((inv_mem hκU) a b)
      · exact (hkey hκU).1 (hQ' s.w hsQ)
    · rintro ⟨hG, hlow⟩
      obtain ⟨hG1, hG2⟩ := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 hG
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV :=
        GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ htr (fun a b => hG1 a b) (fun a b => by rw [map_inv]; exact hG2 a b)
      have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
        funext PP
        show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
        rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      show km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _
      rw [mem_lev, mem_parLev, hrt]
      refine ⟨⟨hUA κ, (hSt κ).2 hκU, fun PP hPP => ?_, fun PP hPP => ?_⟩, Subgroup.one_mem _⟩
      · rw [hoff κ hκU htr PP (Or.inl hPP)]; exact Subgroup.one_mem _
      · by_cases hPs : PP = s.w
        · subst hPs; exact (hkey hκU).2 hlow
        · rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hPs⟩)]; exact Subgroup.one_mem _
  · intro κ hJ htr u hu
    have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1
        (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) := hJ
    have hpar := (mem_lev.1 hJ').1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 (parLev_St hpar)
    have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
      funext PP
      show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
      rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    have hQ' : redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) := parLev_q hpar hsQ
    obtain ⟨hd, hdv⟩ := (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκU)).2 hQ'
    obtain ⟨w0, hw0⟩ : ∃ w0, w0 = dBlk (blk2 D.R.r) 1 (redFn 1 s.w (km D D.R.nV κ)) := ⟨_, rfl⟩
    rw [← hw0] at hdv
    have hQ1 : ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP (km D D.R.nV κ))) = L.xiR t s.w w0 := by
      rw [hw0]
      refine Finset.prod_eq_single_of_mem s.w hsQ fun PP hPP hne => ?_
      rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hne⟩)]
      show L.xiR t PP (ext1 _ _ 1) = 1
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
    have hval : stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) ⟨κ, hJ⟩ =
        L.xiR t s.w w0 := by
      show levFn 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = _
      unfold levFn
      rw [hrt, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, one_mul]
      · exact hQ1
      · intro PP hPP
        refine Finset.prod_eq_one fun c _ => ?_
        rw [hoff κ hκU htr PP (Or.inl hPP)]
        exact (congrArg _ (blockDiagonalExtendByOnePrimeField_one _ _)).trans (map_one _)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (w0 : kP s.w)
    have hw0ne : (w0 : kP s.w) ≠ 0 := w0.ne_zero
    have haP : a ∉ s.w.asIdeal := fun h => hw0ne (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haP (by
      rw [show a = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
    obtain ⟨k, hk⟩ : ∃ k : D.host.Eˣ, (k : D.host.E) = a := ⟨Units.mk0 _ ha0, rfl⟩
    have hres : L.xiR t s.w w0 = (L.xiH t).locK s.w k := hL.xiR t s.w hsQ a k w0 hk ha.symm
    obtain ⟨hia, hφia⟩ := hφa a
    have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
      rw [hu]
      refine le_antisymm hd (not_lt.1 fun hlt => hw0ne ?_)
      rw [hdv]; exact (hφ0 _).2 hlt
    have hu2 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
      have h0 : φ (⟨_, hd⟩ - ⟨_, hia⟩) = 0 := by rw [map_sub, ← hdv, hφia, ha, sub_self]
      have h1 := (hφ0 _).1 h0
      rw [AddSubgroupClass.coe_sub] at h1
      rw [hu]; exact h1
    have hk1 : (L.C.mu0 i).locK s.w k = 1 := by
      have hv1 : Valued.v (((k : D.host.E) : s.w.adicCompletion D.host.E)) = 1 := by
        rw [hk]
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_eq_one_iff]
        exact haP
      exact hunr _ hv1
    have hmul : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k :=
      HChar.loc_mul _ _ s.w (atFin s.w k)
    refine hval.trans (hres.trans ?_)
    rw [hξr u a k hk hu1 hu2, hmul, hk1, one_mul]

end GlobalTheory.MtPara
end

