import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0025
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldFurther
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0034
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0020
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0029

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace unitaryAbsoluteValueBounds

theorem abs_eta_pow (𝔭 : Ideal (𝓞 F)) (M : ℕ) : |etaF K F 𝔭 ^ M| = 1 := by
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h] <;> simp

theorem geom_bound {x : ℝ} (hx : |x| ≤ 1 / 2) (N : ℕ) :
    0 ≤ ∑ l ∈ Finset.range N, x ^ l ∧ ∑ l ∈ Finset.range N, x ^ l ≤ 4 := by
  have hxa := abs_le.mp hx
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hxa
    linarith [hxa.2]
  have hxN : |x ^ N| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by linarith)
  have hxN' := abs_le.mp hxN
  rw [geom_sum_eq hx1 N]
  constructor
  · exact div_nonneg_of_nonpos (by linarith [hxN'.2]) (by linarith [hxa.2])
  · rw [div_le_iff_of_neg (by linarith [hxa.2])]
    linarith [hxa.2, hxN'.1]

theorem abs_x_eq (𝔭 : Ideal (𝓞 F)) (m : ℕ) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| = ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ := by
  rw [abs_mul, abs_eta_pow, one_mul, abs_of_nonneg (by positivity)]

theorem abs_x_le {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 2 ≤ m) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| ≤ 1 / 2 := by
  rw [abs_x_eq]
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (2 : ℝ) ≤ Ideal.absNorm 𝔭 := by
    have : 2 ≤ Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  have hp : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (m - 1) :=
    le_trans hN (le_self_pow₀ (by linarith) (by omega))
  calc ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
    _ = 1 / 2 := by norm_num

theorem alphaN_rank_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hm : finrank K V = 0) {n : 𝓞 F} (hn : n ≠ 0) : alphaN h L 𝔭 n = 0 := by
  have hsub : Subsingleton V := finrank_zero_iff.1 hm
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn le_rfl]
  have h0 : nkCount h L 𝔭 (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) n = 0 := by
    unfold nkCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, y, -, hc⟩
    have hy : h (y : V) (y : V) = algebraMap F K ((0 : 𝓞 F) : F) := by
      rw [Subsingleton.elim (y : V) 0]
      simp
    rw [hy, MeanB.congrP_algebraMap_iff_sub_mem h𝔭, zero_sub, neg_mem_iff, mem_pow_iff_le_vF h𝔭 hn] at hc
    omega
  rw [h0]
  simp

end unitaryAbsoluteValueBounds

theorem alphaN_of_vd_zero_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) :=
  unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd hL hLi h𝔭 hv hm hn

theorem alphaN_eq_of_vF_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0) (hvv : vF 𝔭 n = vF 𝔭 n') :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  rcases Nat.eq_zero_or_pos (finrank K V) with hm | hm
  · rw [unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL hLi h𝔭 hm hn,
      unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL hLi h𝔭 hm hn']
  · rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv hm _ n hn rfl, unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv hm _ n' hn' rfl, hvv]

theorem alphaN_rho_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hv : vd h L 𝔭 = 0) {n : 𝓞 F} (hn : n ≠ 0) :
    0 ≤ alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) ∧ alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) ≤ 4 := by
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n hn rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne']
  exact unitaryAbsoluteValueBounds.geom_bound (unitaryAbsoluteValueBounds.abs_x_le h𝔭 hm) _

theorem alphaN_rho_diff_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hvv : vF 𝔭 n = vF 𝔭 n' + 1) :
    |alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) - alphaN h L 𝔭 n' / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))| ≤
      8 * ((vF 𝔭 n : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(((finrank K V - 1) * ((vF 𝔭 n + 1) / 2) : ℕ) : ℤ)) := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := unitaryAbsoluteValueBounds.one_lt_q h𝔭
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n hn rfl,
    unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n' hn' rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne',
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne', hvv,
    Finset.sum_range_succ _ (vF 𝔭 n' + 1), add_sub_cancel_left, abs_pow, unitaryAbsoluteValueBounds.abs_x_eq, zpow_neg,
    zpow_natCast, inv_pow, ← pow_mul]
  have h1 : ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n' + 1)))⁻¹ ≤
      ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (Nat.mul_le_mul_left _ (by omega)))
  have h2 : (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ := by
    positivity
  have h3 : (1 : ℝ) ≤ 8 * (((vF 𝔭 n' + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((vF 𝔭 n' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ _ := h1
    _ = 1 * _ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h2

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmul
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def pK (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Submodule (𝓞 K) K :=
  locF 𝔭 (Submodule.map (Algebra.linearMap (𝓞 K) K) (extP K 𝔭 ^ k))

def glSub (A : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | Formalism.HermitianLatticesTheory.gmap X A = A}
  one_mem' := autSub_gmap_one A
  mul_mem' := by
    intro a b ha hb
    show Formalism.HermitianLatticesTheory.gmap (a * b) A = A
    rw [autSub_gmap_mul, show Formalism.HermitianLatticesTheory.gmap b A = A from hb, show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
  inv_mem' := by
    intro a ha
    show Formalism.HermitianLatticesTheory.gmap a⁻¹ A = A
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.gmap a A = A from ha]
    rw [← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_glSub {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} :
    X ∈ glSub A ↔ Formalism.HermitianLatticesTheory.gmap X A = A := Iff.rfl

theorem apply_mem {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) {x : V} (hx : x ∈ A) :
    X x ∈ A := by
  have hX' : Formalism.HermitianLatticesTheory.gmap X A = A := hX
  rw [← hX']
  exact Submodule.mem_map_of_mem hx

theorem apply_mem_smul {A : Submodule (𝓞 K) V} {X : V ≃ₗ[K] V} (hX : X ∈ glSub A) (I : Ideal (𝓞 K))
    {x : V} (hx : x ∈ I • A) : X x ∈ I • A := by
  have h2 : A.map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hX
  have h1 : X x ∈ (I • A).map ((X : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hx
  rwa [Submodule.map_smul'', h2] at h1

def sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k}
  one_mem' := ⟨one_mem _, fun x _ y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).add_mem (ha' _ (apply_mem hb hx) _ (apply_mem hb hy)) (hb' x hx y hy)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx y hy => ?_⟩
    have := (pK K 𝔭 k).neg_mem (ha' _ (apply_mem (inv_mem ha) hx) _ (apply_mem (inv_mem ha) hy))
    have e : ∀ z : V, a (a⁻¹ z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    simpa [e] using this

def nSub (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Subgroup (V ≃ₗ[K] V) where
  carrier := {X | X ∈ glSub A ∧ ∀ x ∈ A, X x - x ∈ extP K 𝔭 ^ k • A}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).add_mem (apply_mem_smul ha _ (hb' x hx)) (ha' x hx)
    simpa using this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have := (extP K 𝔭 ^ k • A).neg_mem (apply_mem_smul (inv_mem ha) _ (ha' x hx))
    have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    simpa [e] using this

theorem mem_sSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    {X : V ≃ₗ[K] V} : X ∈ sSub h A 𝔭 k ↔
      X ∈ glSub A ∧ ∀ x ∈ A, ∀ y ∈ A, h (X x) (X y) - h x y ∈ pK K 𝔭 k := Iff.rfl

theorem mem_nSub {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V} :
    X ∈ nSub A 𝔭 k ↔ X ∈ glSub A ∧ ∀ x ∈ A, X x - x ∈ extP K 𝔭 ^ k • A := Iff.rfl

def endL (A A' : Submodule (𝓞 K) V) : AddSubgroup (V →ₗ[K] V) where
  carrier := {D | ∀ x ∈ A, D x ∈ A'}
  zero_mem' := fun x _ => by simp
  add_mem' := fun ha hb x hx => A'.add_mem (ha x hx) (hb x hx)
  neg_mem' := fun ha x hx => A'.neg_mem (ha x hx)

def sesqL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := fun x _ y _ => by simp
  add_mem' := fun ha hb x hx y hy => (pK K 𝔭 k).add_mem (ha x hx y hy) (hb x hx y hy)
  neg_mem' := fun ha x hx y hy => (pK K 𝔭 k).neg_mem (ha x hx y hy)

def hermL (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    AddSubgroup (V →ₗ⋆[K] V →ₗ[K] K) where
  carrier := {s | (∀ x y, star (s x y) = s y x) ∧ ∀ x ∈ A, ∀ y ∈ A, s x y ∈ pK K 𝔭 k}
  zero_mem' := ⟨fun x y => by simp, fun x _ y _ => by simp⟩
  add_mem' := fun ha hb => ⟨fun x y => by simp [ha.1 x y, hb.1 x y],
    fun x hx y hy => (pK K 𝔭 k).add_mem (ha.2 x hx y hy) (hb.2 x hx y hy)⟩
  neg_mem' := fun ha => ⟨fun x y => by simp [ha.1 x y],
    fun x hx y hy => (pK K 𝔭 k).neg_mem (ha.2 x hx y hy)⟩

def nO (𝔭 : Ideal (𝓞 F)) (z : K) : ℕ :=
  ((pK K 𝔭 0).toAddSubgroup.map (AddMonoidHom.mulLeft z)).relIndex (pK K 𝔭 0).toAddSubgroup

end Formalism.HermitianLattices.Ext.L3.D2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsLattice K L₀ := by
    refine ⟨Submodule.fg_span_singleton _, ?_⟩
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : (1 : K) ∈ Submodule.span K (L₀ : Set K) :=
      Submodule.subset_span (Submodule.subset_span rfl)
    simpa using Submodule.smul_mem _ y h1
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀ (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem repMass_eq_prod_psi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) = c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 :=
  MassProductFormula.repMass_eq_prod_psi' hK hF hs hd S hL hLi hc

end Formalism.HermitianLattices.Ext.L3
end
end

