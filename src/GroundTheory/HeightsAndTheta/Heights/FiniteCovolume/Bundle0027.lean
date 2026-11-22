import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCentral
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] archMulAction

namespace UnipotentCentral

omit [DecidableEq ι] in

theorem pair_map {G g : Matrix ι ι ℂ} (hg : (g.map (starRingEnd ℂ))ᵀ * G * g = G)
    (a b : ι → ℂ) : star (g *ᵥ a) ⬝ᵥ (G *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (G *ᵥ b) := by
  have hg' : gᴴ * G * g = G := by
    exact hg
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hg',
    ← dotProduct_mulVec]

omit [DecidableEq ι] in

theorem pair_swap {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a b : ι → ℂ) :
    star b ⬝ᵥ (G *ᵥ a) = star (star a ⬝ᵥ (G *ᵥ b)) := by
  rw [← star_dotProduct, star_mulVec, hG.eq, dotProduct_mulVec, dotProduct_comm]

theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h0 : RationalUnipotent.Statement h)
    (h4 : UnipRadicalOfRational.Statement h v) (h6 : ImaginaryLatticeCocompact.Statement F E) :
    UnipotentCentral.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp K₁ hK₁
  obtain ⟨m, hm, hm'⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨R, hR⟩ := h6 m hm
  have HP := HermAtPlace.proof h v
  have GD := GramAtData.proof h v
  have hXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← HP w, hp.1, map_zero]
  have hYY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 := fun w => by
    rw [← HP w, hp.2.1, map_zero]
  have hXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 := fun w => by
    rw [← HP w, hp.2.2, map_one]
  have hYX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [pair_swap (GD w).1, hXY, star_one]

  let f : (InfinitePlace E → ι → ℂ) → InfinitePlace E → ℂ := fun k w =>
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) + star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2
  have hf : Continuous f := by
    refine continuous_pi fun w => ?_
    have hk : Continuous fun k : InfinitePlace E → ι → ℂ => k w := continuous_apply w
    exact (continuous_const.dotProduct (continuous_const.matrix_mulVec hk)).add
      ((hk.star.dotProduct (continuous_const.matrix_mulVec hk)).div_const 2)
  obtain ⟨B, hB⟩ := hK₁.exists_bound_of_continuousOn hf.continuousOn

  let box : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) ''
    (Set.Icc (-B) B ×ˢ Set.Icc (-R) R)
  have hbox : IsCompact box := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  let T : Set (InfinitePlace E → ℂ) := Set.univ.pi fun _ => box
  have hT : IsCompact T := isCompact_univ_pi fun _ => hbox
  let Φ : (InfinitePlace E → ι → ℂ) × (InfinitePlace E → ℂ) → InfinitePlace E → ι → ℂ :=
    fun p => p.1 + fun w => p.2 w • vecAt v x₀ w
  have hΦ : Continuous Φ := continuous_fst.add (continuous_pi fun w =>
    ((continuous_apply w).comp continuous_snd).smul continuous_const)
  refine ⟨Φ '' (K₁ ×ˢ T), (hK₁.prod hT).image hΦ, ?_⟩
  rintro n ⟨t, ht⟩
  obtain ⟨k, hkK, hku⟩ : ∃ k ∈ K₁, unipCoord h v x₀ w₀ n = k + fun w => t w • vecAt v x₀ w :=
    ⟨_, ht, (sub_add_cancel _ _).symm⟩

  have hnN := mem_unipRadical.1 n.2
  have hnU := mem_archUnitary.1 (n : archUnitary h v).2
  have hu : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = vecAt v w₀ w + (k w + t w • vecAt v x₀ w) := by
    intro w
    have e := congrFun hku w
    rw [unipCoord_apply, Pi.add_apply] at e
    rw [← e]
    abel
  have hXk : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) = 0 := by
    intro w
    have e := pair_map (hnU w) (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hnN w).1, hu w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hXX,
      mul_zero, add_zero] at e
    linear_combination e
  have hkX : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [pair_swap (GD w).1, hXk, star_zero]
  have hkY : ∀ w, star (k w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) =
      star (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w)) := fun w => pair_swap (GD w).1 _ _
  have hre : ∀ w, (t w).re = -(f k w).re := by
    intro w
    have e := pair_map (hnU w) (vecAt v w₀ w) (vecAt v w₀ w)
    rw [hu w, hYY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXY, hXk, hkX, hkY, hYY] at e
    have e2 := congrArg Complex.re e
    simp only [mul_one, mul_zero, add_zero, zero_add, Complex.add_re, Complex.zero_re,
      Complex.star_def, Complex.conj_re] at e2
    show (t w).re = -(star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ k w) +
      star (k w) ⬝ᵥ (gramAt h v w *ᵥ k w) / 2).re
    rw [Complex.add_re, Complex.div_ofNat_re]
    linarith
  have hreB : ∀ w, |(t w).re| ≤ B := fun w => by
    rw [hre w, abs_neg]
    exact (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (f k) w).trans (hB k hkK))

  obtain ⟨a, ha, hRa⟩ := hR fun w => -(t w).im
  have hcre : ∀ w : InfinitePlace E, (w.embedding ((m : E) * a)).re = 0 := by
    intro w
    have e := congrArg w.embedding ha
    rw [map_add, embedding_conj (F := F) w.embedding, map_zero, Complex.add_conj] at e
    have e2 := congrArg Complex.re e
    simp only [Complex.ofReal_re, Complex.zero_re, mul_eq_zero, two_ne_zero, false_or] at e2
    exact e2
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hm' 0 ((m : E) * a) (Submodule.zero_mem _)
    ⟨0, zero_mem _, (smul_zero _).symm⟩ ⟨a, rfl⟩
    (by rw [ha]; simp)
  have hsymm : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hp.2.2, map_one]
  have hγN : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    refine ⟨0, ?_⟩
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement, map_sub, map_sub, map_smul, map_smul, hz, hp.1, hsymm]
      simp
    have e : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) = z - h.toSesq w₀ z • x₀ := by
      have := hγz _ hz'
      rw [map_zero, LinearMap.zero_apply, zero_smul, sub_zero] at this
      exact this
    have hγx' : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    have hdec : z = h.toSesq w₀ z • x₀ + (z - h.toSesq w₀ z • x₀) := by abel
    show (γ : W ≃ₗ[E] W) z = z + (0 : E) • x₀
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hγx', e, zero_smul, add_zero]
    abel
  have hδN : archEmbed h v γ ∈ unipRadical h v x₀ := h4 x₀ γ hγx hγN
  refine ⟨⟨archEmbed h v γ, hδN⟩, ⟨⟨γ, hγLa⟩, hγx, rfl⟩, ?_⟩
  have hDU := mem_archUnitary.1 (archEmbed h v γ).2
  have hD : ∀ (x : W) (w : InfinitePlace E),
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w = vecAt v (γ • x) w := fun x w => by
    rw [← archSmul_apply, archEmbed_smul_vecAt]
  have hDY : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + w.embedding ((m : E) * a) • vecAt v x₀ w := by
    intro w
    rw [hD, hγw]
    funext i
    simp [vecAt]
  have hDX : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w := fun w => by rw [hD, hγx]
  have hDk : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ k w = k w := by
    intro w
    obtain ⟨b, hb⟩ := (mem_unipRadical.1 hδN w).2 (k w) (hXk w)
    have e := pair_map (hDU w) (vecAt v w₀ w) (k w)
    rw [hb, hDY w] at e
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, star_add, star_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hXX, hYX, hXk] at e
    have hb0 : b = 0 := by linear_combination e
    rw [hb, hb0, zero_smul, add_zero]
  have hcoord : unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδN⟩ * n) =
      Φ (k, fun w => t w + w.embedding ((m : E) * a)) := by
    funext w
    rw [unipCoord_apply]
    change ((((archEmbed h v γ : archUnitary h v) * (n : archUnitary h v) : archUnitary h v) :
      InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w - vecAt v w₀ w =
      k w + (t w + w.embedding ((m : E) * a)) • vecAt v x₀ w
    rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, hu w, mulVec_add,
      mulVec_add, mulVec_smul, hDY w, hDX w, hDk w, add_smul]
    abel
  rw [hcoord]
  refine Set.mem_image_of_mem Φ ⟨hkK, fun w _ => ?_⟩
  refine ⟨((t w + w.embedding ((m : E) * a)).re, (t w + w.embedding ((m : E) * a)).im),
    ⟨?_, ?_⟩, Complex.re_add_im (t w + w.embedding ((m : E) * a))⟩
  · rw [Complex.add_re, hcre w, add_zero]
    exact abs_le.1 (hreB w)
  · rw [Complex.add_im]
    have := abs_le.1 (hRa w)
    constructor <;> linarith [this.1, this.2]

end UnipotentCentral

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentHorizontal
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem archUnitary_preserves_form (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) (w : InfinitePlace E) (a b : ι → ℂ) :
    star (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ a) ⬝ᵥ
        (gramAt h v w *ᵥ (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ b)) =
      star a ⬝ᵥ (gramAt h v w *ᵥ b) := by
  have := ArchInvariant.proof h v g⁻¹ (fun _ => a) (fun _ => b) w
  simpa only [invApply, inv_inv] using this

theorem UnipotentHorizontal.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h0 : RationalUnipotent.Statement h) (h4 : UnipRadicalOfRational.Statement h v)
    (h5 : ComplementArchCocompact.Statement h v) : UnipotentHorizontal.Statement h v := by
  intro D La x₀ w₀ hD hx₀ hp
  obtain ⟨m, hm, hγ⟩ := h0 D La x₀ w₀ hD hx₀ hp
  obtain ⟨K5, hK5, hK⟩ := h5 La x₀ w₀ (2 * m) hD.isLattice hp (by omega)
  refine ⟨-K5, hK5.neg, fun n => ?_⟩
  obtain ⟨hxx, -, hxw⟩ := hp
  have hwx : h.toSesq w₀ x₀ = 1 := by
    rw [← LinearMap.isSymm_def.mp h.isSymm x₀ w₀, hxw, map_one]
  have hH := HermAtPlace.proof h v
  have bXX : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← hH, hxx, map_zero]
  have bWX : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 1 := fun w => by
    rw [← hH, hwx, map_one]
  have hn := mem_unipRadical.1 n.2

  obtain ⟨u, hu⟩ : ∃ u, u = unipCoord h v x₀ w₀ n := ⟨_, rfl⟩
  have bXu : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) = 0 := fun w => by
    have e := archUnitary_preserves_form h v n w (vecAt v x₀ w) (vecAt v w₀ w)
    rw [(hn w).1] at e
    rw [hu, unipCoord_apply, mulVec_sub, dotProduct_sub, e, sub_self]
  obtain ⟨t0, ht0⟩ : ∃ t0 : InfinitePlace E → ℂ,
      ∀ w, t0 w = star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ u w) := ⟨fun _ => _, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : InfinitePlace E → ι → ℂ,
      ∀ w, Y w = u w - t0 w • vecAt v x₀ w := ⟨fun _ => _, fun _ => rfl⟩
  have bXY : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bXu, bXX, smul_zero,
      sub_zero]
  have bWY : ∀ w, star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w) = 0 := fun w => by
    rw [hY, mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, bWX, ← ht0, smul_eq_mul,
      mul_one, sub_self]

  obtain ⟨y, hyW, ⟨z, hzLa, hyz⟩, hyK⟩ := hK (-Y) fun w => by
    simp only [Pi.neg_apply, mulVec_neg, dotProduct_neg, neg_eq_zero]
    exact ⟨bXY w, bWY w⟩
  have hzz : h.toSesq z z ∈ integralClosure ℤ E := hD.integral z hzLa z hzLa
  have hzzc : conj F E (h.toSesq z z) = h.toSesq z z := LinearMap.isSymm_def.mp h.isSymm z z
  let a : 𝓞 E := -((2 * m : ℕ) : 𝓞 E) * ⟨h.toSesq z z, hzz⟩
  have haE : (a : E) = -((2 * m : ℕ) : E) * h.toSesq z z := by
    have h2 : (((2 * m : ℕ) : 𝓞 E) : E) = ((2 * m : ℕ) : E) :=
      map_natCast (algebraMap (𝓞 E) E) (2 * m)
    rw [show (a : E) = -(((2 * m : ℕ) : 𝓞 E) : E) * h.toSesq z z from rfl, h2]
  let c : E := (m : E) * (a : E)
  have hyy : h.toSesq y y = ((2 * m : ℕ) : E) * ((2 * m : ℕ) : E) * h.toSesq z z := by
    rw [hyz]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hc : c + conj F E c = -h.toSesq y y := by
    simp only [c, hyy, haE, map_mul, map_neg, map_natCast, hzzc]
    push_cast
    ring
  obtain ⟨γ, hγLa, hγx, hγw, hγz⟩ := hγ y c hyW
    ⟨2 • z, nsmul_mem hzLa 2, by rw [hyz, smul_smul, mul_comm]⟩ ⟨a, rfl⟩ hc

  have hgood : ∀ z : W, h.toSesq x₀ z = 0 → ∃ b : E, γ • z = z + b • x₀ := by
    intro z hz
    have hz' : z - h.toSesq w₀ z • x₀ ∈ hypComplement h x₀ w₀ := by
      rw [mem_hypComplement]
      constructor
      · rw [map_sub, map_smul, hz, hxx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hwx, smul_eq_mul, mul_one, sub_self]
    refine ⟨-h.toSesq y (z - h.toSesq w₀ z • x₀), ?_⟩
    have e : (γ : W ≃ₗ[E] W) z = (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) +
        h.toSesq w₀ z • (γ : W ≃ₗ[E] W) x₀ := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    have e1 : (γ : W ≃ₗ[E] W) (z - h.toSesq w₀ z • x₀) =
        (z - h.toSesq w₀ z • x₀) - h.toSesq y (z - h.toSesq w₀ z • x₀) • x₀ := hγz _ hz'
    have e2 : (γ : W ≃ₗ[E] W) x₀ = x₀ := hγx
    change (γ : W ≃ₗ[E] W) z = _
    rw [e, e1, e2, neg_smul]
    abel
  have hδ := h4 x₀ γ hγx hgood
  have hδw := mem_unipRadical.1 hδ
  have hs : ∀ w, ∃ s : ℂ, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ Y w = Y w + s • vecAt v x₀ w := fun w => (hδw w).2 (Y w) (bXY w)
  choose s hs using hs
  refine ⟨⟨archEmbed h v γ, hδ⟩, Subgroup.mem_map.2 ⟨⟨γ, hγLa⟩, MulAction.mem_stabilizer_iff.2 hγx,
    rfl⟩, fun w => w.embedding c + t0 w + s w, ?_⟩
  have hprod : ∀ w, unipCoord h v x₀ w₀ (⟨archEmbed h v γ, hδ⟩ * n) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        ((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w) -
          vecAt v w₀ w := fun w => by
    rw [unipCoord_apply, Matrix.mulVec_mulVec]
    rfl
  have hdW : ∀ w, (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v w₀ w = vecAt v w₀ w + vecAt v y w + w.embedding c • vecAt v x₀ w :=
    fun w => by
      rw [← vecAt_unitary, show (γ : W ≃ₗ[E] W) w₀ = γ • w₀ from rfl, hγw, StabilizerLevi.vecAt_add,
        StabilizerLevi.vecAt_add, StabilizerLevi.vecAt_smul]
  have hgW : ∀ w, (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      vecAt v w₀ w = u w + vecAt v w₀ w := fun w => by
    rw [hu, unipCoord_apply, sub_add_cancel]
  have huY : ∀ w, u w = Y w + t0 w • vecAt v x₀ w := fun w => by rw [hY, sub_add_cancel]
  rw [Set.mem_neg]
  convert hyK using 1
  funext w
  simp only [Pi.neg_apply, Pi.sub_apply, hprod w, hgW w, huY w, mulVec_add, mulVec_smul, hs w,
    (hδw w).1, hdW w, add_smul]
  abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulus
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisForm (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    LinearMap.BilinForm ℝ (heisY h v x₀ w₀) :=
  LinearMap.mk₂ ℝ (fun y z => ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re)
    (fun y y' z => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_left, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_left,
        Complex.conj_ofReal, Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])
    (fun y z z' => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_right, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_right,
        Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem heisForm_apply (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re := rfl

theorem heisForm_comm (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hH, -⟩ := hyperbolic_at_place h v hp w
  rw [← hForm_conj hH, Complex.conj_re]

theorem heisForm_nondegenerate (hp : IsHyperbolicPair h x₀ w₀) :
    (heisForm h v x₀ w₀).Nondegenerate := by
  classical
  have left : ∀ y : heisY h v x₀ w₀, (∀ z, heisForm h v x₀ w₀ y z = 0) → y = 0 := by
    intro y hy
    apply Subtype.ext
    funext w
    change (y : InfinitePlace E → ι → ℂ) w = 0
    obtain ⟨hH, hd, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
    have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
      rw [← hForm_conj hH, hab, map_one]
    apply eq_zero_of_hForm hd
    intro z
    set q := z - hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w -
      hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w with hq
    have hqa : hForm (gramAt h v w) (vecAt v x₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, ha, hab]
      ring
    have hqb : hForm (gramAt h v w) (vecAt v w₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, hb, hba]
      ring
    have key : ∀ c : ℂ, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (c • q)).re = 0 := by
      intro c
      have hmem : (Pi.single w (c • q) : InfinitePlace E → ι → ℂ) ∈ heisY h v x₀ w₀ := by
        intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [Pi.single_eq_same, hForm_smul_right, hqa, hqb, mul_zero, and_self]
        · simp only [Pi.single_eq_of_ne hw, hForm_zero_right, and_self]
      have := hy ⟨_, hmem⟩
      rw [heisForm_apply, Finset.sum_eq_single w] at this
      · simpa using this
      · intro w' _ hw
        simp [Pi.single_eq_of_ne hw, hForm_zero_right]
      · simp
    have h1 := key 1
    have h2 := key Complex.I
    rw [hForm_smul_right, one_mul] at h1
    rw [hForm_smul_right, Complex.I_mul_re, neg_eq_zero] at h2
    have hyq : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) q = 0 := Complex.ext h1 h2
    have hya : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v x₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).1, map_zero]
    have hyb : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).2, map_zero]
    have hz : z = q + hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w +
        hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w := by
      rw [hq]
      abel
    rw [hz, hForm_add_right, hForm_add_right, hForm_smul_right, hForm_smul_right, hyq, hya, hyb]
    ring
  exact ⟨left, fun y hy => left y fun z => by rw [heisForm_comm hp]; exact hy z⟩

theorem heisForm_heisConjLin (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heisConjLin_apply, heisConjLin_apply, hForm_mulVec_of_unitary _ (archUnitary_at_place g w)]

end Form

theorem UnipotentModulus.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentModulus.Statement h v := by
  intro x₀ w₀ hp μ _ g hg
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (unipRadical h v x₀ : Set (archUnitary h v))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set G := heisConjLin g hg with hG
  set c : unipRadical h v x₀ → unipRadical h v x₀ := fun n => φ ((G (φ.symm n).1, (φ.symm n).2))
    with hcdef
  have hc : ∀ n, ((c n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_conj hp g hg _).symm
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hcm : Measurable c :=
    (φ.continuous.comp ((hGc.comp (continuous_fst.comp φ.symm.continuous)).prodMk
      (continuous_snd.comp φ.symm.continuous))).measurable
  have hmap : (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) =
      Subtype.val ∘ c := by
    funext n
    exact (hc n).symm
  have hGm : MeasurePreserving G Measure.addHaar Measure.addHaar :=
    measurePreserving_of_preserves_bilin _ (heisForm h v x₀ w₀) (heisForm_nondegenerate hp) G
      (heisForm_heisConjLin g hg)
  have hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam := by
    have e : (fun x => φ.symm (c (φ x))) = Prod.map G id := by
      funext x
      simp only [hcdef, Homeomorph.symm_apply_apply, Prod.map, id]
    rw [e]
    exact hGm.prod (MeasurePreserving.id volume)
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  rw [hmap, ← Measure.map_map continuous_subtype_val.measurable hcm,
    map_eq_of_measurePreserving_coordinates lam φ hL c hC μ]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

