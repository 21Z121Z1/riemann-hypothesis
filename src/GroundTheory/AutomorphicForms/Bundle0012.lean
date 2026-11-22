import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinHaar
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.HermitianWitt
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.AutomorphicForms.UnitarySplit
import GroundTheory.AutomorphicForms.Bundle0005

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinHaarDensity
section
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

theorem exists_smooth_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2) := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hsmooth : (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) := by
    intro g
    rw [h.contMDiffAt_iff_expG]
    have hcont : Continuous (fun Y : 𝔤 => g * h.expG Y) :=
      continuous_const.mul h.continuous_expG
    have hg0 : g * h.expG 0 = g := by rw [h.expG_zero, mul_one]
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      have hz₀r : z₀ ∈ ball (0 : Fin d → ℝ) r := hεr hz₀
      obtain ⟨hgW, hcg⟩ := hPW z₀ hz₀r
      have hev : (fun Y : 𝔤 => κ (P z₀ * h.expG Y)) =ᶠ[𝓝 0]
          fun Y => K (c (P z₀ * h.expG Y)) * (((ρ (c (P z₀ * h.expG Y)))⁻¹ : ℝ) : ℂ) := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), P z₀ * h.expG Y ∈ W := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hW.mem_nhds hgW)
        filter_upwards [this] with Y hY
        simp [κ, indicator_of_mem hY]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hc0 := hc (P z₀) hgW
      have hρ0 : ρ (c (P z₀ * h.expG 0)) ≠ 0 := by
        rw [hg0, hcg]; exact (hρpos z₀ hz₀r).ne'
      exact (hK.contDiffAt.comp _ hc0).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ ((hρ.contDiffAt.comp _ hc0).inv hρ0))
    · have hev : (fun Y : 𝔤 => κ (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
        have : ∀ᶠ Y in 𝓝 (0 : 𝔤), g * h.expG Y ∈ Cᶜ := by
          have := hcont.continuousAt (x := 0)
          rw [ContinuousAt, hg0] at this
          exact this (hCc.isClosed.isOpen_compl.mem_nhds hg)
        filter_upwards [this] with Y hY
        exact hκC _ hY
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hκc : Continuous κ := by
    let := h.chartedSpace
    exact hsmooth.continuous
  refine ⟨κ, hsmooth, HasCompactSupport.intro hCc hκC, fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HermitianDisc
section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix GroundTheory.LocalField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem gram_basis_change {ι : Type*} [Fintype ι] (B : V →ₛₗ[conjHom F E] V →ₗ[E] E)
    (b c : Basis ι E V) :
    gram B c = ((b.toMatrix c).map (conjHom F E))ᵀ * gram B b * b.toMatrix c := by
  ext i j
  rw [gram_apply, sesq_eq_sum B b]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, Basis.toMatrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

namespace HermitianForm

variable [Algebra.IsSeparable F E]

theorem det_gram_mem_range (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : (gram h.toSesq b).det ∈ Set.range (algebraMap F E) := by
  apply conj_eq_self_iff.1
  rw [← conjHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← det_transpose,
    isHermitianFor_gram h b]

def detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : Fˣ :=
  Units.mk0 (h.det_gram_mem_range b).choose (by
    intro h0
    have := (h.det_gram_mem_range b).choose_spec
    rw [h0, map_zero] at this
    exact (isUnit_det_gram h b).ne_zero this.symm)

theorem algebraMap_detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : algebraMap F E (h.detUnit b) = (gram h.toSesq b).det :=
  (h.det_gram_mem_range b).choose_spec

theorem detUnit_eq_of_det_eq (h : HermitianForm F E V) (h' : HermitianForm F E V')
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι E V) (b' : Basis ι' E V')
    (hb : (gram h.toSesq b).det = (gram h'.toSesq b').det) : h.detUnit b = h'.detUnit b' := by
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, algebraMap_detUnit, hb]

theorem detUnit_basis_change (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι E V) :
    ∃ u : Eˣ, h.detUnit c = h.detUnit b * normUnits F E u := by
  have hM : IsUnit (b.toMatrix c).det := by
    exact IsUnit.of_mul_eq_one (c.toMatrix b).det
      (by rw [← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one])
  refine ⟨hM.unit, Units.ext ((algebraMap F E).injective ?_)⟩
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, coe_normUnits,
    IsUnit.unit_spec, ← mul_conj, gram_basis_change h.toSesq b c, det_mul, det_mul,
    det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, conjHom_apply]
  ring

def disc [FiniteDimensional E V] (h : HermitianForm F E V) : Fˣ ⧸ (normUnits F E).range :=
  QuotientGroup.mk (h.detUnit (Module.finBasis E V))

theorem disc_eq [FiniteDimensional E V] (h : HermitianForm F E V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι E V) : h.disc = QuotientGroup.mk (h.detUnit b) := by
  have hcard : Fintype.card ι = Fintype.card (Fin (finrank E V)) := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  set e : ι ≃ Fin (finrank E V) := Fintype.equivOfCardEq hcard
  have h1 : h.detUnit (b.reindex e) = h.detUnit b := by
    apply detUnit_eq_of_det_eq
    have : gram h.toSesq (b.reindex e) = (gram h.toSesq b).submatrix e.symm e.symm := by
      ext i j; simp [gram_apply, Basis.reindex_apply]
    rw [this, det_submatrix_equiv_self]
  obtain ⟨u, hu⟩ := h.detUnit_basis_change (Module.finBasis E V) (b.reindex e)
  rw [disc, ← h1, hu]
  exact QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨u, by rw [inv_mul_cancel_left]⟩)

theorem Isometric.disc_eq [FiniteDimensional E V] [FiniteDimensional E V']
    {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    h.disc = h'.disc := by
  obtain ⟨e, he⟩ := H
  set b := Module.finBasis E V
  rw [h.disc_eq b, h'.disc_eq (b.map e)]
  congr 1
  apply detUnit_eq_of_det_eq
  congr 1
  ext i j
  simp only [gram_apply, Basis.map_apply, he]

theorem disc_prod [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') : (h.prod h').disc = h.disc * h'.disc := by
  set b := Module.finBasis E V
  set b' := Module.finBasis E V'
  rw [(h.prod h').disc_eq (b.prod b'), h.disc_eq b, h'.disc_eq b', ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, algebraMap_detUnit]
  have : gram (h.prod h').toSesq (b.prod b') =
      fromBlocks (gram h.toSesq b) 0 0 (gram h'.toSesq b') := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [gram_apply, Basis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply] <;>
      rw [prod_apply] <;>
      simp only [LinearMap.map_zero, LinearMap.zero_apply, add_zero, zero_add]
  rw [this, det_fromBlocks_zero₂₁]

theorem disc_ofUnit (a : Fˣ) : (ofUnit (E := E) a).disc = QuotientGroup.mk a := by
  rw [disc_eq _ (Basis.singleton (Fin 1) E)]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_unique, gram_apply, Basis.singleton_apply, ofUnit_apply, map_one,
    one_mul, mul_one]

theorem disc_of_finrank_eq_zero [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : finrank E V = 0) : h.disc = 1 := by
  have : IsEmpty (Fin (finrank E V)) := by rw [hV]; infer_instance
  rw [disc]
  convert QuotientGroup.mk_one (normUnits F E).range
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_isEmpty, Units.val_one, map_one]

end HermitianForm

def diagForm {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    HermitianForm F E (ι → E) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => ∑ i, conj F E (x i) * algebraMap F E (a i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj,
      conj_algebraMap]
    exact Finset.sum_congr rfl fun i _ => by ring⟩
  nonsingular := by
    have ha : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simp
    have key : ∀ (x : ι → E) (j : ι),
        (∑ i, conj F E (x i) * algebraMap F E (a i) * (Pi.single j 1 : ι → E) i) =
          conj F E (x j) * algebraMap F E (a j) := by
      intro x j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_apply, hij]
      · simp
    constructor
    · intro x y hxy
      funext j
      have h1 := LinearMap.congr_fun hxy (Pi.single j 1)
      simp only [LinearMap.mk₂'ₛₗ_apply, key] at h1
      have h2 := mul_right_cancel₀ (ha j) h1
      rw [← conj_conj (F := F) (x j), h2, conj_conj]
    · intro f
      refine ⟨fun j => conj F E (f (Pi.single j 1) * (algebraMap F E (a j))⁻¹),
        LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [this, smul_eq_mul]
      field_simp [ha i]

theorem diagForm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) (x y : ι → E) :
    (diagForm (E := E) a).toSesq x y = ∑ i, conj F E (x i) * algebraMap F E (a i) * y i := rfl

end GroundTheory.Automorphic

end
end

-- bundled from GroundTheory.AutomorphicForms.HermitianSplit
section
namespace GroundTheory.Automorphic

open Module Matrix

variable {F : Type*} [Field F]
variable {V V' : Type*} [AddCommGroup V] [Module (F × F) V] [AddCommGroup V'] [Module (F × F) V']

theorem map_fst_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.fst F F) = M.map (RingHom.snd F F) := by
  ext i j
  show (conj F (F × F) (M i j)).1 = (M i j).2
  rw [conj_prod]

theorem map_snd_map_conjHom_prod {ι : Type*} (M : Matrix ι ι (F × F)) :
    (M.map (conjHom F (F × F))).map (RingHom.snd F F) = M.map (RingHom.fst F F) := by
  ext i j
  show (conj F (F × F) (M i j)).2 = (M i j).1
  rw [conj_prod]

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HermitianWittExtension
section
noncomputable section

namespace GroundTheory.Automorphic

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

theorem exists_isotropic_partner (h : HermitianForm F E V) (U : Submodule E V) {r : V}
    (hrU : r ∈ U) (hr : ∀ u ∈ U, h.toSesq r u = 0) (μ : U →ₗ[E] E) (hμ : μ ⟨r, hrU⟩ = 1) :
    ∃ s : V, (∀ u : U, h.toSesq s u = μ u) ∧ h.toSesq s s = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend μ
  obtain ⟨s₀, hs₀⟩ := h.nonsingular.2 g
  have hs₀u : ∀ u : U, h.toSesq s₀ u = μ u := fun u => by
    rw [hs₀, ← hg]
    rfl
  obtain ⟨e₀, he₀⟩ := h.toSesq_self_mem_range s₀
  obtain ⟨c, hc⟩ := exists_trace_eq_one (F := F) (E := E)
  have hc1 : c + conj F E c = 1 := by rw [add_conj, hc, map_one]
  refine ⟨s₀ + (-(c * algebraMap F E e₀)) • r, fun u => ?_, ?_⟩
  · rw [map_add, LinearMap.add_apply, h.toSesq_smul_left, hr u u.2, mul_zero, add_zero, hs₀u]
  · have h1 : h.toSesq s₀ r = 1 := by rw [← hμ, ← hs₀u]
    have h2 : h.toSesq r s₀ = 1 := by rw [← h.conj_toSesq, h1, map_one]
    have h3 : h.toSesq r r = 0 := hr r hrU
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, h1, h2, h3]
    rw [← he₀, map_neg, map_mul, conj_algebraMap]
    linear_combination (-(algebraMap F E e₀)) * hc1

theorem exists_extend [FiniteDimensional E V] (h : HermitianForm F E V) (U : Submodule E V)
    (f : U →ₗ[E] V) (hf : Function.Injective f)
    (hfh : ∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x := by
  suffices key : ∀ d : ℕ, ∀ (U : Submodule E V) (f : U →ₗ[E] V),
      finrank E V - finrank E U = d → Function.Injective f →
      (∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) →
      ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x from
    key _ U f rfl hf hfh
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro U f hd hf hfh
  by_cases hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0
  · obtain ⟨g, hg, hgf⟩ := h.exists_extend_of_nondegenerate hU (LinearEquiv.ofInjective f hf)
      (fun x y => by simp only [LinearEquiv.ofInjective_apply]; exact hfh x y)
    exact ⟨g, hg, fun x => by rw [hgf, LinearEquiv.ofInjective_apply]⟩
  push Not at hU
  obtain ⟨r, hrU, hr, hr0⟩ := hU

  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual E U, φ ⟨r, hrU⟩ ≠ 0 := by
    by_contra H
    push Not at H
    exact hr0 (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff E _).1 H))
  set μ : U →ₗ[E] E := (φ ⟨r, hrU⟩)⁻¹ • φ with hμ_def
  have hμ : μ ⟨r, hrU⟩ = 1 := by
    rw [hμ_def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  obtain ⟨s, hs, hss⟩ := h.exists_isotropic_partner U hrU hr μ hμ

  set e := LinearEquiv.ofInjective f hf with he_def
  have he : ∀ x : U, ((e x : LinearMap.range f) : V) = f x := fun x =>
    LinearEquiv.ofInjective_apply _ _
  have hr₂ : ∀ u ∈ LinearMap.range f, h.toSesq (f ⟨r, hrU⟩) u = 0 := by
    rintro _ ⟨u, rfl⟩
    rw [hfh]
    exact hr u u.2
  have hrr : (⟨f ⟨r, hrU⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f) = e ⟨r, hrU⟩ :=
    Subtype.ext (he _).symm
  obtain ⟨s', hs', hss'⟩ := h.exists_isotropic_partner (LinearMap.range f)
    (LinearMap.mem_range_self f ⟨r, hrU⟩) hr₂ (μ ∘ₗ (e.symm : LinearMap.range f →ₗ[E] U))
    (by rw [LinearMap.comp_apply, hrr, LinearEquiv.coe_coe, e.symm_apply_apply, hμ])
  have hs'' : ∀ x : U, h.toSesq s' (f x) = μ x := by
    intro x
    have := hs' (e x)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, he] at this

  have hsU : s ∉ U := by
    intro hsU
    have h1 := hr s hsU
    have h2 : h.toSesq s r = 1 := by rw [← hμ, ← hs]
    rw [← h.conj_toSesq, h2, map_one] at h1
    exact one_ne_zero h1

  set ψ : (U × E) →ₗ[E] V := U.subtype.coprod (LinearMap.toSpanSingleton E V s) with hψ_def
  have hψ : ∀ (u : U) (a : E), ψ (u, a) = u + a • s := fun u a => by
    simp [hψ_def]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hψ] at hp
    by_cases ha : a = 0
    · subst ha
      rw [zero_smul, add_zero] at hp
      rw [Submodule.coe_eq_zero.1 hp]
      rfl
    · exfalso
      apply hsU
      have h2 : a • s = -(u : V) := eq_neg_of_add_eq_zero_right hp
      have : s = a⁻¹ • -(u : V) := by rw [← h2, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
  set f₀ : (U × E) →ₗ[E] V := f.coprod (LinearMap.toSpanSingleton E V s') with hf₀_def
  have hf₀ : ∀ (u : U) (a : E), f₀ (u, a) = f u + a • s' := fun u a => by
    simp [hf₀_def]
  have hL : ∀ (u v : U) (a b : E), h.toSesq (f u + a • s') (f v + b • s') =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hfh, hss']
    rw [← h.conj_toSesq s' (f u), hs'' u, hs'' v]
    ring
  have hR : ∀ (u v : U) (a b : E), h.toSesq ((u : V) + a • s) ((v : V) + b • s) =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hss]
    rw [← h.conj_toSesq s (u : V), hs u, hs v]
    ring
  have hf₀inj : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hf₀] at hp
    have ha : a = 0 := by
      have h1 := congrArg (h.toSesq (f ⟨r, hrU⟩)) hp
      rw [map_add, h.toSesq_smul_right, hfh, hr u u.2, zero_add, map_zero,
        ← h.conj_toSesq s', hs'', hμ, map_one, mul_one] at h1
      exact h1
    subst ha
    rw [zero_smul, add_zero] at hp
    have hu : u = 0 := hf (by rw [hp, map_zero])
    rw [hu]
    rfl
  set e' := LinearEquiv.ofInjective ψ hψinj with he'_def
  have he' : ∀ p : U × E, ((e' p : LinearMap.range ψ) : V) = ψ p := fun p =>
    LinearEquiv.ofInjective_apply _ _
  set f' : LinearMap.range ψ →ₗ[E] V := f₀ ∘ₗ (e'.symm : LinearMap.range ψ →ₗ[E] U × E)
  have hf'inj : Function.Injective f' := hf₀inj.comp e'.symm.injective
  have hf'h : ∀ x y : LinearMap.range ψ, h.toSesq (f' x) (f' y) = h.toSesq x y := by
    intro x y
    obtain ⟨⟨u, a⟩, rfl⟩ := e'.surjective x
    obtain ⟨⟨v, b⟩, rfl⟩ := e'.surjective y
    simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply]
    rw [he', he', hf₀, hf₀, hψ, hψ, hL, hR]
  have hdim : finrank E (LinearMap.range ψ) = finrank E U + 1 := by
    rw [LinearMap.finrank_range_of_inj hψinj, Module.finrank_prod, Module.finrank_self]
  have hle : finrank E (LinearMap.range ψ) ≤ finrank E V := Submodule.finrank_le _
  obtain ⟨g, hg, hgf⟩ := ih (finrank E V - finrank E (LinearMap.range ψ)) (by omega)
    (LinearMap.range ψ) f' rfl hf'inj hf'h
  refine ⟨g, hg, fun u => ?_⟩
  have h1 := hgf (e' (u, 0))
  rw [he', hψ, zero_smul, add_zero] at h1
  rw [h1]
  simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply, hf₀, zero_smul,
    add_zero]

end HermitianForm

end GroundTheory.Automorphic

end
end

