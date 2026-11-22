import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0551
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
section
noncomputable section

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem trace_trProj (hr : r ≠ 0) (Y : Matrix (Fin r) (Fin r) E) : (trProj Y).trace = 0 := by
  have : (r : E) ≠ 0 := by exact_mod_cast hr
  simp only [trProj, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  field_simp; ring

theorem cc_trace_of_isSkew {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) : cc Z.trace = -Z.trace := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [← h7, (h8 Z).1 hZ, trace_neg]

theorem isSkew_sub_smul {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : IsSkew G Z) {c : E} (hc : cc c = -c) : IsSkew G (Z - c • 1) := by
  obtain ⟨-, -, h3, h4, h5, -, -, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h8, sub_eq_add_neg, h3, ← neg_smul, h4, h5, (h8 Z).1 hZ]
  have e : cc (-c) = c := by simp only [cc, map_neg] at hc ⊢; rw [hc, neg_neg]
  rw [e, neg_add, neg_smul, neg_neg]

theorem cc_trace_div {Z : Matrix (Fin r) (Fin r) E} (h : cc Z.trace = -Z.trace) :
    cc (Z.trace / r) = -(Z.trace / r) := by
  simp only [cc, map_div₀, map_natCast] at h ⊢
  rw [h, neg_div]

theorem trProj_mem_dualLie (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) : trProj Z ∈ dualLie G Λ := by
  refine ⟨trace_trProj hr Z, isSkew_sub_smul hS.1 hS.2.1 hZ.1 (cc_trace_div
    (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)), fun X hX => ?_⟩
  have h1 : (X * trProj Z).trace = (X * Z).trace := by
    simp only [trProj, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, trace_sub, trace_smul, hX.1,
      smul_zero, sub_zero]
  rw [h1]
  exact GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hX.2.2 hZ.2)

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hAdj_sub {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (Y Z : Matrix (Fin r) (Fin r) E) : hAdj G (Y - Z) = hAdj G Y - hAdj G Z := by
  obtain ⟨-, -, h3, h4, -, -, -, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [sub_eq_add_neg, h3, ← neg_one_smul E Z, h4, sub_eq_add_neg, ← neg_one_smul E (hAdj G Z)]
  congr 2
  simp [cc]

theorem trace_mul_hAdj {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Y : Matrix (Fin r) (Fin r) E} (hY : IsSkew G Y) (W : Matrix (Fin r) (Fin r) E) :
    (Y * hAdj G W).trace = -cc (Y * W).trace := by
  obtain ⟨-, h2, -, -, -, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  have hY' : Y = -hAdj G Y := by rw [(h8 Y).1 hY, neg_neg]
  conv_lhs => rw [hY']
  rw [Matrix.neg_mul, ← h2, trace_neg, h7, trace_mul_comm W Y]

theorem isIntegral_trace_mul_of_trace_eq_zero (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ endLat Λ) (hZ0 : Z.trace = 0) :
    IsIntegral ℤ (Y * Z).trace := by
  obtain ⟨-, -, -, h4, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  refine GlobalTheory.T.integral_of_trace_integral_unramified E hU _ fun a ha => ?_
  set X := a • Z - hAdj G (a • Z) with hXdef
  have hX : X ∈ lieLat G Λ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [trace_sub, h7, trace_smul, hZ0, smul_zero, sub_eq_zero]; simp [cc]
    · show IsSkew G X
      rw [h8, hXdef, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
    · exact (endLat Λ).sub_mem (smul_mem_endLat ha hZ) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat ha hZ))
  have h := hY.2.2 X hX
  rw [trace_mul_comm, hXdef, Matrix.mul_sub, trace_sub, trace_mul_hAdj hS.1 hS.2.1 hY.2.1,
    Matrix.mul_smul, trace_smul, smul_eq_mul, sub_neg_eq_add] at h
  convert h using 2 <;> ring_nf

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem trace_hAdj_one {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    {Z : Matrix (Fin r) (Fin r) E} (hZ : Z.trace = 1) : (hAdj G Z).trace = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hG hd
  rw [h7, hZ]; simp [cc]

theorem exists_skewLat_trProj_eq (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) {Y : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ dualLie G Λ) : ∃ Z ∈ skewLat G Λ, trProj Z = Y := by
  obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  set c₀ := -(Y * Z₁).trace with hc₀

  have hb : ∀ Z ∈ endLat Λ, IsIntegral ℤ ((Y * Z).trace + c₀ * Z.trace) := by
    intro Z hZ
    have hZt := GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ
    have hm : Z - Z.trace • Z₁ ∈ endLat Λ := (endLat Λ).sub_mem hZ (smul_mem_endLat hZt hZ₁)
    have h0 : (Z - Z.trace • Z₁).trace = 0 := by
      rw [trace_sub, trace_smul, hZ₁1, smul_eq_mul, mul_one, sub_self]
    have := isIntegral_trace_mul_of_trace_eq_zero hU hS hY hm h0
    rw [Matrix.mul_sub, Matrix.mul_smul, trace_sub, trace_smul, smul_eq_mul] at this
    convert this using 1; rw [hc₀]; ring

  have hs : IsIntegral ℤ (c₀ + cc c₀) := by
    have := hb _ (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ Z₁ hS hZ₁)
    rw [trace_mul_hAdj hS.1 hS.2.1 hY.2.1, trace_hAdj_one hS.1 hS.2.1 hZ₁1, mul_one] at this
    convert this using 1
    rw [hc₀]; simp only [cc, map_neg]; ring
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  set s := c₀ + cc c₀ with hsdef
  set c := c₀ - s * t with hcdef
  have hccs : cc s = s := by rw [hsdef]; simp only [cc, map_add, IsCMField.complexConj_apply_apply]; ring
  have hcc : cc c = -c := by
    have e1 : cc c = cc c₀ - s * cc t := by
      rw [hcdef]; simp only [cc, map_sub, map_mul] at hccs ⊢; rw [hccs]
    rw [e1, hcdef]
    have e2 : cc t = 1 - t := by rw [← ht1]; ring
    rw [e2, hsdef]; ring
  refine ⟨Y + c • 1, ⟨?_, ?_⟩, ?_⟩
  · rw [h8, h3, h4, h5, (h8 Y).1 hY.2.1, hcc, neg_add, neg_smul]
  · refine GlobalTheory.T.mem_end_lattice_of_trace_dual E r G Λ _ hS fun Z hZ => ?_
    have e : ((Y + c • 1) * Z).trace = ((Y * Z).trace + c₀ * Z.trace) - s * t * Z.trace := by
      rw [Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, hcdef]; ring
    rw [e]
    exact (hb Z hZ).sub ((hs.mul ht).mul (GlobalTheory.T.end_lattice_trace_integral E r G Λ Z hS hZ))
  · have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
    simp only [trProj, trace_add, hY.1, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, zero_add]
    rw [mul_div_assoc, div_self hrE, mul_one, add_sub_cancel_right]

end GlobalTheory.LieDisc

namespace GlobalTheory.LieDisc
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def trProjHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    skewLat G Λ →+ Matrix (Fin r) (Fin r) E where
  toFun Z := trProj (Z : Matrix (Fin r) (Fin r) E)
  map_zero' := by simp [trProj]
  map_add' Y Z := by
    simp only [trProj, AddSubgroup.coe_add, trace_add, add_div, add_smul]; abel

def traceHom (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : skewLat G Λ →+ E where
  toFun Z := (Z : Matrix (Fin r) (Fin r) E).trace
  map_zero' := by simp
  map_add' Y Z := by simp [trace_add]

theorem trProj_mem_lieLat_iff (hr : r ≠ 0) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {Z : Matrix (Fin r) (Fin r) E} (hZ : Z ∈ skewLat G Λ) :
    trProj Z ∈ lieLat G Λ ↔ Z.trace ∈ AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E) := by
  have hrE : (r : E) ≠ 0 := by exact_mod_cast hr
  have hD := trProj_mem_dualLie hr hS hZ
  constructor
  · intro h
    have hm : (Z.trace / r) • (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ := by
      have := (endLat Λ).sub_mem hZ.2 h.2.2
      simpa [trProj] using this
    obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
    have hi : IsIntegral ℤ (Z.trace / r) := by
      have := GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS (mul_mem_endLat hm hZ₁)
      rwa [Matrix.smul_mul, Matrix.one_mul, trace_smul, hZ₁1, smul_eq_mul, mul_one] at this
    refine ⟨Z.trace / r, ⟨hi, cc_trace_div (cc_trace_of_isSkew hS.1 hS.2.1 hZ.1)⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
  · rintro ⟨b, hb, hbe⟩
    simp only [AddMonoidHom.coe_mulLeft] at hbe
    have e : trProj Z = Z - b • (1 : Matrix (Fin r) (Fin r) E) := by
      rw [trProj, ← hbe, mul_div_cancel_left₀ _ hrE]
    refine ⟨hD.1, hD.2.1, ?_⟩
    rw [e]
    exact (endLat Λ).sub_mem hZ.2 (smul_mem_endLat hb.1 one_mem_endLat)

theorem traceHom_surj (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hS : SelfDualLat G Λ) {b : E} (hb : b ∈ imLat E) : ∃ Z ∈ skewLat G Λ, Z.trace = b := by
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := GlobalTheory.T.hermitian_adjoint_properties E r G hS.1 hS.2.1
  obtain ⟨Z₁, hZ₁, hZ₁1⟩ := GlobalTheory.T.exists_end_lattice_trace_one E r G Λ (Nat.one_le_iff_ne_zero.2 hr) hS
  obtain ⟨t, ht, ht1⟩ := GlobalTheory.T.exists_integral_trace_one_unramified E hU
  have hbt : IsIntegral ℤ (b * t) := hb.1.mul ht
  refine ⟨(b * t) • Z₁ - hAdj G ((b * t) • Z₁), ⟨?_, ?_⟩, ?_⟩
  · rw [h8, hAdj_sub hS.1 hS.2.1, h6, neg_sub]
  · exact (endLat Λ).sub_mem (smul_mem_endLat hbt hZ₁) (GlobalTheory.T.hermitian_adjoint_mem_end_lattice E r G Λ _ hS (smul_mem_endLat hbt hZ₁))
  · rw [trace_sub, h7, trace_smul, hZ₁1, smul_eq_mul, mul_one]
    have hb2 := hb.2
    simp only [cc, map_mul] at hb2 ⊢
    rw [hb2]
    have e2 : IsCMField.complexConj E t = 1 - t := by
      have := ht1; simp only [cc] at this; rw [← this]; ring
    rw [e2]; ring

theorem relIndex_lieLat_dualLie (hr : r ≠ 0) (hU : Unr E) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hS : SelfDualLat G Λ) :
    (lieLat G Λ).relIndex (dualLie G Λ) =
      (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) := by
  let f : skewLat G Λ →+ dualLie G Λ :=
    (trProjHom G Λ).codRestrict (dualLie G Λ) fun Z => trProj_mem_dualLie hr hS Z.2
  let g : skewLat G Λ →+ imLat E :=
    (traceHom G Λ).codRestrict (imLat E) fun Z =>
      ⟨GlobalTheory.T.end_lattice_trace_integral E r G Λ _ hS Z.2.2, cc_trace_of_isSkew hS.1 hS.2.1 Z.2.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨Z, hZ, e⟩ := exists_skewLat_trProj_eq hr hU hS hY
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  have hg : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨Z, hZ, e⟩ := traceHom_surj hr hU hS hb
    exact ⟨⟨Z, hZ⟩, Subtype.ext e⟩
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ hf, ← AddSubgroup.index_comap_of_surjective _ hg]
  congr 1
  ext Z
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
  exact trProj_mem_lieLat_iff hr hS Z.2

end GlobalTheory.LieDisc

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem lieLat_relIndex_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ →
    (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
      ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  intro E _ _ _ r G Λ hr hU hS
  have hr0 : r ≠ 0 := by omega
  rw [LieDisc.closure_dualLie, LieDisc.relIndex_lieLat_dualLie hr0 hU hS]
  exact GlobalTheory.T.imaginary_lattice_scaling_index E r hU (by omega)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniform
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem integral_ball_translate {n : ℕ} (z : V n) (δ : ℝ) (F : V n → ℝ) :
    ∫ w in ball (0 : V n) δ, F (z + w) = ∫ w in ball z δ, F w := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have key : (fun w => (ball (0 : V n) δ).indicator (fun w => F (z + w)) w) =
      fun w => (ball z δ).indicator F (z + w) := by
    funext w
    have hiff : w ∈ ball (0 : V n) δ ↔ z + w ∈ ball z δ := by
      simp [mem_ball, dist_eq_norm]
    by_cases hw : w ∈ ball (0 : V n) δ
    · simp [Set.indicator, hw, hiff.1 hw]
    · simp [Set.indicator, hw, (not_congr hiff).1 hw]
  rw [key]
  exact integral_add_left_eq_self (fun w => (ball z δ).indicator F w) z

theorem morse_local : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K →
    K ⊆ U → ContDiffOn ℝ 2 φ U →
    (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U →
    (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧
    ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U →
      ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤
        ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n *
          ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  intro n U K φ g ε hU hK hKU hφ hlevi hg hgpos hε
  have hcont : ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U :=
    GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two n U φ hU hφ

  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ K, ∀ j l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ ≤ C := by
    have hc : ContinuousOn (fun z => ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖) K :=
      continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun l _ =>
        ((hcont j l).mono hKU).norm
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨C, fun z hz j l => ?_⟩
    have h1 := hC z hz
    rw [Real.norm_of_nonneg (by positivity)] at h1
    refine le_trans ?_ h1
    calc ‖cHess n (fun v => (φ v : ℂ)) z j l‖
        ≤ ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun l => ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
      _ ≤ ∑ j, ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖ :=
          Finset.single_le_sum (f := fun j => ∑ l, ‖cHess n (fun v => (φ v : ℂ)) z j l‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)

  obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧
      ∀ z ∈ K, (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n ≤ D := by
    have hHc : ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z) U :=
      continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j l
    have hc : ContinuousOn (fun z => (cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n) K :=
      ((Complex.continuous_re.comp (continuous_id.matrix_det)).comp_continuousOn
        (hHc.mono hKU)).div_const _
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max D 0, le_max_right _ _, fun z hz =>
      ((le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hD z hz)).trans (le_max_left _ _)⟩

  set τ : ℝ := ε / (2 * (D + ε)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by
    rw [hτ, div_lt_one (by positivity)]; linarith
  have hτd : ∀ d, 0 ≤ d → d ≤ D → d + ε / 2 ≤ (1 - τ) * (d + ε) := by
    intro d hd hdD
    have : τ * (d + ε) ≤ ε / 2 := by
      rw [hτ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith

  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hS : IsCompact (cthickening r K) := hK.cthickening
  obtain ⟨c, hc0, hcK⟩ : ∃ c, 0 < c ∧ ∀ z ∈ K, c ≤ g z := by
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1, one_pos, by simp [hK0]⟩
    · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne (hg.mono hKU)
      exact ⟨g x, hgpos x (hKU hx), fun z hz => hmin hz⟩
  obtain ⟨δ₂, hδ₂, huc⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous (hg.mono hrU)) (τ * c) (by positivity)
  set δ₃ : ℝ := min r (δ₂ / 2) with hδ₃
  have hδ₃0 : 0 < δ₃ := by positivity
  have hgw : ∀ z ∈ K, ∀ w : V n, ‖w‖ ≤ δ₃ → (1 - τ) * g z ≤ g (z + w) := by
    intro z hz w hw
    have hzS : z ∈ cthickening r K := self_subset_cthickening K hz
    have hdist : dist (z + w) z = ‖w‖ := by simp [dist_eq_norm]
    have hzwS : z + w ∈ cthickening r K :=
      mem_cthickening_of_dist_le _ z r K hz (by rw [hdist]; exact hw.trans (min_le_left _ _))
    have h1 := huc (z + w) hzwS z hzS (by rw [hdist]; linarith [min_le_right r (δ₂ / 2)])
    rw [Real.dist_eq, abs_lt] at h1
    have := hcK z hz
    nlinarith

  obtain ⟨η, hη, htr⟩ := GlobalTheory.T.truncatedGaussianIntegral_uniform_posSemidef n C (ε / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hty⟩ := GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split n U K φ η hU hK hKU hφ hη
  refine ⟨min δ₁ δ₃, lt_min hδ₁ hδ₃0, fun z hz =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hty z hz).1, ?_⟩
  set δ : ℝ := min δ₁ δ₃ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₃0
  filter_upwards [htr δ hδ0] with m hm
  intro z hz f hf
  obtain ⟨hzU, h, hh, hh0, hbd⟩ := hty z hz
  set H := cHess n (fun v => (φ v : ℂ)) z with hH
  have hpsd : H.PosSemidef :=
    GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg n φ z (hφ.contDiffAt (hU.mem_nhds (hKU hz))) (hlevi z (hKU hz))
  have hT := hm H hpsd (hC z hz)
  set d := H.det.re / Real.pi ^ n with hd
  have hd0 : 0 ≤ d := by
    have h1 := hpsd.det_nonneg
    have h2 : 0 ≤ H.det.re := (Complex.le_def.1 h1).1
    positivity
  have hdD : d ≤ D := hD z hz

  set Wf : V n → ℝ := fun w => Real.exp (-(m * ((∑ j, ∑ l, H j l * w j *
    (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) with hWf
  set F : V n → ℂ := fun w => f (z + w) * Complex.exp (-((m : ℂ) * h w)) with hF
  set U' : Set (V n) := (fun w => z + w) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hballU : ∀ w ∈ closedBall (0 : V n) δ, z + w ∈ closedBall z δ := by
    intro w hw
    simpa [mem_closedBall, dist_eq_norm] using hw
  have hball' : closedBall (0 : V n) δ ⊆ U' := fun w hw =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans hzU (hballU w hw)
  have hFd : DifferentiableOn ℂ F U' := by
    have h1 : DifferentiableOn ℂ (fun w => f (z + w)) U' :=
      hf.comp ((differentiable_const z).add differentiable_id).differentiableOn
        (fun w hw => hw)
    exact h1.mul ((hh.const_mul (m : ℂ)).neg.cexp.differentiableOn)
  have hWc : Continuous Wf := by
    simp only [hWf]; fun_prop
  have hW0 : ∀ w, 0 ≤ Wf w := fun w => (Real.exp_pos _).le
  have hWinv : ∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → Wf (θ • w) = Wf w := by
    intro θ w hθ
    have hθ' : θ * (starRingEnd ℂ) θ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
    have hsum : (∑ j, ∑ l, H j l * (θ • w) j * (starRingEnd ℂ) ((θ • w) l)) =
        ∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      have e1 : (θ • w) j = θ * w j := by simp
      have e2 : (θ • w) l = θ * w l := by simp
      rw [e1, e2, map_mul]
      calc H j l * (θ * w j) * ((starRingEnd ℂ) θ * (starRingEnd ℂ) (w l))
          = H j l * w j * (starRingEnd ℂ) (w l) * (θ * (starRingEnd ℂ) θ) := by ring
        _ = _ := by rw [hθ', mul_one]
    simp only [hWf, hsum, norm_smul, hθ, one_mul]
  have hcirc := GlobalTheory.T.norm_sq_mul_integral_ball_le_of_circle_invariant' n δ U' F Wf hδ0 hU'o hball' hFd hWc.continuousOn hW0 hWinv
  have hF0 : F 0 = f z := by simp [hF, hh0]
  rw [hF0] at hcirc

  have hmaps : Set.MapsTo (fun w => z + w) (closedBall (0 : V n) δ) U := fun w hw =>
    hball' hw
  have hfc : ContinuousOn (fun w => f (z + w)) (closedBall (0 : V n) δ) :=
    hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hφc : ContinuousOn (fun w => φ (z + w)) (closedBall (0 : V n) δ) :=
    hφ.continuousOn.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hgc : ContinuousOn (fun w => g (z + w)) (closedBall (0 : V n) δ) :=
    hg.comp (continuous_const.add continuous_id).continuousOn hmaps
  have hFc : ContinuousOn F (closedBall (0 : V n) δ) := hFd.continuousOn.mono hball'
  set G : V n → ℝ := fun w => ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w with hG
  have hGc : ContinuousOn (fun w => G (z + w)) (closedBall (0 : V n) δ) := by
    simp only [hG]
    exact ((hfc.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul hφc).neg))).mul hgc
  set k : ℝ := Real.exp (-(m * φ z)) * g z * (1 - τ) with hk
  have hk0 : 0 ≤ k := by
    have := hgpos z (hKU hz)
    have : 0 < 1 - τ := by linarith
    positivity
  have hpt : ∀ w ∈ ball (0 : V n) δ, k * (‖F w‖ ^ 2 * Wf w) ≤ G (z + w) := by
    intro w hw
    have hw' : ‖w‖ < δ := by simpa using hw
    have hw1 : w ∈ closedBall (0 : V n) δ₁ := by
      simp only [mem_closedBall, dist_zero_right]; linarith [min_le_left δ₁ δ₃]
    have hb := hbd w hw1
    have hq : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re =
        (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re := by
      simp [hH, leviV, cHess]
    have hgzw := hgw z hz w (by linarith [min_le_right δ₁ δ₃])
    have hFn : ‖F w‖ ^ 2 = ‖f (z + w)‖ ^ 2 * Real.exp (-(m * (h w).re)) ^ 2 := by
      simp [hF, norm_mul, Complex.norm_exp, mul_pow]
    have hE : Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w) ≤
        Real.exp (-(m * φ (z + w))) := by
      simp only [hWf]
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left hb hm0
      rw [hq]
      nlinarith
    have hP : 0 ≤ ‖f (z + w)‖ ^ 2 := by positivity
    have hgz : 0 ≤ (1 - τ) * g z := by
      have := hgpos z (hKU hz); have : 0 < 1 - τ := by linarith
      positivity
    calc k * (‖F w‖ ^ 2 * Wf w)
        = ((1 - τ) * g z) * (‖f (z + w)‖ ^ 2 *
            (Real.exp (-(m * φ z)) * (Real.exp (-(m * (h w).re)) ^ 2 * Wf w))) := by
          rw [hFn, hk]; ring
      _ ≤ g (z + w) * (‖f (z + w)‖ ^ 2 * Real.exp (-(m * φ (z + w)))) := by
          apply mul_le_mul hgzw (mul_le_mul_of_nonneg_left hE hP)
          · have := hW0 w; positivity
          · exact (hgpos _ (hmaps (ball_subset_closedBall hw))).le
      _ = G (z + w) := by simp only [hG]; ring
  have hint1 : IntegrableOn (fun w => k * (‖F w‖ ^ 2 * Wf w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ)
      (continuousOn_const.mul ((hFc.norm.pow 2).mul hWc.continuousOn))).mono_set
      ball_subset_closedBall
  have hint2 : IntegrableOn (fun w => G (z + w)) (ball (0 : V n) δ) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 δ) hGc).mono_set
      ball_subset_closedBall
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_ball hpt
  rw [integral_const_mul, integral_ball_translate z δ G] at hmono

  set J := ∫ w in ball (0 : V n) δ, Wf w with hJ
  set I := ∫ w in ball z δ, G w with hI
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_ball fun w _ => hW0 w
  set A := ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z with hA
  have hA0 : 0 ≤ A := by have := hgpos z (hKU hz); positivity
  have hAJ : (1 - τ) * (A * J) ≤ I := by
    have h1 := mul_le_mul_of_nonneg_left hcirc hk0
    calc (1 - τ) * (A * J) = k * (‖f z‖ ^ 2 * J) := by rw [hA, hk]; ring
      _ ≤ _ := h1
      _ ≤ I := hmono
  have hmn : 0 ≤ (m : ℝ) ^ n := by positivity
  have hkey := hτd d hd0 hdD
  change A ≤ (d + ε) * (m : ℝ) ^ n * I
  calc A = A * 1 := (mul_one A).symm
    _ ≤ A * ((d + ε / 2) * (m : ℝ) ^ n * J) := mul_le_mul_of_nonneg_left hT hA0
    _ ≤ A * ((1 - τ) * (d + ε) * (m : ℝ) ^ n * J) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        have := mul_nonneg hmn hJ0
        nlinarith
    _ = (d + ε) * (m : ℝ) ^ n * ((1 - τ) * (A * J)) := by ring
    _ ≤ (d + ε) * (m : ℝ) ^ n * I := by
        apply mul_le_mul_of_nonneg_left hAJ
        have : 0 ≤ d + ε := by linarith
        positivity

end GlobalTheory
end

