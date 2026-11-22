import Mathlib

-- bundled from GroundTheory.AutomorphicForms.GL2Classical.Iwasawa
section
open Matrix UpperHalfPlane

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

theorem det_fin_two_kmat (w : ℂ) : (!![w.re, -w.im; w.im, w.re] : Matrix (Fin 2) (Fin 2) ℝ).det =
    Complex.normSq w := by
  rw [Matrix.det_fin_two_of, Complex.normSq_apply]
  ring

def kGL (w : ℂ) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![w.re, -w.im; w.im, w.re] (by
    rw [det_fin_two_kmat]
    exact (Complex.normSq_pos.2 hw).ne')

@[simp]
theorem coe_kGL (w : ℂ) (hw : w ≠ 0) :
    (kGL w hw : Matrix (Fin 2) (Fin 2) ℝ) = !![w.re, -w.im; w.im, w.re] :=
  rfl

theorem det_kGL (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_kGL, det_fin_two_kmat]

theorem det_kGL_pos (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by
  rw [det_kGL]
  exact Complex.normSq_pos.2 hw

theorem denom_kGL (w : ℂ) (hw : w ≠ 0) : denom (kGL w hw) (I : ℂ) = w := by
  rw [denom]
  apply Complex.ext <;> simp

theorem kGL_smul_I (w : ℂ) (hw : w ≠ 0) : kGL w hw • I = I := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_kGL_pos w hw), denom_kGL, div_eq_iff hw]
  rw [num]
  apply Complex.ext <;> simp

theorem kGL_mul (w₁ w₂ : ℂ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    kGL w₁ hw₁ * kGL w₂ hw₂ = kGL (w₁ * w₂) (mul_ne_zero hw₁ hw₂) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_kGL, coe_kGL, coe_kGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def borelGL (z : ℍ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![z.im, z.re; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    simpa using z.im_pos.ne')

@[simp]
theorem coe_borelGL (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl

theorem det_borelGL (z : ℍ) : (borelGL z).det.val = z.im := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelGL, Matrix.det_fin_two_of]
  ring

theorem det_borelGL_pos (z : ℍ) : 0 < (borelGL z).det.val := by
  rw [det_borelGL]
  exact z.im_pos

theorem denom_borelGL (z : ℍ) (w : ℂ) : denom (borelGL z) w = 1 := by
  simp [denom]

theorem borelGL_smul_I (z : ℍ) : borelGL z • I = z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_borelGL_pos z), denom_borelGL, div_one, num]
  apply Complex.ext <;> simp

theorem re_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).re = ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 0 + h 0 1 * h 1 1) /
      Complex.normSq (denom h (I : ℂ)) := by
  rw [UpperHalfPlane.re, coe_smul_of_det_pos hpos, Complex.div_re]
  simp only [num, denom, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, coe_I, Complex.I_re, Complex.I_im]
  ring

theorem im_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by
  rw [im_smul_eq_div_normSq, abs_of_pos hpos, I_im, mul_one]

theorem eq_borelGL_mul_kGL {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    h = borelGL (h • I) * kGL (denom h (I : ℂ)) (denom_ne_zero h I) := by
  have hN : Complex.normSq (denom h (I : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.2 (denom_ne_zero h I)).ne'
  have hN' : Complex.normSq (denom h (I : ℂ)) = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 := by
    simp [denom, Complex.normSq_apply]
    ring
  have hdet : h.det.val = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hre := re_smul_I hpos
  have him := im_smul_I hpos
  rw [hN'] at hre him
  have hD : (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + h 1 1 ^ 2 ≠ 0 := hN' ▸ hN
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, coe_borelGL, coe_kGL]
  have hdr : (denom h (I : ℂ)).re = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [denom]
  have hdi : (denom h (I : ℂ)).im = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [denom]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, hdr, hdi, hre, him, hdet] <;>
    field_simp <;> ring

end GL2Classical

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.GL2Classical.Periodic
section
open Complex MeasureTheory intervalIntegral Filter Topology Set
open UpperHalfPlane hiding I I_re I_im
open scoped Manifold Interval

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

theorem integral_periodic_eq_of_im {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {w | 0 < w.im}) {T : ℝ}
    (hper : ∀ w : ℂ, 0 < w.im → G (w + T) = G w) (x₀ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) :
    ∫ x in x₀..x₀ + T, G (x + y₁ * I) = ∫ x in x₀..x₀ + T, G (x + y₂ * I) := by
  have hsub : [[x₀, x₀ + T]] ×ℂ [[y₁, y₂]] ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    rw [mem_reProdIm] at hw
    have := hw.2
    rw [Set.mem_uIcc] at this
    show 0 < w.im
    rcases this with h | h
    · exact lt_of_lt_of_le hy₁ h.1
    · exact lt_of_lt_of_le hy₂ h.1
  have H := integral_boundary_rect_eq_zero_of_differentiableOn G (x₀ + y₁ * I)
    ((x₀ + T : ℝ) + y₂ * I) (by
      refine hG.mono (Set.Subset.trans ?_ hsub)
      simp)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at H
  have hv : ∫ y in y₁..y₂, G (((x₀ + T : ℝ) : ℂ) + y * I) = ∫ y in y₁..y₂, G ((x₀ : ℂ) + y * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : 0 < y := by
      rw [Set.mem_uIcc] at hy
      rcases hy with h | h
      · exact lt_of_lt_of_le hy₁ h.1
      · exact lt_of_lt_of_le hy₂ h.1
    have := hper ((x₀ : ℂ) + y * I) (by simpa using hy0)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [hv, add_sub_cancel_right, sub_eq_zero] at H
  exact H

theorem integral_vadd_eq_zero {F : ℍ → ℂ} (hF : MDiff F) {T : ℝ} (hT : 0 < T)
    (hper : ∀ z : ℍ, F (T +ᵥ z) = F z) (hzero : IsZeroAtImInfty F) (z : ℍ) :
    ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = 0 := by
  set G : ℂ → ℂ := F ∘ ofComplex
  have hG : DifferentiableOn ℂ G {w | 0 < w.im} := mdifferentiable_iff.1 hF
  have hGw : ∀ w : ℂ, (hw : 0 < w.im) → G w = F ⟨w, hw⟩ := fun w hw => by
    simp only [G, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  have hper' : ∀ w : ℂ, 0 < w.im → G (w + T) = G w := fun w hw => by
    have hw' : 0 < (w + T).im := by simpa using hw
    rw [hGw _ hw', hGw _ hw, ← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]

  have hint : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..T, G ((t + z.re : ℝ) + y * I) =
      ∫ x in z.re..z.re + T, G (x + y * I) := by
    intro y _
    have := intervalIntegral.integral_comp_add_right (fun x : ℝ => G (x + y * I)) z.re (a := 0) (b := T)
    simp only [zero_add] at this
    rw [add_comm z.re T]
    exact this
  have hzint : ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = ∫ x in z.re..z.re + T, G (x + z.im * I) := by
    rw [← hint z.im z.im_pos]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have him : 0 < (((t + z.re : ℝ) : ℂ) + z.im * I).im := by simpa using z.im_pos
    rw [hGw _ him]
    congr 1
    ext
    simp only [coe_vadd, ofReal_add]
    rw [add_assoc]
    exact congrArg _ (Complex.re_add_im (z : ℂ)).symm
  rw [hzint]

  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (hzero.eventually (Metric.closedBall_mem_nhds 0
    (div_pos hε hT)))
  set Y := max A 1 + z.im
  have hY : 0 < Y := by positivity
  rw [integral_periodic_eq_of_im hG hper' z.re z.im_pos hY]
  have hbound : ∀ x ∈ Set.uIoc z.re (z.re + T), ‖G (x + Y * I)‖ ≤ ε / T := by
    intro x _
    have him : 0 < ((x : ℂ) + Y * I).im := by simpa using hY
    rw [hGw _ him]
    have := hA ⟨_, him⟩ (by
      show A ≤ ((x : ℂ) + Y * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]
      have := z.im_pos
      have : A ≤ max A 1 := le_max_left _ _
      linarith)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  calc ‖∫ x in z.re..z.re + T, G (x + Y * I)‖ ≤ ε / T * |z.re + T - z.re| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε := by
        rw [add_sub_cancel_left, abs_of_pos hT]
        field_simp

end GL2Classical

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.GL2Classical.UnitaryEigenSpan
section
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)

def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w

variable {ρ}

theorem orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY

theorem orbitSum_fixed {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by
  unfold orbitSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w _
    change ρ ((k⁻¹ : K) : G) (ρ k w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro w _
    change ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]

theorem card_orbit_pos {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card :=
  Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩

end

variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}

theorem mem_of_stable_of_eigen
    (hT : T = Submodule.span ℂ (Set.range fun g : G => ρ g φ))
    (hinj : ∀ v ∈ T, ι v = 0 → v = 0)
    (hunit : ∀ g : G, ∀ v ∈ T, ∀ w ∈ T, ⟪ι (ρ g v), ι (ρ g w)⟫_ℂ = ⟪ι v, ι w⟫_ℂ)
    (K : Subgroup G) (hφK : ∀ k : K, ρ k φ = φ)
    (horb : ∀ v ∈ T, (Set.range fun k : K => ρ k v).Finite)
    (hfd : FiniteDimensional ℂ ↥(T ⊓ Representation.invariants (ρ.comp K.subtype)))
    {J : Type*} (S : J → Finset G) (ev : J → ℂ) (hφS : ∀ j, ∑ g ∈ S j, ρ g φ = ev j • φ)
    (hP : ∀ z ∈ T, (∀ k : K, ρ k z = z) → (∀ j, ∑ g ∈ S j, ρ g z = ev j • z) → ∃ c : ℂ, z = c • φ)
    (Y : Submodule ℂ E) (hYT : Y ≤ T) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hY0 : Y ≠ ⊥) : φ ∈ Y := by
  have hφT : φ ∈ T := by rw [hT]; exact Submodule.subset_span ⟨1, by simp⟩
  have hTg : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    rw [hT] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) φ = _; rw [map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

  have hadj : ∀ g, ∀ v ∈ T, ∀ w ∈ T, ⟪ι v, ι (ρ g w)⟫_ℂ = ⟪ι (ρ g⁻¹ v), ι w⟫_ℂ := by
    intro g v hv w hw
    rw [← hunit g⁻¹ v hv _ (hTg g w hw), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

  have havg : ∀ z ∈ T, (∀ k : K, ρ k z = z) → ∀ v (hv : v ∈ T),
      ⟪ι z, ι (orbitSum ρ K v (horb v hv))⟫_ℂ = ((horb v hv).toFinset.card : ℂ) * ⟪ι z, ι v⟫_ℂ := by
    intro z hz hzK v hv
    unfold orbitSum
    rw [map_sum, inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨k, rfl⟩ := hw
    rw [hadj _ z hz v hv, ← Subgroup.coe_inv, hzK k⁻¹]

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hyT := hYT hyY
  obtain ⟨g, hg⟩ : ∃ g : G, ⟪ι φ, ι (ρ g y)⟫_ℂ ≠ 0 := by
    by_contra! hall
    have horth : ∀ t ∈ T, ⟪ι t, ι y⟫_ℂ = 0 := by
      intro t ht
      rw [hT] at ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        have := hall h⁻¹
        rw [hadj _ φ hφT y hyT, inv_inv] at this
        exact this
      | zero => rw [map_zero, inner_zero_left]
      | add x x' _ _ hx hx' => rw [map_add, inner_add_left, hx, hx', add_zero]
      | smul c x _ hx => rw [map_smul, inner_smul_left, hx, mul_zero]
    exact hy0 (hinj y hyT (inner_self_eq_zero.1 (horth y hyT)))
  set y' := ρ g y
  have hy'Y : y' ∈ Y := hY g y hyY
  have hy'T : y' ∈ T := hYT hy'Y
  set s := orbitSum ρ K y' (horb y' hy'T)
  have hsY : s ∈ Y := orbitSum_mem _ hY hy'Y
  have hsK : ∀ k : K, ρ k s = s := orbitSum_fixed _
  have hφs : ⟪ι φ, ι s⟫_ℂ ≠ 0 := by
    rw [havg φ hφT hφK y' hy'T]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (card_orbit_pos _).ne') hg

  set M : Submodule ℂ E := Y ⊓ (T ⊓ Representation.invariants (ρ.comp K.subtype))
  have hMfd : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le (inf_le_right : M ≤ T ⊓ Representation.invariants (ρ.comp K.subtype))
  set Mι : Submodule ℂ H := M.map ι
  have hMιfd : FiniteDimensional ℂ Mι := inferInstance
  haveI : CompleteSpace Mι := FiniteDimensional.complete ℂ Mι
  obtain ⟨u, huM, w, hw, hφw⟩ := Mι.exists_add_mem_mem_orthogonal (ι φ)
  obtain ⟨m, hmM, hmP⟩ := Submodule.mem_map.1 huM
  have hmY : m ∈ Y := hmM.1
  have hmT : m ∈ T := hmM.2.1
  have hmK : ∀ k : K, ρ k m = m := fun k => hmM.2.2 k
  set z := φ - m
  have hzT : z ∈ T := sub_mem hφT hmT
  have hzK : ∀ k : K, ρ k z = z := fun k => by rw [map_sub, hφK, hmK]
  have hzι : ι z ∈ Mιᗮ := by
    rw [map_sub, hmP, hφw, add_sub_cancel_left]
    exact hw

  have hzY : ∀ v ∈ Y, ⟪ι z, ι v⟫_ℂ = 0 := by
    intro v hvY
    have hvT := hYT hvY
    have hsv : orbitSum ρ K v (horb v hvT) ∈ M :=
      ⟨orbitSum_mem _ hY hvY, orbitSum_mem _ hTg hvT, fun k => orbitSum_fixed _ k⟩
    have h0 : ⟪ι z, ι (orbitSum ρ K v (horb v hvT))⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hsv) hzι
    rw [havg z hzT hzK v hvT] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (card_orbit_pos _).ne')

  have hzE : ∀ j, ∑ g ∈ S j, ρ g z = ev j • z := by
    intro j
    set D := ∑ g ∈ S j, ρ g z - ev j • z
    have hDY : D ∈ Y := by
      have e : D = -(∑ g ∈ S j, ρ g m - ev j • m) := by
        simp only [D, z, map_sub, Finset.sum_sub_distrib, hφS, smul_sub]
        abel
      rw [e]
      exact neg_mem (sub_mem (Submodule.sum_mem _ fun g _ => hY g m hmY) (Submodule.smul_mem _ _ hmY))
    have hDT := hYT hDY
    have hDorth : ∀ v ∈ Y, ⟪ι D, ι v⟫_ℂ = 0 := by
      intro v hvY
      have hvT := hYT hvY
      simp only [D, map_sub, map_sum, map_smul, inner_sub_left, sum_inner, inner_smul_left, hzY v hvY,
        mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [← hunit g⁻¹ _ (hTg g z hzT) v hvT, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
      exact hzY _ (hY _ _ hvY)
    have := hinj D hDT (inner_self_eq_zero.1 (hDorth D hDY))
    exact sub_eq_zero.1 this

  obtain ⟨c, hc⟩ := hP z hzT hzK hzE
  have hzs := hzY s hsY
  rw [hc, map_smul, inner_smul_left] at hzs
  have hc0 : c = 0 := by
    have := (mul_eq_zero.1 hzs).resolve_right hφs
    simpa using this
  have hz0 : z = 0 := by rw [hc, hc0, zero_smul]
  have : φ = m := sub_eq_zero.1 hz0
  rw [this]
  exact hmY

end GL2Classical

end

end GroundTheory.Automorphic
end

