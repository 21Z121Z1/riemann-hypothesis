import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GoodPointBranchExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

theorem exists_branch {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    {u q : Fin n → ℂ} (hqu : linEval u q = 0)
    {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)} {V : Set (Fin n → ℂ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hS : zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O)
    {N₀ : Set (Fin n → ℂ)} (hN₀ : N₀ ∈ 𝓝 q)
    (hdouble : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N₀ → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0)
    {w : Fin n ⊕ Fin M.m → ℂ} (hwq : IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)
    {r : ℝ} {φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ} {k : ℕ} (hr : 0 < r)
    (hφd : DifferentiableOn ℂ φ (ball 0 r)) (hφi : InjOn φ (ball 0 r)) (hφ0 : φ 0 = w)
    (hφZ : MapsTo φ (ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal))
    (hφU : ∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' ball 0 s)
    (hvan : VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k)
    (hinjD : ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0)
    {G : Set (Fin n ⊕ Fin M.m → ℂ)} (hG : G ∈ 𝓝 w) :
    ∃ γ : VarBranch J (d + 1) q,
      (∃ U ∈ 𝓝 w, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius k ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
  set ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ := fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t) with hψdef
  have hψd : DifferentiableOn ℂ ψ (ball 0 r) :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφd (Sum.inl i)
  have h0r : (0 : Fin (d + 1) → ℂ) ∈ ball 0 r := mem_ball_self hr
  have hψ : HasStrictFDerivAt ψ (fderiv ℂ ψ 0) 0 :=
    (analyticOnNhd_of_differentiableOn isOpen_ball hψd 0 h0r).hasStrictFDerivAt
  have hψ0 : ψ 0 = q := by simp only [hψdef, hφ0, hwq]
  obtain ⟨H, hHd, hH0, hF⟩ := hvan
  have hk : k ≠ 0 := by
    intro hk0
    have h : linEval u (ψ 0) = (0 : Fin (d + 1) → ℂ) 0 ^ k * H 0 := hF 0 h0r
    rw [hψ0, hqu, hk0, pow_zero, one_mul] at h
    exact hH0 0 h0r h.symm
  have hzero : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, linEval u (ψ t) = 0 ↔ t 0 = 0 := by
    intro t ht
    have h : linEval u (ψ t) = t 0 ^ k * H t := hF t ht
    rw [h, mul_eq_zero, pow_eq_zero_iff hk]
    exact or_iff_left (hH0 t ht)
  have hψZ : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, ψ t ∈ zeroSet J := fun t ht =>
    NormalModelFibre.firstCoords_mem_zeroSet M (hφZ ht)
  have hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ zeroSet J ∩ {x | linEval u x = 0} := by
    filter_upwards [ball_mem_nhds (0 : Fin d → ℂ) hr] with v hv
    have hv' := consZero_mem_ball hv
    exact ⟨hψZ _ hv', (hzero _ hv').2 (consZero_apply_zero v)⟩
  obtain ⟨ha, W, hW, hWinj, hcov⟩ := slice_chart hψ hψ0 hinjD hV hqV hg hAg hS hslice
  have hE : ball (0 : Fin (d + 1) → ℂ) r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ ∈ 𝓝 (0 : Fin (d + 1) → ℂ) := by
    have hφc : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    have hψc : ContinuousAt ψ 0 := hψd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    exact inter_mem (inter_mem (ball_mem_nhds 0 hr) (hφc.preimage_mem_nhds (by rw [hφ0]; exact hG)))
      (hψc.preimage_mem_nhds (by rw [hψ0]; exact hN₀))
  obtain ⟨ε₁, hε₁, hε₁E⟩ := Metric.mem_nhds_iff.1 hE
  obtain ⟨ε₂, hε₂, hε₂W⟩ := Metric.mem_nhds_iff.1 hW
  have hs : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hs1 : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ :=
    (ball_subset_ball (min_le_left _ _)).trans hε₁E
  have hsr : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r := fun t ht => (hs1 ht).1.1
  have hs2 : ball (0 : Fin d → ℂ) (min ε₁ ε₂) ⊆ W := (ball_subset_ball (min_le_right _ _)).trans hε₂W
  have hinj : InjOn ψ (ball 0 (min ε₁ ε₂)) := by
    intro t ht t' ht' htt
    by_cases hφe : φ t = φ t'
    · exact hφi (hsr ht) (hsr ht') hφe
    · have hu : linEval u (ψ t) = 0 :=
        hdouble _ (hφZ (hsr ht)) _ (hφZ (hsr ht')) htt (hs1 ht).2 hφe
      have ht0 : t 0 = 0 := (hzero t (hsr ht)).1 hu
      have ht'0 : t' 0 = 0 := (hzero t' (hsr ht')).1 (by rw [← htt]; exact hu)
      have htail : Fin.tail t = Fin.tail t' := hWinj (hs2 (tail_mem_ball ht)) (hs2 (tail_mem_ball ht'))
        (by show ψ (consZero d (Fin.tail t)) = ψ (consZero d (Fin.tail t'))
            rw [consZero_tail t ht0, consZero_tail t' ht'0]
            exact htt)
      calc t = consZero d (Fin.tail t) := (consZero_tail t ht0).symm
        _ = t' := by rw [htail, consZero_tail t' ht'0]
  let γ : VarBranch J (d + 1) q :=
    { radius := min ε₁ ε₂, radius_pos := hs, toFun := ψ, differentiableOn := hψd.mono hsr, injOn := hinj,
      map_zero := hψ0, mapsTo := fun t ht => hψZ t (hsr ht) }
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUs⟩ := hφU (min ε₁ ε₂) hs
    refine ⟨U, hU, fun w' hw' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hUs hw'
    exact ⟨t, ht, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨(hs1 ht).2, φ t, ⟨hφZ (hsr ht), (hs1 ht).1.2⟩, rfl⟩
  · obtain ⟨N, hN, hNS⟩ := hcov (ball 0 (min ε₁ ε₂)) (ball_mem_nhds 0 hs) hs2
    refine ⟨N, hN, fun x hx hxu => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hNS ⟨⟨hx.1, hxu⟩, hx.2⟩
    exact ⟨consZero d v, ⟨consZero_mem_ball hv, consZero_apply_zero v⟩, hvx⟩
  · exact ⟨H, hHd.mono hsr, fun t ht => hH0 t (hsr ht), fun t ht => hF t (hsr ht)⟩
  · have hπ : ∀ x : Fin n → ℂ, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ x = A x :=
      fun x => LinearMap.toMatrix'_mulVec _ x
    have h1 : HasFDerivAt (fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)))
        ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) 0 :=
      (hasFDerivAt_apply 0 0).prodMk (A.hasFDerivAt.comp 0 hψ.hasFDerivAt)
    have h2 : HasFDerivAt (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ))
        ((consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0)))) 0 := by
      have h3 := (consCLM d).hasFDerivAt.comp 0 h1
      have hfun : (fun τ => vecCons (τ 0)
          (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) =
          ⇑(consCLM d) ∘ fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)) := by
        funext τ
        rw [Function.comp_apply, consCLM_apply, hπ]
      rw [hfun]
      exact h3
    rw [h2.fderiv]
    set L := (consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) with hL
    have hLinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
      have hLv : L v = vecCons (v 0) (A (fderiv ℂ ψ 0 v)) := by
        rw [hL, ContinuousLinearMap.comp_apply, consCLM_apply]
        rfl
      have hv' : vecCons (v 0) (A (fderiv ℂ ψ 0 v)) = 0 := by rw [← hLv]; exact hv
      have h0 : v 0 = 0 := by simpa using congrFun hv' 0
      have hA : A (fderiv ℂ ψ 0 v) = 0 := by
        funext j
        simpa using congrFun hv' j.succ
      exact ha v h0 hA
    exact ⟨hLinj, LinearMap.injective_iff_surjective
      (f := (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))).1 hLinj⟩

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

theorem gramVol_const_zero {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  unfold gramVol
  have hw : (Fin.cons 0 (fun _ => 0) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have h0 : (Matrix.of fun (_ _ : Fin (e + 1)) => (0 : ℂ)).det = 0 := Matrix.det_zero
  simp [hw, h0]

theorem succ_le_of_ringKrullDim_quotient {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h

theorem ConeSheetGram.proof (hL : ConeSheetGramLintegral.Statement) : ConeSheetGram.Statement := by
  intro n e h J ℓ A f hJ hdim hℓ hA hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (succ_le_of_ringKrullDim_quotient J hdim)
  rw [mul_setIntegral_eq_of_lintegral (ν := volume) (fun y => IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)
    (fun y x => WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))
    (fun y x t => ‖t‖ ^ (2 * e) *
      gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)
    (fun y x t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ y))
    (fun y x => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => hL n e h J ℓ A F hJ hdim hℓ hA hF) hf]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  unfold sheetSum
  refine finsum_congr fun x => finsum_congr fun _ => ?_
  unfold sheetThrough
  split_ifs with hs
  · rfl
  · simp [gramVol_const_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets

open scoped ENNReal

noncomputable section

theorem IsSheetAt.eventuallyEq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, hγd, hγx, hγZ, -⟩ := hγ
  obtain ⟨U', hU', hxU', -, -, -, V, hV, hsV⟩ := hs
  have hc : ContinuousAt γ (A *ᵥ x) := (hγd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (A *ᵥ x), γ y ∈ V := hc.preimage_mem_nhds (by rwa [hγx])
  filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU', hV'] with y hy hy' hyV
  obtain ⟨hAy, hZy⟩ := hγZ y hy
  have h := hsV (γ y) ⟨hZy, hyV⟩ (by rwa [hAy])
  rwa [hAy] at h

theorem ConeSheetGramLintegral.proof (hPar : ConeSliceSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetGramLintegral.Statement := by
  classical
  intro n e h J ℓ A F hJ hdim hℓ hA hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e h J ℓ A hJ hdim hℓ hA

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i y => (h.matᵀ)⁻¹ *ᵥ s i.1 i.2 y with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := fun i =>
    (Matrix.mulVecLin (h.matᵀ)⁻¹).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hUD i.1).2.2.2 i.2)

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i y =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i y)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) y)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y) with hG_def

  have hGD : ∀ k, ∀ y ∈ D k, G y = ∑ j : Fin (N k), H ⟨k, j⟩ y := by
    intro k y hy
    obtain ⟨hfe, hinjy, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjy, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hAy : A *ᵥ s k j y = y := by
      have hmem : s k j y ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y := hfe ▸ ⟨j, rfl⟩
      exact hmem.2
    have hex : ∃ γ, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) γ := ⟨s k j, hsh j⟩
    have hch : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) =ᶠ[𝓝 y] s k j := by
      have h1 : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) = hex.choose := by
        simp only [sheetThrough, dif_pos hex]
      have h2 := hex.choose_spec.eventuallyEq (hsh j)
      rw [hAy] at h2
      rw [h1]
      exact h2
    have hval : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y = s k j y :=
      hch.eq_of_nhds
    have hgram : gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y') y =
        gramVol (v ⟨k, j⟩) y :=
      gramVol_congr (hch.fun_comp fun f => (h.matᵀ)⁻¹ *ᵥ f)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑' k, (D k).indicator (fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) y with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k y hk]
    intro k' hk'
    exact indicator_of_notMem (fun h' => (hdisj hk').le_bot ⟨h', hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ y, G y = ∑' i : Σ k, Fin (N k), ∫⁻ y in D i.1, H i y := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ z in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hMap := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hMap]
  exact congrArg _ hRHS.symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace FormIntegralPositivity

variable {n : ℕ}

theorem analyticAt_sheet {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    AnalyticAt ℂ s (A *ᵥ x) := by
  obtain ⟨U, hU, hxU, hsU, -⟩ := hs
  rw [analyticAt_pi_iff]
  intro i
  exact ReciprocityTheory.ChartRestriction.G.Geo.osgood d U (fun y => s y i) hU
    (fun y hy => differentiableWithinAt_pi.mp (hsU y hy) i) (A *ᵥ x) hxU

theorem maDens_cons_add {d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s) (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    maDens (fun k => vecCons (fun z => f z + g z) φ k ∘ s) (A *ᵥ x) =
      maDens (fun k => vecCons f φ k ∘ s) (A *ᵥ x) + maDens (fun k => vecCons g φ k ∘ s) (A *ᵥ x) := by
  have hsx : s (A *ᵥ x) = x := by
    obtain ⟨_, _, _, _, h, _⟩ := hs
    exact h
  have hS : ContDiffAt ℝ 2 s (A *ᵥ x) := (analyticAt_sheet hs).restrictScalars.contDiffAt
  have hf' : ContDiffAt ℝ 2 (f ∘ s) (A *ᵥ x) := (hsx ▸ hf).comp _ hS
  have hg' : ContDiffAt ℝ 2 (g ∘ s) (A *ᵥ x) := (hsx ▸ hg).comp _ hS
  have hadd : hessC ((fun z => f z + g z) ∘ s) (A *ᵥ x) =
      hessC (f ∘ s) (A *ᵥ x) + hessC (g ∘ s) (A *ᵥ x) :=
    ReciprocityTheory.AnForm.A.hessC_add (f ∘ s) (g ∘ s) _ hf' hg'
  have key : ∀ F : (Fin n → ℂ) → ℝ, (fun k => hessC (vecCons F φ k ∘ s) (A *ᵥ x)) =
      Function.update (fun k => hessC (vecCons f φ k ∘ s) (A *ᵥ x)) 0 (hessC (F ∘ s) (A *ᵥ x)) := by
    intro F
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp
    · simp
  simp only [maDens]
  rw [key (fun z => f z + g z), key g, hadd, ReciprocityTheory.AnForm.A.mdisc_update_add, ← key f, Complex.add_re,
    mul_add]

theorem dens_sum_nonneg (hD : SheetLogNormDens.Statement) (h : HermNorm n) (u' : Fin n → ℂ) {ε : ℝ}
    (hε : 0 < ε) {e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (e + 1)) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin (e + 1) → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (hx : x ≠ 0) :
    0 ≤ maDens (fun k => vecCons (fsLogReg h u' ε) (fun _ z => Real.log (h.dualNorm z)) k ∘ s) (A *ᵥ x) +
      maDens (fun k => (fun (_ : Fin (e + 1)) z => Real.log (h.dualNorm z)) k ∘ s) (A *ᵥ x) := by
  have hO : IsOpen {z : Fin n → ℂ | z ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  have hL : ContDiffAt ℝ 2 (fun z => Real.log (h.dualNorm z)) x :=
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hb : ContDiffAt ℝ 2 (fsLogReg h u' ε) x :=
    ((FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε).contDiffAt (hO.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hΨ : (fun (_ : Fin (e + 1)) z => Real.log (h.dualNorm z)) =
      vecCons (fun z => Real.log (h.dualNorm z)) (fun _ z => Real.log (h.dualNorm z)) := by
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
  rw [hΨ, ← maDens_cons_add hs _ _ _ hb hL]
  let T : Fin (e + 1) → Matrix (Fin (n + 1)) (Fin n) ℂ :=
    vecCons (FubiniStudyLogRegularization.regMat h u' ε) fun _ => FubiniStudyLogRegularization.regMat h 0 1
  have hpot : (fun k => vecCons (fun z => fsLogReg h u' ε z + Real.log (h.dualNorm z))
      (fun _ z => Real.log (h.dualNorm z)) k ∘ s) =
      fun k => (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s := by
    funext k y
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · simp only [Function.comp_apply, cons_val_zero, T]
      exact FubiniStudyLogRegularization.fsLogReg_add_log h u' hε _
    · simp only [Function.comp_apply, cons_val_succ, T]
      exact FubiniStudyLogRegularization.log_dualNorm_eq h _
  rw [hpot]
  refine hD n (e + 1) (n + 1) J A x s T hs fun k => ?_
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
  · exact FubiniStudyLogRegularization.regMat_mulVec_ne_zero h u' hε hx
  · exact FubiniStudyLogRegularization.regMat_mulVec_ne_zero h 0 one_pos hx

end FormIntegralPositivity

open FormIntegralPositivity in

theorem FormIntPos.proof (hC : ConeToProjective.Statement) (hM : SliceFormMass.Statement)
    (hD : SheetLogNormDens.Statement) : FormIntPos.Statement := by
  intro n e h W u u' ε δ δ' hW hF hε hδ hδδ'
  obtain ⟨F, hF⟩ := hF
  obtain ⟨j, hj⟩ := hW.isRelevant
  have hℓ : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W := ⟨Pi.single j 1, by rwa [linForm_single]⟩
  have hℓW : linForm hℓ.choose ∉ W := hℓ.choose_spec
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hform : ∀ a b, formInt h W e a b = varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) a
      (vecCons b fun _ x => Real.log (h.dualNorm x)) := by
    intro a b
    rw [formInt, dif_pos hℓ]
  have hcone : ∀ δ₀, 0 < δ₀ → coneIntegral h W (e + 1) (fsLogReg h u δ₀) =
      varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) (fsLogReg h u δ₀)
        (fun _ x => Real.log (h.dualNorm x)) := fun δ₀ hδ₀ =>
    hC n (e + 1) h W F hℓ.choose (fsLogReg h u δ₀) hW hF hℓW
      (fun t x ht => FubiniStudyLogRegularization.fsLogReg_smul h u δ₀ ht x)
      (FubiniStudyLogRegularization.contDiffOn_fsLogReg h u hδ₀).continuousOn
  rw [hform, hform, hcone δ hδ, hcone δ' hδ']
  unfold varInt
  split_ifs with hA
  swap
  · simp
  have hAfin := hA.choose_spec
  unfold chartInt

  have hint : ∀ δ₀, 0 < δ₀ → ∀ (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
      (∀ k (t : ℂ) x, t ≠ 0 → ψ k (t • x) = ψ k x) → (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose (fsLogReg h u δ₀)
        fun k x => c k * Real.log (h.dualNorm x) + ψ k x) := by
    intro δ₀ hδ₀ c ψ hψ hψs
    refine Integrable.mono' (hM n e h W F hℓ.choose hA.choose (fsLogReg h u δ₀) c ψ hW hF hℓW hAfin
      (fun t x ht => FubiniStudyLogRegularization.fsLogReg_smul h u δ₀ ht x)
      (FubiniStudyLogRegularization.contDiffOn_fsLogReg h u hδ₀).continuousOn hψ hψs) ?_
      (Eventually.of_forall fun y => ?_)
    · exact (SheetSumMeasurable.measurable_sheetSum hAfin (fun a b => a * b)
        (continuous_fst.mul continuous_snd).measurable (FubiniStudyLogRegularization.measurable_fsLogReg h u δ₀)
        _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_chartDens_le _ _ _ _ y
  have h1 : ∀ δ₀, 0 < δ₀ → Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose
      (fsLogReg h u δ₀) (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) := by
    intro δ₀ hδ₀
    have e1 : (fun (k : Fin (e + 1)) x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k *
        Real.log (h.dualNorm x) + (vecCons (fsLogReg h u' ε) fun _ _ => 0 :
          Fin (e + 1) → (Fin n → ℂ) → ℝ) k x) =
        vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) := by
      funext k x
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
    rw [← e1]
    refine hint δ₀ hδ₀ _ _ (fun k t x ht => ?_) fun k => ?_
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.fsLogReg_smul h u' ε ht x
      · rfl
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε
      · exact contDiffOn_const
  have h2 : ∀ δ₀, 0 < δ₀ → Integrable (chartDens (W ⊔ Ideal.span {linForm hℓ.choose - 1}) hA.choose
      (fsLogReg h u δ₀) fun _ x => Real.log (h.dualNorm x)) := by
    intro δ₀ hδ₀
    have := hint δ₀ hδ₀ (fun _ => 1) (fun _ _ => 0) (fun _ _ _ _ => rfl) fun _ => contDiffOn_const
    simpa using this
  rw [← integral_add (h1 δ hδ) (h2 δ hδ), ← integral_add (h1 δ' hδ') (h2 δ' hδ')]
  refine integral_mono ((h1 δ hδ).add (h2 δ hδ)) ((h1 δ' hδ').add (h2 δ' hδ')) fun y => ?_

  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
  simp only [chartDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp [linForm] at this
  split_ifs with hs
  · have hpos := dens_sum_nonneg hD h u' hε hs.choose_spec hx0
    have hmono := mul_le_mul_of_nonneg_right (FubiniStudyLogRegularization.fsLogReg_mono h u hδ hδδ' x) hpos
    linarith
  · simp

end

end GroundTheory.Heights₂.Heights
end

