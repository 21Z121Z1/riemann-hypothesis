import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LeviTwistLower

theorem main : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  intro n M _ _ _ _ _ z φ ψ δ κ hz hφ hψ hψ0 hδ hκ hκ' hL
  obtain ⟨hκd, hκ1⟩ := contDiff_infty_iff_deriv.1 hκ
  have hκdd : Differentiable ℝ (deriv κ) := (contDiff_infty_iff_deriv.1 hκ1).1
  set k : ℝ → ℝ := fun t => κ (δ * t) with hkdef
  have hk : ContDiff ℝ ∞ k := hκ.comp (contDiff_const.mul contDiff_id)
  have hD : ∀ t, HasDerivAt k (deriv κ (δ * t) * δ) t := by
    intro t
    have h := (hκd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)
    simpa [hkdef, Function.comp_def] using h
  have hDk : deriv k = fun t => deriv κ (δ * t) * δ := funext fun t => (hD t).deriv
  have hDD : ∀ t, deriv (deriv k) t = deriv (deriv κ) (δ * t) * δ ^ 2 := by
    intro t
    rw [hDk]
    have h := ((hκdd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)).mul_const δ
    exact h.deriv.trans (by ring)
  have hks : SmoothR n z (fun x => κ (δ * ψ x)) := SmoothR.comp n z k hk ψ hψ
  refine ⟨hks, fun x ξ => ⟨?_, ?_⟩⟩
  · unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := db_comp_real n z k hk ψ (SmoothR.ckR n z 1 _ hψ) j x
    rw [(hD (ψ x)).deriv] at this
    change db n z j (fun y => ((k (ψ y) : ℝ) : ℂ)) x * _ = _
    rw [this]; ring
  · have hC := chain n M z hz k ψ (contDiff_infty.1 hk 2) hψ x ξ
    rw [(hD (ψ x)).deriv, hDD (ψ x)] at hC
    have hnorm : ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ = ‖dDot n z (fun y => (ψ y : ℂ)) x ξ‖ := by
      have : dbarDot n z (fun y => (ψ y : ℂ)) x ξ = (starRingEnd ℂ) (dDot n z (fun y => (ψ y : ℂ)) x ξ) := by
        unfold dbarDot dDot
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [db_ofReal n z ψ j x, map_mul]
      rw [this, Complex.norm_conj]
    have hsum : Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ =
        Levi n z φ x ξ + Levi n z ψ x ξ + Levi n z (fun y => k (ψ y)) x ξ := by
      rw [levi_add n z (fun y => φ y + ψ y) (fun y => κ (δ * ψ y))
        (SmoothR.ckR n z 2 _ (SmoothR.add n z _ _ hφ hψ)) (SmoothR.ckR n z 2 _ hks) x ξ,
        levi_add n z φ ψ (SmoothR.ckR n z 2 _ hφ) (SmoothR.ckR n z 2 _ hψ) x ξ]
    set α : ℝ := 1 + δ * deriv κ (δ * ψ x) with hα
    have hmem : α ∈ Set.Icc (1 : ℝ) (1 + δ) := by
      obtain ⟨h0, h1⟩ := hκ' (δ * ψ x) (mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x))
      constructor
      · nlinarith
      · nlinarith
    have hnn := hL α hmem x ξ
    rw [levi_add n z φ (fun y => α * ψ y) (SmoothR.ckR n z 2 _ hφ)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z α) hψ)) x ξ,
      levi_const_mul n z α ψ (SmoothR.ckR n z 2 _ hψ) x ξ] at hnn
    rw [hsum, hC, hnorm]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hnn ⊢
    rw [hα] at hnn
    nlinarith

end GlobalTheory.LeviTwistLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducible
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

namespace GlobalTheory.HcIrr

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

theorem map_mem_of_position_stable (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ (c : ι) (f : V c →ₗ[ℂ] V c), ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W)
    (f : ∀ i, V i →ₗ[ℂ] V i) : ∀ x ∈ W, PiTensorProduct.map f x ∈ W := by
  suffices H : ∀ S : Finset ι, ∀ x ∈ W,
      PiTensorProduct.map (fun c => if c ∈ S then f c else LinearMap.id) x ∈ W by
    intro x hx
    simpa using H Finset.univ x hx
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [PiTensorProduct.map_id] using hx
  | insert a S ha ih =>
    intro x hx
    have e : (fun c => if c ∈ insert a S then f c else (LinearMap.id : V c →ₗ[ℂ] V c)) = fun c =>
        (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) a (f a)) c ∘ₗ
          (if c ∈ S then f c else LinearMap.id) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc, Function.update_of_ne]
    rw [e, PiTensorProduct.map_comp]
    exact h a (f a) _ (ih x hx)

theorem position_stable_of_span {c : ι} {G : Type} [Group G] (ρ : Representation ℂ G (V c))
    (hs : Submodule.span ℂ (Set.range ρ) = ⊤) (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ g : G, ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (ρ g)) x ∈ W)
    (f : V c →ₗ[ℂ] V c) : ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W := by
  have hf : f ∈ Submodule.span ℂ (Set.range ρ) := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact h g
  | zero =>
    intro x _
    have := PiTensorProduct.map_update_smul (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (0 : ℂ)
      LinearMap.id
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp
  | add u v _ _ hu hv =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hu x hx) (hv x hx)
  | smul a u _ hu =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hu x hx)

theorem eq_bot_or_top_of_map_stable [∀ i, FiniteDimensional ℂ (V i)]
    (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ f : ∀ i, V i →ₗ[ℂ] V i, ∀ x ∈ W, PiTensorProduct.map f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let e := fun c => Module.finBasis ℂ (V c)
  let B := Basis.piTensorProduct e
  obtain ⟨I, hI⟩ : ∃ I, B.repr x I ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  have hJ : ∀ J, B J ∈ W := by
    intro J
    let f : ∀ c, V c →ₗ[ℂ] V c := fun c => ((e c).coord (I c)).smulRight (e c (J c))
    have hf : PiTensorProduct.map f = (B.coord I).smulRight (B J) := by
      refine B.ext fun p => ?_
      have hc : ∀ c, f c (e c (p c)) = (if p c = I c then (1 : ℂ) else 0) • e c (J c) := by
        intro c
        simp [f, Finsupp.single_apply]
      have hq : (∏ c, if p c = I c then (1 : ℂ) else 0) = if p = I then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      rw [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, hc,
        MultilinearMap.map_smul_univ, hq]
    have hm := h f x hx
    rw [hf, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hm
    exact (W.smul_mem_iff hI).1 hm
  refine eq_top_iff.2 ?_
  rw [← B.span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨J, rfl⟩; exact hJ J)

theorem nontrivial_piTensorProduct [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  let B := Basis.piTensorProduct fun c => Module.finBasis ℂ (V c)
  exact ⟨B fun c => ⟨0, Module.finrank_pos⟩, 0, B.ne_zero _⟩

end General

theorem leviTensor_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ)
    (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  intro K _ _ _ r s b lam hs
  have hirr := fun c => GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple (lam c) (hs c)
  have hspan := fun c => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ (lam c).ρ (hirr c)
  haveI : ∀ c, Nontrivial (lam c : Type) := fun c =>
    GlobalTheory.OuterTensor.nontrivial_of_isIrreducible _ (hirr c)
  haveI : Nontrivial (PiTensorProduct ℂ (fun c => (lam c : Type))) := nontrivial_piTensorProduct
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
      (⊥ : Submodule ℂ (PiTensorProduct ℂ (fun c => (lam c : Type)))) = ⊤)
  have hstable : ∀ (c : Fin s) (f : (lam c : Type) →ₗ[ℂ] (lam c : Type)), ∀ x ∈ S.toSubmodule,
      PiTensorProduct.map (Function.update
        (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c f) x ∈ S.toSubmodule := by
    intro c
    refine position_stable_of_span (lam c).ρ (hspan c) S.toSubmodule fun g x hx => ?_
    rw [← leviTensor_blockExt b lam c g]
    exact S.apply_mem_toSubmodule _ hx
  rcases eq_bot_or_top_of_map_stable S.toSubmodule (map_mem_of_position_stable _ hstable) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end GlobalTheory.HcIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem lintegral_nsq_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A la i W D hW hWt hD hae
  classical
  set e := A.chart i with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  have hT : MeasurableSet e.target := e.open_target.measurableSet

  set c : Y → V n := e.source.piecewise e (fun _ => 0) with hc
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const hS
  set P : V n → ℝ := e.target.piecewise (fun v => A.ph (A.kap + la) i (e.symm v)) (fun _ => 0) with hP
  have hPm : Measurable P :=
    ContinuousOn.measurable_piecewise (A.smooth_ph (A.kap + la) i).continuousOn continuousOn_const hT
  set D' : V n → ℂ := hae.mk _ with hD'
  have hD'm : Measurable D' := hae.measurable_mk
  have hDD' : (D i ∘ e.symm) =ᵐ[volume.restrict W] D' := hae.ae_eq_mk
  have hcs : ∀ y ∈ e.source, c y = e y := fun y hy => by simp [hc, hy]
  have hPt : ∀ v ∈ e.target, P v = A.ph (A.kap + la) i (e.symm v) := fun v hv => by simp [hP, hv]
  set S : Set Y := e.source ∩ c ⁻¹' W with hSdef
  have hSm : MeasurableSet S := hS.inter (hcm hW)
  have hSeq : e.source ∩ e ⁻¹' W = S := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
  set G : Y → ℝ≥0∞ := S.indicator (fun y => ENNReal.ofReal (‖D' (c y)‖ ^ 2 * Real.exp (-P (c y))))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact ENNReal.measurable_ofReal.comp
      (((hD'm.comp hcm).norm.pow_const 2).mul ((hPm.comp hcm).neg.exp))

  set T : Set (V n) := toMeasurable (volume.restrict W) {v | ¬ (D i ∘ e.symm) v = D' v}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume.restrict W T = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hDD'
  set E : Set Y := e.source ∩ c ⁻¹' (T ∩ W)
  have hEm : MeasurableSet E := hS.inter (hcm (hTm.inter hW))
  have hE0 : A.mu E = 0 := by
    rw [A.mu_chart i E hEm Set.inter_subset_left]
    apply setLIntegral_measure_zero
    refine measure_mono_null ?_ (show volume (T ∩ W) = 0 by
      rwa [Measure.restrict_apply hTm] at hT0)
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa [hcs y hy1] using hy2

  have hL : ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
      ∫⁻ y in e.source, G y ∂A.mu := by
    rw [hSeq]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
        ∫⁻ y in e.source, S.indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y)) y ∂A.mu := by
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_left.mpr Set.inter_subset_left]
    rw [h1]
    apply lintegral_congr_ae
    have hnE : ∀ᵐ y ∂A.mu, y ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [ae_restrict_of_ae hnE, ae_restrict_mem hS] with y hyE hys
    by_cases hyS : y ∈ S
    · simp only [G, Set.indicator_of_mem hyS]
      congr 1
      have hyW : e y ∈ W := by simpa [hcs y hys] using hyS.2
      have hyT : e y ∉ T := fun h => hyE ⟨hys, by simp [hcs y hys, h, hyW]⟩
      have hDy : D i y = D' (c y) := by
        rw [hcs y hys]
        have : (D i ∘ e.symm) (e y) = D' (e y) := by
          by_contra hne
          exact hyT (subset_toMeasurable _ _ hne)
        simpa [e.left_inv hys] using this
      have hPy : P (c y) = A.ph (A.kap + la) i y := by
        rw [hcs y hys, hPt _ (e.map_source hys), e.left_inv hys]
      rw [← hDy, hPy]

      unfold WeightedAtlas.nsq
      have hp := A.mem_pick y
      have hg := A.g_ne (A.kap + la) (A.pick y) i y hp hys
      have hg2 : 0 < ‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2 := by positivity
      have ht := A.ph_trans (A.kap + la) (A.pick y) i y hp hys
      rw [hD y hys hyW, norm_mul, mul_pow]
      have : A.ph (A.kap + la) (A.pick y) y =
          A.ph (A.kap + la) i y + Real.log (‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2) := by linarith
      rw [this, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hg2]
      field_simp
    · simp [G, Set.indicator_of_notMem hyS]

  rw [hL, ap_lintegral_chart A i G hGm]
  have h2 : ∫⁻ v in e.target, G (e.symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))) =
      ∫⁻ v in e.target, W.indicator (fun v => ENNReal.ofReal (‖D' v‖ ^ 2 * Real.exp (-P v)) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))) v := by
    refine setLIntegral_congr_fun hT fun v hv => ?_
    have hs := e.map_target hv
    have hcv : c (e.symm v) = v := by rw [hcs _ hs, e.right_inv hv]
    by_cases hvW : v ∈ W
    · have : e.symm v ∈ S := ⟨hs, by simpa [hcv] using hvW⟩
      simp only [G, Set.indicator_of_mem this, Set.indicator_of_mem hvW, hcv]
    · have : e.symm v ∉ S := fun h => hvW (by simpa [hcv] using h.2)
      simp [G, Set.indicator_of_notMem this, Set.indicator_of_notMem hvW]
  rw [h2, lintegral_indicator hW, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWt]
  apply lintegral_congr_ae
  filter_upwards [hDD', ae_restrict_mem hW] with v hv hvW
  have hvt := hWt hvW
  have hs := e.map_target hvt
  simp only [Function.comp_apply] at hv
  rw [← hv, hPt v hvt, A.ph_add A.kap la i _ hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_add, Real.exp_add]
  have := Real.exp_pos (A.ph A.kap i (e.symm v))
  rw [Real.exp_neg (A.ph A.kap i _)]
  field_simp

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixCoprimeDecomposition
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {S : Scheme.{0}}

def postHom {T A : Over S} [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] : (T ⟶ A) →* (T ⟶ A) where
  toFun f := f ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' f g := MonObj.mul_comp _ _ _

theorem bilin_ext {M La Q I J : Type} [AddCommGroup M] [AddCommGroup La] [CommGroup Q] [Fintype I] [Fintype J]
    (bM : Module.Basis I ℤ M) (bL : Module.Basis J ℤ La) (F G : M → La → Q)
    (hF1 : ∀ c c' a, F (c + c') a = F c a * F c' a) (hF2 : ∀ c a a', F c (a + a') = F c a * F c a')
    (hG1 : ∀ c c' a, G (c + c') a = G c a * G c' a) (hG2 : ∀ c a a', G c (a + a') = G c a * G c a')
    (h : ∀ i j, F (bM i) (bL j) = G (bM i) (bL j)) : ∀ c a, F c a = G c a := by
  intro c a
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => F c a) (fun c c' => hF1 c c' a) c,
    GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => G c a) (fun c c' => hG1 c c' a) c]
  refine Finset.prod_congr rfl fun i _ => ?_
  beta_reduce
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bL (F (bM i)) (hF2 _) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bL (G (bM i)) (hG2 _) a]
  simp only [h]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Kil {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (f : T ⟶ o.A) : Prop :=
  ∀ c ∈ w0 ^ r, f ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1

theorem Kil.comp {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T T' : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (h : T' ⟶ T) : Kil o w0 r (h ≫ f) := fun c hc => by
  rw [Category.assoc, hf c hc, MonObj.comp_one]

theorem Kil.act {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (d : D.O) : Kil o w0 r (f ≫ o.act.act d) := fun c hc => by
  haveI := o.act.hom d
  rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, hf c hc, MonObj.one_comp]

theorem vanish {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} (l : D.La → (T ⟶ o.A)) (hadd : ∀ x y, l (x + y) = l x * l y)
    (hlin : ∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) (hk : ∀ a, Kil o w0 r (l a)) :
    ∀ x ∈ wSub D w0 r, l x = 1 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [hlin]
    exact hk z' c hc
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  | add x y _ _ hx hy => rw [hadd, hx, hy, _root_.mul_one]
  | smul d x _ hx =>
    haveI := o.act.hom d
    rw [hlin, hx, MonObj.one_comp]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev

open RepLat in

theorem exists_finiteEtale_linTorsHom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ x y, et (x + y) = et x * et y) ∧ (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) ∧ (∀ x ∈ wSub D w0 r, et x = 1) ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), (∀ x y, l (x + y) = l x * l y) → (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, l x = 1) → ∃! h : T ⟶ Z, ∀ y, h ≫ et y = l y := by
  intro p _ D R _ b N w0 r _ S _ s o K κ hKf hKe hκ hK
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI := hKf
  haveI := hKe
  have hκ' : Kil o w0 r κ := hκ
  have hcan : ∀ {T : Over S} (v v' : T ⟶ K), v ≫ κ = v' ≫ κ → v = v' := fun v v' e =>
    (hK _ (v' ≫ κ) (hκ'.comp v')).unique e rfl
  have hfac : ∀ {T : Over S} (f : T ⟶ o.A), Kil o w0 r f → ∃ u : T ⟶ K, u ≫ κ = f := fun f hf =>
    (hK _ f hf).exists
  let bb := Module.finBasis ℤ D.La
  let n := Module.finrank ℤ D.La
  let bO := Module.finBasis ℤ D.O
  let Z₀ := Out.powObj K n
  let x : Fin n → (Z₀ ⟶ o.A) := fun i => Out.powPr K i ≫ κ
  let et₀ : D.La → (Z₀ ⟶ o.A) := fun a => ∏ i, x i ^ (bb.repr a i)
  have hadd : ∀ a c, et₀ (a + c) = et₀ a * et₀ c := fun a c => by
    simp only [et₀, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et₀ (bb i) = x i := fun i => by
    simp only [et₀, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  have hkil : ∀ a, Kil o w0 r (et₀ a) := fun a c hc => by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    change postHom (T := Z₀) _ (∏ i, x i ^ (bb.repr a i)) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_zpow]
    change (x i ≫ _) ^ _ = 1
    rw [(hκ'.comp (Out.powPr K i)) c hc, one_zpow]
  haveI hZf : IsFinite Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @IsFinite K hKf n
  haveI hZe : Etale Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @Etale K hKe n
  have c1 : ClopenCond Z₀ fun _ h => ∀ (c : D.O) a, h ≫ et₀ (c • a) = h ≫ (et₀ a ≫ o.act.act c) := by
    have hfin : ClopenCond Z₀ fun _ h => ∀ ji : Fin (Module.finrank ℤ D.O) × Fin n,
        h ≫ et₀ (bO ji.1 • bb ji.2) = h ≫ (et₀ (bb ji.2) ≫ o.act.act (bO ji.1)) := by
      refine ClopenCond.forall_finite fun ji => ?_
      obtain ⟨u, hu⟩ := hfac _ (hkil (bO ji.1 • bb ji.2))
      obtain ⟨u', hu'⟩ := hfac _ ((hkil (bb ji.2)).act (bO ji.1))
      refine (clopenCond_eq u u').congr fun T' h => ?_
      rw [← hu, ← hu', ← Category.assoc, ← Category.assoc]
      exact ⟨hcan _ _, fun e => by rw [e]⟩
    refine hfin.congr fun T' h => ⟨fun H ji => H _ _, fun H => ?_⟩
    refine bilin_ext bO bb (fun c a => h ≫ et₀ (c • a)) (fun c a => h ≫ (et₀ a ≫ o.act.act c))
      (fun c c' a => by beta_reduce; rw [add_smul, hadd, MonObj.comp_mul])
      (fun c a a' => by beta_reduce; rw [smul_add, hadd, MonObj.comp_mul])
      (fun c c' a => by beta_reduce; rw [o.act.add, MonObj.comp_mul, MonObj.comp_mul])
      (fun c a a' => by
        beta_reduce
        haveI := o.act.hom c
        rw [hadd, MonObj.mul_comp, MonObj.comp_mul])
      (fun j i => H (j, i))
  obtain ⟨U, hU, HU⟩ := c1
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU V i).2 ((Hi V i).2 ⟨𝟙 V, Category.id_comp i⟩)
  have hVadd : ∀ a c, i ≫ et₀ (a + c) = (i ≫ et₀ a) * (i ≫ et₀ c) := fun a c => by
    rw [hadd, MonObj.comp_mul]
  have hVlin : ∀ (c : D.O) a, i ≫ et₀ (c • a) = (i ≫ et₀ a) ≫ o.act.act c := fun c a => by
    rw [hi, Category.assoc]
  refine ⟨V, fun a => i ≫ et₀ a, hV1, hV2, hVadd, hVlin,
    vanish _ hVadd hVlin fun a => (hkil a).comp i, fun T l hladd hllin hlw => ?_⟩
  have hlk : ∀ a, Kil o w0 r (l a) := fun a c hc => by
    rw [← hllin]
    exact hlw _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  choose y hy using fun j : Fin n => hfac _ (hlk (bb j))
  let h : T ⟶ Z₀ := (Out.powIsLimit K n).lift (Fan.mk T y)
  have hh : ∀ j, h ≫ Out.powPr K j = y j := fun j => (Out.powIsLimit K n).fac (Fan.mk T y) ⟨j⟩
  have hhe : ∀ a, h ≫ et₀ a = l a := fun a => by
    rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bb (fun a => h ≫ et₀ a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
      GlobalTheory.LatticeTorsion.eq_prod_zpow bb l hladd a]
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [hb, ← hy j, ← hh j, Category.assoc]
  have hext : ∀ u u' : T ⟶ Z₀, (∀ a, u ≫ et₀ a = u' ≫ et₀ a) → u = u' := fun u u' e =>
    (Out.powIsLimit K n).hom_ext fun ⟨j⟩ => by
      have := e (bb j)
      rw [hb] at this
      exact hcan _ _ (by simp only [x, Category.assoc] at this; exact this)
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 fun c a => by rw [hhe, hllin, ← hhe a, Category.assoc])
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hhe], fun g hg => ?_⟩
  exact (cancel_mono i).1 (hext _ _ fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hhe])

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespondStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechDegreeZero_cocycles_correspond : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧ ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  first | exact @GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond | exact GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond | (intros; apply GlobalTheory.CechPoset.orderedCech_degreeZero_cocycles_correspond <;> assumption)
end

