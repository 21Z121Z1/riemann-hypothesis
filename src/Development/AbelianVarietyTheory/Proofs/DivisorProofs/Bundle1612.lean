import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

theorem exists_isDens_pos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)],
    Nonempty (AnRead p σ 1) → ∃ w : AlgChart p σ 1 → CxPts p σ → ℝ,
      IsDens w ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y := by
  intro k _ X p σ _ _ _ ⟨R⟩
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2,
    ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩, fun c y hy => ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring
  · refine continuousOn_finset_sum _ fun i _ => ?_
    have hg : ContinuousOn (fun y => f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2)
        c.e.source := fun y hy => by
      refine ContinuousAt.continuousWithinAt ?_
      by_cases h : y ∈ tsupport (f i)
      · exact (f i).continuous.continuousAt.mul
          ((continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
        rw [hz, Pi.zero_apply, zero_mul]
    exact hg.comp c.e.continuousOn_symm fun v hv => c.e.map_target hv
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormType
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm.PullType

variable {n m : ℕ}

def scale (n : ℕ) (s t : ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.fromBlocks (s • 1) 0 0 (t • 1)))

theorem scale_single (s t : ℂ) (i : Fin (n + n)) :
    scale n s t (bas n {i}) = (if i.val < n then s else t) • bas n {i} := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [bas_singleton, ← map_smul]
  refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_))
  rcases i with i | i <;> rintro (b | b) <;> simp [Pi.single_apply, Matrix.one_apply]

theorem scale_bas (s t : ℂ) (S : Finset (Fin (n + n))) :
    scale n s t (bas n S) = (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) • bas n S := by
  induction S using Finset.induction_on with
  | empty => simp [bas_empty]
  | insert a S ha ih =>
    obtain ⟨ε, h⟩ := bas_mul (n := n) (S := {a}) (T := S) (by simpa using ha)
    have h' : bas n (insert a S) = ε • (bas n {a} * bas n S) := by
      rw [h, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]
    rw [h', Units.smul_def, map_zsmul, map_mul, scale_single, ih, smul_mul_smul_comm, smul_comm]
    congr 1
    rw [Finset.filter_insert, Finset.filter_insert]
    by_cases hn : a.val < n
    · rw [if_pos hn, if_pos hn, if_neg (not_le.2 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring
    · rw [if_neg hn, if_neg hn, if_pos (not_lt.1 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring

theorem repr_scale (s t : ℂ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (scale n s t α) S =
      (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) * (bas n).repr α S := by
  conv_lhs => rw [← (bas n).sum_repr α]
  simp only [map_sum, map_smul, scale_bas, Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem isType_iff (p q : ℕ) (α : Alt n) :
    IsType p q α ↔ scale n 2 1 α = (2 : ℂ) ^ p • α ∧ scale n 1 2 α = (2 : ℂ) ^ q • α := by
  have h2 {a b : ℕ} (h : (2 : ℂ) ^ a = 2 ^ b) : a = b := by
    have : (2 : ℕ) ^ a = 2 ^ b := by exact_mod_cast h
    exact Nat.pow_right_injective le_rfl this
  constructor
  · intro h
    constructor <;> refine (bas n).ext_elem fun S => ?_ <;>
      rw [repr_scale, map_smul, Finsupp.smul_apply, smul_eq_mul] <;>
      by_cases hS : (bas n).repr α S = 0
    · simp [hS]
    · simp [(h S hS).1]
    · simp [hS]
    · simp [(h S hS).2]
  · rintro ⟨h₁, h₂⟩ S hS
    have e₁ := congrArg (fun β => (bas n).repr β S) h₁
    have e₂ := congrArg (fun β => (bas n).repr β S) h₂
    simp only [repr_scale, map_smul, Finsupp.smul_apply, smul_eq_mul, one_pow, mul_one, one_mul] at e₁ e₂
    exact ⟨h2 (mul_right_cancel₀ hS e₁), h2 (mul_right_cancel₀ hS e₂)⟩

theorem scale_pull (L : V n →L[ℂ] V m) (s t : ℂ) (α : Alt m) :
    scale n s t (pull L α) = pull L (scale m s t α) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, scale, scale, pull, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  simp [Matrix.fromBlocks_multiply]

end GlobalTheory.CxForm.PullType

namespace GlobalTheory.CxForm

theorem isType_pull_linear (n m : ℕ) (L : V n →L[ℂ] V m) (p q : ℕ) (α : Alt m) (h : IsType p q α) :
    IsType p q (pull L α) := by
  rw [PullType.isType_iff] at h ⊢
  rw [PullType.scale_pull, PullType.scale_pull, h.1, h.2, map_smul, map_smul]
  exact ⟨rfl, rfl⟩

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotStages
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.QuotStage

open Matrix

theorem quotGram_eq_inv_toBlocks₂₂ {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) (hH : IsUnit H.det)
    (hu : IsUnit (subGram H).det) : quotGram H = (H⁻¹.toBlocks₂₂)⁻¹ := by
  have hS : IsUnit (quotGram H).det := isUnit_det_quotGram hH hu
  letI iA : Invertible H.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  have hS' : IsUnit (H.toBlocks₂₂ - H.toBlocks₂₁ * ⅟H.toBlocks₁₁ * H.toBlocks₁₂).det := by
    rw [invOf_eq_nonsing_inv]; exact hS
  letI iS : Invertible (H.toBlocks₂₂ - H.toBlocks₂₁ * ⅟H.toBlocks₁₁ * H.toBlocks₁₂) :=
    invertibleOfIsUnitDet _ hS'
  letI iH : Invertible (fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂) :=
    fromBlocks₁₁Invertible _ _ _ _
  have h1 : H⁻¹ = ⅟(fromBlocks H.toBlocks₁₁ H.toBlocks₁₂ H.toBlocks₂₁ H.toBlocks₂₂) := by
    rw [invOf_eq_nonsing_inv, fromBlocks_toBlocks]
  rw [h1, invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₂₂, ← invOf_eq_nonsing_inv (⅟ _), invOf_invOf,
    quotGram, invOf_eq_nonsing_inv]

theorem quotStages : ∀ (m l n : Type) [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l] [DecidableEq n], (∀ K : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ, K.PosDef → subGram (quotGram K) = quotGram (K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) ∧ quotGram (quotGram K) = quotGram (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))) ∧ ∀ (m' l' : Type) [Fintype m'] [Fintype l'] [DecidableEq m'] (e : m' ≃ m) (f : l' → l) (K : Matrix (m ⊕ l) (m ⊕ l) ℂ), quotGram (K.submatrix (Sum.map e f) (Sum.map e f)) = (quotGram K).submatrix f f := by
  intro m l n _ _ _ _ _ _
  refine ⟨fun K hK => ⟨?_, ?_⟩, ?_⟩
  · have h11 : (K.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).toBlocks₁₁ = K.toBlocks₁₁ := by
      ext; rfl
    rw [quotGram, quotGram, h11, subGram]
    ext i j
    simp only [toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply, Matrix.sub_apply, mul_apply,
      submatrix_apply, Sum.map_inl, Sum.map_inr, id]
  · have hKu : IsUnit K.det := (isUnit_iff_isUnit_det _).1 hK.isUnit
    have hKs : IsUnit (subGram K).det := (isUnit_iff_isUnit_det _).1 (posDef_subGram hK).isUnit
    have hQ := posDef_quotGram hK
    have hQu : IsUnit (quotGram K).det := (isUnit_iff_isUnit_det _).1 hQ.isUnit
    have hQs : IsUnit (subGram (quotGram K)).det :=
      (isUnit_iff_isUnit_det _).1 (posDef_subGram hQ).isUnit
    have hB : (K⁻¹.toBlocks₂₂).PosDef := hK.inv.submatrix Sum.inr_injective
    have hBu : IsUnit (K⁻¹.toBlocks₂₂).det := (isUnit_iff_isUnit_det _).1 hB.isUnit
    have hQinv : (quotGram K)⁻¹ = K⁻¹.toBlocks₂₂ := by
      rw [quotGram_eq_inv_toBlocks₂₂ K hKu hKs, nonsing_inv_nonsing_inv _ hBu]
    have hK' := hK.submatrix (Equiv.sumAssoc m l n).injective
    have hK'u : IsUnit (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)).det :=
      (isUnit_iff_isUnit_det _).1 hK'.isUnit
    have hK's : IsUnit (subGram (K.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))).det :=
      (isUnit_iff_isUnit_det _).1 (posDef_subGram hK').isUnit
    rw [quotGram_eq_inv_toBlocks₂₂ _ hQu hQs, hQinv, quotGram_eq_inv_toBlocks₂₂ _ hK'u hK's,
      inv_submatrix_equiv]
    rfl
  · intro m' l' _ _ _ e f K
    have h11 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₁ = K.toBlocks₁₁.submatrix e e := by
      ext; rfl
    have h12 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₁₂ = K.toBlocks₁₂.submatrix e f := by
      ext; rfl
    have h21 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₁ = K.toBlocks₂₁.submatrix f e := by
      ext; rfl
    have h22 : (K.submatrix (Sum.map e f) (Sum.map e f)).toBlocks₂₂ = K.toBlocks₂₂.submatrix f f := by
      ext; rfl
    rw [quotGram, quotGram, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv,
      submatrix_mul_equiv]
    rfl

end GlobalTheory.QuotStage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMetricNormProductFormula
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem quotGram_pyth_rankTwo (G : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (hG : G.PosDef)
    (x : Fin 1 ⊕ Fin 1 → ℂ) (τ : ℂ) (v : Fin 1 → ℂ) (hv : v 0 = x (.inr 0)) :
    (form (quotGram G) v v).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re =
      (form G x x).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re -
        ‖form G x (Sum.elim (fun _ => τ) 0)‖ ^ 2 := by
  have hH := hG.isHermitian
  have h11 : G (.inl 0) (.inl 0) ≠ 0 := (hG.diag_pos (i := .inl 0)).ne'
  have hr : starRingEnd ℂ (G (.inl 0) (.inl 0)) = G (.inl 0) (.inl 0) := hH.apply _ _
  have h12 : G (.inl 0) (.inr 0) = starRingEnd ℂ (G (.inr 0) (.inl 0)) := (hH.apply _ _).symm
  have hinv : (G.toBlocks₁₁)⁻¹ 0 0 = (G (.inl 0) (.inl 0))⁻¹ := by
    rw [Matrix.inv_def, Matrix.det_unique, Matrix.adjugate_fin_one]
    simp [Matrix.toBlocks₁₁, Ring.inverse_eq_inv']
  obtain ⟨r, hr'⟩ : ∃ r : ℝ, G (.inl 0) (.inl 0) = r := ⟨_, (Complex.conj_eq_iff_re.1 hr).symm⟩
  simp only [form_eq_sum, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, mul_zero, add_zero,
    quotGram, Matrix.sub_apply, Matrix.mul_apply, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁,
    Matrix.toBlocks₁₂, Matrix.of_apply, Fin.default_eq_zero]
  rw [hinv, hv, h12]
  rw [hr'] at h11 ⊢
  generalize x (Sum.inl 0) = x₁ at ⊢
  generalize x (Sum.inr 0) = x₂ at ⊢
  generalize G (Sum.inr 0) (Sum.inl 0) = g at ⊢
  generalize G (Sum.inr 0) (Sum.inr 0) = d at ⊢
  have hr0 : (r : ℂ) ≠ 0 := h11
  have hB : τ * (r : ℂ) * starRingEnd ℂ τ + 0 * g * starRingEnd ℂ τ =
      ((r * Complex.normSq τ : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.mul_conj]; ring
  have hn (z : ℂ) : ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hB, Complex.ofReal_re, hn, ← Complex.re_mul_ofReal, ← Complex.re_mul_ofReal, ← Complex.sub_re]
  congr 1
  simp only [Complex.ofReal_mul, ← Complex.mul_conj, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]
  field_simp
  ring

theorem quot_form_pyth_rankTwo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)),
    IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U,
      ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re =
        (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  intro k _ X p σ S h hS h₁ h₃ U t w _ y hy
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  let u : Γ(S.X₂, U) → Fin 1 ⊕ Fin 1 → ℂ := fun s i => (a.mid hS).crd p σ s y (finSumFinEquiv i)
  have hform (s s' : Γ(S.X₂, U)) : h.form s s' y = form (h.gram a.frame y) (u s) (u s') := by
    rw [h.form_eq (a.mid hS) ha s s' hy, h.gram_frame hS a ha, form_eq_sum, form_eq_sum,
      ← finSumFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← finSumFinEquiv.sum_comp]
    rfl
  have hf : u (S.f.app U t) = Sum.elim (fun _ => a.sub.crd p σ t y 0) 0 := by
    funext i
    refine (congrFun ((a.mid hS).crd_app a.sub S.f t hy ha) (finSumFinEquiv i)).trans ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one]
    have e := a.crd_frame hS ha i (.inl 0)
    refine (congrArg (· * _) e).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply, Subsingleton.elim i 0]
  have hg : a.quot.crd p σ (S.g.app U w) y 0 = u w (.inr 0) := by
    refine (congrFun (a.quot.crd_app (a.mid hS) S.g w hy ha) 0).trans ?_
    have e₃ (b) : (a.mid hS).e (finSumFinEquiv b) = a.frame b := by simp [VBExt.AdaptedChart.mid]
    have e₁ : a.quot.crd p σ (S.g.app a.U (a.frame (.inl 0))) y = 0 := by
      rw [show S.g.app a.U (a.frame (.inl 0)) = 0 from congr(($(S.zero)).app a.U (a.e 0)),
        Chart.crd_zero]
    have e₂ : a.quot.crd p σ (S.g.app a.U (a.frame (.inr 0))) y = Pi.single 0 1 :=
      a.quot.crd_frame ha 0
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
    refine (congrArg₂ (· + ·) (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₁) 0))
      (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₂) 0))).trans ?_
    simp [u]
  have hq : (h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y =
      form (quotGram (h.gram a.frame y)) (a.quot.crd p σ (S.g.app U w) y)
        (a.quot.crd p σ (S.g.app U w) y) := by
    rw [(h.quot hS h₁ h₃).form_eq a.quot ha _ _ hy, h.quot_G hS h₁ h₃ a ha]
  rw [hq, hform, hform, hform, hf]
  exact quotGram_pyth_rankTwo _ (h.posDef_gram_frame hS a ha) _ _ _ hg

end GlobalTheory.CurveDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_le_of_formallyUnramified (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Nontrivial C]
    [Algebra.FormallyUnramified B C] (g g' : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R B]
    [Algebra.IsStandardSmoothOfRelativeDimension g' R C] : g' ≤ g := by
  have : Nontrivial B := (algebraMap B C).domain_nontrivial
  have : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Free B Ω[B⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map R B C x).mp (Subsingleton.elim _ _)
  have h1 := LinearMap.rank_le_of_surjective _ hs
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g', Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g] at h1
  simpa using h1

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_surjective_away {R B A L : Type} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra A L] (t : A) [IsLocalization.Away t L] [Nontrivial L] (φ : R →+* B) (ψ : B →+* A)
    (hψ : Function.Surjective ψ) (g g' : ℕ) (hφ : RingHom.IsStandardSmoothOfRelativeDimension g φ)
    (hL : RingHom.IsStandardSmoothOfRelativeDimension g' ((algebraMap A L).comp (ψ.comp φ))) :
    g' ≤ g := by
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B A := ψ.toAlgebra
  letI : Algebra B L := ((algebraMap A L).comp ψ).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (ψ.comp φ)).toAlgebra
  haveI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyUnramified B A := Algebra.FormallyUnramified.of_surjective (Algebra.ofId B A) hψ
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g' R L := hL
  exact relDim_le_of_formallyUnramified R B L g g'

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G),
    IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  intro k _ N G ν hν ⟨x⟩ g g' hG hN
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hG.exists_isStandardSmoothOfRelativeDimension (ν.left x)
  let V' : N.left.Opens := ν.left ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage ν.left
  have hN' : SmoothOfRelativeDimension g' (ν.left ≫ G.hom) := by rw [Over.w ν]; exact hN
  have e' : V' ≤ (ν.left ≫ G.hom) ⁻¹ᵁ U := fun y hy => e hy
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g') _ hN' ⟨U, hU⟩ ⟨V', hV'⟩ e'
  have : Nonempty V' := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(N.left, V')
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1
      (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have hψ : Function.Surjective (ν.left.appLE V V' le_rfl).hom := by
    have := ν.left.app_surjective V hV
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this
  refine relDim_le_of_surjective_away (L := Localization.Away t) t (G.hom.appLE U V e).hom
    (ν.left.appLE V V' le_rfl).hom hψ g g' h ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE ν.left G.hom U V V' e le_rfl]
  exact h₁

end GlobalTheory
end

