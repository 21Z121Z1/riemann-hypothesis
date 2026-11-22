import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

theorem exists_int_mul_integral (x : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * x) := by
  have h : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using hi⟩

omit [IsCMField E] in

theorem finite_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (k : ℤ) (hk : k ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ ((k : E) * x) ∧ ∀ τ : Ψ, ‖τ.1 x‖ ≤ R}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (‖(k : ℂ)‖ * R)
  have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
  refine Set.Finite.of_finite_image (f := fun x => (k : E) * x) (hfin.subset ?_)
    (fun x _ y _ h => mul_left_cancel₀ hk' h)
  rintro _ ⟨x, ⟨hi, hb⟩, rfl⟩
  refine ⟨hi, fun φ => ?_⟩
  have : ‖φ x‖ ≤ R := by
    by_cases hφ : φ ∈ Ψ
    · exact hb ⟨φ, hφ⟩
    · have h2 : ComplexEmbedding.conjugate φ ∈ Ψ := by
        by_contra h3
        exact hφ ((hΨ φ).2 h3)
      have := hb ⟨_, h2⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

omit [IsCMField E] in

theorem exists_common_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ v ∈ Λ, ∀ a, IsIntegral ℤ ((k : E) * v a) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  choose d hd hdi using (exists_int_mul_integral (E := E))
  refine ⟨∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin r)), d (p.1 p.2),
    Finset.prod_ne_zero_iff.2 fun p _ => hd _, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro a
    have hm : (v, a) ∈ S ×ˢ (Finset.univ : Finset (Fin r)) :=
      Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : (Fin r → E) × Fin r => d (p.1 p.2)) hm
    rw [hc]
    have := (hdi (v a)).mul (isIntegral_algebraMap (R := ℤ) (A := E) (x := c))
    have e : ((d (v a) * c : ℤ) : E) * v a = (d (v a) : E) * v a * algebraMap ℤ E c := by
      simp only [Int.cast_mul, eq_intCast]
      ring
    exact e ▸ this
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro a
    rw [Pi.add_apply, mul_add]
    exact (hx a).add (hy a)
  | smul c x _ hx =>
    intro a
    have := (hx a).mul (RingOfIntegers.isIntegral_coe c)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, mul_comm]
    exact this

omit [IsCMField E] in

theorem exists_int_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiples.main
  | exact _root_.GlobalTheory.IntegralMultiples.main
  | (apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiples.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiples.main ..)

theorem finite_vectors (r : ℕ) (X : Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  refine (Set.Finite.pi' fun _ : Fin r => finite_bounded X.Ψ X.cmType k hk R).subset ?_
  rintro v ⟨hv, hb⟩ a
  exact ⟨hi v hv a, fun τ => hb τ a⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem latFin : ((∀ (r : ℕ) (X : Data E r) (R : ℝ), {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite) ∧ (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite)) :=
  ⟨finite_vectors, finite_automorphisms⟩

end GlobalTheory.LatFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndexRangeMulVecLinEqAbsNormDet
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in

theorem _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 E)), A.det ≠ 0 →
      (((LinearMap.range A.mulVecLin).toAddSubgroup.index : ℕ) : ℚ) =
        |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|) := by
  intro ι _ _ A hA
  classical
  set f := A.mulVecLin with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h : A.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hA h)
  let b := Module.Free.chooseBasis ℤ (ι → 𝓞 E)
  let fZ : (ι → 𝓞 E) →ₗ[ℤ] (ι → 𝓞 E) := f.restrictScalars ℤ
  have hinjZ : Function.Injective fZ := hinj
  let e := LinearEquiv.ofInjective fZ hinjZ
  have key := AddSubgroup.index_eq_natAbs_det b (LinearMap.range f).toAddSubgroup (b.map e)
  rw [key]
  have hdet : (b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)) = LinearMap.det fZ := by
    rw [Module.Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, e]
  have h2 : (((b.det fun i ↦ ((b.map e i : LinearMap.range fZ) : ι → 𝓞 E)).natAbs : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    rw [hdet, LinearMap.det_restrictScalars, hf, ← Matrix.toLin'_apply', LinearMap.det_toLin',
      Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSplit

theorem lintegral_le_of_section {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [ProperSpace A] [ProperSpace B]
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure B) [ν.IsAddHaarMeasure]
    (L : A → B) (hL : Continuous L) (hadd : ∀ x y, L (x + y) = L x + L y)
    (s : B → A) (hs : ∀ b, L (s b) = b) (S : Set A) (hS : MeasurableSet S)
    (hinv : ∀ b x, s b + x ∈ S ↔ x ∈ S)
    (hb : ∀ C : ℝ, ∃ D : ℝ, ∀ x ∈ S, ‖L x‖ ≤ C → ‖x‖ ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : B → ℝ≥0∞, Measurable g →
      ∫⁻ y in S, g (L y) ∂μ ≤ K * ∫⁻ z, g z ∂ν := by
  have hLm : Measurable L := hL.measurable
  set ρ : Measure B := (μ.restrict S).map L with hρ
  have happ : ∀ T : Set B, MeasurableSet T → ρ T = μ (L ⁻¹' T ∩ S) := by
    intro T hT
    rw [hρ, Measure.map_apply hLm hT, Measure.restrict_apply (hLm hT)]
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun T hT => ?_⟩
    obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := hb C
    rw [happ T hT.measurableSet]
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 D) ?_)
      (isCompact_closedBall (0 : A) D).measure_lt_top
    intro x hx
    simpa using hD x hx.2 (hC _ hx.1)
  haveI : ρ.IsAddLeftInvariant := by
    refine ⟨fun b => ?_⟩
    ext T hT
    have hm : Measurable fun z : B => b + z := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hT, happ _ (hm hT), happ _ hT,
      ← measure_preimage_add μ (s b) (L ⁻¹' T ∩ S)]
    congr 1
    ext x
    simp [hadd, hs, hinv]
  refine ⟨(ρ.addHaarScalarFactor ν : ℝ≥0∞), ENNReal.coe_lt_top, fun g hg => le_of_eq ?_⟩
  rw [← lintegral_map hg hLm, ← hρ]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ρ ν]
  rw [lintegral_smul_measure]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frameSplit : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by
  intro r X R
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  refine lintegral_le_of_section (volume : Measure (Frame X.Ψ r)) (volume : Measure (V (nd X)))
    (fun y => WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
      ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2)
    ?_ ?_
    (fun z τ a c => if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0)
    ?_ _ ?_ ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fun_prop
  · intro x y
    ext j
    simp
  · intro z
    ext j
    have h := ((Fintype.equivFin (Ent X)).symm j).2.2
    simp only [dif_pos h]
    exact congrArg (fun k => z k) ((Fintype.equivFin (Ent X)).apply_symm_apply j)
  · apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop
  · intro z x
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    refine forall_congr' fun τ => forall_congr' fun a => forall_congr' fun c =>
      forall_congr' fun h => ?_
    rw [dif_neg h, zero_add]
  · intro C
    refine ⟨max (max C R) 0, fun x hx hC => ?_⟩
    have h0 : 0 ≤ max (max C R) 0 := le_max_right _ _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun c => ?_
    by_cases h : c < a
    · have := (PiLp.norm_apply_le _ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).trans hC
      have h' : ‖x τ a c‖ ≤ C := by
        have e := (Fintype.equivFin (Ent X)).symm_apply_apply ⟨τ, ⟨(a, c), h⟩⟩
        simp only at this
        erw [e] at this
        exact this
      exact h'.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hx τ a c h).trans ((le_max_right _ _).trans (le_max_left _ _))

end GlobalTheory.FrameSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulProd
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeadBound

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)

def IsDom (la : Wt X.Ψ r) (n : ℕ) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsBddSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * g x ^ n

variable {X g}

theorem IsDom.of_bdd {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (h : X.IsBddSec la P) :
    IsDom X g la 0 P := by
  obtain ⟨C, hC⟩ := h.2
  exact ⟨h, C, fun x hx => by simpa using hC x hx⟩

theorem IsDom.zero (la : Wt X.Ψ r) (n : ℕ) : IsDom X g la n 0 :=
  ⟨bdd_zero X la, 0, fun x _ => by simp [Data.pnorm]⟩

theorem IsDom.add {la : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la n Q) : IsDom X g la n (P + Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_add X hP.1 hQ.1, C + C', fun x hx => ?_⟩
  calc X.pnorm la (P + Q) x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (nfac_nonneg X la x)
    _ = X.pnorm la P x + X.pnorm la Q x := by rw [add_mul]; rfl
    _ ≤ C * g x ^ n + C' * g x ^ n := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * g x ^ n := by ring

theorem IsDom.smul {la : Wt X.Ψ r} {n : ℕ} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : IsDom X g la n P) :
    IsDom X g la n (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨bdd_smul X a hP.1, ‖a‖ * C, fun x hx => ?_⟩
  calc X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
        rw [pnorm_eq, pnorm_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    _ ≤ ‖a‖ * (C * g x ^ n) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg a)
    _ = ‖a‖ * C * g x ^ n := by ring

theorem IsDom.mul {la la' : Wt X.Ψ r} {n n' : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la' n' Q) : IsDom X g (la + la') (n + n') (P * Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_mul X hP.1 hQ.1, C * C', fun x hx => ?_⟩
  have e : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x := by
    rw [pnorm_eq, pnorm_eq, pnorm_eq, Pi.mul_apply, norm_mul, nfac_add X hx]
    ring
  rw [e]
  calc X.pnorm la P x * X.pnorm la' Q x ≤ (C * g x ^ n) * (C' * g x ^ n') :=
        mul_le_mul (hC x hx) (hC' x hx) (pnorm_nonneg X _ _ _)
          ((pnorm_nonneg X _ _ _).trans (hC x hx))
    _ = C * C' * g x ^ (n + n') := by ring

theorem IsDom.sum {ι : Type*} (S : Finset ι) {la : Wt X.Ψ r} {n : ℕ} {P : ι → Frame X.Ψ r → ℂ}
    (hP : ∀ i ∈ S, IsDom X g la n (P i)) : IsDom X g la n (∑ i ∈ S, P i) :=
  Finset.sum_induction P (IsDom X g la n) (fun _ _ ha hb => ha.add hb) (IsDom.zero la n) hP

theorem IsDom.mul_pow {la L : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hQ : IsDom X g la n Q)
    (hP : IsDom X g L 1 P) (m : ℕ) : IsDom X g (la + m • L) (n + m) (Q * P ^ m) := by
  induction m with
  | zero => simpa using hQ
  | succ m ih =>
    have h := ih.mul hP
    rwa [add_assoc, ← succ_nsmul, add_assoc, mul_assoc, ← pow_succ] at h

theorem IsDom.mul_prod {ι : Type*} (S : Finset ι) {la L : Wt X.Ψ r} {n : ℕ} {Q : Frame X.Ψ r → ℂ}
    {P : ι → Frame X.Ψ r → ℂ} (hQ : IsDom X g la n Q) (hP : ∀ i, IsDom X g L 1 (P i)) (α : ι → ℕ) :
    IsDom X g (la + (∑ i ∈ S, α i) • L) (n + ∑ i ∈ S, α i) (Q * ∏ i ∈ S, P i ^ α i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hQ
  | insert a S ha ih =>
    have h := ih.mul_pow (hP a) (α a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), mul_comm (P a ^ α a), add_nsmul,
      ← add_assoc, ← add_assoc, ← mul_assoc]
    exact h

theorem IsDom.of_sq_le {W : Frame X.Ψ r → ℝ} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {K : ℝ} (hW : ∀ x, 0 ≤ W x)
    (hK : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * W x) :
    IsDom X (fun x => Real.sqrt (W x)) la 1 P := by
  refine ⟨hP, Real.sqrt K, fun x hx => ?_⟩
  rw [pow_one, ← Real.sqrt_mul' _ (hW x)]
  exact Real.le_sqrt_of_sq_le (hK x hx)

end

theorem main : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ), a ≤ T + 1 →
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec G (t k)) → ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
    X.IsBddSec (G + T • Xa.L) (leadM X Fl.s Fl.w0 t T a cc) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + T • Xa.L) (leadM X Fl.s Fl.w0 t T a cc) x ^ 2 ≤
      C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ T := by
  intro r X Xa Fl G T a δ ha t ht cc
  set W : Frame X.Ψ r → ℝ := fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWdef
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨K0, hK0⟩ := Fl.denom_le_family
  obtain ⟨K1, hK1⟩ := Fl.s_le_w
  have hw0 : IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 Fl.w0 :=
    IsDom.of_sq_le Fl.weightForm_vanishes.1.1 hW hK0
  have hs : ∀ k, IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 (Fl.s k) := fun k =>
    IsDom.of_sq_le (Fl.s_van k).1.1 hW (K := K1) fun x hx =>
      (Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Fl.s k) x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)).trans (hK1 x hx)
  have e : leadM X Fl.s Fl.w0 t T a cc = ∑ α ∈ multiLt (nd X) a, ∑ k,
      cc α k • (t k * (∏ q, Fl.s q ^ α q) * Fl.w0 ^ (T - ∑ q, α q)) := by
    funext x
    simp only [leadM, monoM, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hD : IsDom X (fun x => Real.sqrt (W x)) (G + T • Xa.L) T (leadM X Fl.s Fl.w0 t T a cc) := by
    rw [e]
    refine IsDom.sum _ fun α hα => IsDom.sum _ fun k _ => IsDom.smul _ ?_
    have hlt : ∑ q, α q < a := by
      simpa [multiLt, Finset.Nat.mem_antidiagonalTuple] using hα
    have hle : ∑ q, α q ≤ T := by omega
    have h := ((IsDom.of_bdd (ht k)).mul_prod Finset.univ hs α).mul_pow hw0 (T - ∑ q, α q)
    rwa [add_assoc, ← add_nsmul, zero_add, Nat.add_sub_cancel' hle] at h
  obtain ⟨hb, C, hC⟩ := hD
  refine ⟨hb, C ^ 2, fun x hx => ?_⟩
  calc _ ≤ (C * Real.sqrt (W x) ^ T) ^ 2 :=
        pow_le_pow_left₀ (pnorm_nonneg X _ _ _) (hC x hx) 2
    _ = C ^ 2 * (Real.sqrt (W x) ^ 2) ^ T := by ring
    _ = C ^ 2 * W x ^ T := by rw [Real.sq_sqrt (hW x)]

end GlobalTheory.LeadBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
section
open Metric

namespace GlobalTheory

theorem norm_fderiv_le_of_closedBall_subset {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set H} {f : H → ℂ} {C r : ℝ} {y : H} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hy : closedBall y r ⊆ U) (hC : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hyU : y ∈ U := hy (mem_closedBall_self hr.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hyU)
  refine ContinuousLinearMap.opNorm_le_bound' _ (div_nonneg hC0 hr.le) fun v hv => ?_
  have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hR : 0 < r / ‖v‖ := div_pos hr hv0
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (r / ‖v‖), y + t • v ∈ U := by
    intro t ht
    apply hy
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (le_div_iff₀ hv0).1 ht
  have hlin : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hd : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 (r / ‖v‖)) := by
    intro t ht
    exact ((hf.differentiableAt (hU.mem_nhds (hmem t ht))).comp t
      (hlin t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball 0 (r / ‖v‖)) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball _ hR.ne'])
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
    have h1 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rw [hder.deriv] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

theorem differentiableOn_tsum_of_norm_le :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H)
      (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u →
      (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro H _ _ ι U f u hU hf hu hb x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : ∀ y ∈ ball x (ε / 2), closedBall y (ε / 2) ⊆ U := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have h := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (f := f)
    (f' := fun i y => fderiv ℂ (f i) y) (u := fun i => u i / (ε / 2)) (s := ball x (ε / 2))
    (x₀ := x) (x := x) (hu.div_const _) isOpen_ball (convex_ball x _).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hsub y hy (mem_closedBall_self hr.le)))).hasFDerivAt)
    (fun i y hy => norm_fderiv_le_of_closedBall_subset hU (hf i) hr (hsub y hy) (hb i))
    (mem_ball_self hr) (Summable.of_norm_bounded hu (fun i => hb i x hx)) (mem_ball_self hr)
  exact h.differentiableAt.differentiableWithinAt

end GlobalTheory
end

