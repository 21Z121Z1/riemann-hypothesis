import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreDerivativePolynomialValueAdd
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := GlobalTheory.T.laguerreSignedBinomCoeff_mul k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStripsStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  first | exact @GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | exact GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | (intros; apply GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem ratM_mulVec_tmul (γ : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ratM F γ *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (γ *ᵥ x) i := by
  ext i
  simp only [mulVec, dotProduct, ratM, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem ratM_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratM F γ *ᵥ fv F x = fv F (γ *ᵥ x) :=
  ratM_mulVec_tmul γ 1 x

theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

theorem stab_cong_iff_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E) (hM : 1 ≤ M)
    (hrat : ∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) :
    ((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧
        ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔
      ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧
        ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)),
          ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x) := by
  set B : Matrix (Fin n) (Fin n) E := (β : Matrix (Fin n) (Fin n) E) with hB
  set C : Matrix (Fin n) (Fin n) E := ((β⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hC
  have hBC : B * C = 1 := Units.mul_inv β
  have hCB : C * B = 1 := Units.inv_mul β
  have hRBC : ∀ z, ratM F B *ᵥ (ratM F C *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hBC, ratM_one, one_mulVec]
  have hRCB : ∀ z, ratM F C *ᵥ (ratM F B *ᵥ z) = z := by
    intro z; rw [mulVec_mulVec, ← ratM_mul, hCB, ratM_one, one_mulVec]
  have gen : ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ Λ,
      (fun i => a ⊗ₜ[F] x i) ∈ hat F (Λ : Set (Fin n → E)) :=
    fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩
  constructor
  · rintro ⟨hstab, hcong⟩
    refine ⟨fun z hz => ?_, fun z hz => ⟨ratM F C *ᵥ z, ?_, hRBC z⟩⟩
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨y, hy, hxy⟩ := hcong x hx
        refine ⟨fun i => a ⊗ₜ[F] y i, gen a ha y hy, ?_⟩
        rw [ratM_mulVec_tmul]
        ext i
        have := congrFun hxy i
        simp only [Pi.sub_apply, Pi.smul_apply] at this ⊢
        rw [← TensorProduct.tmul_sub, this]
        exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) M (y i)
      | zero => exact ⟨0, zero_mem _, by simp⟩
      | add z w _ _ h1 h2 =>
        obtain ⟨y1, hy1, e1⟩ := h1
        obtain ⟨y2, hy2, e2⟩ := h2
        refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
        rw [mulVec_add, smul_add, ← e1, ← e2]; abel
      | neg z _ h =>
        obtain ⟨y, hy, e⟩ := h
        refine ⟨-y, neg_mem hy, ?_⟩
        rw [mulVec_neg, smul_neg, ← e]; abel
    · induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        rw [ratM_mulVec_tmul]
        refine gen a ha _ ((hstab _).2 ?_)
        rw [mulVec_mulVec, hBC, one_mulVec]; exact hx
      | zero => simp
      | add z w _ _ h1 h2 => rw [mulVec_add]; exact add_mem h1 h2
      | neg z _ h => rw [mulVec_neg]; exact neg_mem h
  · rintro ⟨hcong, hsurj⟩
    have himg : ∀ x ∈ Λ, B *ᵥ x ∈ Λ := by
      intro x hx
      obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      rw [← hrat, ← ratM_mulVec_fv, sub_eq_iff_eq_add.mp e]
      exact add_mem (nsmul_mem hy M) ((hrat x).2 hx)
    refine ⟨fun x => ⟨himg x, fun hx => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := hsurj _ ((hrat _).2 hx)
      rw [← ratM_mulVec_fv] at e
      have hyx : y = fv F x := by
        have := congrArg (fun z => ratM F C *ᵥ z) e
        simpa only [hRCB] using this
      rw [← hrat, ← hyx]; exact hy
    · obtain ⟨y, hy, e⟩ := hcong _ ((hrat x).2 hx)
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      set w : Fin n → E := (M : E)⁻¹ • (B *ᵥ x - x) with hw
      have hMw : M • w = B *ᵥ x - x := by
        rw [hw, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hM0]
      have hfw : fv F w = y := by
        apply nsmul_cancel (F := F) hM
        rw [← fv_nsmul, hMw, fv_sub, ← ratM_mulVec_fv, e]
      exact ⟨w, (hrat w).1 (hfw ▸ hy), hMw.symm⟩

end GlobalTheory.LocGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisSpansUnitaryLieStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_basis_spans_unitary_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  first | exact @GlobalTheory.SkewSpan.mem_span_of_skew | exact GlobalTheory.SkewSpan.mem_span_of_skew | (intros; apply GlobalTheory.SkewSpan.mem_span_of_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeEqSumOfScalarSplitStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineDegree_eq_sum_of_scalar_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  first | exact @GlobalTheory.Nef.degLine_eq_sum_of_split | exact GlobalTheory.Nef.degLine_eq_sum_of_split | (intros; apply GlobalTheory.Nef.degLine_eq_sum_of_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeGeOfTwistedSectionStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineDegree_ge_of_twisted_section : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ (n : ℕ) (h : Place k F → Matrix (Fin n) (Fin n) F), admitted h → ∀ (v₀ : Place k F) (π : F), π ≠ 0 → ord v₀ π = 1 → ∀ (e : ℤ) (p : Fin n → F), p ≠ 0 → (∀ (v : Place k F) (i : Fin n), v.1 ((twistAt v₀ (π ^ (-e)) h v).mulVec p i) ≤ 1) → e ≤ degLine h p := by
  first | exact @GlobalTheory.Nef.degLine_ge_of_twist | exact GlobalTheory.Nef.degLine_ge_of_twist | (intros; apply GlobalTheory.Nef.degLine_ge_of_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasureStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) = ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  first | exact @GlobalTheory.FlagTransport.lintegral_trF_cpt | exact GlobalTheory.FlagTransport.lintegral_trF_cpt | (intros; apply GlobalTheory.FlagTransport.lintegral_trF_cpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameRealUnitaryStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_realUnitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := by
  first | exact @GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | exact GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf | (intros; apply GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorLowerBoundStatement
section
open NumberField IsDedekindDomain GlobalTheory.SUVol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlatStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_eq_comap_map_of_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W') (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π → ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  first | exact @GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | exact GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | (intros; apply GlobalTheory.FlatBaseChangeIdeal.map_comap_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentity
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.SUVol.DensChart

open scoped Pointwise

theorem mem_grpBall_iff_norm {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) {ε : ℝ}
    (hε : 0 < ε) (g : H) :
    g ∈ grpBall H ε ↔ ‖(fun τ i j => ((((g : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) i j) - (fun (_ : ι) i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j)‖ < ε := by
  rw [pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem tanBall_eq_ball {ι : Type} [Fintype ι] {r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tanBall ι r ε = Metric.ball 0 ε := by
  ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem density_at_one : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  intro ι _ r H _ μ W _ _ _ _ _ lam _ Q D h a ρ hD hQ0 hDi hon hh ha0 hat hρ hμ
  set f : W → (ι → Fin r → Fin r → ℂ) := fun w τ i j =>
    ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf
  set one : ι → Fin r → Fin r → ℂ := fun _ i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hone
  have hf0 : f 0 = one := by simp [hf, hone, hQ0]
  have hD' : HasStrictFDerivAt f D 0 := hD
  obtain ⟨K, -, hK⟩ := (D : W →ₗ[ℝ] (ι → Fin r → Fin r → ℂ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hDi)
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hnorm : ∀ w, ‖w‖ ≤ K' * ‖D w‖ := by
    intro w
    have h1 := hK.le_mul_dist w 0
    simp only [dist_zero_right, map_zero] at h1
    calc ‖w‖ ≤ K * ‖D w‖ := h1
      _ ≤ K' * ‖D w‖ := by gcongr; linarith
  have hcw : ∀ c : ℝ, 0 ≤ c → ∀ w, c / K' * ‖w‖ ≤ c * ‖D w‖ := by
    intro c hc w
    calc c / K' * ‖w‖ ≤ c / K' * (K' * ‖D w‖) := by gcongr; exact hnorm w
      _ = c * ‖D w‖ := by field_simp
  have approx : ∀ κ : ℝ, 0 < κ → ∃ δ > 0, ∀ w : W, ‖w‖ < δ → ‖f w - one - D w‖ ≤ κ * ‖w‖ := by
    intro κ hκ
    have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD'.hasFDerivAt).def hκ
    obtain ⟨δ, hδ, hh'⟩ := Metric.eventually_nhds_iff.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hh' (y := w) (by rwa [dist_zero_right])
    simpa [hf0] using this
  set V : ℝ → ℝ≥0∞ := fun ε => lam (D ⁻¹' Metric.ball 0 ε) with hVdef
  set S : ℝ → Set W := fun ε => D ⁻¹' Metric.ball 0 ε ∩ Metric.ball 0 ρ with hSdef
  set F : ℝ → ℝ≥0∞ := fun ε => μ (Q '' S ε) with hFdef
  have hV0 : ∀ ε : ℝ, 0 < ε → V ε ≠ 0 := fun ε hε =>
    (Metric.isOpen_ball.preimage D.continuous).measure_ne_zero lam ⟨0, by simp [hε]⟩
  have hVt : ∀ ε : ℝ, V ε ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := lam) (x := 0) (r := K' * ε)).ne
      (measure_mono fun w hw => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ ≤ K' * ε := by gcongr
  have hVhom : ∀ t ε : ℝ, 0 < t → 0 < ε → V (t * ε) = ENNReal.ofReal (t ^ Module.finrank ℝ W) * V ε := by
    intro t ε ht _
    have hs : D ⁻¹' Metric.ball 0 (t * ε) = t • (D ⁻¹' Metric.ball 0 ε) := by
      ext w
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
      simp only [Set.mem_preimage, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht]
      rw [inv_mul_lt_iff₀ ht]
    simp only [hVdef]
    rw [hs, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]
  have hSmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurableSet_ball.preimage D.measurable).inter measurableSet_ball
  have hSeq : ∀ ε : ℝ, ε < ρ / K' → S ε = D ⁻¹' Metric.ball 0 ε := by
    intro ε hε
    refine Set.inter_eq_left.2 fun w hw => ?_
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ < K' * (ρ / K') := by gcongr; linarith [norm_nonneg (D w)]
      _ = ρ := by field_simp
  have hFint : ∀ ε : ℝ, F ε = ∫⁻ w in S ε, h w ∂lam := fun ε =>
    hμ (S ε) (hSmeas ε) Set.inter_subset_right
  have hF : Tendsto (fun ε => F ε / V ε) (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨a', hb', ha'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (lt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : a' * V ε ≤ F ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc b < a' := hb'
        _ = a' * V ε / V ε := (ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)).symm
        _ ≤ F ε / V ε := ENNReal.div_le_div_right hle _
    · obtain ⟨a', ha', hb'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (gt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : F ε ≤ a' * V ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc F ε / V ε ≤ a' * V ε / V ε := ENNReal.div_le_div_right hle _
        _ = a' := ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)
        _ < b := hb'
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (t⁻¹ * ε) ≤ μ (grpBall H ε) ∧ μ (grpBall H ε) ≤ F (t * ε) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    obtain ⟨δ1, hδ1, H1⟩ := approx ((t - 1) / K') (div_pos (by linarith) hK'0)
    obtain ⟨δ2, hδ2, H2⟩ := approx ((1 - t⁻¹) / K') (div_pos (by linarith) hK'0)
    obtain ⟨ε0, hε0, hon0⟩ := hon (min ρ δ2) (lt_min hρ hδ2)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hε0 (lt_min (div_pos hδ1 hK'0) (div_pos hρ hK'0)))]
      with ε hε
    obtain ⟨hεp, hε1⟩ := hε
    simp only [lt_min_iff] at hε1
    obtain ⟨hεe, hεd, hερ⟩ := hε1
    constructor
    · refine measure_mono ?_
      rintro _ ⟨w, ⟨hw1, -⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff] at hw1
      rw [mem_grpBall_iff_norm H hεp]
      change ‖f w - one‖ < ε
      have hDw : ‖D w‖ < ε := by
        calc ‖D w‖ < t⁻¹ * ε := hw1
          _ < 1 * ε := by gcongr
          _ = ε := one_mul ε
      have hw : ‖w‖ < δ1 := by
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δ1 / K') := by gcongr; linarith
          _ = δ1 := by field_simp
      have e1 := H1 w hw
      have e2 := hcw (t - 1) (by linarith) w
      have e3 : ‖f w - one‖ ≤ ‖D w‖ + ‖f w - one - D w‖ := by
        calc ‖f w - one‖ = ‖D w + (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have e4 : t * ‖D w‖ < ε := by
        calc t * ‖D w‖ < t * (t⁻¹ * ε) := by gcongr
          _ = ε := by field_simp
      nlinarith
    · refine measure_mono fun g hg => ?_
      have hg0 : g ∈ grpBall H ε0 := fun τ i j => (hg τ i j).trans hεe
      obtain ⟨w, hw, rfl⟩ := hon0 g hg0
      rw [lt_min_iff] at hw
      rw [mem_grpBall_iff_norm H hεp] at hg
      change ‖f w - one‖ < ε at hg
      refine ⟨w, ⟨?_, mem_ball_zero_iff.2 hw.1⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have e1 := H2 w hw.2
      have e2 := hcw (1 - t⁻¹) (by linarith) w
      have e3 : ‖D w‖ ≤ ‖f w - one‖ + ‖f w - one - D w‖ := by
        calc ‖D w‖ = ‖(f w - one) - (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e4 : t⁻¹ * ‖D w‖ < ε := by linarith
      calc ‖D w‖ = t * (t⁻¹ * ‖D w‖) := by field_simp
        _ < t * ε := by gcongr
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze (F := F) (V := V)
    (A := fun ε => μ (grpBall H ε)) (n := Module.finrank ℝ W) hat hVhom hF hA
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  simp only [hVdef]
  rw [tanBall_eq_ball hε, Measure.map_apply D.measurable measurableSet_ball]

end GlobalTheory.SUVol.DensChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquationStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.mellinSplit_neg | exact GlobalTheory.mellinSplit_neg | (intros; apply GlobalTheory.mellinSplit_neg <;> assumption)
end

