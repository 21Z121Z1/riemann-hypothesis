import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformTaylorBoundLeviPluriharmonicSplitStatement
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧ ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re + (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.PluriTaylor.taylor_levi_unif | exact GlobalTheory.PluriTaylor.taylor_levi_unif | (intros; apply GlobalTheory.PluriTaylor.taylor_levi_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAndSeparates
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp.ScBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E]

end GlobalTheory.KSp.ScBasic
end

namespace GlobalTheory.KSp

open MeasureTheory Matrix in
private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [_root_.GlobalTheory.KSp.sc, z.ne_zero]

open MeasureTheory Matrix in
private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

open MeasureTheory Matrix in
private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : _root_.GlobalTheory.KSp.sc F χ m 0 = 0 := by
  simp [_root_.GlobalTheory.KSp.sc]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : _root_.GlobalTheory.WeilM.ResEtaPow (R := F) ⊥ χ m), _root_.GlobalTheory.KSp.sc F χ m 1 = 1 ∧ (∀ z z' : E, _root_.GlobalTheory.KSp.sc F χ m (z * z') = _root_.GlobalTheory.KSp.sc F χ m z * _root_.GlobalTheory.KSp.sc F χ m z') ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖_root_.GlobalTheory.KSp.sc F χ m (z : E)‖ ^ 2 = _root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (c (z : E))⁻¹ * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = _root_.GlobalTheory.KSp.sc F χ m (z : E)) ∧ (∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) = (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m ((z : E) * c (z : E)) = ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hinj := hE.algebraMap_injective
  have hinv := hE.invol
  have hpos : ∀ t : Fˣ, 0 < _root_.GlobalTheory.SplitWeil.nabs F t :=
    _root_.GlobalTheory.SplitWeil.nabs_pos F
  have hmul := _root_.GlobalTheory.SplitWeil.nabs_mul F
  have hunit : ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := fun z => sc_units_eq_mul_nabs_norm_rpow F χ m z
  have hnorm : ∀ z : Eˣ, algebraMap F E ((Units.map (Algebra.norm F : E →* F) z : Fˣ) : F) =
      (z : E) * c z := fun z => by
    simpa using hE.algebraMap_norm (z : E)
  have hNc : ∀ z : Eˣ, Units.map (Algebra.norm F : E →* F) (Units.map (c : E →* E) z) =
      Units.map (Algebra.norm F : E →* F) z := by
    intro z
    apply Units.ext
    apply hinj
    rw [hnorm, hnorm]
    simp [hinv, mul_comm]
  have hNa : ∀ t : Fˣ, Units.map (Algebra.norm F : E →* F) (Units.map (algebraMap F E : F →* E) t)
      = t * t := by
    intro t
    apply Units.ext
    apply hinj
    rw [hnorm]
    simp
  have hbase : ∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) =
      (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m := by
    intro t
    have h1 := hunit (Units.map (algebraMap F E : F →* E) t)
    simp only [Units.coe_map, MonoidHom.coe_coe] at h1
    rw [h1, hχ t, hNa, hmul, Real.mul_rpow (hpos t).le (hpos t).le, ← sq,
      rpow_natCast_div_two_sq (hpos t) m, mul_pow]
    simp only [_root_.GlobalTheory.KSp.sgn, bot_sup_eq]
    split_ifs with h₁ h₂ h₂ <;>
      first
        | (push_cast; ring1)
        | exact absurd (Subgroup.mem_sup_right h₂) h₁
        | exact absurd (by rwa [bot_sup_eq] at h₁) h₂
  refine ⟨?_, ?_, hunit, ?_, ?_, hbase, ?_⟩
  · simpa [_root_.GlobalTheory.SplitWeil.nabs_one] using hunit 1
  · intro z z'
    rcases eq_or_ne z 0 with rfl | hz
    · simp [sc_zero']
    rcases eq_or_ne z' 0 with rfl | hz'
    · simp [sc_zero']
    obtain ⟨u, rfl⟩ : ∃ u : Eˣ, (u : E) = z := ⟨Units.mk0 z hz, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u : Eˣ, (u : E) = z' := ⟨Units.mk0 z' hz', rfl⟩
    rw [← Units.val_mul, hunit, hunit, hunit, map_mul, map_mul, hmul,
      Real.mul_rpow (hpos _).le (hpos _).le]
    push_cast [Circle.coe_mul]
    ring
  · intro z
    rw [hunit, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hpos _).le _), rpow_natCast_div_two_sq (hpos _) m]
  · intro z
    have h1 := hunit (Units.map (c : E →* E) z)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, map_inv] at h1
    have hs := hpos (Units.map (Algebra.norm F : E →* F) z)
    have habs_inv : ∀ t : Fˣ, _root_.GlobalTheory.SplitWeil.nabs F t⁻¹ =
        (_root_.GlobalTheory.SplitWeil.nabs F t)⁻¹ := fun t =>
      eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, _root_.GlobalTheory.SplitWeil.nabs_one])
    rw [h1, hNc, hunit,
      _root_.GlobalTheory.WeilM.ResEtaPow.map_conj hE hχ z, inv_inv,
      habs_inv, Real.inv_rpow hs.le, ← rpow_natCast_div_two_sq hs m]
    have ha0 : ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
    push_cast at ha0 ⊢
    field_simp
  · intro z
    have hz : Units.map (Algebra.norm F : E →* F) z ∈ (Units.map (Algebra.norm F : E →* F)).range :=
      ⟨z, rfl⟩
    rw [← hnorm, hbase]
    simp [_root_.GlobalTheory.KSp.sgn, hz]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySignsHaarIsMulRightInvariant
section
namespace GlobalTheory

open MeasureTheory

theorem unitarySigns_haar_isMulRightInvariant :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : MeasureTheory.Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
      μ.IsMulRightInvariant := by
  intro n ε μ _
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumMatrixCoefficientSq
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLintegralSobolevPointwiseStatement
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  first | exact @GlobalTheory.weighted_lintegral_sobolev_pointwise | exact GlobalTheory.weighted_lintegral_sobolev_pointwise | (intros; apply GlobalTheory.weighted_lintegral_sobolev_pointwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPoint
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange_point :
    ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT
  letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra
  obtain ⟨act', -, hT'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R)
    (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT

  let M₁ := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)
  let f : R₁ →+* FractionRing A₁ := (algebraMap A₁ (FractionRing A₁)).comp ρ₁
  have hf : ∀ m : M₁, IsUnit (f m) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := hm
    have : ρ₁ (algebraMap A₁ R₁ a) = a := by
      simpa using congrArg (fun φ : A₁ →+* A₁ => φ a) hret
    simp only [f, RingHom.comp_apply, this]
    exact IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)
  let ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁ :=
    IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf
  have hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f :=
    IsLocalization.lift_comp hf
  refine ⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance,
    inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩
  · ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  · intro σ hσ
    have hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) := by
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      rw [hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]
      rfl
    letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra
    let fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { ρK with commutes' := fun _ => rfl }
    let gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }
    refine ⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      mul_one]
    show ρK (algebraMap R₁ _ r) = _
    rw [← RingHom.comp_apply ρK, hρK]
    rfl

end GlobalTheory.KeyOriginCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
section
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorsorFieldPoint

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor (B D : Type) [CommRing B] [CommRing D]
    [Algebra B D] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.FormallyUnramified B D := by
  obtain ⟨-, -, hff, hbij⟩ := h
  haveI : NeZero q := ⟨hq.ne'⟩
  let g : D →ₐ[B] (Multiplicative (ZMod q) → D) :=
    Pi.algHom B (fun _ ↦ D) fun σ ↦ (act σ : D →ₐ[B] D)
  let F : D ⊗[B] D →ₐ[D] (Multiplicative (ZMod q) → D) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId D _) g
  have hF : (F : D ⊗[B] D → _) = Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ ↦ D) fun _ ↦ AlgHom.id B D) g := by
    ext x : 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all
  have hFb : Function.Bijective F := by rw [hF]; exact hbij
  haveI : Algebra.FormallyUnramified D (Multiplicative (ZMod q) → D) :=
    (Algebra.FormallyUnramified.pi_iff _).2 fun _ ↦ inferInstance
  haveI : Algebra.FormallyUnramified D (D ⊗[B] D) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective F hFb).symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat D

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.TorsorFieldPoint.exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K]
    (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  intro B K _ _ f D _ _ q hq act h
  haveI := _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, -, hff, -⟩ := h
  letI : Algebra B K := f.toAlgebra
  haveI : Nontrivial (K ⊗[B] D) := Module.FaithfullyFlat.rTensor_nontrivial B D K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] D)
  letI : Field (K ⊗[B] D ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (K ⊗[B] D ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified K (K ⊗[B] D ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  refine ⟨K ⊗[B] D ⧸ m, inferInstance, inferInstance, inferInstance,
    Algebra.FormallyUnramified.isSeparable K _,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext b
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

end GlobalTheory.TorsorFieldPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorFieldEqProdGaloisStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_field_eq_prod_galois : ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (exact GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (intros; apply GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois  <;> assumption)
end

