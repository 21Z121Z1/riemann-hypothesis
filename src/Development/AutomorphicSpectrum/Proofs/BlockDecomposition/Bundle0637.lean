import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RankinSelberg.Unfolded

open Ad3 Ad3.R

theorem localChar_inv' (c : HeckeCharacter ℚ) (v : Pl) :
    localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rfl

theorem glAt_prodEquiv (v : Pl) (g : G2) :
    glAt v (AdelicGLn.prodEquiv ℚ 2 g).2 = finAt v g := by
  apply Units.ext
  ext i j
  simp [GroundTheory.Automorphic.GodementSection.glAt_apply, AdelicGLn.prodEquiv_apply_snd]

theorem wh_mul_right {φ : G2 → ℂ} {r : G2} {u : ℂ} (h : ∀ g, φ (g * r) = u * φ g) (g : G2) :
    Wh φ (g * r) = u * Wh φ g := by
  unfold Wh
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, h, mul_assoc]

theorem q_torus {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hφ : Lift k N f ω φ) (hW : ∀ t : ℝˣ, Wh φ (realEmb (dg2 t 1)) = WR k t) (t : ℝˣ) (r : GL (Fin 2) ℝ)
    (hr : r.val * r.valᵀ = 1) (hd : r.det.val = 1) :
    (fun y => Wh φ (realEmb y) * conj (Wh φ (realEmb y))) (dg2 t 1 * r) = WR k t * conj (WR k t) := by
  obtain ⟨u, hu, hru⟩ := hφ.rot r hr hd
  have hu1 : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  show Wh φ (realEmb (dg2 t 1 * r)) * conj (Wh φ (realEmb (dg2 t 1 * r))) = _
  rw [map_mul, wh_mul_right hru, hW, map_mul]
  linear_combination (WR k t * conj (WR k t)) * hu1

theorem locConst_section (hL : Loc2) (hA : A10) {ψ : ∀ v : Pl, AddChar (Qv v) Circle} (v : Pl) (hψ : IsStd (ψ v))
    (m : Measure (integralGL (Qv v) 2)) [m.IsHaarMeasure] [IsProbabilityMeasure m]
    {μ₁ μ₂ c : (Qv v)ˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) (hc : IsUnit1 c)
    {φ₀ Ψ : (Fin 2 → Qv v) → ℂ} (hφ₀ : SB φ₀) (hΨ : SB Ψ) (x : Qv v) {s : ℂ} (hs : 0 < s.re) :
    IsLocallyConstant (fun g => GodementSectionLocal.localSection c c⁻¹ s Ψ g *
      Av (W2 (ψ v) μ₁ μ₂ φ₀) (fun g => W2 (ψ v) μ₁ μ₂ φ₀ (g * uni2 x)) c s g) := by
  have hW : W2 (ψ v) μ₁ μ₂ φ₀ ∈ V2 (ψ v) μ₁ μ₂ := Submodule.subset_span ⟨φ₀, hφ₀, rfl⟩
  have hW' := (hL (Qv v) (ψ v) hψ μ₁ μ₂ h₁ h₂).1.stable _ hW (uni2 x)
  have h := hA (Qv v) (ψ v) hψ m μ₁ μ₂ c h₁ h₂ hc _ hW _ hW'
  exact ((h.2 Ψ hΨ).1 s hs).mul ((h.1 s hs).2)

theorem e6 : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6 := by
  intro hL hB hA hE2 hE3 hE5 hE6a hF2 k N _ hk χ hχ f a hf ha ω φ hω hφ μ₁ μ₂ φ₀ hM mK _ _ m hm γ hγ
  obtain ⟨C, hC0, hC⟩ := hE5 k (by omega)
  refine ⟨C, hC0, ?_⟩
  intro S hS c δ hc hδ hun x h hx Ψ hΨ s hs
  have hcu : ∀ v, IsUnit1 (localChar c v) := fun v => (hB.1 v).2.2.2.2.2.2 c
  have hun' : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v) := fun v hv => by
    rw [localChar_inv']
    exact isUnramifiedChar_inv_iff.2 (hun v hv)
  have hc1 := ((hE2 S s hs).1 c hun).1
  have hc2 := ((hE2 S s hs).1 c⁻¹ hun').1
  have hW := (hF2 k N hk χ hχ f a hf ha ω φ hω hφ).2.2.2
  have hs0 : 0 < s.re := by linarith
  set A : ∀ v : S, GL (Fin 2) (Qv v.1) → ℂ := fun v g =>
    GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) g *
      Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
        (localChar c v.1) s g with hAdef
  have hAlc : ∀ v, IsLocallyConstant (A v) := fun v => by
    have := (hm v.1).1
    have := (hm v.1).2
    exact locConst_section (ψ := fun v => localAdelicChar ℚ v) hL hA v.1 (hB.1 v.1).1 (m v.1)
      (hM.u₁ v.1) (hM.u₂ v.1) (hcu v.1) (hM.sb v.1) (hΨ v) (x v) hs0
  set T : ℂ := (∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s with hT
  have hpt : ∀ κ : KA, godementSection c c⁻¹ s (tst γ S Ψ) κ.1 *
      Ag (fun g => Wh φ g * conj (Wh φ (g * h))) c s κ.1 =
      (C * (if δ then -1 else 1) * GG k s * T) * ∏ v : S, A v (finAt v.1 κ.1) := by
    intro κ
    have e1 := GroundTheory.Automorphic.GodementSection.godementSection_tensor c c⁻¹ s γ (restrictedTensor2 S Ψ) κ.1
    have e2 := GroundTheory.Automorphic.GodementSection.finSection_restrictedTensor2 c c⁻¹ S hΨ hc1 hc2
      (s := s) (by linarith) (g := (AdelicGLn.prodEquiv ℚ 2 κ.1).2)
      (fun v _ => by rw [glAt_prodEquiv]; exact κ.2.2 v)
    have e3 := hE6a k N hk χ hχ f a hf ha ω φ hω hφ μ₁ μ₂ φ₀ hM S hS c hun x h hx s hs κ
    have e4 := hC γ hγ c δ hc hδ s hs κ (fun y => Wh φ (realEmb y) * conj (Wh φ (realEmb y)))
      (fun t r hr hd => q_torus hφ hW t r hr hd)
    simp only [inv_inv, localChar_inv', glAt_prodEquiv] at e2
    have e0 : godementSection c c⁻¹ s (tst γ S Ψ) κ.1 = _ := e1
    rw [e0, e2]
    simp only [hAdef, Finset.prod_mul_distrib]
    linear_combination (archSection c c⁻¹ s γ (AdelicGLn.prodEquiv ℚ 2 κ.1).1 *
      ∏ v : S, GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) (finAt v.1 κ.1)) * e3 +
      ((∏ v : S, GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) (finAt v.1 κ.1)) *
      (∏ v : S, Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
        (localChar c v.1) s (finAt v.1 κ.1)) * T) * e4
  have hJ : Jg mK (fun g => Wh φ g * conj (Wh φ (g * h))) c (tst γ S Ψ) s =
      (C * (if δ then -1 else 1) * GG k s * T) * ∫ κ : KA, ∏ v : S, A v (finAt v.1 κ.1) ∂mK := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hJ, hE3 mK m hm S A hAlc]
  have hZ : ZS m μ₁ μ₂ φ₀ S x Ψ c s = ∏ v : S, ∫ κ, A v κ.1 ∂m v.1 := rfl
  rw [hZ]
  ring

end GlobalTheory.CompanionTheory.RankinSelberg.Unfolded

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBound
section
noncomputable section

open Complex

namespace GlobalTheory.CompanionTheory.RankinSelberg.RealGamma

lemma gammaR_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h := (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  have e : (fun z : ℂ => (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by
    funext z; simp
  rwa [e] at h

lemma gammaC_eq : Gammaℂ = fun s => Gammaℝ s * Gammaℝ (s + 1) := by
  funext s; exact (Gammaℝ_mul_Gammaℝ_add_one s).symm

lemma gammaC_ne_zero {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [gammaC_eq]
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos ?_)
  simp only [add_re, one_re]; linarith

lemma gammaC_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℂ s := by
  rw [gammaC_eq]
  have h1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (z + 1)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℝ) (f := fun z : ℂ => z + 1) s
      (gammaR_differentiableAt h1) (differentiableAt_id.add_const 1)
  exact (gammaR_differentiableAt hs).mul h2

lemma shift_re_pos {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) : 0 < (s + (k : ℂ) - 1).re := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [sub_re, add_re, natCast_re, one_re]; linarith

lemma shift_differentiableAt {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Gammaℂ (z + (k : ℂ) - 1)) s :=
  DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℂ) (f := fun z : ℂ => z + (k : ℂ) - 1) s
    (gammaC_differentiableAt (shift_re_pos hk hs))
    ((differentiableAt_id.add_const _).sub_const 1)

lemma GG_differentiableAt {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Ad3.R.GG k) s :=
  (gammaC_differentiableAt hs).mul (shift_differentiableAt hk hs)

lemma GG_ne_zero {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : 0 < s.re) : Ad3.R.GG k s ≠ 0 :=
  mul_ne_zero (gammaC_ne_zero hs) (gammaC_ne_zero (shift_re_pos hk hs))

lemma tail_re_pos (δ : Bool) {s : ℂ} (hs : 0 < s.re) : 0 < (s + if δ then 0 else 1 : ℂ).re := by
  cases δ <;> simp <;> linarith

lemma lR_ne_zero {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : 0 < s.re) : Ad3.lR k δ s ≠ 0 :=
  mul_ne_zero (gammaC_ne_zero (shift_re_pos hk hs)) (Gammaℝ_ne_zero_of_re_pos (tail_re_pos δ hs))

lemma lR_differentiableAt {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Ad3.lR k δ) s := by
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (z + if δ then 0 else 1)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Gammaℝ) (f := fun z : ℂ => z + if δ then 0 else 1) s
      (gammaR_differentiableAt (tail_re_pos δ hs)) (differentiableAt_id.add_const _)
  exact (shift_differentiableAt hk hs).mul h2

lemma gamR_differentiableAt {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : Ad3.R.Strip s) :
    DifferentiableAt ℂ (Ad3.gamR k δ) s := by
  have h1 : 0 < (1 - s).re := by simp only [sub_re, one_re]; linarith [hs.2]
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Ad3.lR k δ (1 - z)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Ad3.lR k δ) (f := fun z : ℂ => 1 - z) s
      (lR_differentiableAt hk δ h1) (differentiableAt_id.const_sub 1)
  exact (h2.const_mul _).div (lR_differentiableAt hk δ hs.1) (lR_ne_zero hk δ hs.1)

lemma negI_pow_two_mul (k : ℕ) : (-I) ^ (2 * k) = (-1 : ℂ) ^ k := by
  rw [pow_mul]; simp

lemma gamma_identity {k : ℕ} (hk : 1 ≤ k) (δ : Bool) {s : ℂ} (hs : Ad3.R.Strip s) :
    (-1) ^ k * Ad3.R.GG k (1 - s) * Gammaℝ (s + if δ then 1 else 0) =
      Ad3.gamR k δ s * Ad3.R.GG k s * ((if δ then -I else 1) * Gammaℝ (1 - s + if δ then 1 else 0)) := by
  have hne := lR_ne_zero hk δ hs.1
  have hG := gammaC_ne_zero (shift_re_pos hk hs.1)
  have hC1 := Gammaℝ_mul_Gammaℝ_add_one s
  have hC2 := Gammaℝ_mul_Gammaℝ_add_one (1 - s)
  unfold Ad3.gamR Ad3.R.GG
  cases δ with
  | false =>
    have hR : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith [hs.1])
    simp only [Bool.false_eq_true, if_false, add_zero, tsub_zero, one_mul, Ad3.lR] at *
    rw [negI_pow_two_mul, ← hC1, ← hC2]
    field_simp
  | true =>
    have hR : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
    have hp : (-I) ^ (2 * k - 1) * (-I) = (-1 : ℂ) ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), negI_pow_two_mul]
    simp only [if_true, add_zero, Ad3.lR] at *
    rw [← hp, ← hC1, ← hC2]
    field_simp

theorem main : Ad3.R.RealPlaceGammaFactors := by
  intro k δ hk
  refine ⟨fun s hs => (GG_differentiableAt hk hs).differentiableWithinAt,
    fun s hs => GG_ne_zero hk hs,
    fun s hs => (gamR_differentiableAt hk δ hs).differentiableWithinAt,
    fun s hs => gamma_identity hk δ hs⟩

end GlobalTheory.CompanionTheory.RankinSelberg.RealGamma

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactor
section
noncomputable section

open GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.TateGamma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exponent_eq_zero {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) : quasiCharExponent c = 0 := by
  simp [quasiCharExponent, hc.2]

theorem isUnit1_inv {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) : Ad3.IsUnit1 c⁻¹ :=
  ⟨continuous_quasiChar_inv hc.1, fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hc.2, inv_one]⟩

theorem lFactor_ne_zero {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    localLFactor c s ≠ 0 :=
  localLFactor_ne_zero hc.1 (by rw [exponent_eq_zero hc]; simpa using hs)

theorem differentiableAt_lFactor {c : Fˣ →* ℂˣ} (hc : Ad3.IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (localLFactor c) s := by
  by_cases h : IsUnramifiedChar c
  · have e : localLFactor c =
        fun s => (1 - ((c (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ :=
      funext fun s => localLFactor_of_isUnramified h s
    rw [e]
    refine DifferentiableAt.inv ?_ ?_
    · exact (((differentiable_qpow (K := F)).const_mul _).const_sub 1) s
    · exact one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hc.1
        (by rw [exponent_eq_zero hc]; simpa using hs)
  · have e : localLFactor c = fun _ => (1 : ℂ) :=
      funext fun s => localLFactor_of_not_isUnramified h s
    rw [e]
    exact differentiableAt_const _

theorem gam_strip : Ad3.R.LocalGammaFunctionalEquation := by
  intro F _ _ _ _ _ _ ψ hψ c hc
  have hc' := isUnit1_inv hc
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have h1 : 0 < (1 - s).re := by
      have := hs.2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hL : DifferentiableAt ℂ (fun s => localLFactor c⁻¹ (1 - s)) s :=
      DifferentiableAt.comp (f := fun s : ℂ => 1 - s) s (differentiableAt_lFactor hc' h1)
        ((differentiableAt_const _).sub differentiableAt_id)
    have hg : DifferentiableAt ℂ (Ad3.gam ψ c) s := by
      unfold Ad3.gam
      exact ((differentiable_localEpsilon s).mul hL).div (differentiableAt_lFactor hc hs.1)
        (lFactor_ne_zero hc hs.1)
    exact hg.differentiableWithinAt
  · have h0 : 0 < s.re := hs.1
    have h1 : 0 < (1 - s).re := by
      have := hs.2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hL := lFactor_ne_zero hc h0
    have hL' := lFactor_ne_zero hc' h1
    have hε := localEpsilon_mul_localEpsilon_inv_eq_of_strip (χ := c) hψ.1 hψ.2.1 hc.1
      (s := s) (by rw [exponent_eq_zero hc]; simpa using h0)
      (by rw [exponent_eq_zero hc]; simpa using hs.2)
    have hcc : (c⁻¹)⁻¹ = c := inv_inv c
    unfold Ad3.gam
    rw [hcc, sub_sub_cancel, ← hε]
    field_simp

end GlobalTheory.CompanionTheory.TateGamma

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGlobalIdentity
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

theorem globalIdentity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS →
    Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0 := by
  intro hB0 hA1 hG0 hG2a hG4 hG5 hGS hFT hF2 hF5 hF6 hF6c hE6 hG6
  intro k N _ hk χ hχ f a hf ha ω φ hOm hL hP μ₁ μ₂ φ₀ hM m hm S hS c δ hc hδ hu x Ψ hΨ
  obtain ⟨μ, 𝓕, mK, 𝓓, h0⟩ := hG0
  obtain ⟨C0, hC0⟩ := hG2a μ 𝓕 mK 𝓓 h0
  obtain ⟨hB1, -, -, -, hBun, -⟩ := hB0
  obtain ⟨h, hh⟩ := hBun S x
  obtain ⟨γ, hγ⟩ := hGS
  haveI := h0.haarK
  haveI := h0.probK
  obtain ⟨C1, hC1, hE⟩ := hE6 k N hk χ hχ f a hf ha ω φ hOm hL μ₁ μ₂ φ₀ hM mK m hm γ hγ
  obtain ⟨⟨Cb, hCb⟩, hDec⟩ := hF5 k N hk χ hχ f a hf ha ω φ hOm hL
  obtain ⟨hWc, -, -, -⟩ := hF2 k N hk χ hχ f a hf ha ω φ hOm hL
  have hcusp := hF6c k N hk χ hχ f a hf ha ω φ hOm hL
  have hinf : ∀ w, infAt w h = 1 := hh.2.2
  have hDecH := hDec h hinf
  have hDec1 : Dec φ := by
    have := hDec 1 (fun w => by simp)
    simpa using this
  have hcontR : Continuous fun g : G2 => φ (g * h) := hL.cont.comp (continuous_mul_right h)
  have hleftR : LInv fun g : G2 => φ (g * h) := fun γ' g => by
    simp only [mul_assoc]; exact hL.left γ' (g * h)
  have hWh : ∀ g, Wh (fun g : G2 => φ (g * h)) g = Wh φ (g * h) := fun g => by
    simp only [Wh, mul_assoc]
  have hWhF : Wh (fun g : G2 => φ (g * h)) = fun g => Wh φ (g * h) := funext hWh
  have hWcR : Continuous (Wh fun g : G2 => φ (g * h)) := by
    rw [hWhF]; exact hWc.comp (continuous_mul_right h)
  have hPar : Par (fun g => φ g * conj (φ (g * h))) (fun g => Wh φ g * conj (Wh φ (g * h))) := by
    have := hF6 φ (fun g => φ (g * h)) hL.cont hcontR hL.left hleftR hDec1
      ⟨Cb, fun g => hCb _⟩ hcusp hWc hWcR
    rw [hWhF] at this
    exact this
  have hAut : Aut (fun g => φ g * conj (φ (g * h))) := by
    refine ⟨hL.cont.mul (Complex.continuous_conj.comp hcontR), ?_, ?_, ⟨Cb * Cb, fun g => ?_⟩, ?_⟩
    · intro γ' g
      simp only [mul_assoc]
      rw [hL.left γ' g, hL.left γ' (g * h)]
    · intro z g
      simp only [mul_assoc]
      rw [hL.cen z g, hL.cen z (g * h)]
      have : (ω.toIdele z : ℂ) * conj (ω.toIdele z : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe]; simp
      simp only [map_mul]
      linear_combination (φ g * conj (φ (g * h))) * this
    · have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 1)
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hCb _) (hCb _) (norm_nonneg _) hb0
    · intro M
      obtain ⟨D, hD⟩ := hDecH M
      have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 1)
      refine ⟨Cb * D, fun x' a' κ => ?_⟩
      rw [norm_mul, RCLike.norm_conj, mul_assoc Cb D]
      exact mul_le_mul (hCb _) (hD x' a' κ) (norm_nonneg _) hb0
  obtain ⟨hΦ, hsFA⟩ := hFT γ hγ S Ψ hΨ
  have hsΨ : ∀ v : S, SB (sF (localAdelicChar ℚ v.1) (Ψ v)) := fun v =>
    (hA1 (Qv v.1) (localAdelicChar ℚ v.1) (hB1 v.1).1 1 1 (Ψ v) 1 (hΨ v)).2.1
  obtain ⟨hΦ', -⟩ := hFT γ hγ S (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) hsΨ
  have hci : IsOfFinOrder c⁻¹ := hc.inv
  have hδi : ∀ w : InfinitePlace ℚ, (c⁻¹.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1 := by
    intro w
    have h1 : (c⁻¹.infiniteComponent w (-1) : Circle) = (c.infiniteComponent w (-1))⁻¹ := rfl
    rw [h1, Circle.coe_inv, hδ w]
    cases δ <;> simp
  have hui : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v) := by
    intro v hv
    have h1 : localChar c⁻¹ v = (localChar c v)⁻¹ := by
      ext a'
      rfl
    rw [h1]
    exact isUnramifiedChar_inv_iff.2 (hu v hv)
  obtain ⟨E, E', hd, hd', hEq, hfe, hnz⟩ := hG4 μ 𝓕 mK 𝓓 h0 _ hAut _ hΦ c hc
  have hsgn : (if δ then (-1 : ℂ) else 1) ≠ 0 := by cases δ <;> simp
  refine ⟨((C0 : ℝ) : ℂ) * C1 * (if δ then -1 else 1), E, E', ?_, hd, hd', ?_, hfe, ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ hC1) hsgn
    exact_mod_cast hC0.1
  · intro s hs
    obtain ⟨h1, h2⟩ := hEq s hs
    constructor
    · rw [h1, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ c s hs,
        hE S hS c δ hc hδ hu x h hh Ψ hΨ s hs]
      ring
    · rw [h2, hsFA, hG5 μ 𝓕 mK 𝓓 C0 h0 hC0 _ _ hAut hPar _ hΦ' c⁻¹ s hs,
        hE S hS c⁻¹ δ hci hδi hui x h hh _ hsΨ s hs]
      ring
  · intro h1 hc1
    exact hG6 k N hk χ hχ f a hf ha ω φ hOm hL hP μ 𝓕 mK 𝓓 h0 S hS c hc hc1 hu x h hh (hnz h1)

end GlobalTheory.CompanionTheory.RankinSelberg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergTheorem
section
open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.RankinSelbergTop

open Ad3 Ad3.R

theorem isUnit1_mul_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) : IsUnit1 (μ₁ * μ₂⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => μ₁ x * (μ₂ x)⁻¹
    exact h₁.1.mul h₂.1.inv
  · show ‖((μ₁ x * (μ₂ x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, h₁.2, h₂.2]; simp

theorem isUnramifiedChar_mul_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnramifiedChar μ₁) (h₂ : IsUnramifiedChar μ₂) : IsUnramifiedChar (μ₁ * μ₂⁻¹) := by
  intro x hx
  have e₁ : μ₁ x = 1 := h₁ hx
  have e₂ : μ₂ x = 1 := h₂ hx
  rw [MonoidHom.mem_ker]
  show μ₁ x * (μ₂ x)⁻¹ = 1
  rw [e₁, e₂]; simp

theorem rs_of (hB : B0) (h0 : F0) (h1 : F1) (h7 : F7) (hX : X1) : RS := by
  intro k N _ hk χ hχ f a hf ha hp
  obtain ⟨ω, hω⟩ := h0 N χ
  obtain ⟨-, φ, hφ⟩ := h1 k N χ f a hf ha.2.1 ω hω
  obtain ⟨μ₁, μ₂, φ₀, hM, hsat⟩ := h7 k N hk χ hχ f a hf ha ω φ hω hφ hp
  have hN : N ≠ 0 := NeZero.ne N
  have hfin : {v : Pl | pOf v ∣ N}.Finite :=
    ((N.divisors : Set ℕ).toFinite.preimage hB.2.1.injOn).subset (fun v hv => by
      simp only [Set.mem_setOf_eq] at hv
      simp [Nat.mem_divisors, hv, hN])
  let D : Dat := ⟨k, hk, fun v => μ₁ v * (μ₂ v)⁻¹, fun v => isUnit1_mul_inv (hM.u₁ v) (hM.u₂ v), hfin.toFinset,
    fun v hv => by
      have hv' : ¬ pOf v ∣ N := by simpa using hv
      obtain ⟨e₁, e₂, -⟩ := hM.good v hv'
      exact isUnramifiedChar_mul_inv e₁ e₂⟩
  have hbad : ∀ v, v ∈ D.bad ↔ pOf v ∣ N := fun v => by simp [D]
  refine ⟨D, rfl, ⟨hbad, fun v hv => ?_⟩, ?_⟩
  · exact hsat v (by rwa [hbad] at hv)
  · exact hX k N hk χ hχ f a hf ha ω φ hω hφ hp μ₁ μ₂ φ₀ hM D rfl (fun v => rfl) hbad

example : B0 → F0 → F1 → F7 → X1 → RS := rs_of

end GlobalTheory.CompanionTheory.RankinSelbergTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryLowerBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_theory_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → ∀ j : Fin (r + 1), j.val = 1 → Real.exp (s j) ≤ M * Real.exp (s 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | exact GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.simple_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_norm_cm_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzArchContinuousIntegrableStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_arch_continuous_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple.schwartzArch_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_split_intertwiner : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k) (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N), ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | exact GlobalTheory.CompanionTheory.SegQuotTwo.quottwo | (intros; apply GlobalTheory.CompanionTheory.SegQuotTwo.quottwo <;> assumption)
end

