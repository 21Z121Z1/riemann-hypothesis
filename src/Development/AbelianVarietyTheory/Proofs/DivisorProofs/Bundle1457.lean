import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKSoDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsFrameU (σ : E →ₐ[F] E) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin q → Fin n → E) : Prop :=
  (∀ i j, form σ J (x i) (x j) = 0) ∧ (∀ i j, form σ J (y i) (y j) = 0) ∧
    ∀ i j, form σ J (x i) (y j) = if i = j then 1 else 0

def IsTorusU {σ : E →ₐ[F] E} {n q : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : Fin q → Fin n → E) (t : Fin q → ℝ)
    (a : UA σ J) : Prop :=
  (∀ i, (mat a - 1) *ᵥ incV F (x i) = realAd F (t i - 1) • incV F (x i)) ∧
  (∀ i, (mat a - 1) *ᵥ incV F (y i) = realAd F ((t i)⁻¹ - 1) • incV F (y i)) ∧
  ∀ z : Fin n → E, (∀ i, form σ J z (x i) = 0) → (∀ i, form σ J z (y i) = 0) → (mat a - 1) *ᵥ incV F z = 0

open scoped Classical in

abbrev semK (κ : Type) [Fintype κ] (k : ℕ) : Seminorm ℂ (SInf F κ) :=
  (Finset.Iic (k, k)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)

def SoDecayUnif : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k

end GlobalTheory.ThKSoDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.KappaPowMod

theorem algebraicModulusOneAll_one : StandardLatticesGL3.Mod1All 1 := by
  refine ⟨one_mem _, fun σ => ?_⟩
  have e : (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 := rfl
  rw [e, map_one, norm_one]

theorem algebraicModulusOneAll_mul {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem algebraicModulusOneAll_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem algebraicModulusOneAll_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero => simpa using algebraicModulusOneAll_one
  | succ n ih => rw [pow_succ]; exact algebraicModulusOneAll_mul ih ha

theorem algebraicModulusOneAll_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using algebraicModulusOneAll_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact algebraicModulusOneAll_inv (algebraicModulusOneAll_pow ha _)

def phiQ (D : D7) : D.host.E →+* TaylorLogMetric.Qbar :=
  D.host.φ₀.codRestrict TaylorLogMetric.Qbar fun x => Formalism.L2.KerInert.AlgP.phi_mem_Qbar x

theorem splitPrime_rootChoice_algebraicModulusOneAll {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) (hp : p.Prime) (hs : SplitK D p) :
    StandardLatticesGL3.Mod1All (k.rt p) := by
  set h := 2 * classNumber D.host.K with hh
  have h0 : h ≠ 0 := mul_ne_zero two_ne_zero (classNumber_ne D)
  set x : D.host.E := (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) with hx
  have hx0 : x ≠ 0 := by
    have h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0 := by simpa using k.pi_ne_zero p hp hs
    simpa [hx] using h1
  have hpow := k.rt_pow p hp hs
  have hmem : k.rt p ∈ TaylorLogMetric.Qbar := by
    have hq : k.rt p ^ h ∈ TaylorLogMetric.Qbar := by
      rw [hpow]
      exact div_mem (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _) (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _)
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := h) (Nat.pos_of_ne_zero h0)
      (mem_algebraicClosure_iff.1 hq))
  refine ⟨hmem, fun σ => ?_⟩
  let ψ : D.host.E →+* ℂ := σ.comp (phiQ D)
  have hc : ψ (D.host.conj x) = starRingEnd ℂ (ψ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  have hψ0 : ψ x ≠ 0 := (map_ne_zero ψ).2 hx0
  have e : (⟨k.rt p, hmem⟩ : TaylorLogMetric.Qbar) ^ h = phiQ D x / phiQ D (D.host.conj x) := by
    apply Subtype.ext
    simp only [IntermediateField.coe_pow, IntermediateField.coe_div]
    exact hpow
  have hn : ‖σ ⟨k.rt p, hmem⟩‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_div₀]
    change ‖ψ x / ψ (D.host.conj x)‖ = 1
    rw [hc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hψ0)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 hn

theorem kappa_pow_mod1All : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ),
    StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  intro D cc δ B m
  refine algebraicModulusOneAll_pow ?_ m
  show StandardLatticesGL3.Mod1All (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))
  exact finprod_induction StandardLatticesGL3.Mod1All algebraicModulusOneAll_one (fun _ _ => algebraicModulusOneAll_mul)
    fun p => algebraicModulusOneAll_zpow (splitPrime_rootChoice_algebraicModulusOneAll B.kc p p.2.1 p.2.2) _

end GlobalTheory.KappaPowMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalising
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lattice_count_diag_mul : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D κ _ _ m n T S hST L hL
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.exists_denominator_bound_matrix_mul D.host.E κ (Fin m) T
  obtain ⟨N, C₁, hC₁, hcount⟩ := GlobalTheory.T.weighted_integral_tuple_lattice_count_bound D (κ × Fin n) (M * L) (Nat.mul_pos hM0 hL)
  obtain ⟨C₂, hC₂, hnorm⟩ := GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField D κ m n T
  refine ⟨N, C₂ ^ N * C₁, mul_nonneg (pow_nonneg (by linarith) _) hC₁, ?_⟩
  intro s hs B hB
  set e : Matrix (Fin m) (Fin n) D.host.E → (κ × Fin n → D.host.E) := fun ξ p => (T * ξ) p.1 p.2 with he
  have he_inj : Function.Injective e := by
    intro ξ ξ' h
    have h' : T * ξ = T * ξ' := Matrix.ext fun k j => congrFun h (k, j)
    calc ξ = S * T * ξ := by rw [hST, Matrix.one_mul]
      _ = S * T * ξ' := by rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc]
      _ = ξ' := by rw [hST, Matrix.one_mul]
  set s' : κ × Fin n → ℝ := fun p => s p.1 with hs'
  have hs'pos : ∀ p, 0 < s' p := fun p => hs p.1
  have hc := hcount s' hs'pos
  set G : (κ × Fin n → D.host.E) → ℝ≥0∞ := {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s' k) ^ N)⁻¹)) with hG
  have hterm : ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C₂ ^ N) * G (e ξ) := by
    intro ξ
    by_cases hξ : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)
    · rw [Set.indicator_of_mem (by exact hξ : ξ ∈ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      have hmem : e ξ ∈ {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)} := by
        intro p
        have := hM L (fun i => ξ i p.2) (fun i => hξ i p.2) p.1
        simpa [he, Matrix.mul_apply] using this
      rw [hG, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
      apply ENNReal.ofReal_le_ofReal
      have hA := hnorm s hs B hB ξ
      set W := ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ with hW
      set A := ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 with hAdef
      have hW0 : 0 ≤ W := by positivity
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun p _ => div_nonneg (by positivity) (hs p.1).le)
      have h1 : 1 + A ≤ C₂ * (1 + W) := by nlinarith
      have hp1 : 0 < (1 + A) ^ N := by positivity
      have hp2 : 0 < (1 + W) ^ N := by positivity
      have h2 : (1 + A) ^ N ≤ C₂ ^ N * (1 + W) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 N
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]
      linarith
    · rw [Set.indicator_of_notMem (by exact hξ : ξ ∉ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      exact bot_le
  calc _ ≤ ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ENNReal.ofReal (C₂ ^ N) * G (e ξ) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₂ ^ N) * ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, G (e ξ) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ∑' η, G η := by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective he_inj G
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ENNReal.ofReal (C₁ * ∏ p, max 1 (s' p) ^ Module.finrank ℚ D.host.E) := by gcongr
    _ = ENNReal.ofReal (C₂ ^ N * C₁ * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), mul_assoc]
      congr 2
      rw [Fintype.prod_prod_type]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp only [hs', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield D]
      ring_nf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeGeHeightPolynomialVectorsDet
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace GlobalTheory.HSShort.DetTop

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ w' : Matrix (Fin n) (Fin N) F, w * w' = 1 := by
  have hr : LinearMap.range w.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hw
  obtain ⟨g', hg'⟩ := w.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g', ?_⟩
  have := congrArg LinearMap.toMatrix' hg'
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' w.mulVecLin = w := LinearMap.toMatrix'_toLin' w
  rwa [e] at this

theorem linSubst_det {F : Type} [Field F] {B N n d : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) :
    linSubst w P.det = (P.map (linSubst w)).det := by
  have := RingHom.map_det (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
    MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom P
  exact this

end GlobalTheory.HSShort.DetTop

namespace GlobalTheory.HSShort.DetTop

theorem arch {F V : Type} [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) {B N : ℕ} (hN : 0 < N) (σ : F →+* ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.det ≠ 0) (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ)
    (Bd : Fin d → ℝ) (hP : P.det ≠ 0) (hhom : IsMultiHomogeneous a P.det) (hBd : ∀ k, 0 < Bd k)
    (hbd : ∀ k (u : Fin B × Fin N → ℂ), (∀ i, frameNorm A (fun j => u (i, j)) = 1) →
      cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) :
    blockSphereMean B N (linSubst A (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
  haveI := blockSphereMeasure_isProbability (B := B) hN
  have hmap0 : map σ P.det ≠ 0 := fun h =>
    hP (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
  have hf0 : linSubst A (map σ P.det) ≠ 0 :=
    GlobalTheory.HeightUnique.linSubst_ne_zero (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA)) hmap0
  have hfm : IsMultiHomogeneous a (linSubst A (map σ P.det)) :=
    GlobalTheory.HeightUnique.linSubst_homog A (isMultiHomogeneous_map_ring a _ hhom σ)
  have hint := Closed.sphereLogIntegrable B N a _ hf0 hfm
  have hae := ae_blockSphere_eval_ne_zero B N a _ hf0 hfm
  have hpt : ∀ z : BlockSphere B N, eval (blockPoint z) (linSubst A (map σ P.det)) ≠ 0 →
      Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ≤
        ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := by
    intro z hz
    set u : Fin B × Fin N → ℂ := fun q => A.mulVec (fun k => blockPoint z (q.1, k)) q.2 with hu
    have hunit : ∀ i, frameNorm A (fun j => u (i, j)) = 1 := fun i => by
      show frameNorm A (A.mulVec (fun k => blockPoint z (i, k))) = 1
      rw [GlobalTheory.MaxPoint.frameNorm_mulVec hA]
      have hz := (z i).2
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq] at hz
      simpa [blockPoint, spherePoint] using hz
    have hev : eval (blockPoint z) (linSubst A (map σ P.det)) = (Matrix.of fun i k => eval₂ σ u (P i k)).det := by
      rw [GlobalTheory.MaxPoint.eval_linSubst, MvPolynomial.eval_map]
      have := RingHom.map_det (eval₂Hom σ u) P
      rw [coe_eval₂Hom] at this
      rw [this]; rfl
    rw [hev] at hz ⊢
    obtain ⟨hG, hH⟩ := GlobalTheory.T.hadamard_ineq_complex_combinations_basis F V nm d b σ (Matrix.of fun i k => eval₂ σ u (P i k))
    have hprod : ∏ k, cnrm nm σ (fun i => (Matrix.of fun i k => eval₂ σ u (P i k)) i k) b ≤ ∏ k, Bd k :=
      Finset.prod_le_prod (fun k _ => Real.sqrt_nonneg _) (fun k _ => hbd k u hunit)
    have hpos : 0 < ‖(Matrix.of fun i k => eval₂ σ u (P i k)).det‖ := norm_pos_iff.2 hz
    have hsq : 0 < Real.sqrt (nm.gram σ b).det.re := Real.sqrt_pos.2 hG
    have hle := Real.log_le_log (mul_pos hpos hsq) (hH.trans hprod)
    rw [Real.log_mul hpos.ne' hsq.ne', Real.log_prod (fun k _ => (hBd k).ne'), Real.log_sqrt hG.le] at hle
    linarith
  unfold blockSphereMean
  calc ∫ z, Real.log ‖eval (blockPoint z) (linSubst A (map σ P.det))‖ ∂(blockSphereProb B N)
      ≤ ∫ _z, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2) ∂(blockSphereProb B N) :=
        integral_mono_ae hint (integrable_const _) (by
          filter_upwards [hae] with z hz
          exact hpt z hz)
    _ = _ := by simp

end GlobalTheory.HSShort.DetTop

theorem GlobalTheory.HSShort.deg_ge_ht_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ), Lat w A Λ → ∀ (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ) (Bd : Fin d → ℝ), P.det ≠ 0 → IsMultiHomogeneous a P.det → (∀ k, 0 < Bd k) → (∀ k m, ∑ i, coeff m (linSubst w (P i k)) • b i ∈ M) → (∀ k σ (u : Fin B × Fin N → ℂ), (∀ i, frameNorm (A σ) (fun j => u (i, j)) = 1) → cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) → ht w A P.det - ∑ k, Real.log (Bd k) ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM B N n w A Λ hL P a Bd hP hhom hBd hcoef hbd
  obtain ⟨w', hw'⟩ := GlobalTheory.HSShort.DetTop.exists_rightInv w hL.spans
  have hdet := GlobalTheory.HSShort.DetTop.linSubst_det w P
  have hg0 : linSubst w P.det ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hw' hP
  have hcg : ∀ m, coeff m (linSubst w P.det) ∈
      Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
    rw [hdet]
    exact GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors F V M d b _ (P.map (linSubst w)) (fun k m => by simpa using hcoef k m)
  have hfin := GlobalTheory.T.finiteHeight_sub_mean_le_degree_fullLattice_detIdeal F V nm M d b hM _ _ hg0 hcg
  have harch : ∀ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det)) ≤
      ∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2 := fun σ =>
    GlobalTheory.HSShort.DetTop.arch nm b hL.pos σ (A σ) (hL.det σ) P a Bd hP hhom hBd (fun k u hu => hbd k σ u hu)
  have hr : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast NumberField.Embeddings.card F ℂ
  have hht : ht w A P.det = finPart (linSubst w P.det) +
      mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) := by
    simp only [ht, formHeight, finPart, mean, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hmean : mean F (fun σ => blockSphereMean B N (linSubst (A σ) (map σ P.det))) ≤
      ∑ k, Real.log (Bd k) - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 := by
    unfold mean
    calc (∑ σ, blockSphereMean B N (linSubst (A σ) (map σ P.det))) / (Module.finrank ℚ F : ℝ)
        ≤ (∑ σ : F →+* ℂ, (∑ k, Real.log (Bd k) - Real.log (nm.gram σ b).det.re / 2)) / (Module.finrank ℚ F : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => harch σ) hr.le
      _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← Finset.sum_div]
          field_simp
  rw [hht]
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.FrameMove

variable {D : D7}

theorem levChi_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    levChi V β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) κ =
      ((ext1 P.H P.chi (rTup β (datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (finE V κ)) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  simp [datY]
  rfl

set_option maxHeartbeats 1600000 in

theorem frame_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i n hF PY PW hY hW P
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (Fin.pos i)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg
    hrk hc hc' (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := GlobalTheory.KapIsot.frames_inner (Yc D 0) (Wc D i) hF PY PW hY hW
    (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact GlobalTheory.KapIsot.odd_r D.R) _ _ _ j Φ hΦ
  refine ⟨h, fun κ hκ => ?_⟩
  have hx := hh (h⁻¹ * κ * h)
  rw [show h * (h⁻¹ * κ * h) * h⁻¹ = κ by group] at hx
  obtain ⟨l1, l2⟩ := GlobalTheory.LevTrans.levtrans (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ ⟨PY.ψ (h⁻¹ * κ * h), PY.into _⟩
  rw [hx] at l1 l2
  obtain ⟨hp, hH⟩ := mem_lev.1 hκ.2
  have hpY := l1.2 hp
  have hrt : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ)) =
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h))) := l2 hpY
  refine ⟨?_, ?_⟩
  · show PY.ψ (h⁻¹ * κ * h) ∈
      (GfC (Yc D 0) ⊓ (lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)).comap (finE (Yc D 0)) : Subgroup _)
    refine Subgroup.mem_inf.2 ⟨PY.into _, ?_⟩
    show finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)) ∈ lev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P)
    refine mem_lev.2 ⟨hpY, ?_⟩
    rw [← hrt]
    exact hH
  · have e1 : levChi (Wc D i) (R.βW i) (R.datWp i P) (PW.ψ κ) =
        ((ext1 P.H P.chi (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) (PW.ψ κ))) : ℂˣ) : ℂ) :=
      levChi_datY (Wc D i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) R.Pg P (fun _ _ => 1) (fun _ => 1) (PW.ψ κ)
    have e2 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) =
        ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) (PY.ψ (h⁻¹ * κ * h)))) : ℂˣ) : ℂ) :=
      levChi_datY (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) R.Pg P R.chi (fun _ => 1) (PY.ψ (h⁻¹ * κ * h))
    rw [e1, e2, hrt]

end GlobalTheory.FrameMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionFiniteInOpenOffBadForm
section
set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

noncomputable section

namespace GlobalTheory.HSShort.Supp

theorem finite_of_finite_pts {k : Type} [Field k] (S : LinSys k) (hS : S.IsVariety) (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y) (hZ : IsClosed Z)
    (h : {x : S.Pt Ω | ptOf x.1 ∈ Z}.Finite) : Z.Finite := by
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  have hf : (Z ∩ closedPoints S.Y).Finite := by
    refine (h.image fun x => ptOf x.1).subset ?_
    rintro y ⟨hyZ, hy⟩
    by_contra hne
    refine subset_of_forall_pt_mem k S hS Ω {y} hy ∅ isOpen_empty (fun x hx => hne ⟨x, ?_, hx⟩) rfl
    have e : ptOf x.1 = y := hx
    change ptOf x.1 ∈ Z
    rw [e]
    exact hyZ
  have hc : IsClosed (Z ∩ closedPoints S.Y) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints S.Y)]
    exact hf.isClosed_biUnion fun y hy => hy.2
  rw [← JacobsonSpace.closure_inter_closedPoints hZ, hc.closure_eq]
  exact hf

theorem exists_finite_lines {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {G : MvPolynomial (Fin 1 × Fin N) K}
    (hG : G ≠ 0) : ∃ R : Set (Fin N → K), R.Finite ∧ ∀ y : Fin N → K, y ≠ 0 →
      (∀ ξ : Fin N → K, ∑ j, ξ j * y j = 0 → eval (fun p => ξ p.2) G = 0) → ∃ r ∈ R, ∃ c : K, y = c • r := by
  classical
  refine ⟨(fun p : MvPolynomial (Fin 1 × Fin N) K => fun j => coeff (Finsupp.single ((0 : Fin 1), j) 1) p) ''
    (UniqueFactorizationMonoid.factors G).toFinset, (Finset.finite_toSet _).image _, fun y hy hz => ?_⟩
  have irr := HyperplaneFactor.irreducible_lin hy
  obtain ⟨n, hn⟩ := HyperplaneFactor.exists_dvd_pow_of_zeros (a := lin y) (b := G) fun x hx => by
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz (fun j => x (0, j)) (by rwa [HyperplaneFactor.eval_lin] at hx)
    simpa only [e] using h1
  obtain ⟨q, hq, ha⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG irr (irr.prime.dvd_of_dvd_pow hn)
  obtain ⟨a, ha⟩ := ha.symm
  obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
  rw [ht, mul_comm] at ha
  refine ⟨_, ⟨q, by simpa using hq, rfl⟩, t, funext fun j => ?_⟩
  have h1 := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) ha
  rw [coeff_C_mul, HyperplaneFactor.coeff_lin] at h1
  simpa using h1.symm

theorem finite_and_inOpen : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → ∀ (g : MvPolynomial (Fin T.N) F), (∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0) → (∀ (K : Type) [Field K] [Algebra F K] (y : Fin T.N → K), {x : T.Pt K | aeval (T.coords x.1) g ≠ 0 ∧ ∃ c : K, T.coords x.1 = c • y}.Finite) → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f ≠ 0 → (∀ x ∈ T.geomPts E (T.linSection E s), aeval (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1) g ≠ 0) → ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite ∧ T.InOpen E (T.linSection E s) := by
  intro F _ _ T hT δ f hf g hbd hfin E _ _ s hG hg
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  refine ⟨finite_of_finite_pts _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed ?_, ?_⟩
  · obtain ⟨R, hR, hl⟩ := exists_finite_lines hG
    refine ((hR.biUnion fun y _ => hfin (AlgebraicClosure E) y).preimage
      (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).1.injOn).subset fun x hx => ?_
    have hm : x ∈ T.geomPts E (T.linSection E s) := (LinSys.mem_subPts_iff _ _ x).2 hx
    have hy := hT.alg.bpf.coords_ne_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1
    obtain ⟨r, hr, hc⟩ := hl _ hy fun ξ hξ => by
      rw [EtaleSection.eval_spec]
      refine (GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F T.D T.N δ _ f hf).1 _ _ ξ _ hy (fun p hp => ?_)
        ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hm) hξ
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hp
      rwa [LinSys.baseHom_ptOver] at this
    exact Set.mem_biUnion hr ⟨hg x hm, hc⟩
  · exact subset_of_forall_pt_mem E _ hv (AlgebraicClosure E) _ (T.linSection E s).support.isClosed
      (T.toLinSys.bcFst E ⁻¹' (T.U : Set T.Y)) (T.U.isOpen.preimage (T.toLinSys.bcFst E).continuous)
      fun x hx hb => hg x ((LinSys.mem_subPts_iff _ _ x).2 hx)
        (hbd (AlgebraicClosure E) (LinSys.toBase x) hb)

end GlobalTheory.HSShort.Supp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolIso

theorem modelI_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Λ : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (Λ • Φ) h = Λ * M.I om Φ h := by
  unfold Model.I theta thetaSum
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext g
  exact tsum_mul_left

end GlobalTheory.PolIso
end

