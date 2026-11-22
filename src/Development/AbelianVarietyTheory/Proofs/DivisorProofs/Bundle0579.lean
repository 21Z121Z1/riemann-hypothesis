import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummationStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeThetaKernel_poisson_summation : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧ ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y = κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  first | exact @GlobalTheory.HeckePoisson.theta_poisson | exact GlobalTheory.HeckePoisson.theta_poisson | (intros; apply GlobalTheory.HeckePoisson.theta_poisson <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrdersOfZmodPExtremes
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.comap_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffReal
section
open Formalism.L2.DIV

namespace GlobalTheory.CuspMult

theorem idemOf_coeff_real : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ)
    (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X →
    ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  intro K G _ _ _ σ X hX hS g
  rw [coeff_idemOf, map_sum, star_sum]
  refine Finset.sum_nbij' (fun χ t => χ t⁻¹) (fun χ t => χ t⁻¹) hS hS
    (fun χ _ => by simp) (fun χ _ => by simp) fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  simp only [map_mul, map_div₀, map_natCast, star_mul', star_div₀, star_natCast]
  rw [h1, h2]
  rfl

end GlobalTheory.CuspMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  first | exact @GlobalTheory.HeckeMellinProd.mellin_prod | exact GlobalTheory.HeckeMellinProd.mellin_prod | (intros; apply GlobalTheory.HeckeMellinProd.mellin_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
section
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

noncomputable section
namespace GlobalTheory.KS

theorem isCob_of_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  intro X J K V U hU z z' b h1 h2 hz'
  obtain ⟨y', hy'⟩ := hz'
  have cov : ∀ O : X.Opens, O ≤ ⨆ k, O ⊓ U k := fun O x hx => by
    have : x ∈ ⨆ k, U k := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  have glue : ∀ i, ∃ t : Γ(X, V i), ∀ k, rsT t (V i ⊓ U k) = rsT (y' k) (V i ⊓ U k) - b i k := by
    intro i
    refine exists_rsT_eq (fun k => V i ⊓ U k) (fun k => inf_le_left) (cov _) _ fun k l => ?_
    have e : (V i ⊓ U k) ⊓ (V i ⊓ U l) ≤ V i ⊓ U k ⊓ U l := fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
    have e₁ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U k := inf_le_left
    have e₂ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U l := fun x hx => ⟨hx.1.1, hx.2⟩
    have e₃ : V i ⊓ U k ⊓ U l ≤ U k ⊓ U l := fun x hx => ⟨hx.1.2, hx.2⟩
    rw [← rsT_rsT e₁ e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => rsT s (V i ⊓ U k ⊓ U l)) (hy' k l)
    simp only [rsT_sub] at k₀
    rw [h2, rsT_rsT inf_le_right e₃, rsT_rsT inf_le_left e₃] at k₀
    simp only [rsT_sub]
    rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
    linear_combination k₀
  choose y hy using glue
  refine ⟨y, fun i i' => ?_⟩
  refine eq_of_rsT_eq (fun k => V i ⊓ V i' ⊓ U k) (fun k => inf_le_left) (cov _) _ _ fun k => ?_
  have e₁ : V i ⊓ V i' ⊓ U k ≤ V i ⊓ U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have e₂ : V i ⊓ V i' ⊓ U k ≤ V i' ⊓ U k := fun x hx => ⟨hx.1.2, hx.2⟩
  show rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) (V i ⊓ V i' ⊓ U k)
  rw [h1, rsT_sub, rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (y i'), ← rsT_rsT inf_le_left e₁ (y i), hy, hy]
  simp only [rsT_sub]
  rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
  ring

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolutionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_iff_convolution : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y → (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  first | (exact @GlobalTheory.Shin.kills_iff_conv) | (exact GlobalTheory.Shin.kills_iff_conv) | (intros; apply GlobalTheory.Shin.kills_iff_conv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularAdicCompletion
section
open Ideal WittVector

namespace GlobalTheory

theorem isSMulRegular_natCast_adicCompletion (p : ℕ) (A : Type) [CommRing A]
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A)
      (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  set I : Ideal A := Ideal.span {(p : A)}
  intro x y hxy
  have key : ∀ z : AdicCompletion I A, (p : AdicCompletion I A) * z = 0 → z = 0 := by
    intro z hz
    apply AdicCompletion.ext
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (z.val (n + 1))
    have hz' : (p • z).val (n + 1) = 0 := by
      rw [nsmul_eq_mul, hz]; rfl
    rw [AdicCompletion.val_smul_apply, ← ha, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hz'
    have hmem : (p : A) * a ∈ Ideal.span {(p : A) ^ (n + 1)} := by
      have : p • a = (p : A) * a := by rw [nsmul_eq_mul]
      rw [← this, ← Ideal.span_singleton_pow]
      simpa [smul_eq_mul, Ideal.mul_top] using hz'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    have hab : a = (p : A) ^ n * b := by
      apply hp
      simp only [smul_eq_mul]
      rw [← hb]; ring
    have htr := z.property (Nat.le_succ n)
    change AdicCompletion.transitionMap I A (Nat.le_succ n) (z.val (n + 1)) = z.val n at htr
    rw [← htr, ← ha, AdicCompletion.val_zero_apply]
    change (Submodule.Quotient.mk a : A ⧸ (I ^ n • ⊤ : Submodule A A)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hab]
    simp only [smul_eq_mul, Ideal.mul_top, I, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩
  have h0 : (p : AdicCompletion I A) * (x - y) = 0 := by
    rw [mul_sub, sub_eq_zero]; exact hxy
  exact sub_eq_zero.mp (key _ h0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEqStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointShape_unique_and_degW_eq : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ), JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' → (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  first | exact @GlobalTheory.JointShapeUniq.jointShape_unique_deg | exact GlobalTheory.JointShapeUniq.jointShape_unique_deg | (intros; apply GlobalTheory.JointShapeUniq.jointShape_unique_deg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerFontaineThetaEqSpanOfDistinguished
section
open Ideal WittVector

noncomputable section

namespace GlobalTheory

theorem mem_span_of_step_adic {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    x ∈ span {a} := by
  classical
  let g : {z // P z} → A × {z // P z} := fun z =>
    ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)
  have hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1 := fun z =>
    (h z.1 z.2).choose_spec.choose_spec.1
  let xs : ℕ → {z // P z} := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n
  have hxs : ∀ n, xs (n + 1) = (g (xs n)).2 := fun n => rfl
  let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1
  have hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1 := fun n => Finset.sum_range_succ _ _
  have hY : ∀ n, x = a * S n + q ^ n * (xs n).1 := by
    intro n
    induction n with
    | zero => simp [S, xs]
    | succ n ih =>
      rw [hS, hxs]
      linear_combination ih + q ^ n * hg (xs n)
  have hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]
      refine add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (span {q}) A).prec' S (by
    intro m n hmn
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← neg_sub]
    exact neg_mem (hC m n hmn))
  have hxL : x - a * L = 0 := by
    refine (inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)
    have hn := hL n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢
    rw [sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by
      linear_combination hY n]
    exact add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))
  exact mem_span_singleton'.2 ⟨L, by rw [mul_comm]; exact (sub_eq_zero.1 hxL).symm⟩

theorem ker_fontaineTheta_eq_span_of_dvd : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) →
    ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 →
    (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) →
    RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  intro p _ R _ _ _ hreg ξ hθξ hdiv
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    refine mem_span_of_step_adic (p : WittVector p (PreTilt R p)) ξ
      (fun x => fontaineTheta R p x = 0) ?_ x hx
    intro x hx
    have hc : PreTilt.coeff 0 (x.coeff 0) = 0 := by
      rw [← mk_fontaineTheta, hx, map_zero]
    obtain ⟨d, hd⟩ := hdiv _ hc
    have hm : x - ξ * teichmuller p d ∈ span {(p : WittVector p (PreTilt R p))} := by
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul]
      change x.coeff 0 - constantCoeff ξ * (teichmuller p d).coeff 0 = 0
      rw [teichmuller_coeff_zero, ← hd, sub_self]
    obtain ⟨z, hz⟩ := mem_span_singleton'.1 hm
    refine ⟨teichmuller p d, z, by linear_combination -hz, ?_⟩
    apply hreg
    change (p : R) * fontaineTheta R p z = (p : R) * 0
    rw [mul_zero, ← map_natCast (fontaineTheta R p) p, ← map_mul, mul_comm, hz, map_sub, map_mul,
      hx, hθξ, zero_mul, sub_zero]
  · intro hx
    obtain ⟨a, rfl⟩ := mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, map_mul, hθξ, mul_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEqStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → v ^ Q = w ^ Q → GlobalTheory.EtC.RedChern.defect Q q U v = GlobalTheory.EtC.RedChern.defect Q q U w := by
  first
  | exact @GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | exact GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndexStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_dual_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) = r ^ fdeg E := by
  first | exact @GlobalTheory.lieLat_relIndex_dual | exact GlobalTheory.lieLat_relIndex_dual | (intros; apply GlobalTheory.lieLat_relIndex_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHolomorphicMorseInequalityUniformStatement
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_morse_inequality_uniform : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U → (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧ ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U → ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤ ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  first | exact @GlobalTheory.morse_local | exact GlobalTheory.morse_local | (intros; apply GlobalTheory.morse_local <;> assumption)
end

