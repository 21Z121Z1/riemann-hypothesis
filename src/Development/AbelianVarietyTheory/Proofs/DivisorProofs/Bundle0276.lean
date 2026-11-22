import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLengthFiltrationInterKerCofactorLinearFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FixNormCls

variable {E : Type} [Field E] [NumberField E]

def ord (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ :=
  FractionalIdeal.count E P (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have : (RingOfIntegers.mapRingEquiv τ) x ∈
        P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      convert hx using 1
      exact (RingOfIntegers.mapRingEquiv τ).symm_apply_apply x
    have h2 := h this
    rw [Submodule.mem_bot, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective] at h2
    rw [Submodule.mem_bot]; exact h2

theorem mem_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ (primeMap τ P).asIdeal ↔ RingOfIntegers.mapRingEquiv τ.symm a ∈ P.asIdeal :=
  Ideal.mem_comap

theorem ord_zero (P : HeightOneSpectrum (𝓞 E)) : ord P (0 : E) = 0 := by
  simp [ord, FractionalIdeal.count_zero]

theorem ord_mul (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x * y) = ord P x + ord P y := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

theorem ord_inv (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P x⁻¹ = - ord P x := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem ord_div (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x / y) = ord P x - ord P y := by
  rw [div_eq_mul_inv, ord_mul P hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

theorem ord_one (P : HeightOneSpectrum (𝓞 E)) : ord P (1 : E) = 0 := by
  simp [ord, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem ord_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    ord (primeMap τ P) (τ x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  exact GlobalTheory.OrdTransport.count_spanSingleton_ringEquiv (𝓞 E) E (RingOfIntegers.mapRingEquiv τ) τ
    (fun a => rfl) P (primeMap τ P)
    (fun a => by
      rw [mem_primeMap]
      have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ a) = a :=
        RingOfIntegers.ext (by change τ.symm (τ (a : E)) = (a : E); exact τ.symm_apply_apply _)
      rw [this]) x hx

theorem primeMap_primeMap (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E)) :
    primeMap τ (primeMap τ P) = P := by
  ext a
  rw [mem_primeMap, mem_primeMap]
  have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ.symm a) = a := by
    apply RingOfIntegers.ext
    change τ.symm (τ.symm (a : E)) = (a : E)
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq, hτ]
  rw [this]

end GlobalTheory.FixNormCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdImIteratedWirtingerDerivWordDifferentiableOn
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

noncomputable def mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) (z : Φ → ℂ) : ℂ :=
  c σ * Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ))

theorem hasFDerivAt_logIm (τ : Φ) {z : Φ → ℂ} (hz : (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ((Real.log (z τ).im : ℝ) : ℂ))
      (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))) z := by
  have h1 : HasFDerivAt (fun z : Φ → ℂ => (z τ).im) (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)) z :=
    (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)).hasFDerivAt
  have h2 := h1.log hz
  exact ofRealCLM.hasFDerivAt.comp z h2

theorem hasFDerivAt_expo (A : Φ → ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (fun z : Φ → ℂ => ∑ τ, A τ * ((Real.log (z τ).im : ℝ) : ℂ))
      (∑ τ, A τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ))))) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (fun τ _ => (hasFDerivAt_logIm τ (hz τ)).const_mul (A τ))
  have e : (∑ τ, fun y : Φ → ℂ => A τ * ((Real.log (y τ).im : ℝ) : ℂ)) = fun y => ∑ τ, A τ * ((Real.log (y τ).im : ℝ) : ℂ) := by
    ext y; simp [Finset.sum_apply]
  rw [e] at this; exact this

theorem hasFDerivAt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) :
    HasFDerivAt (mono c a σ)
      (c σ • (Complex.exp (∑ τ, a σ τ * ((Real.log (z τ).im : ℝ) : ℂ)) • ∑ τ, a σ τ • (ofRealCLM.comp (((z τ).im)⁻¹ • (imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Φ => ℂ) τ)))))) z :=
  ((hasFDerivAt_expo (a σ) hz).cexp).const_mul (c σ)

open Classical in
theorem wirt_mono (c : ℂ → ℂ) (a : ℂ → Φ → ℂ) (σ : ℂ) {z : Φ → ℂ} (hz : ∀ τ, 0 < (z τ).im) (τ₀ : Φ) (b : Bool) :
    wirt τ₀ b (mono c a σ) z =
      mono (fun σ => (if b then I else -I) / 2 * c σ * a σ τ₀) (fun σ => a σ - Pi.single τ₀ 1) σ z := by
  have hz' : ∀ τ, (z τ).im ≠ 0 := fun τ => (hz τ).ne'
  rw [wirt, (hasFDerivAt_mono c a σ hz').fderiv]
  simp [mono, Pi.single_apply]
  have hy := hz τ₀
  have e1 : ∀ x, ((if x = τ₀ then (1:ℂ) else 0).im) = 0 := fun x => by split_ifs <;> simp
  have e2 : ∀ x, ((if x = τ₀ then I else 0).im) = if x = τ₀ then 1 else 0 := fun x => by split_ifs <;> simp
  simp only [e1, e2, ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have he : ∑ x, (a σ x - if x = τ₀ then 1 else 0) * ((Real.log (z x).im : ℝ) : ℂ) =
      ∑ x, a σ x * ((Real.log (z x).im : ℝ) : ℂ) - ((Real.log (z τ₀).im : ℝ) : ℂ) := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [he, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hy]
  have hy' : ((z τ₀).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp <;> field_simp <;> ring

theorem wirtWord_mono (U : Set (Φ → ℂ)) (hU : IsOpen U) (hUpos : ∀ z ∈ U, ∀ τ, 0 < (z τ).im) (w : List (Φ × Bool)) :
    ∀ (c : ℂ → ℂ) (a : ℂ → Φ → ℂ), Differentiable ℂ c → (∀ τ, Differentiable ℂ (fun σ => a σ τ)) →
      ∃ (c' : ℂ → ℂ) (a' : ℂ → Φ → ℂ), Differentiable ℂ c' ∧ (∀ τ, Differentiable ℂ (fun σ => a' σ τ)) ∧
        ∀ σ, Set.EqOn (wirtWord w (mono c a σ)) (mono c' a' σ) U := by
  induction w with
  | nil => exact fun c a hc ha => ⟨c, a, hc, ha, fun σ z _ => rfl⟩
  | cons l w ih =>
    intro c a hc ha
    obtain ⟨c₁, a₁, hc₁, ha₁, h₁⟩ := ih c a hc ha
    classical
    refine ⟨fun σ => (if l.2 then I else -I) / 2 * c₁ σ * a₁ σ l.1, fun σ => a₁ σ - Pi.single l.1 1,
      ((differentiable_const _).mul hc₁).mul (ha₁ l.1), fun τ => ?_, fun σ z hz => ?_⟩
    · simp only [Pi.sub_apply]
      exact (ha₁ τ).sub (differentiable_const _)
    · rw [wirtWord_cons, GoodAdd.wirt_congr hU (h₁ σ) _ _ hz]
      convert wirt_mono c₁ a₁ σ (hUpos z hz) l.1 l.2

theorem mono_differentiable {c : ℂ → ℂ} {a : ℂ → Φ → ℂ} (hc : Differentiable ℂ c)
    (ha : ∀ τ, Differentiable ℂ (fun σ => a σ τ)) (z : Φ → ℂ) : Differentiable ℂ (fun σ => mono c a σ z) := by
  unfold mono
  refine hc.mul (Differentiable.cexp ?_)
  exact Differentiable.fun_sum fun τ _ => (ha τ).mul (differentiable_const _)

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons l w ih => intro y hy; rw [wirtWord_cons, wirtWord_cons]; exact GoodAdd.wirt_congr hU ih _ _ hy

end GlobalTheory.HeckeTwo.ProdImWirt

theorem GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLiftStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_of_surjective_ker_le_smul : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  first | exact @GlobalTheory.FlatLift.projective_reduction_of_flat_lift | exact GlobalTheory.FlatLift.projective_reduction_of_flat_lift | (intros; apply GlobalTheory.FlatLift.projective_reduction_of_flat_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PscoTCore
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem psco_t_core : GlobalTheory.PsCo.Cw2a.CoreCondition := by
  intro A _ _ I _ _ D dm J Z u η E μ r h1 h2 h3 h4 h5
  exact GlobalTheory.weighted_det_divergence_mem_ideal (K := ℂ) D dm J Z u η E μ r h1 h2 h3 h4 h5

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  first | exact @GlobalTheory.QFam.qConj_ring | exact GlobalTheory.QFam.qConj_ring | (intros; apply GlobalTheory.QFam.qConj_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneLatticeSpanSingletonStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_lattice_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  first | exact @GlobalTheory.finGen_line_span_principal_target | exact GlobalTheory.finGen_line_span_principal_target | (intros; apply GlobalTheory.finGen_line_span_principal_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionUniformizerNilpotent
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem reduction_ker_uniformiser_eq_range_pow : ∀ (p : ℕ) (W k Λ : Type) [CommRing W] [IsDomain W] [Field k] [CommRing Λ] (h e : ℕ) (c : W →+* k) (ρ : Λ →+* Matrix (Fin h) (Fin h) W) (π : Λ) (u : Λˣ), (p : W) ≠ 0 → Function.Surjective c → (∀ w, c w = 0 → (p : W) ∣ w) → c p = 0 → 0 < e → (p : Λ) = π ^ e * u → ((ρ π).map c) ^ e = 0 ∧ ∀ x : Fin h → k, (ρ π).map c *ᵥ x = 0 → ∃ y, x = ((ρ π).map c) ^ (e - 1) *ᵥ y := by
  intro p W k Λ _ _ _ _ h e c ρ π u hp hc hker hcp he hpu
  have hmap : ∀ M : Matrix (Fin h) (Fin h) W, M.map c = c.mapMatrix M := fun M => rfl
  have key : ρ π * ρ (π ^ (e - 1) * ↑u) = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he, ← hpu, map_natCast]
  have key' : ρ (π ^ (e - 1) * ↑u) * ρ π = (p : Matrix (Fin h) (Fin h) W) := by
    rw [← map_mul, mul_comm, map_mul, key]
  have hpv : ∀ v : Fin h → W, (p : Matrix (Fin h) (Fin h) W) *ᵥ v = (p : W) • v := by
    intro v
    exact Matrix.natCast_mulVec p v
  have hpk : (p : k) = 0 := by rw [← map_natCast c]; exact hcp
  refine ⟨?_, ?_⟩
  · have hpe : π ^ e = (p : Λ) * ↑u⁻¹ := by
      rw [hpu, mul_assoc, Units.mul_inv, mul_one]
    rw [hmap, ← map_pow, ← map_pow, hpe, map_mul, map_mul, map_natCast, map_natCast,
      ← map_natCast (algebraMap k (Matrix (Fin h) (Fin h) k)) p, hpk, map_zero, zero_mul]
  · intro x hx
    choose xt hxt using fun i => hc (x i)
    have hcx : c ∘ xt = x := funext hxt
    have hdiv : ∀ i, (p : W) ∣ (ρ π *ᵥ xt) i := by
      intro i; apply hker
      rw [RingHom.map_mulVec, hcx, hx]; rfl
    choose z hz using hdiv
    have hinj : ∀ v : Fin h → W, ρ π *ᵥ v = 0 → v = 0 := by
      intro v hv
      have h1 : (p : W) • v = 0 := by
        rw [← hpv, ← key', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
      exact (smul_eq_zero.mp h1).resolve_left hp
    have hxtz : ρ π *ᵥ xt = (p : W) • z := funext fun i => by rw [hz i]; rfl
    have hxB : xt = (ρ π ^ (e - 1)) *ᵥ (ρ ↑u *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, ← map_pow, ← map_mul]
      apply sub_eq_zero.mp
      apply hinj
      rw [Matrix.mulVec_sub, hxtz, Matrix.mulVec_mulVec, key, hpv, sub_self]
    refine ⟨c ∘ (ρ ↑u *ᵥ z), ?_⟩
    funext i
    rw [hmap, ← map_pow, ← hxt i, hxB, RingHom.map_mulVec]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_pair_lift_to_prime_power_field : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧ ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  first | (exact @GlobalTheory.Shin.reg_norm_frob) | (exact GlobalTheory.Shin.reg_norm_frob) | (intros; apply GlobalTheory.Shin.reg_norm_frob  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArithIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def moveLin (δ : GL (Fin r) E) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  ((δ : Matrix (Fin r) (Fin r) E).mulVecLin).restrictScalars (𝓞 E)

omit [IsCMField E] in
theorem moveLin_apply (δ : GL (Fin r) E) (v : Fin r → E) :
    moveLin δ v = (δ : Matrix (Fin r) (Fin r) E).mulVec v := rfl

omit [NumberField E] [IsCMField E] in
theorem inv_mulVec_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
      ((δ : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in
theorem mulVec_inv_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    (δ : Matrix (Fin r) (Fin r) E).mulVec
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit [IsCMField E] in
theorem mem_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (y : Fin r → E) :
    y ∈ L.map (moveLin δ) ↔
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [moveLin_apply, inv_mulVec_mulVec]
    exact hx
  · intro h
    exact ⟨_, h, by rw [moveLin_apply, mulVec_inv_mulVec]⟩

omit [IsCMField E] in
theorem span_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E))
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span E ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) = ⊤ := by
  have hsurj : Function.Surjective (δ : Matrix (Fin r) (Fin r) E).mulVecLin := fun y =>
    ⟨_, mulVec_inv_mulVec δ y⟩
  have : ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) =
      (δ : Matrix (Fin r) (Fin r) E).mulVecLin '' (L : Set (Fin r → E)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, ← Submodule.map_span, hL, Submodule.map_top, LinearMap.range_eq_top]
  exact hsurj

theorem isUStab_conj (X₂ X : Data E r) (δ : GL (Fin r) E) (hG : X₂.Gm = X.Gm)
    (hδ : ∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hK : ∀ x, x ∈ X₂.Λ.map (moveLin δ) ↔
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ X₂.Λ.map (moveLin δ)) :
    IsUStab X₂.Gm X₂.Λ (δ⁻¹ * γ * δ) := by
  have hval : ∀ x, (((δ⁻¹ * γ * δ : GL (Fin r) E)) : Matrix (Fin r) (Fin r) E).mulVec x =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((γ : Matrix (Fin r) (Fin r) E).mulVec ((δ : Matrix (Fin r) (Fin r) E).mulVec x)) := by
    intro x
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [hval, hval, ← hδ, mulVec_inv_mulVec, mulVec_inv_mulVec, hG, (X.Γ_stab γ hγ).1, ← hG, hδ]
  · rw [hval, ← mem_map_moveLin, ← hK, mem_map_moveLin, inv_mulVec_mulVec]

omit [NumberField E] [IsCMField E] in

theorem relIndex_ne_zero_of_reps (Γ₂ A : Subgroup (GL (Fin r) E)) (δ : GL (Fin r) E)
    (S : Finset (GL (Fin r) E))
    (h : ∀ γ ∈ A, ∃ s ∈ S, s⁻¹ * (δ⁻¹ * γ * δ) ∈ Γ₂) :
    (Γ₂.map (MulAut.conj δ).toMonoidHom).relIndex A ≠ 0 := by
  classical
  set H := Γ₂.map (MulAut.conj δ).toMonoidHom with hH
  choose! f hfS hf using h
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    refine Finite.of_injective
      (fun q : A ⧸ H.subgroupOf A => (⟨f (q.out : A), hfS _ q.out.2⟩ : S)) ?_
    intro p q hpq
    have hpq' : f (p.out : A) = f (q.out : A) := congrArg Subtype.val hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have ha := hf _ p.out.2
    have hb := hf _ q.out.2
    rw [hpq'] at ha
    have hc := Γ₂.mul_mem (Γ₂.inv_mem ha) hb
    refine ⟨_, hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_map_conj_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  intro E _ _ _ r X₂ X δ hG hδ
  set Λ' := X₂.Λ.map (moveLin δ) with hΛ'
  have hfg : Λ'.FG := X₂.Λ_fg.map _
  have hsp := span_map_moveLin δ X₂.Λ X₂.Λ_span
  obtain ⟨n₁, hn₁, h₁⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice X.Λ Λ' hfg X.Λ_span
  obtain ⟨n₂, hn₂, h₂⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice Λ' X.Λ X.Λ_fg hsp
  have hnat : ∀ (L : Submodule (𝓞 E) (Fin r → E)) (k : ℕ) (v : Fin r → E), v ∈ L →
      (k : E) • v ∈ L := by
    intro L k v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv k
  have hA : ∀ v ∈ Λ', ((n₁ * n₂ : ℕ) : E) • v ∈ X.Λ := by
    intro v hv
    have := hnat _ n₂ _ (h₁ v hv)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm n₂] at this
  have hB : ∀ v ∈ X.Λ, ((n₁ * n₂ : ℕ) : E) • v ∈ Λ' := by
    intro v hv
    have := hnat _ n₁ _ (h₂ v hv)
    rwa [smul_smul, ← Nat.cast_mul] at this
  obtain ⟨K, hK, hKΛ⟩ := GlobalTheory.T.exists_finite_relIndex_stabilizer_commensurable_lattice X.Λ Λ' (n₁ * n₂) (Nat.mul_pos hn₁ hn₂) X.Λ_fg hA hB X.Γ
    (fun γ hγ => (X.Γ_stab γ hγ).2)
  obtain ⟨S, hS⟩ := X₂.Γ_index
  have hAH : (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex (X.Γ ⊓ K) ≠ 0 :=
    relIndex_ne_zero_of_reps X₂.Γ (X.Γ ⊓ K) δ S fun γ hγ =>
      hS _ (isUStab_conj X₂ X δ hG hδ hγ.1 (hKΛ γ hγ.2))
  refine Subgroup.relIndex_ne_zero_trans hAH ?_
  rwa [Subgroup.inf_relIndex_left]

end GlobalTheory.ArithIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAddStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relLen_trans_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ), RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  first | exact @GlobalTheory.relLen_chain_add | exact GlobalTheory.relLen_chain_add | (intros; apply GlobalTheory.relLen_chain_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLengthFiltrationInterKerCofactorLinearFactorStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  first | exact @GlobalTheory.HerbCore.relLen_lin_filKer | exact GlobalTheory.HerbCore.relLen_lin_filKer | (intros; apply GlobalTheory.HerbCore.relLen_lin_filKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFlatOfCompFlatOfMapMaximalIdealStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq : ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E] (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' → IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  first | exact @GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | exact GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal | (intros; apply GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal <;> assumption)
end

