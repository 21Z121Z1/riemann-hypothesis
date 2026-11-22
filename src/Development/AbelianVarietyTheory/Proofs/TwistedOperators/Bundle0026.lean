import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
section
noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.ThetaGLSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

variable (m : ℕ) in

def aug (χ : GL (Fin n) k →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) :=
  Submodule.span ℂ {z | ∃ h : GL (Fin n) k, ∃ Φ ∈ SB (Matrix (Fin n) (Fin m) k),
    z = om 1 (1 : GL (Fin m) k) h Φ - (χ h : ℂ) • Φ}

def IsSub {m : ℕ} (χ : GL (Fin n) k →* ℂˣ) (N : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Prop :=
  aug m χ ≤ N ∧ N ≤ SB _ ∧ ∀ g : GL (Fin m) k, ∀ Φ ∈ N, om 1 g (1 : GL (Fin n) k) Φ ∈ N

variable {m : ℕ}

theorem om_add (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ + Ψ) = om μ g h Φ + om μ g h Ψ := by
  funext x; simp only [om, Pi.add_apply]; ring

theorem om_smul (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (c : ℂ) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x; simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_sub (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ - Ψ) = om μ g h Φ - om μ g h Ψ := by
  funext x; simp only [om, Pi.sub_apply]; ring

theorem om_comm (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g 1 (om μ 1 h Φ) = om μ 1 h (om μ g 1 Φ) := by
  simp only [← Model.om_mul, mul_one, one_mul]

theorem aug_le_SB (χ : GL (Fin n) k →* ℂˣ) : aug m χ ≤ SB (Matrix (Fin n) (Fin m) k) := by
  rw [aug, Submodule.span_le]
  rintro _ ⟨h, Φ, hΦ, rfl⟩
  exact Submodule.sub_mem _ (Model.om_mem_SB 1 1 h hΦ) (Submodule.smul_mem _ _ hΦ)

theorem isSub_aug (χ : GL (Fin n) k →* ℂˣ) : IsSub χ (aug m χ) := by
  refine ⟨le_rfl, aug_le_SB χ, fun g Φ hΦ => ?_⟩
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, Ψ, hΨ, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨h, om 1 g 1 Ψ, Model.om_mem_SB 1 g 1 hΨ, ?_⟩
    rw [om_sub, om_smul, om_comm]
  | zero =>
    rw [show om (1 : kˣ →* ℂˣ) g (1 : GL (Fin n) k) 0 = 0 from funext fun x => by simp [om]]
    exact (aug m χ).zero_mem
  | add x y _ _ hx hy => rw [om_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [om_smul]; exact Submodule.smul_mem _ c hx

theorem IsSub.sup {χ : GL (Fin n) k →* ℂˣ} {N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (h : IsSub χ N)
    (h' : IsSub χ N') : IsSub χ (N ⊔ N') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun g Φ hΦ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
  rw [om_add]
  exact Submodule.add_mem_sup (h.2.2 g y hy) (h'.2.2 g z hz)

end GlobalTheory.ThetaGLSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp

theorem substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2

theorem mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : MvPolynomial.coeff k' (substF h g (MvPolynomial.monomial k 1)) ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by
  have key : (substF h g).comp (substF h' g') = substF (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, substF_X, substF_X]
    simp only [map_sum, map_mul, substF_X, algHom_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomial
section
noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MetaplecticOneParameterSchwartzIntertwining
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory.RealWeil

theorem integral_norm_sq_eq_norm_toLp_sq {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem metaplectic_oneParam_schwartz : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this

end GlobalTheory.RealWeil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEq
section
namespace GlobalTheory

open Finset

theorem multilinear_sum_eq_of_prod_fun_eq
    {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l) :
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) =
        a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  classical
  intro h
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ V l) ∧
      ∀ u ∈ (a.support.image (fun c => (f c l : X l → ℂ)) ∪
        a.support.image (fun c => (g c l : X l → ℂ))), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule (V l) _ (by
      intro u hu
      simp only [Finset.mem_union, Finset.mem_image] at hu
      rcases hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (f c l).2
      · exact (g c l).2)
  choose s E hEV hE using hkey
  let e : ∀ l, X l → V l := fun l x => ⟨E l x, hEV l x⟩
  have expand : ∀ (u : ∀ l, V l),
      (∀ l, (u l : X l → ℂ) = ∑ x ∈ s l, (u l : X l → ℂ) x • E l x) →
      Φ u = ∑ ξ ∈ Fintype.piFinset s, (∏ l, (u l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro u hu
    have hu' : u = fun l => ∑ x ∈ s l, (u l : X l → ℂ) x • e l x := by
      funext l
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hu l
    conv_lhs => rw [hu', MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  have gen : ∀ f' : κ → ∀ l, V l,
      (∀ c ∈ a.support, ∀ l, (f' c l : X l → ℂ) = ∑ x ∈ s l, (f' c l : X l → ℂ) x • E l x) →
      (a.sum fun c b => b * Φ (f' c)) = ∑ ξ ∈ Fintype.piFinset s,
        (a.sum fun c b => b * ∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
    intro f' hf'
    calc (a.sum fun c b => b * Φ (f' c))
        = ∑ c ∈ a.support, a c * ∑ ξ ∈ Fintype.piFinset s,
            (∏ l, (f' c l : X l → ℂ) (ξ l)) * Φ (fun l => e l (ξ l)) := by
          unfold Finsupp.sum
          refine Finset.sum_congr rfl fun c hc => ?_
          show a c * Φ (f' c) = _
          rw [expand (f' c) (hf' c hc)]
      _ = _ := by
          simp only [Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun c _ => ?_
          ring
  rw [gen f (fun c hc l => hE l _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))),
    gen g (fun c hc l => hE l _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)))]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [h ξ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensor
section
open scoped InnerProductSpace

namespace GlobalTheory.DensityMultiPlace

theorem multilinear_translates_zero : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  intro ι _ H _ _ _ G _ π hu hs Sm hd hinv L C hL n c v hv φ u
  classical
  let w : Fin n → (∀ i, G i) → ∀ i, Sm i :=
    fun j g i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩
  have key : ∀ s : Finset ι, ∀ (g : ∀ i, G i) (u : ∀ i, Sm i),
      ∑ j, c j * (∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) * L (s.piecewise u (w j g)) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro g u
      simpa [w] using hv g
    · intro a s ha ih g u
      have hnorm : ∀ (m : ∀ i, Sm i) (x : Sm a),
          ∏ i, ‖((Function.update m a x) i : H i)‖
            = (∏ i ∈ Finset.univ.erase a, ‖(m i : H i)‖) * ‖x‖ := by
        intro m x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self,
          mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hbd : ∀ j (x : Sm a), ‖L.toLinearMap (s.piecewise u (w j g)) a x‖
          ≤ (C * ∏ i ∈ Finset.univ.erase a, ‖((s.piecewise u (w j g)) i : H i)‖) * ‖x‖ := by
        intro j x
        rw [MultilinearMap.toLinearMap_apply, mul_assoc, ← hnorm]
        exact hL _
      have hden : DenseRange (Sm a).subtypeL := (hd a).denseRange_val
      have hui : IsUniformInducing (Sm a).subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
      let Λ : Fin n → (H a →L[ℂ] ℂ) := fun j =>
        (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) •
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)).extend (Sm a).subtypeL
      have hΛ : ∀ j (x : Sm a), Λ j (x : H a) = (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) *
          L (Function.update (s.piecewise u (w j g)) a x) := by
        intro j x
        have := ContinuousLinearMap.extend_eq
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)) hden hui x
        simp only [Λ, ContinuousLinearMap.smul_apply, smul_eq_mul]
        erw [this]
        rw [LinearMap.mkContinuous_apply, MultilinearMap.toLinearMap_apply]
      have hupd : ∀ j (k : G a), s.piecewise u (w j (Function.update g a k))
          = Function.update (s.piecewise u (w j g)) a ⟨π a k (v j a), hinv a k _ (v j a).2⟩ := by
        intro j k
        funext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.piecewise_eq_of_notMem _ _ _ ha, w]
        · rw [Function.update_of_ne hia]
          by_cases his : i ∈ s
          · simp [Finset.piecewise_eq_of_mem _ _ _ his]
          · simp [Finset.piecewise_eq_of_notMem _ _ _ his, w, Function.update_of_ne hia]
      have hG : ∀ k : G a, ∑ j, Λ j (π a k (v j a)) = 0 := by
        intro k
        have h1 := ih (Function.update g a k) u
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (π a k (v j a) : H a) = ((⟨π a k (v j a), hinv a k _ (v j a).2⟩ : Sm a) : H a) from rfl,
          hΛ, hupd, mul_assoc]
      have h2 := GlobalTheory.T.irreducibleUnitary_vector_density (H a) (G a) (π a) (hu a) (hs a) n (fun j => (v j a : H a)) Λ hG
        (φ a) (u a)
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΛ, Finset.prod_insert ha, Finset.piecewise_insert]
      ring
  have h := key Finset.univ (fun _ => 1) u
  simp only [Finset.piecewise_univ] at h
  rw [Finset.sum_mul]
  rw [← h]

end GlobalTheory.DensityMultiPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

theorem nabs_le_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) :
    nabs k x ≤ nabs k y := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have hx := measureReal_cball ν x
  have hy := measureReal_cball ν y
  have h2 : ν.real (𝒪[k] : Set k) = 1 := by rw [Measure.real, h1]; simp
  rw [h2, mul_one] at hx hy
  rw [← hx, ← hy]
  have h3 : cball x ⊆ cball y := fun z hz => le_trans (show valuation k z ≤ _ from hz) h
  exact measureReal_mono h3 (isCompact_cball y).measure_lt_top.ne

theorem nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k

theorem nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩

theorem nabs_eq_iff (x y : kˣ) : nabs k x = nabs k y ↔ valuation k (x : k) = valuation k (y : k) := by
  rw [le_antisymm_iff, le_antisymm_iff, nabs_le_iff, nabs_le_iff]

theorem nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by
  rw [← nabs_one k, nabs_eq_iff, Units.val_one, map_one]

variable (k) in
theorem isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

theorem nabs_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x y : kˣ, nabs k (x * y) = nabs k x * nabs k y) ∧ (∀ x : kˣ, 0 < nabs k x) ∧ (∀ x y : kˣ, nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k)) ∧ (∀ x : kˣ, nabs k x = 1 ↔ valuation k (x : k) = 1) ∧ (∀ (ϖ : 𝒪[k]) (x : kˣ), Irreducible ϖ → (x : k) = (ϖ : k) → nabs k x = (resCard k : ℝ)⁻¹) ∧ IsLocallyConstant (nabs k) ∧ 1 < resCard k :=
  fun k _ _ _ _ => ⟨nabs_mul k, nabs_pos k, nabs_le_iff, nabs_eq_one_iff,
    fun _ _ h h' => nabs_uniformiser h h', isLocallyConstant_nabs k, one_lt_resCard k⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorStable_piTensorPureKernelSpan : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.TensHead.stab_piOps_piKer | exact GlobalTheory.TensHead.stab_piOps_piKer | (intros; apply GlobalTheory.TensHead.stab_piOps_piKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountableStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_tensor_product_operatorStable_countable : ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.simple_tensor | exact GlobalTheory.TensHead.simple_tensor | (intros; apply GlobalTheory.TensHead.simple_tensor <;> assumption)
end

