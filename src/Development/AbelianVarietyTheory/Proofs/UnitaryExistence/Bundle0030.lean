import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Half

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_add_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x + x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x' y :=
  _root_.GlobalTheory.AdLat.hermA_add_left c G x x' y

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_add_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y + y') =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x y' := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x - x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x' y := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.hermA_add_left, _root_.GlobalTheory.AdLat.hermA_neg_left,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_neg_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (-y) = -_root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y - y') =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x y' := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.Half.herm_add_right, _root_.GlobalTheory.AdLat.Half.herm_neg_right,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (r • x) y = r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (r • y) =
      _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : Set E) (L : Set (Fin n → E)) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ y ∈ L, _root_.GlobalTheory.AdLat.hermA c G z (_root_.GlobalTheory.AdLat.fv F y) ∈
      _root_.GlobalTheory.AdLat.hat1 F J)
    (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F J := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hw
    have hw' : (fun i => a ⊗ₜ[F] y i) =
        (a ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • _root_.GlobalTheory.AdLat.fv F y := by
      funext i
      simp [_root_.GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hw', _root_.GlobalTheory.AdLat.Half.herm_smul_right]
    have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] (1 : E)) =
        a ⊗ₜ[F] (1 : E) := by
      simp [_root_.GlobalTheory.AdLat.sg]
    rw [hsg]
    refine _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun x hx y hy => ?_)
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F ha rfl) (hz y hy)
    rw [Set.mem_singleton_iff.1 hx, one_mul]
    exact hy
  | zero =>
    have h0 : _root_.GlobalTheory.AdLat.hermA c G z 0 = 0 := by
      simp [_root_.GlobalTheory.AdLat.hermA]
    rw [h0]
    exact zero_mem _
  | add w w' _ _ hw hw' =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_add_right]
    exact add_mem hw hw'
  | neg w _ hw =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_neg_right]
    exact neg_mem hw

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ L) : _root_.GlobalTheory.AdLat.fv F y ∈ _root_.GlobalTheory.AdLat.hat F L :=
  AddSubgroup.subset_closure ⟨1, _root_.GlobalTheory.AdLat.adele_one_integral F, y, hy, rfl⟩

end GlobalTheory.AdLat.Half

namespace GlobalTheory.AdLat

open Half

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.trivial_level_of_half : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E)
    (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (M : ℕ) (I I' : Ideal (𝓞 E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) →
    G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) →
    (∀ x y, _root_.GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ y) = _root_.GlobalTheory.AdLat.hermA c G x y) →
    0 < M → I ⊔ I' = ⊤ → I * I' = Ideal.span {(M : 𝓞 E)} →
    (∀ b ∈ I', ∃ b' ∈ I, ((b' : 𝓞 E) : E) = c (b : E)) →
    (∀ b ∈ I, ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) -
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) = M • y) →
    ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ z - z = M • y := by
  intro F E _ _ _ _ _ n L c G J g M I I' hFG hspan hc hG hdet hJ hdual hg hM hsup hprod hcI hhalf
  set Lh := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hLh
  generalize (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) = gm at hg hhalf ⊢
  let e : 𝓞 E → _root_.GlobalTheory.AdLat.RA F E :=
    fun b => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)
  have hh : ∀ b ∈ I, ∀ z ∈ Lh, ∃ y ∈ Lh, gm *ᵥ (e b • z) - e b • z = M • y := hhalf
  have hu : ∀ (r : _root_.GlobalTheory.AdLat.RA F E) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      gm *ᵥ (r • z) - r • z = r • (gm *ᵥ z - z) := fun r z => by
    rw [Matrix.mulVec_smul, smul_sub]
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hnat : ∀ (m : ℕ) (v : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      m • v = (algebraMap F (_root_.GlobalTheory.AdLat.RA F E) m) • v := fun m v => by
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hMcancel : ∀ x y : Fin n → _root_.GlobalTheory.AdLat.RA F E, M • x = M • y → x = y := by
    intro x y hxy
    rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at hxy
    exact smul_right_injective _ hM0 hxy
  have heM : e (M : 𝓞 E) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M := by
    simp only [e, map_natCast]
    push_cast
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hMI : (M : 𝓞 E) ∈ I := by
    have h1 : (M : 𝓞 E) ∈ Ideal.span {(M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← hprod] at h1
    have h2 : I * I' ≤ I := Ideal.mul_le_left
    exact h2 h1

  have hstab : ∀ z ∈ Lh, gm *ᵥ z - z ∈ Lh := fun z hz => by
    obtain ⟨y, hy, hyz⟩ := hh _ hMI z hz
    rw [hu, heM, ← hnat] at hyz
    rw [hMcancel _ _ hyz]
    exact hy
  have hgL : ∀ z ∈ Lh, gm *ᵥ z ∈ Lh := fun z hz => by
    rw [← sub_add_cancel (gm *ᵥ z) z]
    exact add_mem (hstab z hz) hz
  have hpair : ∀ z ∈ Lh, ∀ w ∈ Lh,
      _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F (J : Set E) :=
    fun z hz w hw => _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv c G J L z
      ((_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual z).2
        hz) w hw
  intro z hz
  obtain ⟨i, hi, i', hi', hii'⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ I')
  obtain ⟨b, hb, hbc⟩ := hcI i' hi'
  have he1 : e i + e i' = 1 := by
    have h1 : (i : E) + (i' : E) = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hii'
    simp only [e, ← TensorProduct.tmul_add]
    rw [h1]
    rfl
  set w := gm *ᵥ z - z with hw
  obtain ⟨y₁, hy₁, hwy₁⟩ := hh i hi z hz
  rw [hu] at hwy₁
  set v : Fin n → _root_.GlobalTheory.AdLat.RA F E := ((M : F)⁻¹) • (e i' • w) with hv
  have hMv : M • v = e i' • w := by
    rw [hv, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hM0, one_smul]
  have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (e b) = e i' := by
    simp only [e, _root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgEquiv.coe_algHom, hbc, hc]
  have hvL : v ∈ Lh := by
    refine (_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual v).1
      fun y hy => ?_
    set Y := _root_.GlobalTheory.AdLat.fv F y
    have hY : Y ∈ Lh := _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) y hy
    obtain ⟨y₂, hy₂, hY₂⟩ := hh b hb Y hY
    rw [hu] at hY₂
    have key : _root_.GlobalTheory.AdLat.hermA c G w Y =
        -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) := by
      rw [hw, _root_.GlobalTheory.AdLat.Half.herm_sub_left, _root_.GlobalTheory.AdLat.Half.herm_sub_right, ← hg z Y]
      ring
    have h2 : e i' * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) =
        algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [← hsg, ← _root_.GlobalTheory.AdLat.Half.herm_smul_right, hY₂, hnat,
        _root_.GlobalTheory.AdLat.Half.herm_smul_right, AlgHom.commutes]
    have h3 : _root_.GlobalTheory.AdLat.hermA c G v Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [hv, algebra_compatible_smul (_root_.GlobalTheory.AdLat.RA F E),
        _root_.GlobalTheory.AdLat.Half.herm_smul_left, _root_.GlobalTheory.AdLat.Half.herm_smul_left, key, mul_neg,
        h2, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM0, map_one, one_mul]
    rw [h3]
    exact neg_mem (hpair _ (hgL z hz) y₂ hy₂)
  refine ⟨y₁ + v, add_mem hy₁ hvL, ?_⟩
  calc w = e i • w + e i' • w := by rw [← add_smul, he1, one_smul]
    _ = M • (y₁ + v) := by rw [hwy₁, ← hMv, smul_add]

end GlobalTheory.AdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpChain

theorem isDerivAt0_comp_linear {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem isHolTo_slice {g m : ℕ} {X : Scheme.{0}} (e : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo (Set.univ ×ˢ Set.univ) e) : IsHolTo Set.univ (fun z => e (0, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin m → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

theorem isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_slice _ h
  simp only at h2
  exact h2

theorem isDerivAt0_ex_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (k' : Fin F.n) (P' : (F.Di k').La →+ (Fin g → ℂ)) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsPeriod (F.Di k') ty P' → (∀ z, (F.ex k' P' (L z)).left = (F.ex k P z).left) → ∀ w (v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsDerivAt0 (fun z => (F.ex k P z).left) w v ↔ IsDerivAt0 (fun z => (F.ex k' P' z).left) (L w) v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P _ k' P' L hP' hL w v
  rw [← isDerivAt0_comp_linear _ (isHolTo_ex F k' P' hP') L w v]
  simp only [hL]

end GlobalTheory.ExpChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.DerivEig

open GlobalTheory.HolHom

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem fst_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.fst (epsMul s x) = x.fst := by
  simp [epsMul]

theorem snd_epsMul (s : ℂ) (x : DualNumber ℂ) : TrivSqZeroExt.snd (epsMul s x) = s * x.snd := by
  simp [epsMul]

theorem isDerivAt_epsMul {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt c z w v)
    (s : ℂ) : HolHom.IsDerivAt c z (s • w) (spMap (epsMul s) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← h.1]
    congr 2
    ext1
    exact RingHom.ext fun x => fst_epsMul s x
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), snd_epsMul, h.2 U hU, map_smul, smul_eq_mul]

theorem isDerivAt_of_comp_linear {c : V → (Sp ℂ ⟶ X)} (hc : HolAt c 0) (L : V →L[ℂ] V) {w : V}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : HolHom.IsDerivAt (fun t => c (L t)) 0 w v) : HolHom.IsDerivAt c 0 (L w) v := by
  have h0 : c (L 0) = c 0 := by rw [map_zero]
  refine ⟨h.1.trans h0, fun U hU f => ?_⟩
  rw [h.2 U (by beta_reduce; rw [h0]; exact hU) f]
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((hc U hU).2 f).hasFDerivAt
  exact congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv

end General

theorem eq_of_relab_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) {τ τ' : E →+* ℂ}
    (h : ∀ a : 𝓞 E, relab c σ τ (a : E) = relab c σ τ' (a : E)) : τ = τ' := by
  refine IsLocalization.ringHom_ext (𝓞 E)⁰ (RingHom.ext fun a => ?_)
  exact congrArg Subtype.val (σ.injective (h a))

end GlobalTheory.DerivEig

open GlobalTheory.HolHom GlobalTheory.DerivEig in

theorem GlobalTheory.isEigAt_iff_of_isDerivAt0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∀ (w : Fin g → ℂ) (v : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)) (τ : E →+* ℂ), IsDerivAt0 (fun z => (F.ex k P z).left) w v → (IsEigAt c τ v ↔ ∀ j, w j ≠ 0 → (e j).1 = τ) := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP w v τ hv
  have hhol : HolAt (fun z => (F.ex k P z).left) 0 := holAt_of_isHolTo (isHolTo_ex F k hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  have hact : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (fun j => relab c σ (e j).1 (a : E) * w j) (v ≫ (Xo.univ.t.act.act a).left) := by
    intro a
    let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
      ContinuousLinearMap.pi fun j => relab c σ (e j).1 (a : E) • ContinuousLinearMap.proj j
    have h1 := hv'.comp (Xo.univ.t.act.act a).left
    have h2 : (fun t => (F.ex k P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (F.ex k P (L t)).left := by
      funext t
      rw [← Over.comp_left, ← F.ex_lin k P hP a t]
      rfl
    rw [h2] at h1
    exact isDerivAt_of_comp_linear hhol L h1
  have hsc : ∀ a : 𝓞 E, HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0
      (relab c σ τ (a : E) • w) (spMap (epsMul (algebraMap c.F (CAt σ) (embK c τ a))) ≫ v) :=
    fun a => isDerivAt_epsMul hv' _
  constructor
  · intro h j hj
    refine eq_of_relab_eq c σ fun a => ?_
    have h1 := hact a
    have h2 : HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)
        (v ≫ (Xo.univ.t.act.act a).left) :=
      Eq.mpr (congrArg (HolHom.IsDerivAt (fun z => (F.ex k P z).left) 0 (relab c σ τ (a : E) • w)) (h a)) (hsc a)
    have h3 := eq_of_forall_fderiv_eq hhol (F.ex_diff k P hP).2 fun U hU f =>
      (h1.2 U hU f).symm.trans (h2.2 U hU f)
    exact mul_right_cancel₀ hj (congrFun h3 j)
  · intro h a
    have h1 := hact a
    have h3 : (fun j => relab c σ (e j).1 (a : E) * w j) = relab c σ τ (a : E) • w := by
      funext j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
    rw [h3] at h1
    exact h1.unique (hsc a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem isIntegral_rat_zeta_of_coeff (n : ℕ) : IsIntegral ℚ (zeta n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : zeta 0 = 1 := by simp [zeta]
    rw [this]; exact isIntegral_one
  · have h := Complex.isPrimitiveRoot_exp n hn.ne'
    exact (h.isIntegral hn).tower_top

theorem exists_coeff_containing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (s : Finset ℂ), (∀ z ∈ s, IsAlgebraic ℚ z) → ∃ c : Coeff l, ∀ z ∈ s, z ∈ c.F := by
  intro E _ _ _ H l s hs
  classical
  let b := Module.finBasis ℚ E
  let S : Set ℂ := (s : Set ℂ) ∪ Set.range (fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2)) ∪
    {zeta l.M', H.rt0, zeta l.A}
  have hfin : S.Finite := ((s.finite_toSet).union (Set.finite_range _)).union (Set.toFinite _)
  haveI : Finite S := hfin.to_subtype
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ((hx | ⟨p, rfl⟩) | hx)
    · exact (hs x hx).isIntegral
    · exact (Algebra.IsIntegral.isIntegral (R := ℚ) (b p.2)).map p.1.toRatAlgHom
    · rcases hx with rfl | rfl | rfl
      · exact isIntegral_rat_zeta_of_coeff _
      · refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
        rw [H.sqrt_neg_disc_sq]
        exact (isIntegral_natCast _).neg
      · exact isIntegral_rat_zeta_of_coeff _
  have hsub : S ⊆ IntermediateField.adjoin ℚ S := IntermediateField.subset_adjoin _ _
  refine ⟨⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint, ?_, ?_, ?_⟩, ?_⟩
  · intro τ a
    rw [← b.sum_repr a, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (hsub (Or.inl (Or.inr ⟨(τ, i), rfl⟩)))
  · exact hsub (Or.inr (by simp))
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    intro x hx
    exact Or.inr (Or.inr hx)
  · intro z hz
    exact hsub (Or.inl (Or.inl hz))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelGroupFiniteIndexUnitaryStabiliser
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem princ_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ _
  haveI := Di.fin
  have hΛ : (LinearMap.range φ0).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map φ0 Module.Finite.fg_top
  have hM : 0 < l.M * l.A := Nat.mul_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨S, hS⟩ := GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM
  refine ⟨S, fun γ hγ => ?_⟩
  obtain ⟨s, hs, hst, hc⟩ := hS γ hγ
  refine ⟨s, hs, hst, fun a _ => ?_, fun a => ?_⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.A • b, by rw [e, map_nsmul, mul_smul]⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.M • b, by rw [e, map_nsmul, mul_comm, mul_smul]⟩

end GlobalTheory.FrameUnif
end

