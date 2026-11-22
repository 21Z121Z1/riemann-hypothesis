import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def BernsteinUnitaryProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ →
    IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible

namespace BernsteinUnitaryProductIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem ind₂_stdSum (H : BernsteinUnitaryProductIrreducible) {r t N : ℕ} (h : r + t = N)
    {π₁ : Representation ℂ (GL (Fin r) k) V} {π₂ : Representation ℂ (GL (Fin t) k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible := by
  subst h
  exact H k r t V W π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂

theorem detRep_hyp (t : ℕ) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin t) χ) ∧ (detRep (Fin t) χ).IsIrreducible ∧
      IsUnitarisable (detRep (Fin t) χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hs.detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩

theorem prod₂_detRep (H : BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  have h := detRep_hyp t hs hu
  H k r t V ℂ π _ s i u h.1 h.2.1 h.2.2

end BernsteinUnitaryProductIrreducible

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def BorelCasselman : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsAdmissible π → Function.Bijective (iwahoriProj π)

example (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsAdmissible (detRep n χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, fun _ _ _ => inferInstance⟩

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory

namespace SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IrreducibleAdmissible : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π

def JacquetFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsSmooth π → HasFiniteLength π → HasFiniteLength (jac e π)

def InductionFiniteLength : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd e ρ)

def InductionContragredient : Prop :=
  ∀ (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    IsSmooth ρ → ∃ Φ : (parInd e (contra ρ)).Equiv (contra (parInd e ρ)),
      ∀ (f' : IndSp e (contra ρ)) (f : IndSp e ρ),
        (Φ f' : Module.Dual ℂ (IndSp e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ

end SmGL

namespace Published

def BernsteinZelevinskyFiniteness : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    IrreducibleAdmissible k ∧ JacquetFiniteLength k ∧ InductionFiniteLength k ∧
      InductionContragredient k

end Published

namespace SmGL

section Transport

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]

theorem hasFiniteLength_iff_wellFounded (ρ : Representation F G V) :
    HasFiniteLength ρ ↔
      WellFoundedGT (Subrepresentation ρ) ∧ WellFoundedLT (Subrepresentation ρ) := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff', isArtinian_iff]
  refine and_congr ⟨fun _ => φ.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.symm.toOrderEmbedding.wellFoundedGT⟩ ⟨fun h => ?_, fun _ => ?_⟩
  · haveI : WellFoundedLT (Submodule (MonoidAlgebra F G) ρ.asModule) := ⟨h⟩
    exact φ.toOrderEmbedding.wellFoundedLT
  · exact φ.symm.toOrderEmbedding.wellFoundedLT.wf

theorem hasFiniteLength_comp_iff (ρ : Representation F G V) (s : H →* G) (hs : Function.Surjective s) :
    HasFiniteLength (ρ.comp s : Representation F H V) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (ρ.comp s : Representation F H V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨h, rfl⟩ := hs g
        exact S.apply_mem_toSubmodule h hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (s h) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_isIrreducible {ρ : Representation F G V} (h : ρ.IsIrreducible) :
    HasFiniteLength ρ := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  haveI : Finite (Subrepresentation ρ) := IsSimpleOrder.instFinite
  exact (hasFiniteLength_iff_wellFounded ρ).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isLocallyConstant_smInd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P : Subgroup G} {σ : Representation ℂ P W} (f : smoothPart (ind P σ)) :
    IsLocallyConstant (f.1.1 : G → W) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : {g : G | ind P σ g f.1 = f.1} ∈ nhds ((fun y => x⁻¹ * y) x) :=
    IsOpen.mem_nhds f.2 (by simp)
  filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
  have hy' : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
  rwa [mul_inv_cancel_left] at hy'

theorem InductionContragredient.nonempty_equiv (h : InductionContragredient k) (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) :
    Nonempty ((parInd e (contra ρ)).Equiv (contra (parInd e ρ))) := by
  haveI : LocallyCompactSpace (GL n k) := SplitFlip.locallyCompact_GL
  borelize (GL n k)
  obtain ⟨Φ, -⟩ := h _ _ _ e Measure.haar W ρ hρ
  exact ⟨Φ⟩

theorem JacquetFiniteLength.lower (h : JacquetFiniteLength k) (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    HasFiniteLength (jacLower e π) := by
  have : jacLower e π = jac (opp e) π := MonoidHom.ext (jacLower_eq e π)
  rw [this]
  exact h _ _ _ (opp e) V π hπ hl

theorem InductionFiniteLength.lower (h : InductionFiniteLength k) (e : (Σ a, m a) ≃ n)
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) :
    HasFiniteLength (parIndLower e ρ) := by
  have key : ∀ χ : Levi k m →* ℂˣ, deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) = χ →
      HasFiniteLength (smInd (parabLower k e) ((twist ρ χ).comp (leviProjLower k e))) := by
    rintro _ rfl
    exact h _ _ _ (opp e) W ρ hρ hl
  exact key _ (MonoidHom.ext fun g => deltaHalf_opp (m := m) g)

theorem InductionContragredient.lower (h : InductionContragredient k) (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) :
    ∃ Φ : (parIndLower e (contra ρ)).Equiv (contra (parIndLower e ρ)),
      ∀ (f' : IndSpLower e (contra ρ)) (f : IndSpLower e ρ),
        (Φ f' : Module.Dual ℂ (IndSpLower e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ := by
  have key : ∀ χ : Levi k m →* ℂˣ, deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) = χ →
      ∃ Φ : (smInd (parabLower k e) ((twist (contra ρ) χ).comp (leviProjLower k e))).Equiv
          (contra (smInd (parabLower k e) ((twist ρ χ).comp (leviProjLower k e)))),
        ∀ f' f, (Φ f').1 f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ := by
    rintro _ rfl
    exact h _ _ _ (opp e) μ W ρ hρ
  exact key _ (MonoidHom.ext fun g => deltaHalf_opp (m := m) g)

section Two

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem JacquetFiniteLength.two (h : JacquetFiniteLength k) (e : a ⊕ b ≃ n)
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    HasFiniteLength (jac₂ e π) :=
  (hasFiniteLength_comp_iff _ _ (leviTwo k a b).surjective).2 (h _ _ _ (SmGL.two e) V π hπ hl)

end Two

example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmooth (detRep n χ) ∧ (detRep n χ).IsIrreducible ∧ HasFiniteLength (detRep n χ) ∧
      IsAdmissible (detRep n χ) :=
  have h := (isSmooth_ofChar_iff _).2 (hχ.detChar (n := n))
  ⟨h, isIrreducible_ofChar _, hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _), h,
    fun _ _ _ => inferInstance⟩

example : IsSmooth (ofChar (deltaHalf k m)) ∧ HasFiniteLength (ofChar (deltaHalf k m)) :=
  ⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_deltaHalf k),
    hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)⟩

end SmGL

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolPartShear
section
noncomputable section

open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.Published.Metaplectic.Model

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem shear_mem (C : Matrix ι ι ℝ) (hC : Cᵀ = C) : fromBlocks 1 0 C 1 ∈ symplecticGroup ι ℝ := by
  rw [SymplecticGroup.mem_iff]
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hC]

def chirp (C : Matrix ι ι ℝ) (f : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => cexp (-π * I * ((x ⬝ᵥ C *ᵥ x : ℝ) : ℂ)) * f x

theorem chirp_rho (C : Matrix ι ι ℝ) (hC : Cᵀ = C) (p q : ι → ℝ) (φ ψ : 𝓢(ι → ℝ, ℂ)) (h : ⇑ψ = chirp C φ) :
    chirp C (rho (p, q) φ) = rho (act (fromBlocks 1 0 C 1) (p, q)) ψ := by
  funext x
  have hs : p ⬝ᵥ C *ᵥ x = x ⬝ᵥ C *ᵥ p := by
    rw [dotProduct_mulVec, ← hC, vecMul_transpose, hC, dotProduct_comm]
  rw [act_fromBlocks, rho_apply, h]
  simp only [chirp, rho_apply, one_mulVec, zero_mulVec, add_zero, mulVec_add, dotProduct_add, add_dotProduct, hs]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit [Fintype ι] in
theorem holPart_shear (C : Matrix ι ι ℝ) (i : ι) : holPart (fromBlocks 1 0 C 1) i i = (2 + I * C i i) / 2 := by
  simp [holPart]; norm_num

theorem shear_coeff (c : ℝ) :
    (∫ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 * ((2 + I * c) / 2) =
      (∫ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 := by
  have hc : ∀ x : ℝ, conj (cexp (-π * x ^ 2)) = cexp (-π * x ^ 2) := by
    intro x; rw [← Complex.exp_conj]; simp
  have e1 : ∀ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) =
      cexp (-(π * (2 + I * c)) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e2 : ∀ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) = cexp (-(π * 2) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add]; congr 1; ring
  simp_rw [e1, e2]
  have hp := Real.pi_pos
  rw [integral_gaussian_complex (by simp; positivity), integral_gaussian_complex (by simp; positivity)]
  have h2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    have := Complex.cpow_nat_inv_pow z (n := 2) two_ne_zero
    simpa using this
  rw [h2, h2]
  have h3 : (2 + I * c : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h4 : (π : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

def sgnRep (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousConstSMul ℂ E] :
    ℤˣ →* (E →L[ℂ] E) where
  toFun g := (((g : ℤ) : ℂ)) • (1 : E →L[ℂ] E)
  map_one' := by simp
  map_mul' g h := by ext; simp [smul_smul, mul_comm]

theorem empty_case (ι : Type) [Fintype ι] [DecidableEq ι] [IsEmpty ι] :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀) := by
  have hs : Subsingleton (symplecticGroup ι ℝ) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hsq : ∀ g : ℤˣ, (((g : ℤ) : ℂ)) ^ 2 = 1 := by
    intro g; rcases Int.units_eq_one_or g with rfl | rfl <;> simp
  let φ₀ : 𝓢(ι → ℝ, ℂ) := (HasCompactSupport.of_compactSpace (fun _ : ι → ℝ => (1 : ℂ))).toSchwartzMap contDiff_const
  refine ⟨ℤˣ, inferInstance, inferInstance, inferInstance, 1, sgnRep _, sgnRep _, φ₀, fun a => ⟨1, Subsingleton.elim _ _⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨inferInstance, Set.univ, trivial, isOpen_univ, isOpen_discrete _, ?_⟩
    have : Finite ((1 : ℤˣ →* symplecticGroup ι ℝ) ⁻¹' {x}) := inferInstance
    refine ⟨Equiv.toHomeomorphOfDiscrete
      { toFun := fun g => (⟨x, trivial⟩, ⟨g.1, Subsingleton.elim _ _⟩)
        invFun := fun y => ⟨y.2.1, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun y => Prod.ext (Subtype.ext (Subsingleton.elim _ _)) rfl }, fun _ => Subsingleton.elim _ _⟩
  · simp
  · intro g f
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep]
  · intro f; exact continuous_of_discreteTopology
  · intro g φ
    change ((g : ℤ) : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume φ = SchwartzMap.toLpCLM ℂ ℂ 2 volume (((g : ℤ) : ℂ) • φ)
    rw [map_smul]
  · change Continuous fun x : ℤˣ × 𝓢(ι → ℝ, ℂ) => (((x.1 : ℤ) : ℂ)) • x.2
    exact ((continuous_of_discreteTopology (f := fun g : ℤˣ => ((g : ℤ) : ℂ))).comp continuous_fst).smul continuous_snd
  · intro g w φ
    rw [Subsingleton.elim (act _ w) w]
    simp [sgnRep]
  · intro g _ hg φ
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact absurd rfl hg
    · simp [sgnRep]
  · intro x; simp [φ₀, dotProduct]
  · intro g
    rcases Int.units_eq_one_or g with rfl | rfl <;> simp [sgnRep, integral_neg]
  · intro g _
    exact ⟨_, by simp [hsq g], rfl⟩

end GlobalTheory.Published.Metaplectic.Model

end
end

