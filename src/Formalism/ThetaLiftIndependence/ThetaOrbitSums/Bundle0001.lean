import Formalism.ThetaLiftIndependence.Statement

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
section
namespace Formalism.ThetaLiftIndependence

namespace ChainScalarLemmas

variable {𝕜 : Type} [RCLike 𝕜] {E : ℕ → Type} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]

theorem adjoint_downChain_succ_apply (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (m : ℕ) (x : E 0) :
    LinearMap.adjoint (downChain T (m + 1)) x =
      LinearMap.adjoint (T m) (LinearMap.adjoint (downChain T m) x) := by
  show LinearMap.adjoint ((downChain T m).comp (T m)) x = _
  rw [LinearMap.adjoint_comp]
  rfl

theorem mem (T : ∀ j, E (j + 1) →ₗ[𝕜] E j) (S : ∀ j, Submodule 𝕜 (E j))
    (hS : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (T j) x ∈ S (j + 1)) :
    ∀ (m : ℕ), ∀ x ∈ S 0, LinearMap.adjoint (downChain T m) x ∈ S m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    show LinearMap.adjoint (LinearMap.id : E 0 →ₗ[𝕜] E 0) x ∈ S 0
    rw [LinearMap.adjoint_id]
    exact hx
  | succ m ih =>
    intro x hx
    rw [adjoint_downChain_succ_apply]
    exact hS m _ (ih x hx)

end ChainScalarLemmas

end Formalism.ThetaLiftIndependence
end

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
section
namespace Formalism.ThetaLiftIndependence

namespace DeterminantSwapLemmas

variable {𝕜 E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

lemma mem_orth_ker_adjoint (T : E →ₗ[𝕜] F) (x : E) :
    T x ∈ (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← LinearMap.adjoint_inner_left, LinearMap.mem_ker.mp hu, inner_zero_left]

noncomputable def restr (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ →ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
  (T.comp (LinearMap.ker T)ᗮ.subtype).codRestrict _ (fun x => mem_orth_ker_adjoint T x)

lemma restr_apply (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((restr T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := rfl

lemma restr_injective (T : E →ₗ[𝕜] F) : Function.Injective (restr T) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h0 : T x = 0 := by
    have := congrArg (fun y : (LinearMap.ker (LinearMap.adjoint T))ᗮ => (y : F)) hx
    simpa [restr_apply] using this
  have hk : (x : E) ∈ LinearMap.ker T := h0
  have hmem : (x : E) ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨hk, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

lemma finrank_orth_ker (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.ker T)ᗮ = Module.finrank 𝕜 (LinearMap.range T) := by
  have h1 := (LinearMap.ker T).finrank_add_finrank_orthogonal
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  omega

lemma finrank_eq (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.ker T)ᗮ =
      Module.finrank 𝕜 (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
  rw [finrank_orth_ker, finrank_orth_ker, LinearMap.finrank_range_adjoint]

noncomputable def equiv (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ ≃ₗ[𝕜] (LinearMap.ker (LinearMap.adjoint T))ᗮ :=
  LinearEquiv.ofBijective (restr T)
    ⟨restr_injective T,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_eq T)).mp
        (restr_injective T)⟩

lemma equiv_apply (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((equiv T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := rfl

end DeterminantSwapLemmas

end Formalism.ThetaLiftIndependence
end

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap
section
namespace Formalism.ThetaLiftIndependence

namespace EigenvalueSwapLemmas

theorem eig_le {𝕜 E F : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (B ∘ₗ A) μ) ≤
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘ₗ B) μ) := by
  have h : ∀ x ∈ Module.End.eigenspace (B ∘ₗ A) μ, A x ∈ Module.End.eigenspace (A ∘ₗ B) μ := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    simp only [LinearMap.comp_apply] at hx ⊢
    rw [hx, map_smul]
  refine LinearMap.finrank_le_finrank_of_injective (f := A.restrict h) ?_
  intro x y hxy
  have hx := (Module.End.mem_eigenspace_iff.1 x.2)
  have hy := (Module.End.mem_eigenspace_iff.1 y.2)
  have hA : A x = A y := congrArg Subtype.val hxy
  apply Subtype.ext
  have : μ • (x : E) = μ • (y : E) := by
    rw [← hx, ← hy]; simp [hA]
  exact smul_right_injective E hμ this

end EigenvalueSwapLemmas
end Formalism.ThetaLiftIndependence
end

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel
section
namespace Formalism.ThetaLiftIndependence

namespace FiniteFieldPlancherel

open Classical

theorem charSum {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (g : Module.Dual 𝔽 U) :
    ∑ e : U, ψ (g e) = if g = 0 then (Fintype.card U : ℂ) else 0 := by
  by_cases hg : g = 0
  · subst hg; simp
  · rw [if_neg hg]
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra h
      push Not at h
      apply hψ
      ext a
      simp [h a]
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by simp [h x])
    set e0 : U := (a / g x) • x with he0
    have hge0 : g e0 = a := by
      rw [he0, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
    have hshift : ∑ e : U, ψ (g e) = (∑ e : U, ψ (g e)) * ψ a := by
      calc ∑ e : U, ψ (g e) = ∑ e : U, ψ (g (e + e0)) :=
            (Fintype.sum_equiv (Equiv.addRight e0) _ _ (fun _ => rfl)).symm
        _ = (∑ e : U, ψ (g e)) * ψ a := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [map_add, AddChar.map_add_eq_mul, hge0]
    have h1 : (∑ e : U, ψ (g e)) * (ψ a - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) ha

theorem orth {𝔽 U : Type} [Field 𝔽] [AddCommGroup U] [Module 𝔽 U] [Fintype U]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) [Fintype 𝔽] (f g : Module.Dual 𝔽 U) :
    ∑ e : U, star (ψ (f e)) * ψ (g e) = if f = g then (Fintype.card U : ℂ) else 0 := by
  have h : ∀ e, star (ψ (f e)) * ψ (g e) = ψ ((g - f) e) := by
    intro e
    rw [LinearMap.sub_apply, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      Complex.star_def, mul_comm]
  simp_rw [h]
  rw [charSum ψ hψ]
  by_cases hfg : f = g
  · simp [hfg]
  · rw [if_neg hfg, if_neg (fun h' => hfg (sub_eq_zero.mp h').symm)]

end FiniteFieldPlancherel
end Formalism.ThetaLiftIndependence
end

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.GaussOp
section
open scoped BigOperators

namespace Formalism.ThetaLiftIndependence

namespace GaussOperatorLemmas

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

theorem sum_units_eq_sub {M : Type*} [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)

theorem sum_units_char (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])

theorem core (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp

end GaussOperatorLemmas

open GaussOperatorLemmas in
theorem gaussOp_eq : GaussOp := by
  intro 𝔽 V _ _ _ _ _ ψ ρ hψ v hv
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) •
        ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) *
        ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv

end Formalism.ThetaLiftIndependence
end

-- bundled from Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
section
namespace Formalism.ThetaLiftIndependence

open MulAction in
theorem orbitSum : OrbitSum := by
  classical
  intro H X _ _ _ _ k _ _ F hF
  rw [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_equiv (selfEquivSigmaOrbits H X).symm (fun p => F p.2) F (fun p => rfl),
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hconst : ∀ y : orbit H (Quotient.out o), F y = F (Quotient.out o) := by
    rintro ⟨y, a, rfl⟩
    exact hF a _
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard := card_orbit_mul_card_stabilizer_eq_card_group H (Quotient.out o)
  rw [Nat.card_eq_fintype_card, ← hcard]
  have h1 : (Fintype.card (orbit H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟨_, mem_orbit_self (Quotient.out o)⟩⟩ :
      0 < Fintype.card (orbit H (Quotient.out o))).ne'
  have h2 : (Fintype.card (stabilizer H (Quotient.out o)) : k) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := stabilizer H (Quotient.out o))).ne'
  push_cast
  field_simp

end Formalism.ThetaLiftIndependence
end

