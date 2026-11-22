import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeftStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tensorProduct_map_id_right : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  first | exact @GlobalTheory.norm_tensorProduct_map_left | exact GlobalTheory.norm_tensorProduct_map_left | (intros; apply GlobalTheory.norm_tensorProduct_map_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.SqrtNegRam

theorem not_isUnramifiedAt_of_sq_eq_neg :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (p : ℕ), p.Prime →
      ¬ (p : ℤ) ∣ discr E → ∀ δ : K, δ ^ 2 = -(p : K) → ∀ w : HeightOneSpectrum (𝓞 K),
        (p : 𝓞 K) ∈ w.asIdeal → ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  intro E K _ _ _ _ _ p hp hd δ hδ w hpw hunr
  have hmax := w.isMaximal
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hv : Algebra.IsUnramifiedAt ℤ (w.asIdeal.under (𝓞 E)) := by
    refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd _ inferInstance ?_
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hpw
  have h1 : w.asIdeal.ramificationIdx (𝓞 E) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hunr
  have h2 : (w.asIdeal.under (𝓞 E)).ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hv
  have h3 : w.asIdeal.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) (w.asIdeal.under (𝓞 E)) w.asIdeal, h1, h2]
  have hZ : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 h3
  have hint : IsIntegral ℤ δ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hδ]
    have : (-(p : K)) = algebraMap ℤ K (-(p : ℤ)) := by simp
    rw [this]
    exact isIntegral_algebraMap
  set y : 𝓞 K := ⟨δ, hint⟩ with hy
  have hy2 : y ^ 2 = (p : 𝓞 K) * (-1) := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 K) K (y ^ 2) = algebraMap (𝓞 K) K ((p : 𝓞 K) * (-1))
    rw [map_pow, map_mul, map_neg, map_one, map_natCast]
    change δ ^ 2 = _
    rw [hδ]; ring
  have hu : (-1 : 𝓞 K) ∉ w.asIdeal := by
    intro h
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using w.asIdeal.neg_mem h))
  exact GlobalTheory.UnramSquare.not_sq_mul_unit K w.asIdeal hZ p hp hpw y (-1) hu hy2

end GlobalTheory.SqrtNegRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticExistsIntegralGeneratorCommonDenominato
section
open NumberField

namespace GlobalTheory

open NumberField in
private theorem exists_integral_generator_common_denom_of_finrank_two
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra! hx
    have htop : (⊤ : IntermediateField F E) = ⊥ := by
      ext x
      simp only [IntermediateField.mem_top, true_iff]
      exact IntermediateField.mem_bot.mpr (hx x)
    have h1 := IntermediateField.finrank_eq_one_iff.mpr htop
    rw [IntermediateField.finrank_top'] at h1
    omega
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have hint : IsIntegral ℤ (n • x) := hnx x (Finset.mem_singleton_self x)
  obtain ⟨θ, hθx⟩ : ∃ θ : 𝓞 E, (θ : E) = (n : E) * x :=
    ⟨⟨n • x, hint⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hθ : (θ : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    apply hx
    refine ⟨a / n, ?_⟩
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
    rw [map_div₀, map_intCast, ha, hθx]
    field_simp
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hθ
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -hst
  obtain ⟨b, hb1⟩ : ∃ b : Module.Basis (Fin 2) F E, ⇑b = ![(1 : E), (θ : E)] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [h, Fintype.card_fin]),
      coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩
  have hb : ∀ z : E, z = algebraMap F E (b.repr z 0) + algebraMap F E (b.repr z 1) * θ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    rw [Fin.sum_univ_two, hb1]
    simp [Algebra.smul_def]
  set B := RingOfIntegers.basis E
  obtain ⟨d, hd, hdint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin 2 =>
      b.repr (B p.1 : E) p.2)
  have hmem : ∀ i k, IsIntegral ℤ (d • b.repr (B i : E) k) := fun i k =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  refine ⟨θ, hθ, (d : 𝓞 F), by exact_mod_cast hd, ?_⟩
  let M : Submodule ℤ (𝓞 E) :=
    { carrier := {z | ∃ u v : 𝓞 F, z = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ}
      add_mem' := by
        rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
        exact ⟨u + u', v + v', by simp only [map_add]; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨u, v, rfl⟩
        exact ⟨c • u, c • v, by simp only [zsmul_eq_mul, map_mul, map_intCast]; ring⟩ }
  have hall : ∀ y : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) (d : 𝓞 F) * y ∈ M := by
    intro y
    have hspan : y ∈ Submodule.span ℤ (Set.range B) := by rw [B.span_eq]; trivial
    induction hspan using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      refine ⟨⟨_, hmem i 0⟩, ⟨_, hmem i 1⟩, ?_⟩
      rw [RingOfIntegers.ext_iff]
      have e := hb (B i : E)
      have key : algebraMap F E (d : F) * (B i : E) =
          algebraMap F E (d • b.repr (B i : E) 0) +
            algebraMap F E (d • b.repr (B i : E) 1) * θ := by
        simp only [zsmul_eq_mul, map_mul, map_intCast]
        linear_combination (d : E) * e
      exact key
    | zero => simpa using M.zero_mem
    | add z w _ _ hz hw => rw [mul_add]; exact M.add_mem hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact M.smul_mem c hz
  intro y
  obtain ⟨u, v, huv⟩ := hall y
  exact ⟨u, v, huv⟩

open NumberField in

theorem _root_.GlobalTheory.quadratic_exists_integral_generator_common_denominator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  intro F E _ _ _ _ _ _
  exact exists_integral_generator_common_denom_of_finrank_two F E
    (Algebra.IsQuadraticExtension.finrank_eq_two F E)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGenStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by
  first | exact @GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | exact GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen | (intros; apply GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMemStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_one_of_linear_mem' : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  first | exact @GlobalTheory.residue_degree_one_of_linear_mem | exact GlobalTheory.residue_degree_one_of_linear_mem | (intros; apply GlobalTheory.residue_degree_one_of_linear_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_eigenvalue_sum_formula : ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ ∀ α ∈ e.2, ‖α‖ = 1) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
  first | exact @GlobalTheory.longest_segment_unique_of_bounded_remainder | exact GlobalTheory.longest_segment_unique_of_bounded_remainder | (intros; apply GlobalTheory.longest_segment_unique_of_bounded_remainder <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBotStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  first | exact @GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | exact GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | (intros; apply GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubsingletonObjOfIsEmpty
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem subsingleton_obj_of_isEmpty (G : Shv R) (U : Scheme.{0}) [IsEmpty U] :
    Subsingleton (G.val.obj (op U)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_propQCTopology (P := @WeaklyEtale) U)).isZero

theorem isZero_freeOn_of_isEmpty (X : Scheme.{0}) [IsEmpty X] : IsZero ((freeOn R).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)) ((freeOn R).obj X)).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · exact (subsingleton_obj_of_isEmpty R ((freeOn R).obj X) U.unop).elim _ _
  · have : IsEmpty (ULift.{1} (U.unop ⟶ X)) :=
      ⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩
    have hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R) := inferInstance
    have hx : x = 0 := hs.elim x 0
    subst hx
    simp

end GlobalTheory.Et

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryConjugateLocal
section
noncomputable section
namespace GlobalTheory.UStab
open GlobalTheory.HermCSA
open scoped TensorProduct

section Ring
variable {R : Type} [Ring R]

def IsUn (σ : R →+ R) (g : R) : Prop := σ g * g = 1

def SConj (γ δ : R) : Prop := ∃ x : Rˣ, δ = x * γ * ↑x⁻¹

def UConj (σ : R →+ R) (δ δ' : R) : Prop := ∃ g : Rˣ, σ g * g = 1 ∧ δ' = g * δ * ↑g⁻¹

end Ring

def IsRegElt (F : Type) {C : Type} [Field F] [Ring C] [Algebra F C] (γ : C) : Prop :=
  Module.finrank F (Algebra.adjoin F {γ}) ^ 2 = Module.finrank F C

abbrev sK {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K] : K ⊗[ℤ] C →+ K ⊗[ℤ] C :=
  (ext C K s).toAddMonoidHom

section Ext
variable {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K]

@[simp] theorem sK_tmul (k : K) (c : C) : sK s K (k ⊗ₜ c) = k ⊗ₜ s c := rfl

theorem sK_mul (hm : ∀ x y, s (x * y) = s y * s x) (u v : K ⊗[ℤ] C) :
    sK s K (u * v) = sK s K v * sK s K u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k c =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k' c' => simp [Algebra.TensorProduct.tmul_mul_tmul, hm, mul_comm]
    | add v w hv hw => rw [mul_add, map_add, map_add, hv, hw, add_mul]
  | add u w hu hw => rw [add_mul, map_add, map_add, hu, hw, mul_add]

theorem sK_sK (hi : ∀ x, s (s x) = x) (u : K ⊗[ℤ] C) : sK s K (sK s K u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k c => simp [hi]
  | add u w hu hw => rw [map_add, map_add, hu, hw]

end Ext

section Grp
variable {G : Type} [Group G]

end Grp

section Alg
variable {R : Type} [Ring R] (σ : R →+ R)

theorem σ_one (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) : σ 1 = 1 := by
  have h := hm (σ 1) 1
  rw [mul_one, hi] at h
  simpa using h.symm

def σU (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) : Rˣ :=
  ⟨σ u, σ ↑u⁻¹, by rw [← hm, Units.inv_mul, σ_one σ hm hi], by rw [← hm, Units.mul_inv, σ_one σ hm hi]⟩

theorem σU_val (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σ (u : R) = (σU σ hm hi u : R) := rfl

theorem σU_inv_val (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σ (↑u⁻¹ : R) = ↑(σU σ hm hi u)⁻¹ := rfl

theorem σU_mul (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u v : Rˣ) :
    σU σ hm hi (u * v) = σU σ hm hi v * σU σ hm hi u := by
  ext; simp only [Units.val_mul, ← σU_val σ hm hi, hm]

theorem σU_inv (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σU σ hm hi u⁻¹ = (σU σ hm hi u)⁻¹ := by
  ext; rfl

end Alg

section Alg2
variable {R : Type} [Ring R] (σ : R →+ R) (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x)
include hm hi

end Alg2

end GlobalTheory.UStab

namespace GlobalTheory.UStab
open GlobalTheory.HermCSA NumberField
open scoped TensorProduct

section Loc
variable {C : Type} [Ring C] (s : C →+ C) (hm : ∀ x y, s (x * y) = s y * s x) (hi : ∀ x, s (s x) = x)
  (K : Type) [CommRing K]

def uK (x : Cˣ) : (K ⊗[ℤ] C)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] K ⊗[ℤ] C).toMonoidHom x

theorem uK_val (x : Cˣ) : ((uK K x : (K ⊗[ℤ] C)ˣ) : K ⊗[ℤ] C) = (1 : K) ⊗ₜ (x : C) := rfl

include hm hi

theorem σU_uK (x : Cˣ) :
    σU (sK s K) (sK_mul s K hm) (sK_sK s K hi) (uK K x) = uK K (σU s hm hi x) := by
  ext; rfl

theorem hv (x : Cˣ) : ((σU (sK s K) (sK_mul s K hm) (sK_sK s K hi) (uK K x) * uK K x : (K ⊗[ℤ] C)ˣ) : K ⊗[ℤ] C)
    = (1 : K) ⊗ₜ (s x * (x : C)) := by
  rw [σU_uK s hm hi, Units.val_mul, uK_val, uK_val, Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl

end Loc
end GlobalTheory.UStab

namespace GlobalTheory.UStab
open GlobalTheory.HermCSA NumberField
open scoped TensorProduct

section Loc2
variable {C : Type} [Ring C] (s : C →+ C) (hm : ∀ x y, s (x * y) = s y * s x) (hi : ∀ x, s (s x) = x)
  (K : Type) [CommRing K]
include hm hi

end Loc2
end GlobalTheory.UStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.Et.H0

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem sh : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)]
  have h : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)
  have h2 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1}) := by
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor _) h
  exact h2

def yonedaAdd (X : Scheme.{0}) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) ≃+ P.obj (op X) where
  toEquiv := (((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P).trans
    uliftYonedaEquiv
  map_add' _ _ := rfl

def eAdd (X : Scheme.{0}) : H R 0 X ≃+ C(X, R) :=
  (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R)).trans <|
  ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homAddEquiv _ (coef R)).trans <|
  (yonedaAdd R X (coef R).obj).trans <|
  ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift)

theorem eAdd_smul (X : Scheme.{0}) (r : R) (x : H R 0 X) : eAdd R X (r • x) = r • eAdd R X x := by
  have h1 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x) =
      ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x :=
    (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (freeOn R).obj X) (Y := coef R)).map_smul (ULift.up r) x
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x))))) =
    r • AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x))))
  rw [h1]
  have h2 : yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
      (ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) =
      ULift.up r • yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) := rfl
  rw [h2]
  exact (congrArg AddEquiv.ulift (LinearEquiv.map_smul (((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv) (ULift.up r) _)).trans rfl

def e (X : Scheme.{0}) : H R 0 X ≃ₗ[R] C(X, R) :=
  { eAdd R X with map_smul' := eAdd_smul R X }

theorem yonedaAdd_naturality_left {X Y : Scheme.{0}} (f : X ⟶ Y) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (g : uliftYoneda.{1}.obj Y ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) :
    yonedaAdd R X P (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R)) ≫ g) =
      P.map f.op (yonedaAdd R Y P g) := by
  change uliftYonedaEquiv ((((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P)
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).map (uliftYoneda.{1}.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality (F := P ⋙ CategoryTheory.forget _) _ f.op).symm

theorem addEquiv₀_pull {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y) :
    Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (pull R 0 f x) =
      (freeOn R).map f ≫ Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R)).symm.surjective x
  change Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ ((freeOn R).map f)).comp (Abelian.Ext.addEquiv₀.symm φ) (zero_add 0)) = _
  rw [AddEquiv.apply_symm_apply, Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀]
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

theorem e_pull {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y) :
    e R X (pull R 0 f x) = (e R Y x).comp f.base.hom := by
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (pull R 0 f x))))) =
    (AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op Y)).symm.toLinearEquiv)
      (yonedaAdd R Y (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x))))).comp f.base.hom
  rw [addEquiv₀_pull]
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        ((presheafToSheaf _ _).map (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R))) ≫
          Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)))) = _
  have hn := (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv_naturality_left
    (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R)))
    (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)
  erw [hn, yonedaAdd_naturality_left]
  generalize yonedaAdd R Y (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)) = z
  have := NatTrans.naturality_apply (isoSheafify _ (sh R)).inv f.op z
  change AddEquiv.ulift ((isoSheafify _ (sh R)).inv.app (op X) ((coef R).obj.map f.op z)) =
    (AddEquiv.ulift ((isoSheafify _ (sh R)).inv.app (op Y) z)).comp f.base.hom
  erw [this]
  rfl

theorem main :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) ∧
      ∃ e : ∀ X : Scheme.{0}, H R 0 X ≃ₗ[R] C(X, R),
        ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y), e X (pull R 0 f x) = (e Y x).comp f.base.hom :=
  ⟨sh R, e R, fun f x => e_pull R f x⟩

end GlobalTheory.Et.H0
end
end

