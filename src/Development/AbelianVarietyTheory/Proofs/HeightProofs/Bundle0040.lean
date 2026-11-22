import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
section
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleCocompact

variable (F : Type) [Field F] [NumberField F]

theorem exists_bound_sub_integer :
    ∃ C : InfinitePlace F → ℝ, ∀ x : F, ∃ y : 𝓞 F, ∀ v : InfinitePlace F, v (x - y) ≤ C v := by
  classical
  refine ⟨fun v => ∑ i, v (integralBasis F i), fun x => ?_⟩
  refine ⟨∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i, fun v => ?_⟩
  have h : x - ((∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F)
      = ∑ i, ((Int.fract ((integralBasis F).repr x i) : ℚ) : F) * integralBasis F i := by
    conv_lhs => enter [1]; rw [← (integralBasis F).sum_repr x]
    change _ - algebraMap (𝓞 F) F _ = _
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, Int.fract, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  rw [h, ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, norm_mul, InfinitePlace.norm_embedding_eq v (integralBasis F i), map_ratCast,
    Complex.norm_ratCast]
  refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
  rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
  exact_mod_cast (Int.fract_lt_one _).le

omit [NumberField F] in
theorem properSpace_completion (v : InfinitePlace F) : ProperSpace v.Completion := by
  refine ⟨fun x r => ?_⟩
  have h := InfinitePlace.Completion.isometry_extensionEmbedding v
  rw [← h.preimage_closedBall]
  exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

theorem exists_compact_infinite :
    ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧
      ∀ a : InfiniteAdeleRing F, ∃ y : 𝓞 F, a - algebraMap F (InfiniteAdeleRing F) y ∈ K := by
  obtain ⟨C, hC⟩ := exists_bound_sub_integer F
  haveI := properSpace_completion F
  refine ⟨Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) (1 + C v),
    isCompact_univ_pi fun v => isCompact_closedBall _ _, fun a => ?_⟩
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (a v) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hU
    ⟨a, fun v _ => Metric.mem_ball_self one_pos⟩
  obtain ⟨y, hy⟩ := hC x
  refine ⟨y, fun v _ => ?_⟩
  have h1 : ‖a v - algebraMap F (InfiniteAdeleRing F) x v‖ < 1 := by
    rw [← dist_eq_norm, dist_comm]; exact hx v trivial
  have h2 : ‖algebraMap F (InfiniteAdeleRing F) (x - y) v‖ ≤ C v := by
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    exact hy v
  have h3 : (a - algebraMap F (InfiniteAdeleRing F) y) =
      (a - algebraMap F (InfiniteAdeleRing F) x) + algebraMap F (InfiniteAdeleRing F) (x - y) := by
    rw [map_sub]; ring
  rw [mem_closedBall_zero_iff, h3]
  exact (norm_add_le (a v - algebraMap F (InfiniteAdeleRing F) x v) _).trans (add_le_add h1.le h2)

theorem isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem exists_compact_adele : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  intro F _ _
  obtain ⟨K, hK, hK'⟩ := exists_compact_infinite F
  refine ⟨K ×ˢ {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    hK.prod (isCompact_integral F), fun a => ?_⟩
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a.2
  obtain ⟨y, hy⟩ := hK' (a.1 - algebraMap F (InfiniteAdeleRing F) x)
  refine ⟨x + y, ?_, ?_⟩
  · change a.1 - algebraMap F (InfiniteAdeleRing F) (x + y) ∈ K
    rw [map_add, ← sub_sub]; exact hy
  · change ∀ v, (a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y)) v ∈ v.adicCompletionIntegers F
    have h : a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y) =
        b - algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      rw [hab, map_add, one_smul]; ring
    rw [h]
    intro v
    exact sub_mem (hb v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y)

end GlobalTheory.AdeleCocompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulNormLeOne
section
open IsDedekindDomain NumberField

namespace GlobalTheory.AbsNormAdicBounds

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_norm_eq_zpow (y : v.adicCompletion F) (hy : y ≠ 0) :
    ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  simp

theorem norm_absNorm_lt_one :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have h := (NumberField.FinitePlace.norm_lt_one_iff_mem F v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem v.asIdeal)
  rwa [map_natCast, map_natCast] at h

theorem norm_absNorm_mul_le_one :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ * (Ideal.absNorm v.asIdeal : ℝ) ≤ 1 := by
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases h0 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = 0
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ := exists_norm_eq_zpow v _ h0
    have hlt := norm_absNorm_lt_one v
    rw [hk] at hlt ⊢
    have hk0 : k < 0 := (zpow_lt_one_iff_right₀ hq).1 hlt
    rw [← zpow_add_one₀ (by linarith)]
    exact zpow_le_one_of_nonpos₀ hq.le (by omega)

theorem exists_nat_mul_norm_le_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (H : ℝ) (hH : 1 ≤ H) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ H ∧
      ∀ y : v.adicCompletion F, ‖y‖ ≤ H → ‖(n : v.adicCompletion F) * y‖ ≤ 1 := by
  have hqN := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hqN
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hH hq
  refine ⟨Ideal.absNorm v.asIdeal ^ m, pow_pos (by omega) m, by exact_mod_cast hm1, ?_⟩
  intro y hy
  have hyle : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
    by_cases h0 : y = 0
    · rw [h0, norm_zero]; positivity
    · obtain ⟨k, hk⟩ := exists_norm_eq_zpow v y h0
      have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ k <
          (Ideal.absNorm v.asIdeal : ℝ) ^ ((m + 1 : ℕ) : ℤ) := by
        rw [zpow_natCast, ← hk]; exact hy.trans_lt hm2
      have hkm : k < ((m + 1 : ℕ) : ℤ) := (zpow_lt_zpow_iff_right₀ hq).1 hlt
      rw [hk, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hq.le (by push_cast at hkm; omega)
  rw [norm_mul, Nat.cast_pow, norm_pow]
  calc ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ m * ‖y‖
      ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ m *
          (Ideal.absNorm v.asIdeal : ℝ) ^ m := by gcongr
    _ = (‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ *
          (Ideal.absNorm v.asIdeal : ℝ)) ^ m := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ (by positivity) (norm_absNorm_mul_le_one v)

end GlobalTheory.AbsNormAdicBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulApply
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct NNReal

namespace GlobalTheory.AdeleDenominators

section Local

variable {F : Type} [Field F] [NumberField F]

theorem valued_absNorm_le (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      FinitePlace.embedding v (algebraMap (𝓞 F) F (Ideal.absNorm v.asIdeal : ℕ)) := by
    simp
  rw [h1, FinitePlace.embedding_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) 1).2 (by simpa using Ideal.absNorm_mem v.asIdeal)
  simpa using h2

theorem local_den (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ max 1 ‖x‖₊ ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  by_cases hx : Valued.v x ≤ 1
  · exact ⟨1, one_pos, by simp, by simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hx⟩
  · have h1 : 1 < Valued.v x := not_le.1 hx
    have h0 : Valued.v x ≠ 0 := (zero_lt_one.trans h1).ne'
    obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v x = WithZero.exp e := ⟨_, (WithZero.exp_log h0).symm⟩
    have hpos : 0 < e := by
      rw [he, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1; exact h1
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    refine ⟨Ideal.absNorm v.asIdeal ^ k,
      pow_pos (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)) k, ?_, ?_⟩
    · refine le_max_of_le_right (le_of_eq ?_)
      apply NNReal.eq
      rw [coe_nnnorm, FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
      simp [WithZero.exp]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, he, Nat.cast_pow, map_pow]
      calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ k * WithZero.exp (k : ℤ) := by
            gcongr; exact valued_absNorm_le v
        _ = 1 := by rw [← WithZero.exp_nsmul, ← WithZero.exp_add]; simp

theorem adele_den (c : FiniteAdeleRing (𝓞 F) F) (h : HeightOneSpectrum (𝓞 F) → ℝ≥0)
    (hf : (Function.mulSupport h).Finite) (h1 : ∀ v, 1 ≤ h v) (hc : ∀ v, ‖c v‖₊ ≤ h v) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ ∏ᶠ v, h v ∧
      ∀ v, (n : v.adicCompletion F) * c v ∈ v.adicCompletionIntegers F := by
  classical
  choose m hm0 hm1 hm2 using fun v => local_den v (c v)
  have hm3 : ∀ v, (m v : ℝ≥0) ≤ h v := fun v => (hm1 v).trans (max_le (h1 v) (hc v))
  refine ⟨∏ v ∈ hf.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, ?_, fun v => ?_⟩
  · rw [finprod_eq_prod h hf, Nat.cast_prod]
    exact Finset.prod_le_prod' fun v _ => hm3 v
  · by_cases hv : v ∈ hf.toFinset
    · rw [← Finset.prod_erase_mul _ _ hv, Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (hm2 v)
    · have hv1 : h v = 1 := by simpa using hv
      have hm : m v = 1 := by
        have := hm3 v
        rw [hv1] at this
        have h' : m v ≤ 1 := by exact_mod_cast this
        have := hm0 v
        omega
      have := hm2 v
      rw [hm, Nat.cast_one, one_mul] at this
      exact mul_mem (natCast_mem _ _) this

theorem family_den {ι : Type} [Fintype ι] (c : ι → FiniteAdeleRing (𝓞 F) F) (h : HeightOneSpectrum (𝓞 F) → ℝ≥0)
    (hf : (Function.mulSupport h).Finite) (h1 : ∀ v, 1 ≤ h v) (hc : ∀ p v, ‖c p v‖₊ ≤ h v) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0) ≤ (∏ᶠ v, h v) ^ Fintype.card ι ∧
      ∀ p v, (n : v.adicCompletion F) * c p v ∈ v.adicCompletionIntegers F := by
  choose n hn using fun p => adele_den (c p) h hf h1 (hc p)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => (hn p).1, ?_, ?_⟩
  · push_cast
    calc ∏ p, (n p : ℝ≥0) ≤ ∏ _p : ι, ∏ᶠ v, h v := Finset.prod_le_prod' fun p _ => (hn p).2.1
      _ = (∏ᶠ v, h v) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  · intro p v
    classical
    have e : ((∏ q, n q : ℕ) : v.adicCompletion F) * c p v =
        ((∏ q ∈ Finset.univ.erase p, n q : ℕ) : v.adicCompletion F) * ((n p : v.adicCompletion F) * c p v) := by
      rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ p)]
    rw [e]
    exact mul_mem (natCast_mem _ _) ((hn p).2.2 v)

end Local

section Lattice

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ I := by
  obtain ⟨α, hα, hαI⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI
  have hn : Ideal.absNorm (Ideal.span {α}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hα
  refine ⟨_, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {α}))
  have : ((Ideal.absNorm (Ideal.span {α}) : ℕ) : E) = β • algebraMap (𝓞 E) E α := by
    rw [Algebra.smul_def, ← map_mul, hβ, map_natCast]
  rw [this]
  exact Submodule.smul_mem (I : Submodule (𝓞 E) E) β hαI

theorem exists_nat_smul_mem {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (L : Submodule (𝓞 E) W) (hL : Submodule.span E (L : Set W) = ⊤) (x : W) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set W) := by rw [hL]; trivial
  have key : ∀ (n : ℕ) (y : W), y ∈ L → (n : E) • y ∈ L := fun n y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy n
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_pos hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, Nat.cast_mul, mul_smul]; exact key _ _ hsy
    · rw [Nat.cast_mul, mul_smul]; exact key _ _ htz
  | smul e y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have hi : IsIntegral ℤ ((m.natAbs : E) * e) := by
      have h0 := hint e (Finset.mem_singleton_self e)
      rw [zsmul_eq_mul] at h0
      rcases Int.natAbs_eq m with h | h
      · rw [h] at h0; simpa using h0
      · rw [h] at h0; simpa using h0.neg
    refine ⟨m.natAbs * s, mul_pos (Int.natAbs_pos.2 hm) hs, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (m.natAbs : E) * e := ⟨⟨_, hi⟩, rfl⟩
    have : ((m.natAbs * s : ℕ) : E) • e • y = r • ((s : E) • y) := by
      rw [← algebraMap_smul E r, smul_smul, smul_smul, hr]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem _ hsy

end Lattice

theorem column_expand {F E R W n κ : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [AddCommGroup W] [Module E W] [Fintype n] [DecidableEq n] [Fintype κ] (b : Module.Basis κ F E)
    (f : Module.Basis n E W) (M : Matrix n n (R ⊗[F] E)) (i : n) (B N : ℕ) :
    M.mulVec (fun l => (1 : R) ⊗ₜ[F] (Pi.single i ((B * N : ℕ) : E) : n → E) l) =
      ∑ j, ∑ k, fun l => ((N : R) * (Algebra.TensorProduct.basis R b).repr (M j i) k) ⊗ₜ[F]
        f.repr (((B : E) * b k) • f j) l := by
  have hv : (fun l => (1 : R) ⊗ₜ[F] (Pi.single i ((B * N : ℕ) : E) : n → E) l) =
      Pi.single i ((B * N : ℕ) : R ⊗[F] E) := by
    funext l
    by_cases hl : l = i
    · subst hl
      rw [Pi.single_eq_same, Pi.single_eq_same]
      exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) _
    · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, TensorProduct.tmul_zero]
  have e1 : ((B * N : ℕ) : R ⊗[F] E) = (N : R) ⊗ₜ[F] (B : E) := by
    have a1 : ((B : ℕ) : R ⊗[F] E) = (1 : R) ⊗ₜ[F] (B : E) :=
      (map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) _).symm
    rw [Nat.cast_mul, a1, Algebra.TensorProduct.natCast_def N, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  rw [hv, Matrix.mulVec_single]
  funext l
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · rw [Finset.sum_apply]
    have hy2 := (Algebra.TensorProduct.basis R b).sum_repr (M l i)
    change M l i * _ = _
    conv_lhs => rw [← hy2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MulOpposite.unop_op, e1, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul',
      Algebra.TensorProduct.tmul_mul_tmul,
      smul_eq_mul, mul_one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, mul_comm (b k), mul_comm _ (N : R)]
  · intro j _ hj
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hj.symm, smul_zero,
      TensorProduct.tmul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem natCast_mul_apply {F : Type} [Field F] [NumberField F] (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((N : FiniteAdeleRing (𝓞 F) F) * a) v = (N : v.adicCompletion F) * a v := by first | rfl | simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem denomBound (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    GlobalTheory.SmoothForms.DenomBound θ V := by
  classical
  obtain ⟨A, hA0, hA⟩ := exists_nat_mem D.host.AA (Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  set b := Module.finBasis D.host.F D.host.E with hb
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℕ, 0 < B ∧ ∀ j k, ((B : D.host.E) * b k) • V.frame j ∈ V.L0 := by
    choose m hm0 hm using fun p : Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      exists_nat_smul_mem V.L0 V.standardTuple_isLattice.span_eq_top (b p.2 • V.frame p.1)
    refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm0 p, fun j k => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, k)), Nat.cast_mul, mul_assoc, mul_smul, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hm (j, k)) _
  refine ⟨A * B, Fintype.card (Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E)), fun g => ?_⟩
  obtain ⟨N, hN0, hN1, hN⟩ := family_den
    (fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ p.1 p.2.1) p.2.2)
    (fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt V v g) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite V g)
    (fun v => le_max_left _ _)
    (fun p v => le_max_of_le_right (le_max_of_le_right (Finset.le_sup (f := fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ p.1 p.2.1) p.2.2)‖₊)
      (Finset.mem_univ p))))
  refine ⟨A * (B * N), by positivity, ?_, fun i => ?_⟩
  · have h1 : (∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt V v g) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => le_max_left _ _)
    have h2 : (N : ℝ≥0) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g ^ _ := hN1.trans (pow_le_pow_left' h1 _)
    have h3 : (N : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^
        Fintype.card (Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E)) := by exact_mod_cast h2
    push_cast
    rw [← mul_assoc]
    gcongr
  · refine Submodule.subset_span ⟨A, hA, Pi.single i ((B * N : ℕ) : D.host.E), ?_, ?_⟩
    · refine ⟨(finHom V g⁻¹).1.mulVec (Formalism.L2.Pj.finVec V (Pi.single i ((B * N : ℕ) : D.host.E))), ?_, ?_⟩
      · have hz : (finHom V g⁻¹).1.mulVec (Formalism.L2.Pj.finVec V (Pi.single i ((B * N : ℕ) : D.host.E))) =
            ∑ j, ∑ k, fun l => ((N : Af D.host.F) *
              GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹ j i) k) ⊗ₜ[D.host.F]
              V.frame.repr (((B : D.host.E) * b k) • V.frame j) l :=
          column_expand b V.frame (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g⁻¹) i B N
        rw [hz]
        refine sum_mem fun j _ => sum_mem fun k _ => AddSubgroup.subset_closure ⟨_, fun v => ?_, _, hB j k, rfl⟩
        rw [natCast_mul_apply]; exact hN (j, i, k) v
      · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
    · rw [← Pi.single_smul, smul_eq_mul, ← Nat.cast_mul]

end GlobalTheory.AdeleDenominators

end
end

