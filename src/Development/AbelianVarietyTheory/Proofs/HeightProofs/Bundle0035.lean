import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_action_at_real_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) := by
  first | exact @GlobalTheory.FockCompare.RealAction.real_action | exact GlobalTheory.FockCompare.RealAction.real_action | (intros; apply GlobalTheory.FockCompare.RealAction.real_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalCommutationRelations_weylNumber : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  first | exact @GlobalTheory.WeylNumber.weyl_number | exact GlobalTheory.WeylNumber.weyl_number | (intros; apply GlobalTheory.WeylNumber.weyl_number <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective : ∀ D : D7, Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) := by
  first | exact @GlobalTheory.CMTypePlaces.places_bijective | exact GlobalTheory.CMTypePlaces.places_bijective | (intros; apply GlobalTheory.CMTypePlaces.places_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexStructureOfInvolutions_properties : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  first | exact @GlobalTheory.FockCxAlg.cx_alg | exact GlobalTheory.FockCxAlg.cx_alg | (intros; apply GlobalTheory.FockCxAlg.cx_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_heisenberg_level_and_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → ∀ (V W : HSp D) (f : WA V W → ℂ), (∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f) → Sm (iotaW σ V W) f → Continuous f := by
  first | exact @GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | exact GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | (intros; apply GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  first | exact @GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | exact GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | (intros; apply GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedBasisOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_basis_orthogonal : ∀ (D : D7) (V : HSp D) (s : InvFam V) (P N : Submodule D.host.E V.V) (τ₀ : D.what₂.Tau), IsOrthDec V τ₀ P N → (∀ τ, (∀ x ∈ P, s τ x = x) ∧ ∀ x ∈ N, s τ x = -x) → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Adapted V b s := by
  first | exact @GlobalTheory.FockCompare.exists_adapted_of_isOrthDec | exact GlobalTheory.FockCompare.exists_adapted_of_isOrthDec | (intros; apply GlobalTheory.FockCompare.exists_adapted_of_isOrthDec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCapitulationFieldSize
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.Mem
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem exists_eq_top_of_root_step {G ι : Type} [CommGroup G] [Finite G] [Preorder ι] (C : ι → Subgroup G)
    (hC : Monotone C) (S : ι → ℝ → Prop) (hS : ∀ i s t, s ≤ t → S i s → S i t)
    (step : ∀ i t (c : G) (k : ℕ), S i t → 0 < k → c ^ k ∈ C i → ∃ j, i ≤ j ∧ S j (t + Real.log k) ∧ c ∈ C j) :
    ∀ (m : ℕ) (i : ι) (t : ℝ), (C i).index = m → S i t → ∃ j, i ≤ j ∧ S j (t + Real.log m) ∧ C j = ⊤ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i t hm hi
    by_cases htop : C i = ⊤
    · exact ⟨i, le_rfl, hS i t _ (le_add_of_nonneg_right (Real.log_natCast_nonneg m)) hi, htop⟩
    obtain ⟨c, hc⟩ : ∃ c, c ∉ C i := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.2 fun x _ => h x)
    set D : Subgroup G := C i ⊔ Subgroup.zpowers c with hD
    have hle : C i ≤ D := le_sup_left
    have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
    have hmul := Subgroup.relIndex_mul_index hle
    set k := (C i).relIndex D with hk
    have hm0 : m ≠ 0 := hm ▸ Subgroup.index_ne_zero_of_finite
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, zero_mul, hm] at hmul
      exact hm0 hmul.symm
    have hk1 : k ≠ 1 := fun h => hc (Subgroup.relIndex_eq_one.1 h hcD)
    obtain ⟨j, hij, hj, hcj⟩ := step i t c k hi (Nat.pos_of_ne_zero hk0) (Subgroup.pow_relIndex_mem _ hcD)
    have hDj : D ≤ C j := sup_le (hC hij) ((Subgroup.zpowers_le_of_mem hcj))
    have hD0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hj0 : (C j).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidx : (C j).index ≤ D.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Subgroup.index_dvd_of_le hDj)
    have hlt : (C j).index < m := by
      rw [← hm, ← hmul]
      have : 2 ≤ k := by omega
      have := Nat.pos_of_ne_zero hD0
      nlinarith
    obtain ⟨l, hjl, hl, hl'⟩ := ih _ hlt j _ rfl hj
    refine ⟨l, hij.trans hjl, hS l _ _ ?_ hl, hl'⟩
    rw [add_assoc, ← Real.log_mul (by exact_mod_cast hk0) (by exact_mod_cast hj0)]
    refine add_le_add le_rfl (Real.log_le_log (by positivity) ?_)
    rw [← hm, ← hmul]
    exact_mod_cast Nat.mul_le_mul_left k hidx

theorem Sz.weaken {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨h0, h1.trans ha, h2.trans hb⟩

section

variable {E : Type} [Field E] [NumberField E] (r : (E →+* ℂ) → ℕ) (n : ℕ)

noncomputable def typeNormMod (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Submodule (𝓞 K) K :=
  ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ

def GenTypeNorm (K : IntermediateField ℚ ℂ) (β : K) (𝔞 : Ideal (𝓞 E)) : Prop :=
  Submodule.span (𝓞 K) {β} = typeNormMod r K 𝔞 ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n

variable {r n}

theorem typeNormMod_eq (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) :
    typeNormMod r K 𝔞 = ∏ τ : E →+* ℂ, extendIdealHom (τ.codRestrict K (hK τ)) 𝔞 ^ r τ := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K (hK τ)) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

theorem typeNormMod_mul (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I J : Ideal (𝓞 E)) : typeNormMod r K (I * J) = typeNormMod r K I * typeNormMod r K J := by
  simp only [typeNormMod_eq K hK, map_mul, mul_pow, Finset.prod_mul_distrib]

theorem typeNormMod_pow (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I : Ideal (𝓞 E)) (k : ℕ) : typeNormMod r K (I ^ k) = typeNormMod r K I ^ k := by
  simp only [typeNormMod_eq K hK, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]

theorem GenTypeNorm.mul {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ J) :
    GenTypeNorm r n K (β * γ) (I * J) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [typeNormMod_mul K hK, ← h1.1, ← h2.1, Submodule.span_mul_span, Set.singleton_mul_singleton]
  · rw [map_mul, map_mul, norm_mul, mul_pow, h1.2, h2.2, Nat.cast_mul, mul_pow]

theorem GenTypeNorm.cancel {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (hβ : β ≠ 0) (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ (I * J)) :
    GenTypeNorm r n K (β⁻¹ * γ) J := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, h2.1, typeNormMod_mul K hK, ← h1.1, ← mul_assoc,
      Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hβ, ← Submodule.one_eq_span, one_mul]
  · have h3 := h2.2 σ
    rw [map_mul, Nat.cast_mul, mul_pow, ← h1.2 σ] at h3
    have h4 : ‖σ β‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hβ
    rw [map_mul, map_inv₀, norm_mul, norm_inv, mul_pow, h3]
    field_simp

theorem GenTypeNorm.root {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I : Ideal (𝓞 E)} {β : K} {k : ℕ} (hk : 0 < k) (hβ : β ≠ 0) (h : GenTypeNorm r n K (β ^ k) (I ^ k)) :
    GenTypeNorm r n K β I := by
  refine ⟨?_, fun σ => ?_⟩
  · refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β k hk hβ ?_ ?_).symm
    · rw [typeNormMod_eq K hK]
      exact fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _
    · rw [← typeNormMod_pow K hK, h.1]
  · have := h.2 σ
    rw [map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

theorem genTypeNorm_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (a : 𝓞 E) :
    GenTypeNorm r n K (∏ τ : E →+* ℂ, (⟨τ (a : E), hK τ _⟩ : K) ^ r τ) (Ideal.span {a}) := by
  refine ⟨?_, fun σ => ?_⟩
  · simp only [typeNormMod_eq K hK, extendIdealHom_span, span_singleton_prod_pow]
    rfl
  · have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this

variable (r n)

def HasTypeNormGen (F : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∃ β : F, β ≠ 0 ∧ ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (h : F ≤ K),
    GenTypeNorm r n K (IntermediateField.inclusion h β) 𝔞

variable {r n}

theorem HasTypeNormGen.mono {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') {I : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) : HasTypeNormGen r n F' I := by
  obtain ⟨β, h0, hβ⟩ := hI
  exact ⟨IntermediateField.inclusion h β, (map_ne_zero _).2 h0, fun K _ hK => hβ K (h.trans hK)⟩

theorem HasTypeNormGen.mul {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F J) : HasTypeNormGen r n F (I * J) := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β * γ, mul_ne_zero h0 h1, fun K _ hK => ?_⟩
  rw [map_mul]
  exact (hβ K hK).mul (fun τ x => hK (hF τ x)) (hγ K hK)

theorem HasTypeNormGen.cancel {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F (I * J)) : HasTypeNormGen r n F J := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β⁻¹ * γ, mul_ne_zero (inv_ne_zero h0) h1, fun K _ hK => ?_⟩
  rw [map_mul, map_inv₀]
  exact (hβ K hK).cancel (fun τ x => hK (hF τ x)) ((map_ne_zero _).2 h0) (hγ K hK)

theorem hasTypeNormGen_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {a : 𝓞 E} (ha : a ≠ 0) :
    HasTypeNormGen r n F (Ideal.span {a}) := by
  refine ⟨∏ τ : E →+* ℂ, (⟨τ (a : E), hF τ _⟩ : F) ^ r τ, ?_, fun K _ hK => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    intro h
    have h' : τ (a : E) = 0 := congrArg Subtype.val h
    rw [map_eq_zero] at h'
    exact ha (by exact_mod_cast h')
  · rw [map_prod]
    simp only [map_pow]
    exact genTypeNorm_span hr K (fun τ x => hK (hF τ x)) a

theorem HasTypeNormGen.hasTypeNormGen_of_class_eq [IsCMField E] [IsGalois ℚ E]
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : (Ideal (𝓞 E))⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) (hJ : HasTypeNormGen r n F (J : Ideal (𝓞 E))) :
    HasTypeNormGen r n F (I : Ideal (𝓞 E)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  refine (hasTypeNormGen_span hr hF hx).cancel hF ?_
  rw [hxy]
  exact (hasTypeNormGen_span hr hF hy).mul hF hJ

def typeNormClasses [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (F : {F : IntermediateField ℚ ℂ // ∀ (τ : E →+* ℂ) x, τ x ∈ F}) : Subgroup (ClassGroup (𝓞 E)) where
  carrier := {c | ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = c ∧ HasTypeNormGen r n F.1 (I : Ideal (𝓞 E))}
  one_mem' := ⟨1, map_one _, by
    have := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
    exact this⟩
  mul_mem' := by
    rintro _ _ ⟨I, rfl, hI⟩ ⟨J, rfl, hJ⟩
    exact ⟨I * J, map_mul _ _ _, hI.mul F.2 hJ⟩
  inv_mem' := by
    rintro _ ⟨I, rfl, hI⟩
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (ClassGroup.mk0 I)⁻¹
    refine ⟨J, hJ, hI.cancel F.2 ?_⟩
    have h1 := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at h1
    exact HasTypeNormGen.hasTypeNormGen_of_class_eq hr F.2 (I := I * J) (J := 1) (by rw [map_mul, hJ, mul_inv_cancel, map_one]) h1

end

theorem exists_sz_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ (τ : E →+* ℂ) x, τ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr F a b hF hE
  have key := exists_eq_top_of_root_step (typeNormClasses hr)
    (fun i j hij c ⟨I, hI, h⟩ => ⟨I, hI, h.mono hij⟩) (fun i t => Sz i.1 (a + t) (b + t))
    (fun i s t hst h => h.weaken (by linarith) (by linarith)) ?_ _ ⟨F, hE⟩ 0 rfl (by simpa using hF)
  · obtain ⟨j, hj, hS, htop⟩ := key
    have hle : Real.log ((typeNormClasses hr ⟨F, hE⟩).index) ≤ Real.log (classNumber E) := by
      refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
      have := Nat.le_of_dvd Nat.card_pos (typeNormClasses hr ⟨F, hE⟩).index_dvd_card
      rw [Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    refine ⟨j.1, hj, Sz.weaken hS (by linarith) (by linarith), fun K _ hK 𝔞 h𝔞 => ?_⟩
    have : NumberField K := NumberField.mk
    let I : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    obtain ⟨J, hJ, hJ'⟩ : ClassGroup.mk0 I ∈ typeNormClasses hr j := htop ▸ Subgroup.mem_top _
    obtain ⟨β, h0, hβ⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr j.2 hJ.symm hJ'
    exact ⟨IntermediateField.inclusion hK β, (map_ne_zero _).2 h0, hβ K hK⟩
  · rintro ⟨L, hL⟩ t c k hS hk ⟨J, hJ, hJ'⟩
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨y, hy0, hy⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr hL (I := I ^ k) (by rw [map_pow, hJ]) hJ'
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ k = (y : ℂ) := IsAlgClosed.exists_pow_nat_eq _ hk
    have : FiniteDimensional ℚ L := hS.1
    have : NumberField L := NumberField.mk
    have h1 : typeNormMod r L (I : Ideal (𝓞 E)) ^ k = Submodule.span (𝓞 L) {y} := by
      rw [← typeNormMod_pow L hL]
      exact (hy L le_rfl).1.symm
    have h2 := GlobalTheory.T.field_size_adjoin_kth_root L _ _ k y _ z hS hk hy0 h1 hz
    have hzm : z ∈ L ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ L ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
    have hle : L ≤ L ⊔ ℚ⟮z⟯ := le_sup_left
    have hz0 : (⟨z, hzm⟩ : (L ⊔ ℚ⟮z⟯ : IntermediateField ℚ ℂ)) ≠ 0 := by
      intro h
      have h' : z = 0 := congrArg Subtype.val h
      rw [h', zero_pow hk.ne'] at hz
      exact hy0 (Subtype.ext hz.symm)
    refine ⟨⟨L ⊔ ℚ⟮z⟯, fun τ x => hle (hL τ x)⟩, hle, by simpa only [add_assoc] using h2, I, rfl,
      ⟨z, hzm⟩, hz0, fun K _ hK => ?_⟩
    refine GenTypeNorm.root (fun τ x => hK (hle (hL τ x))) hk ((map_ne_zero _).2 hz0) ?_
    have h3 := hy K (hle.trans hK)
    have h4 : IntermediateField.inclusion hK ⟨z, hzm⟩ ^ k = IntermediateField.inclusion (hle.trans hK) y :=
      Subtype.ext hz
    rw [h4]
    exact h3

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenberg_derivative_linear_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, Sm ι f) → (∀ u, ∀ f ∈ M, hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  first | exact @GlobalTheory.FockCompare.exists_heisenberg_operators | exact GlobalTheory.FockCompare.exists_heisenberg_operators | (intros; apply GlobalTheory.FockCompare.exists_heisenberg_operators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  first | exact @GlobalTheory.FockCompare.RealChart.exists_chart | exact GlobalTheory.FockCompare.RealChart.exists_chart | (intros; apply GlobalTheory.FockCompare.RealChart.exists_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_mem_open_adele_subgroup : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)), IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  first | exact @GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | exact GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | (intros; apply GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  first | exact @GlobalTheory.FockCompare.exists_real_chart | exact GlobalTheory.FockCompare.exists_real_chart | (intros; apply GlobalTheory.FockCompare.exists_real_chart <;> assumption)
end

