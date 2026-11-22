import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0010
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0011
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0009
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0068
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightSpaceEqBotOutsideSupport

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS
  rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    coeff m (glDerivation K LL S a a F) = ((wtS LL S m a : ℤ) : K) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (coeff m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, coeff_smul, smul_eq_mul] at h
  have hc : coeff m F ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem monomial_mem_weightSpace (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) (c : K) :
    monomial m c ∈ weightSp (glOps K n LL S) (wtS LL S m) := by
  rw [polynomial_mem_weightSpace_iff]
  intro a
  rw [diagonal_derivation_monomial, smul_monomial, smul_eq_mul]

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  classical
  refine ⟨polynomial_gl_commutation LL S, ?_, ?_⟩
  · intro x
    haveI : ∀ m : x.support, FiniteDimensional K (Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) :=
      fun m => homogeneous_multidegree_findim _
    refine ⟨⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i), inferInstance, ?_, ?_⟩
    · have key : ∑ m ∈ x.support, monomial m (coeff m x) ∈
          ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i) := by
        apply Submodule.sum_mem
        intro m hm
        apply Submodule.mem_iSup_of_mem (⟨m, hm⟩ : x.support)
        rw [Pol, mem_restrictSupport_iff]
        intro m' hm'
        have h1 := support_monomial_subset (Finset.mem_coe.1 hm')
        rw [Finset.mem_singleton] at h1
        subst h1
        intro i
        rfl
      convert key using 1
      exact x.as_sum
    · intro a b y hy
      refine Submodule.iSup_induction _ (motive := fun y => glOps K n LL S a b y ∈
        ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) hy ?_ ?_ ?_
      · intro m z hz
        exact Submodule.mem_iSup_of_mem m (gl_operator_preserves_multidegree LL S _ a b z hz)
      · simp
      · intro z w hz hw
        rw [map_add]
        exact Submodule.add_mem _ hz hw
  · rw [eq_top_iff]
    intro F _
    have key : ∑ m ∈ F.support, monomial m (coeff m F) ∈ ⨆ mu : Fin n → ℤ, weightSp (glOps K n LL S) mu := by
      apply Submodule.sum_mem
      intro m _
      exact Submodule.mem_iSup_of_mem (wtS LL S m) (monomial_mem_weightSpace LL S m _)
    convert key using 1
    exact F.as_sum

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repResIsGLRep
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_Umon_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨⟨a, b⟩, rfl⟩ := hu; exact hW a b
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem v2rep_isoIn_stable (E : GLOps n K V) (W : Submodule K V) (mu : Fin n → ℤ) :
    IsStableUnderOperators E (isotypicPartIn E W mu) := by
  intro a b x hx
  unfold isotypicPartIn at hx ⊢
  have h : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, hhw, rfl⟩
    exact Submodule.subset_span
      ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, hhw, rfl⟩
  exact h hx

theorem v2rep_iSup_stable (E : GLOps n K V) {ι : Sort*} (p : ι → Submodule K V) (hp : ∀ i, IsStableUnderOperators E (p i)) :
    IsStableUnderOperators E (⨆ i, p i) := by
  intro a b x hx
  exact Submodule.iSup_induction (motive := fun y => E a b y ∈ ⨆ i, p i) p hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (hp i a b y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

def restrictToStableSubmodule (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

theorem v2rep_res_apply (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (a b : Fin n) (x : W) :
    ((restrictToStableSubmodule E W hW a b x : W) : V) = E a b x := rfl

theorem v2rep_res_weightSp (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (mu : Fin n → ℤ) :
    weightSp (restrictToStableSubmodule E W hW) mu = (weightSp E mu).comap W.subtype := by
  ext x
  simp only [weightSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.subtype_apply]
  refine forall_congr' fun a => ?_
  rw [← Submodule.coe_eq_zero, Submodule.coe_sub, Submodule.coe_smul, v2rep_res_apply]
  simp

theorem v2rep_res_isGLRep [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V)
    [FiniteDimensional K W] (hW : IsStableUnderOperators E W) (hw : W ≤ ⨆ ν, weightSp E ν) : IsGLRep (restrictToStableSubmodule E W hW) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := v2rep_comm E hR a b c d (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, v2rep_res_apply]
    rw [h, add_sub_cancel_left]
    congr 1
    · split_ifs <;> simp [v2rep_res_apply]
    · split_ifs <;> simp [v2rep_res_apply]
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · rw [eq_top_iff]
    intro y _
    have h1 := v2rep_graded E W (fun a => hW a a) y y.2 (hw y.2)
    have h2 : (⨆ ν, weightSp E ν ⊓ W) = (⨆ ν, weightSp (restrictToStableSubmodule E W hW) ν).map W.subtype := by
      rw [Submodule.map_iSup]
      refine iSup_congr fun ν => ?_
      rw [v2rep_res_weightSp, Submodule.map_comap_subtype, inf_comm]
    rw [h2] at h1
    obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'

theorem stable_subspace_complete_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : StableSubspaceCompleteReducibility := by
  intro K V _ _ _ _ n E hR W hfd hW hw
  have := hfd
  set W' : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  obtain ⟨P2, hcompl, hP2⟩ := h2 K W n (restrictToStableSubmodule E W hW) (v2rep_res_isGLRep E hR W hW hw)
    (W'.comap W.subtype) (fun a b x hx => hW'st a b x hx)
  have hbot : P2 = ⊥ := by
    by_contra hne
    let Z : Submodule K V := P2.map W.subtype
    have hZW : Z ≤ W := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZW
    have hZst : IsStableUnderOperators E Z := by
      rintro a b _ ⟨y, hy, rfl⟩
      exact ⟨restrictToStableSubmodule E W hW a b y, hP2 a b y hy, rfl⟩
    have hZne : Z ≠ ⊥ := by
      intro h
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h5 : (y : V) ∈ Z := ⟨y, hy, rfl⟩
      rw [h] at h5
      exact hy0 (Subtype.ext h5)
    obtain ⟨mu, v, hvZ, hhw⟩ := v2rep_exists_hwv E hR Z hZst (hZW.trans hw) hZne
    obtain ⟨y, hy, rfl⟩ := hvZ
    have h1 : (y : V) ∈ W' :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, y, y.2, hhw, rfl⟩)
    have h3 : y ∈ (W'.comap W.subtype) ⊓ P2 := ⟨h1, hy⟩
    rw [hcompl.inf_eq_bot] at h3
    have h4 : y = 0 := h3
    exact hhw.1 (by rw [h4]; rfl)
  have htop : W'.comap W.subtype = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  intro x hx
  have : (⟨x, hx⟩ : W) ∈ W'.comap W.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightComponentsMemInvariant
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem weight_components_mem_invariant [CharZero K] (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (s : Finset (Fin n → ℤ)) : ∀ f : (Fin n → ℤ) → V, (∀ mu ∈ s, f mu ∈ weightSp E mu) →
      ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W :=
  _root_.UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant E W hW s

theorem weightSpace_independent [CharZero K] (E : GLOps n K V) : iSupIndep (weightSp E) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv h0 i hi
  have := weight_components_mem_invariant E ⊥ (fun a x hx => by simp [(Submodule.mem_bot K).1 hx]) s v hv (by simp [h0]) i hi
  simpa using this

variable (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)

@[simp] theorem restricted_operator_coe (a b : Fin n) (x : W) : ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

theorem restricted_mem_weightSpace_iff (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isHWV_iff (lam : Fin n → ℤ) (v : W) : IsHWV (restrictStableOperators E W h) lam v ↔ IsHWV E lam (v : V) := by
  unfold IsHWV
  rw [restricted_mem_weightSpace_iff]
  refine and_congr (by simp) (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isGLRep [CharZero K] (hE : IsGLRep E) : IsGLRep (restrictStableOperators E W h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    ext x
    have h1 := congrArg (fun f : Module.End K V => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restricted_operator_coe]
    rw [h1]
    split_ifs <;> simp
  · intro x
    obtain ⟨W0, hfd, hx0, hst⟩ := hE.2.1 (x : V)
    refine ⟨W0.comap W.subtype, ?_, hx0, fun a b y hy => hst a b _ hy⟩
    have h1 : FiniteDimensional K ((W0.comap W.subtype).map W.subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective W.subtype W.injective_subtype (W0.comap W.subtype)).symm
  · rw [eq_top_iff]
    intro x _
    have hx : (x : V) ∈ ⨆ mu, weightSp E mu := by rw [hE.2.2]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
    have hmem := weight_components_mem_invariant E W (fun a => h a a) f.support f (fun mu _ => hf mu)
      (by have : ∑ mu ∈ f.support, f mu = (x : V) := hsum
          rw [this]; exact x.2)
    have hx2 : x = ∑ mu ∈ f.support.attach, (⟨f mu.1, hmem mu.1 mu.2⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only
      rw [Finset.sum_attach f.support (fun mu => f mu)]
      exact hsum.symm
    rw [hx2]
    refine Submodule.sum_mem _ fun mu _ => ?_
    exact Submodule.mem_iSup_of_mem mu.1 ((restricted_mem_weightSpace_iff E W h mu.1 _).2 (hf mu.1))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

@[simp] theorem restrictRepresentation_coe (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (a b : Fin n) (x : W) :
    ((restrictRepresentation E W h a b x : W) : V) = E a b x := rfl

@[simp] theorem homRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (f : V →ₗ[K] V') (x : V) :
    homRepresentation E E' a b f x = E' a b (f x) - f (E a b x) := by
  simp [homRepresentation]

theorem restrict_mem_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictRepresentation E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSp_iff_diagonal_apply, mem_weightSp_iff_diagonal_apply]
  constructor
  · intro hx a
    have e := congrArg Subtype.val (hx a)
    simpa using e
  · intro hx a
    ext
    simpa using hx a

theorem restrictRepresentation_isRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V)
    (h : IsSubrepresentation E W) : IsGLRep (restrictRepresentation E W h) := by
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    have e := congrArg (fun f => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restrictRepresentation_coe]
    rw [e]
    split_ifs <;> simp
  · obtain ⟨s, π, -, hinv, -, hmem, hsum⟩ := weight_projections_exist E hE
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ mu ∈ s, (⟨π mu x, hinv mu W (fun a y hy => h a a y hy) x x.2⟩ : W) := by
      ext
      simp [hsum]
    rw [hx]
    refine Submodule.sum_mem _ fun mu _ => ?_
    refine Submodule.mem_iSup_of_mem mu ?_
    rw [restrict_mem_weightSpace_iff]
    exact hmem mu x

theorem weightProjection_diagonal_apply_eq_smul [CharZero K] (E : GLOps n K V) (hE : IsGLRep E) (nu : Fin n → ℤ) (π : Module.End K V)
    (hπ : IsWtProj E nu π) (a : Fin n) (x : V) : π (E a a x) = (nu a : K) • π x := by
  have hx : x ∈ (⨆ mu, weightSp E mu) := hE.2.2 ▸ Submodule.mem_top
  refine Submodule.iSup_induction (p := weightSp E) (motive := fun y => π (E a a y) = (nu a : K) • π y) hx
    (fun mu y hy => ?_) ?_ (fun y w hy hw => ?_)
  · rw [(mem_weightSp_iff_diagonal_apply E mu y).1 hy a, map_smul]
    by_cases hmu : mu = nu
    · subst hmu
      rfl
    · rw [hπ.2 mu hmu y hy, smul_zero, smul_zero]
  · simp
  · simp only [map_add, hy, hw, smul_add]

theorem homRepresentation_isRep [CharZero K] [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V)
    (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (homRepresentation E E') := by
  refine ⟨fun a b c d => ?_, fun f => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · ext f x
    have h1 := congrArg (fun g => g (f x)) (hE'.1 a b c d)
    have h2 := congrArg (fun g => f (g x)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, homRepresentation_apply, map_sub]
    split_ifs at h1 h2 ⊢ <;>
      simp only [LinearMap.zero_apply, map_zero, sub_zero, zero_sub, homRepresentation_apply, map_sub,
        map_neg] at h1 h2 ⊢ <;>
      (rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]; abel)
  · obtain ⟨s, π, hπ, -, -, -, hsum⟩ := weight_projections_exist E hE
    obtain ⟨s', π', -, -, -, hmem', hsum'⟩ := weight_projections_exist E' hE'
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ mu ∈ s, ∑ mu' ∈ s', (π' mu').comp (f.comp (π mu)) := by
      ext x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_comm]
      simp only [← map_sum]
      rw [hsum x, hsum' (f x)]
    rw [hf]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun mu' _ => ?_
    refine Submodule.mem_iSup_of_mem (mu' - mu) ?_
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [weightProjection_diagonal_apply_eq_smul E hE mu (π mu) (hπ mu) a x, map_smul, map_smul,
      (mem_weightSp_iff_diagonal_apply E' mu' _).1 (hmem' mu' _) a]
    simp only [Pi.sub_apply, Int.cast_sub, sub_smul]

theorem root_differences_bddAbove [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E W, ∃ nu ∈ wtsOf E W, ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  refine ⟨s.sup fun mu => s.sup fun nu => Finset.univ.sup fun a => (mu a - nu a).toNat, ?_⟩
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
  have hmu' : mu ∈ s := by
    by_contra hc
    apply hmu
    rw [weightSpace_eq_bot_outside_support E s hs mu hc, bot_inf_eq]
  have hnu' : nu ∈ s := by
    by_contra hc
    apply hnu
    rw [weightSpace_eq_bot_outside_support E s hs nu hc, bot_inf_eq]
  have hk : mu a - nu a = (k : ℤ) := by
    have e := congrFun heq a
    simp only [Pi.sub_apply, Pi.smul_apply, rootW, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      sub_zero, smul_eq_mul, mul_one] at e
    exact e
  have hk' : k ≤ (mu a - nu a).toNat := by omega
  exact Finset.le_sup_of_le hmu' (Finset.le_sup_of_le hnu' (Finset.le_sup_of_le (Finset.mem_univ a) hk'))

end

theorem restriction_is_representation : RestrictionIsRepresentation := by
  intro n K V _ _ _ _ _ E hE W h
  exact restrictRepresentation_isRep E hE W h

theorem hom_space_is_representation : HomSpaceIsRepresentation := by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE'
  exact homRepresentation_isRep E E' hE hE'

theorem homRep_ell_bounded_by_target : HomRepEllBoundedByTarget := by
  intro n K W _ _ _ _ _ E hE L hL
  refine csSup_le' ?_
  rintro k ⟨a, b, hab, hk⟩
  have hres := restrictRepresentation_isRep E hE L hL

  have hne : weightSp (homRepresentation (restrictRepresentation E L hL) E) ((k : ℤ) • rootW a b) ≠ ⊥ := by
    intro h0; apply hk; rw [h0, bot_inf_eq]
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hex : ∃ nu, ∃ x ∈ weightSp (restrictRepresentation E L hL) nu, g x ≠ 0 := by
    by_contra hc
    apply hg0
    refine linearMap_ext_on_weightSpaces _ hres g 0 fun nu x hx => ?_
    by_contra h1
    exact hc ⟨nu, x, hx, h1⟩
  obtain ⟨nu, x, hx, hgx⟩ := hex
  have hx' : (x : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu x).1 hx
  have hx0 : (x : W) ≠ 0 := by
    intro h0
    apply hgx
    have : x = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hgw : g x ∈ weightSp E ((k : ℤ) • rootW a b + nu) := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    have h1 := congrArg (fun f : L →ₗ[K] W => f x) ((mem_weightSp_iff_diagonal_apply _ _ g).1 hg c)
    simp only [homRepresentation_apply, LinearMap.smul_apply] at h1
    have h2 : restrictRepresentation E L hL c c x = (nu c : K) • x := (mem_weightSp_iff_diagonal_apply _ _ x).1 hx c
    rw [h2, map_smul, sub_eq_iff_eq_add] at h1
    rw [h1, Pi.add_apply, Int.cast_add, add_smul]
  refine le_csSup (root_differences_bddAbove E hE ⊤) ⟨(k : ℤ) • rootW a b + nu, ?_, nu, ?_, a, b, hab, by abel⟩
  · intro h0
    have : g x ∈ weightSp E ((k : ℤ) • rootW a b + nu) ⊓ ⊤ := ⟨hgw, trivial⟩
    rw [h0] at this
    exact hgx ((Submodule.mem_bot K).1 this)
  · intro h0
    have : (x : W) ∈ weightSp E nu ⊓ ⊤ := ⟨hx', trivial⟩
    rw [h0] at this
    exact hx0 ((Submodule.mem_bot K).1 this)

end Formalism.MainNotions.G.GLWeightTheory
end
end

