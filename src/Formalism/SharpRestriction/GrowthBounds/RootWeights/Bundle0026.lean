import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0025
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntryRestrictionMem
import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0023

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorOfReducibility
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightSpace {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (mu : Fin n → ℤ) :
    Submodule K V :=
  weightSp E mu ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

theorem mem_highestWeightSpace_iff {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {E : GLOps n K V}
    {mu : Fin n → ℤ} {x : V} : x ∈ highestWeightSpace E mu ↔ x ∈ weightSp E mu ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp [highestWeightSpace, Submodule.mem_iInf]

theorem weightSpace_le_hwv_sup_nMinus (D : Formalism.BasicNotions.D7) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) :
    weightSp E mu ≤ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu) := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D (weight_condition_from_integral_form D) E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  obtain ⟨Θ, _, hΘ⟩ := weight_projections_integral_findim E
  have hle : ∀ ν, isoSub E ν ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
    intro ν
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, v, hv, rfl⟩
    have hY : loweringWordSpan E v ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u', hu', rfl⟩
      obtain ⟨⟨κ, hκ⟩, h⟩ := lowering_word_weight_or_nMinus hs hv.2.1 hu'
      change Θ mu (u' v) ∈ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)
      rw [hΘ mu κ _ hκ]
      split_ifs with hk
      · subst hk
        rcases h with h | h
        · refine Submodule.mem_sup_left (mem_highestWeightSpace_iff.2 ⟨hκ, ?_⟩)
          rw [h]
          exact hv.2.2
        · exact Submodule.mem_sup_right ⟨h, hκ⟩
      · exact Submodule.zero_mem _
    exact hY (lowering_word_span_enveloping_stable hE hv hu v (Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩))
  intro x hx
  have h1 : x ∈ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
    have : (⊤ : Submodule K V) ≤ (highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu)).comap (Θ mu) := by
      rw [← htop]
      exact iSup_le hle
    exact this Submodule.mem_top
  have h2 : Θ mu x ∈ highestWeightSpace E mu ⊔ (nMinus E ⊓ weightSp E mu) := h1
  rwa [hΘ mu mu x hx, if_pos rfl] at h2

theorem extremal_projector_of_reducibility (D : Formalism.BasicNotions.D7) (h : adm5 D) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨_, h2, h3⟩ := h K V n E hE mu hmu ord hord T hT
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (weightSpace_le_hwv_sup_nMinus D E hE mu hx)
  obtain ⟨hy1, hy2⟩ := mem_highestWeightSpace_iff.1 hy
  rw [map_add, h3 y hy1 hy2, h2 z hz.2 hz.1, add_zero]
  exact hy2 a b (by
    have : (a : ℕ) < (b : ℕ) := by omega
    exact this)

theorem condition_iff_additive_maps (D : Formalism.BasicNotions.D7) : adm5 D ↔ SimpleRaisingKillsExtremalProjector := ⟨extremal_projector_of_reducibility D, sizes_bound_of_log_estimates D⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaPartB
section
noncomputable section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_module_weight_lemma_part_b : GeneratedModuleWeightDescription :=
  generated_module_weight_lemma_of_interfaces transvectionExpansion torus_acts_through_weight binomial_stable_contains_components twist_exponents_are_weight_entries generic_monomials_specialise

theorem valuationsAdditive_D7 (D : Formalism.BasicNotions.D7) : ValuationsAdditive D := valuations_additive_of_generated_weight_description D generated_module_weight_lemma_part_b

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorTraceFormula
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def smulRightLinear {K L W : Type} [Field K] [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]
    (ξ : L →ₗ[K] K) : W →ₗ[K] (L →ₗ[K] W) where
  toFun := fun m => ξ.smulRight m
  map_add' := fun m m' => by ext x; simp
  map_smul' := fun c m => by
    ext x
    simp only [LinearMap.smulRight_apply, RingHom.id_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _

theorem isotypic_projector_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorTraceFormula := by
  intro n K W _ _ _ _ _ E hE lam e he v0 hv0 hL P hP ι _ b m
  have hEL := restrictRepresentation_isRep E hE _ hL
  have hv0' := highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0
  have hcyc := cyclicSubmodule_restrict_eq_top E v0 hL
  have hPe := fun g => invariant_projection_equivariant D h2 (restrictRepresentation E _ hL) E hEL hE P hP g

  let Θ : W →ₗ[K] W := ∑ i, (LinearMap.applyₗ (b i)) ∘ₗ P ∘ₗ smulRightLinear (b.coord i)
  have hΘ : ∀ m, Θ m = ∑ i, P ((b.coord i).smulRight m) (b i) := by
    intro m
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    rfl
  have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.eqLocus ((Fintype.card ι : K) • Θ) e := by
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam
    · subst hmu
      refine Submodule.span_le.2 ?_
      rintro y ⟨u, hu, v, hv, rfl⟩
      have hy : u v ∈ isoSub E mu := Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      obtain ⟨φ, hφ, hφv⟩ := exists_equivariant_cyclic_to_hwv D h2 E hE mu v0 v hv0 hv hL
      obtain ⟨uL, _, huL⟩ := equivariant_lifts_monoid (restrictRepresentation E _ hL) E φ hφ hu
      have hm : u v = φ (uL ⟨v0, self_mem_cyclicSubmodule E v0⟩) := by rw [huL, hφv]
      obtain ⟨P0, hP0⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEL)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hL)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W φ) := by
        intro a c g
        ext x
        simp only [LinearMap.llcomp_apply, homRepresentation_apply, map_sub]
        rw [hφ]
      change ((Fintype.card ι : K) • Θ) (u v) = e (u v)
      rw [he.1 _ hy, LinearMap.smul_apply, hΘ, hm, Finset.smul_sum]
      set l := uL ⟨v0, self_mem_cyclicSubmodule E v0⟩ with hl
      have hterm : ∀ i, (Fintype.card ι : K) • P ((b.coord i).smulRight (φ l)) (b i) = (b.repr l i) • φ (b i) := by
        intro i
        have h3 : (b.coord i).smulRight (φ l) = LinearMap.llcomp K _ _ W φ ((b.coord i).smulRight l) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEL) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W φ) hT P0 P hP0 hP ((b.coord i).smulRight l)
        have h5 := schur_invariant_projection_trace D h2 _ hEL mu _ hv0' hcyc P0 hP0 ((b.coord i).smulRight l)
        rw [Module.finrank_eq_card_basis b, LinearMap.trace_smulRight] at h5
        rw [h3, ← h4, LinearMap.llcomp_apply, ← map_smul, ← LinearMap.smul_apply, h5]
        simp [Module.Basis.coord_apply]
      rw [Finset.sum_congr rfl fun i _ => hterm i]
      conv_rhs => rw [← b.sum_repr l]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    · intro y hy
      have hWm : IsSubrepresentation E (isoSub E mu) := fun a c => isotypic_stable_under_gl_operator E mu a c
      have hEm := restrictRepresentation_isRep E hE _ hWm
      obtain ⟨P1, hP1⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEm)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hWm)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) := by
        intro a c g
        ext x
        simp
      have hzero : ∀ ξ : cyclicSubmodule E v0 →ₗ[K] K, P (ξ.smulRight y) = 0 := by
        intro ξ
        have h3 : ξ.smulRight y = LinearMap.llcomp K _ _ W (isoSub E mu).subtype
            (ξ.smulRight (⟨y, hy⟩ : isoSub E mu)) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEm) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) hT P1 P hP1 hP (ξ.smulRight (⟨y, hy⟩ : isoSub E mu))
        have hmem : ∀ x, P (ξ.smulRight y) x ∈ isoSub E mu := by
          intro x
          rw [h3, ← h4]
          simp
        have hv00 : P (ξ.smulRight y) ⟨v0, self_mem_cyclicSubmodule E v0⟩ = 0 := by
          by_contra h0
          have h6 := highest_vector_mem_isotypic E lam _ (equivariant_image_highest_vector _ E _ (hPe _) lam _ hv0' h0)
          exact h0 ((he.1 _ h6).symm.trans (he.2 mu hmu _ (hmem _)))
        ext x
        exact equivariant_kills_cyclic_of_zero _ E _ (hPe _) _ hv00 x (by rw [hcyc]; trivial)
      change ((Fintype.card ι : K) • Θ) y = e y
      rw [he.2 mu hmu y hy, LinearMap.smul_apply, hΘ]
      simp [hzero]
  have hm : m ∈ (⨆ mu, isoSub E mu) := by rw [isotypic_submodules_span_top D h2 n K W E hE]; trivial
  have := hle hm
  change ((Fintype.card ι : K) • Θ) m = e m at this
  rw [LinearMap.smul_apply, hΘ] at this
  exact this

theorem isotypicProjectorTheoremField_of_sharp_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorEllPBound) : IsotypicProjectorTheoremField D :=
  lattice_theorem_of_trace_formula D h2 h (isotypic_projector_trace_formula D h2)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem descPochhammer_succ_eval_right (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval x = (descPochhammer ℤ j).eval x * (x - j) := by
  rw [descPochhammer_succ_right]
  simp

theorem descPochhammer_succ_eval_add_one (j : ℕ) (x : ℤ) :
    (descPochhammer ℤ (j + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℤ j).eval x := by
  rw [descPochhammer_succ_left]
  simp

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem raise_lower_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) : E a b (E b a z) = E b a (E a b z) + (((mu a - mu b : ℤ)) : KK O) • z := by
  have hz' : z ∈ ⨅ c, LinearMap.ker (E c c - ((mu c : ℤ) : KK O) • (1 : Module.End (KK O) V)) := hz
  have hw : ∀ c, E c c z = ((mu c : ℤ) : KK O) • z := by
    intro c
    have h := (Submodule.mem_iInf _).mp hz' c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  have hc := congrArg (fun f : Module.End (KK O) V => f z) (hE.1 a b b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, eq_self_iff_true] at hc
  rw [hw a, hw b] at hc
  rw [← sub_eq_iff_eq_add', hc, Int.cast_sub, sub_smul]

theorem raise_lower_pow_commutator_on_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {mu : Fin n → ℤ} {z : V}
    (hz : z ∈ weightSp E mu) (r : ℕ) :
    E a b (((E b a) ^ r) z) = ((E b a) ^ r) (E a b z) +
      ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ (r - 1)) z := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : ∀ s x, E b a (((E b a) ^ s) x) = ((E b a) ^ (s + 1)) x := by
      intro s x
      rw [pow_succ', Module.End.mul_apply]
    have hy := integral_operator_pow_shifts_weight hE hz b a r
    have h0 := raise_lower_commutator_on_weight (a := a) (b := b) hE hy
    have hA : (mu + (r : ℤ) • rootW b a) a = mu a - r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    have hB : (mu + (r : ℤ) • rootW b a) b = mu b + r := by
      simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
    rw [hA, hB] at h0
    have e2 : ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • E b a (((E b a) ^ (r - 1)) z) =
        ((r : KK O) * ((((mu a - mu b : ℤ)) : KK O) - r + 1)) • ((E b a) ^ r) z := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h
        simp
      · rw [e1, Nat.sub_add_cancel h]
    rw [← e1, h0, ih, map_add, map_smul, e1, e2, Nat.add_sub_cancel, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem raise_pow_lower_pow_expansion {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) {nu : Fin n → ℤ} {y : V}
    (hy : y ∈ weightSp E nu) (k l : ℕ) :
    ((E a b) ^ k) (((E b a) ^ l) y) = ∑ j ∈ range (k + 1),
      ((((k.choose j * l.descFactorial j : ℕ)) : KK O) *
        (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O)) •
        ((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have step : ∀ j ∈ range (k + 1),
        E a b (((E b a) ^ (l - j)) (((E a b) ^ (k - j)) y)) =
          ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y) +
          (((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1)) •
            ((E b a) ^ (l - (j + 1))) (((E a b) ^ (k + 1 - (j + 1))) y) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hw := integral_operator_pow_shifts_weight hE hy a b (k - j)
      rw [raise_lower_pow_commutator_on_weight hE hab hw (l - j)]
      congr 1
      · rw [← Module.End.mul_apply (E a b), ← pow_succ', show k - j + 1 = k + 1 - j by omega]
      · rw [show l - j - 1 = l - (j + 1) by omega, show k + 1 - (j + 1) = k - j by omega]
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    simp only [map_smul]
    refine (Finset.sum_congr rfl (fun j hj => ?_)).trans
      (weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + k - l) : ℤ) : KK O))
        (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : KK O) *
          (((descPochhammer ℤ j).eval (nu a - nu b + ((k + 1 : ℕ) : ℤ) - l) : ℤ) : KK O))
        (fun j => ((l - j : ℕ) : KK O) * (((((nu + ((k - j : ℕ) : ℤ) • rootW a b) a -
              (nu + ((k - j : ℕ) : ℤ) • rootW a b) b : ℤ)) : KK O) - ((l - j : ℕ) : KK O) + 1))
        (fun j => ((E b a) ^ (l - j)) (((E a b) ^ (k + 1 - j)) y)) k ?_ ?_ ?_)
    · beta_reduce
      rw [step j hj]
    · simp
    · intro j hj
      beta_reduce
      have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
      have hA : (nu + ((k - j : ℕ) : ℤ) • rootW a b) a = nu a + ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm]
      have hB : (nu + ((k - j : ℕ) : ℤ) • rootW a b) b = nu b - ((k - j : ℕ) : ℤ) := by
        simp [rootW, Pi.single_apply, hab, hab.symm] <;> ring
      rw [hA, hB]
      have hx : nu a - nu b + ((k + 1 : ℕ) : ℤ) - (l : ℤ) = (nu a - nu b + (k : ℤ) - (l : ℤ)) + 1 := by
        push_cast
        ring
      rw [hx, descPochhammer_succ_eval_add_one, descPochhammer_succ_eval_right, Nat.choose_succ_succ, Nat.descFactorial_succ]
      have hch : (k.choose (j + 1) : KK O) * ((j : KK O) + 1) = (k.choose j : KK O) * ((k : KK O) - j) := by
        have := congrArg (Nat.cast : ℕ → KK O) (Nat.choose_succ_right_eq k j)
        push_cast [hjk] at this
        exact this
      generalize (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) = P
      by_cases hjl : j ≤ l
      · push_cast [hjk, hjl]
        linear_combination (((l : KK O) - j) * (l.descFactorial j : KK O) * (P : KK O)) * hch
      · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h0' : l - j = 0 := by omega
        simp [h0, h0']
    · simp [Nat.choose_succ_self]

theorem raise_lower_dividedPower_binomial [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {nu : Fin n → ℤ} {y : V} (hy : y ∈ weightSp E nu) (k l : ℕ) :
    divPowE E a b k (divPowE E b a l y) = ∑ j ∈ range (k + 1),
      if j ≤ l then ((Ring.choose (nu a - nu b + k - l) j : ℤ) : KK O) •
        divPowE E b a (l - j) (divPowE E a b (k - j) y) else 0 := by
  simp only [divPowE, LinearMap.smul_apply, map_smul]
  rw [raise_pow_lower_pow_expansion hE hab hy k l, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · simp only [smul_smul]
    congr 1
    have hP : (descPochhammer ℤ j).eval (nu a - nu b + (k : ℤ) - (l : ℤ)) =
        (j.factorial : ℤ) * Ring.choose (nu a - nu b + (k : ℤ) - (l : ℤ)) j := by
      first
      | rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
      | (rw [Ring.choose]; simp)
    rw [hP]
    have h1 : ((k.factorial : ℕ) : KK O) = (k.choose j : KK O) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : KK O) = ((l - j).factorial : KK O) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : KK O) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : KK O) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

