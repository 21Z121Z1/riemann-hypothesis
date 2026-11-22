import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.MatrixActionLinear

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem actM_add (A : Fin n → Fin n → Module.End ℂ M) (X Y : Mx n) : actM A (X + Y) = actM A X + actM A Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul (A : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Mx n) : actM A (c • X) = c • actM A X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actM_single (A : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : actM A (Matrix.single a b 1) = A a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Ne.symm hc]
  · simp

end PositivityTheory.CW.MatrixActionLinear

namespace PositivityTheory.CW

open MatrixActionLinear in
theorem e3b : faceMap_castSucc_comp_eq_succ := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m
  haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup
  haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul

  let P : Module.End ℂ (kfin ε σ) → Prop := fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)
  have hone : P 1 := ⟨1, fun v => rfl⟩
  have hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, h₁, h₂, _root_.add_apply]
  have hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁.comp D₂, fun v => ?_⟩
    rw [Module.End.mul_apply, h₁, h₂]
    rfl
  have hzero : P 0 := ⟨0, fun v => by simp⟩
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hgen : ∀ a b, P (A a b) := by
    intro a b
    obtain ⟨h1, h2, h3, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
    set X₁ := cpart1 ε (Matrix.single a b 1)
    set X₂ := cpart2 ε (Matrix.single a b 1)
    have hX₁ : X₁ ∈ lieSet ε := h1
    have hX₂ : X₂ ∈ lieSet ε := h2
    have eA : A a b = actM A X₁ + Complex.I • actM A X₂ := by
      rw [← actM_single A a b, h3, actM_add, actM_smul]
    refine ⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩
    have hv : IsKFin ε σ (v : H) := v.2
    rw [eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v,
      hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]
    rfl
  have hcas : P (casimirK ε A) := by
    unfold casimirK
    exact hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)
  have hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hadd _ _ hone hcas)
  exact hpow m

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.HighestWeightKernel

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem inner_compact (hU : IsInfUnitary ε E) {a b : Fin n} (h : ε a = ε b) (x y : V) :
    ⟪E b a x, y⟫_ℂ = ⟪x, E a b y⟫_ℂ := by
  have := hU b a x y
  simpa [adjSign, h.symm] using this

theorem exists_hull (hL : LocFin ε E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ IsKStableSub ε E Y ∧ W ≤ Y := by
  classical
  choose S hSfin hSmem hSk using hL
  let bW := Module.finBasis ℂ W
  let Y : Submodule ℂ V := ⨆ i, S (bW i : V)
  haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _
  refine ⟨Y, Submodule.finite_iSup _, ?_, ?_⟩
  · intro a b hab v hv
    refine Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_
    · intro i x hx
      exact (le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  · intro w hw
    have hrep := bW.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V) := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw']
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    exact (le_iSup (fun i => S (bW i : V)) i) (hSmem _)

theorem inner_casimirK (hU : IsInfUnitary ε E) (w : V) :
    ⟪w, casimirK ε E w⟫_ℂ =
      ((∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))
  have hba : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]
  first
    | rfl
    | simp
    | norm_cast

theorem mem_ker_iff (μ : ℝ) (x : V) :
    x ∈ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V)) ↔ casimirK ε E x = (μ : ℂ) • x := by
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem sq_le_of_khw (hU : IsInfUnitary ε E) {w : V} (hw0 : w ≠ 0) {μ : ℝ} (hwμ : casimirK ε E w = (μ : ℂ) • w)
    {Λ : Fin n → ℝ} (hkw : IsKHWVec ε E Λ w) : (∑ a, Λ a ^ 2) ≤ μ := by
  have h1 := inner_casimirK hU w
  rw [hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    exact h1
  have h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a) := by simp
    have hle := Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem
    have hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2 := by
      rw [hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linarith
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [← Finset.sum_mul] at h3
  nlinarith

theorem mem_of_eig (hgl : IsGlRep E) (hU : IsInfUnitary ε E) (hL : LocFin ε E)
    (h3 : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
      ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w)
    (hint : ∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z)
    {Y : Submodule ℂ V} (hYk : IsKStableSub ε E Y) {μ : ℝ}
    (hY : ∀ (w : V) (Λ : Fin n → ℤ), IsKHWVec ε E (fun a => ((Λ a : ℤ) : ℝ)) w →
      (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ μ → w ∈ Y)
    {v : V} (hv : Eig ε E μ v) : v ∈ Y := by
  classical
  have key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k →
      IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Z hZf hZk hZs hZc
      by_cases hZ0 : Z = ⊥
      · rw [hZ0]
        exact bot_le
      obtain ⟨w, Λ, hwZ, hw0, hkw⟩ := h3 Z hZf hZs hZ0
      have hΛ : ∀ a, ∃ z : ℤ, Λ a = z := fun a => hint w a (Λ a) hw0 (hkw.1 a)
      choose Λz hΛz using hΛ
      have hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w := by
        have : Λ = fun a => ((Λz a : ℤ) : ℝ) := funext hΛz
        rw [← this]
        exact hkw
      have hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ := sq_le_of_khw hU hw0 (hZc w hwZ) hkw'
      have hwY : w ∈ Y := hY w Λz hkw' hsq
      let Kw : Submodule ℂ V := sInf {T | w ∈ T ∧ IsKStableSub ε E T}
      have hKwS : IsKStableSub ε E Kw := by
        intro a b hab x hx
        rw [Submodule.mem_sInf] at hx ⊢
        intro T hT
        exact hT.2 a b hab x (hx T hT)
      have hwKw : w ∈ Kw := Submodule.mem_sInf.2 (fun T hT => hT.1)
      have hKwZ : Kw ≤ Z := sInf_le ⟨hwZ, hZs⟩
      have hKwY : Kw ≤ Y := sInf_le ⟨hwY, hYk⟩
      haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ
      have hZ'lt : Kwᗮ ⊓ Z < Z := by
        refine lt_of_le_of_ne inf_le_right (fun h => ?_)
        have hwZ' : w ∈ Kwᗮ ⊓ Z := by
          rw [h]
          exact hwZ
        have h0 : ⟪w, w⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1
        exact hw0 (inner_self_eq_zero.1 h0)
      haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z) := by
        intro a b hab x hx
        refine ⟨?_, hZs a b hab x hx.2⟩
        show E a b x ∈ Kwᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← inner_compact hU hab]
        exact Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1
      have hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k :=
        hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt
      have hZ'le : Kwᗮ ⊓ Z ≤ Y :=
        ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)
      have hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z :=
        Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ
      rw [← hsplit]
      exact sup_le hKwY hZ'le
  obtain ⟨S, hSf, hvS, hSk⟩ := hL v
  haveI : FiniteDimensional ℂ S := hSf
  let Z : Submodule ℂ V := S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))
  have hZk : IsKStableSub ε E Z := by
    intro a b hab x hx
    refine ⟨hSk a b hab x hx.1, ?_⟩
    have hx2 := (mem_ker_iff μ x).1 hx.2
    refine (mem_ker_iff μ _).2 ?_
    have hc := ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab
    have := congrArg (fun U : Module.End ℂ V => U x) hc
    simp only [Module.End.mul_apply] at this
    rw [this, hx2, map_smul]
  exact key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk
    (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩

end PositivityTheory.CW.HighestWeightKernel

namespace PositivityTheory.CW

open PositivityTheory.CW.HighestWeightKernel

theorem k_types_finite_of_highest_weight (h : KStableHighestWeightVector) : KTypesBoundedFinite := by
  classical
  intro n ε V _ _ E hgl hU hL hfinHW hint R
  let F : Set (Fin n → ℤ) := {Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}
  have hFfin : F.Finite := by
    refine (Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
    intro Λ hΛ a _
    have hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R := by
      refine le_trans ?_ hΛ
      exact Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ a)
    have h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq (Λ a)
    have h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by
      have := Int.le_self_sq (-(Λ a))
      rw [neg_sq] at this
      exact_mod_cast this
    have hc := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  haveI : Finite F := hFfin.to_subtype
  let W0 : Submodule ℂ V :=
    ⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}
  haveI : ∀ Λ : F, FiniteDimensional ℂ
      (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _
  haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _
  obtain ⟨Y, hYf, hYk, hWY⟩ := exists_hull hL W0
  haveI : FiniteDimensional ℂ Y := hYf
  refine Submodule.finiteDimensional_of_le (S₂ := Y) ?_
  refine Submodule.span_le.2 ?_
  rintro v ⟨μ, hμR, hv⟩
  refine mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv
  intro w Λ hkw hsq
  have hΛF : Λ ∈ F := le_trans hsq hμR
  exact hWY ((le_iSup (fun Λ : F => Submodule.span ℂ
    {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive
section
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end

