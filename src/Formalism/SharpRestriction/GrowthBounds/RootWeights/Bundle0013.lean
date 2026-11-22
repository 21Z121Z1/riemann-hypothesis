import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0008
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringWordWeightOrNMinus
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0010

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_extremal_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (π : Module.End K V) (hπ : IsWtProj E 0 π)
    (ord : List (Fin n × Fin n)) (hord : NormalOrder n ord) (T : ℕ) (hT : Module.finrank K V ≤ T) :
    Inv = pp E 0 ord T * π := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hkill := nontrivial_isotypic_weight_zero_killed hE hs
  obtain ⟨_, h5b, h5c⟩ := h5 K V n E hE 0 (by
    intro a b hab
    have : (a : ℕ) < (b : ℕ) := hab
    simp only [Pi.zero_apply]
    omega) ord hord T hT
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    intro mu x hx
    rw [LinearMap.mem_eqLocus, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hx0, hxr⟩ := hinv x hx
      rw [hInv.1 x hx, hπ.1 x hx0, h5c x hx0 hxr]
    · rw [hInv.2 mu hmu x hx, hkill _ π hπ h5b mu hmu x hx]
  have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus Inv (pp E 0 ord T * π) := by
    rw [← htop]
    exact iSup_le hle
  exact LinearMap.ext fun x => this (Submodule.mem_top (x := x))

theorem invariant_projection_denominator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZLattice E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L : ℕ)
    (hL : ∀ (k : ℕ) (a b : Fin n), a ≠ b → weightSp E 0 ≠ ⊥ → weightSp E ((k : ℤ) • rootW a b) ≠ ⊥ → k ≤ L)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * deF p n L)) • Inv x ∈ M := by
  have hcz := dvr_fraction_field_charZero_prime S hG.prime
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨ord, hord⟩ := exists_normalOrder n
  have hπ : IsWtProj E 0 (Θ 0) := by
    constructor
    · intro y hy
      rw [hΘ2 0 0 y hy, if_pos rfl]
    · intro nu hnu y hy
      rw [hΘ2 0 nu y hy, if_neg hnu]
  rw [invariant_projection_extremal_formula D h2 h5 E hE Inv hInv (Θ 0) hπ ord hord _ le_rfl, Module.End.mul_apply, ← normal_order_length_eq hord]
  exact (extremal_projector_lattice_scaled_mem S hG.prime (gl_rep_shifts_weights hE) hM.1 L hL ord hord.2.1 _ _
    (binomial_subring_preserves_lattice hM.1 _ (hΘ1 0) x hx) (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x)).1

theorem root_multiple_apply_first {n : ℕ} (a b : Fin n) (hab : a ≠ b) (k : ℕ) : ((k : ℤ) • rootW a b) a = k := by
  simp [rootW, Pi.single_apply, hab]

private theorem bddAbove_root_multiples_in_weights {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ a b, a ≠ b ∧ (k : ℤ) • rootW a b ∈ wtsOf E (⊤ : Submodule K V)} := by
  classical
  have hfin : (wtsOf E (⊤ : Submodule K V)).Finite := by
    have hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite := fun a =>
      (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn
    refine (Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_
    intro mu hmu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro a
    have hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥ := hmu
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu'
    have hxw := (Submodule.mem_inf.1 hx).1
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw
    have h3 := hxw a
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩
  have hfin2 : ((fun p : (Fin n → ℤ) × Fin n => (p.1 p.2).toNat) ''
      (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n)))).Finite :=
    (hfin.prod Set.finite_univ).image _
  refine hfin2.bddAbove.mono ?_
  rintro k ⟨a, b, hab, h⟩
  refine ⟨((k : ℤ) • rootW a b, a), ⟨h, Set.mem_univ _⟩, ?_⟩
  show (((k : ℤ) • rootW a b) a).toNat = k
  rw [root_multiple_apply_first a b hab k]
  simp

theorem invariant_denominator_sharp_of (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) : InvariantDenominatorEllPBound := by
  unfold InvariantDenominatorEllPBound
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv x hx
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  refine invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx
  intro k a b hab h0 hk
  rw [hMQ]
  unfold ellP
  refine le_csSup (bddAbove_root_multiples_in_weights E) ⟨a, b, hab, ?_⟩
  show weightSp E _ ⊓ ⊤ ≠ ⊥
  rwa [inf_top_eq]

private theorem bddAbove_root_multiples_in_weight_differences {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧
      mu - nu = (k : ℤ) • rootW a b} := by
  classical
  have hfin : (wtsOf E (⊤ : Submodule K V)).Finite := by
    have hA : ∀ a : Fin n, {m : ℤ | (E a a).HasEigenvalue (m : K)}.Finite := fun a =>
      (Module.End.finite_hasEigenvalue (E a a)).preimage Int.cast_injective.injOn
    refine (Set.Finite.pi (t := fun a => {m : ℤ | (E a a).HasEigenvalue (m : K)}) hA).subset ?_
    intro mu hmu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    intro a
    have hmu' : weightSp E mu ⊓ ⊤ ≠ ⊥ := hmu
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu'
    have hxw := (Submodule.mem_inf.1 hx).1
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hxw
    have h3 := hxw a
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h3, hx0⟩
  have hfin2 : ((fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) ''
      (wtsOf E (⊤ : Submodule K V) ×ˢ (wtsOf E (⊤ : Submodule K V) ×ˢ (Set.univ : Set (Fin n))))).Finite :=
    (hfin.prod (hfin.prod Set.finite_univ)).image _
  refine hfin2.bddAbove.mono ?_
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩
  refine ⟨(mu, nu, a), ⟨hmu, hnu, Set.mem_univ _⟩, ?_⟩
  have h1 := congrFun h a
  simp [rootW, Pi.single_apply, hab] at h1
  show (mu a - nu a).toNat = k
  omega

theorem invariant_projection_lemma_of (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h5 : adm5 D) : InvariantProjectionField D := by
  unfold InvariantProjectionField
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  refine ⟨fun π hπ ord hord T hT => invariant_projection_extremal_formula D h2 h5 E hE Inv hInv π hπ ord hord T hT, fun x hx => ?_⟩
  refine invariant_projection_denominator D h2 h5 p n' O S hG n V E hE M hM Inv hInv _ ?_ x hx
  intro k a b hab h0 hk
  rw [hMQ]
  unfold ellOf
  refine le_csSup (bddAbove_root_multiples_in_weight_differences E) ⟨(k : ℤ) • rootW a b, ?_, 0, ?_, a, b, hab, sub_zero _⟩
  · show weightSp E _ ⊓ ⊤ ≠ ⊥
    rwa [inf_top_eq]
  · show weightSp E 0 ⊓ ⊤ ≠ ⊥
    rwa [inf_top_eq]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.MonomialsAreWeightVectors
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem v2con_X_pderiv {R : Type*} [CommRing R] {σ : Type*} (v w : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : R)) := by
  rw [pderiv_monomial, show (X v : MvPolynomial σ R) = monomial (Finsupp.single v 1) 1 from rfl,
    monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem v2con_X_pderiv_self {R : Type*} [CommRing R] {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    (X v : MvPolynomial σ R) * pderiv v (monomial m c) = monomial m (c * (m v : R)) := by
  rw [v2con_X_pderiv]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [tsub_add_cancel_of_le hle]

theorem v2con_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : R) * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply]
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : l ∈ S <;> by_cases h2 : LL.vec l = true <;>
    simp [h1, h2, -pderiv_monomial, v2con_X_pderiv_self, mul_comm]

theorem v2con_coeff_diag {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (glAct R LL S a a x) = ((wtS LL S m a : ℤ) : R) * coeff m x := by
  classical
  induction x using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [v2con_diag, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem monomials_are_weight_vectors : MonomialsAreWeightVectors := by
  intro R _ _ ι _ LL n S
  constructor
  · intro m c
    rw [weightSp, Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    change glAct R LL S a a (monomial m c) - _ = 0
    rw [v2con_diag, smul_monomial, smul_eq_mul, sub_self]
  · intro ν x hx m hm
    rw [weightSp, Submodule.mem_iInf] at hx
    funext a
    have h := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    have h2 := congrArg (coeff m) h
    change coeff m (glAct R LL S a a x) = _ at h2
    rw [v2con_coeff_diag, coeff_smul, smul_eq_mul] at h2
    have hc : coeff m x ≠ 0 := mem_support_iff.mp hm
    have h3 := mul_right_cancel₀ hc h2
    exact_mod_cast h3

theorem v2con_stable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (N : ℕ) (a b : Fin n) (x : MvPolynomial (ι × Fin n) R)
    (hx : x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N}) :
    glAct R LL S a b x ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
  classical
  rw [mem_restrictSupport_iff] at hx
  have hmono : ∀ (m' : ι × Fin n →₀ ℕ) (c' : R), m'.degree ≤ N →
      monomial m' c' ∈ restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m' c' hm'
    rw [mem_restrictSupport_iff]
    intro y hy
    have := Finset.mem_singleton.mp (support_monomial_subset hy)
    subst this
    exact hm'
  have hterm : ∀ (m : ι × Fin n →₀ ℕ) (c : R) (u w : ι × Fin n), m.degree ≤ N →
      (X u : MvPolynomial (ι × Fin n) R) * pderiv w (monomial m c) ∈
        restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ N} := by
    intro m c u w hm
    rw [v2con_X_pderiv]
    by_cases h0 : m w = 0
    · simp [h0]
    · apply hmono
      have hle : Finsupp.single w 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have e1 : (m - Finsupp.single w 1).degree + 1 = m.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, Finsupp.degree_single] at this
        exact this
      rw [map_add, Finsupp.degree_single]
      omega
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hdeg : m.degree ≤ N := hx hm
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun l _ => ?_)
  split_ifs
  · exact hterm m _ _ _ hdeg
  · rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hterm m _ _ _ hdeg)
  · exact Submodule.zero_mem _

theorem polynomial_locally_finite : PolynomialLocallyFinite := by
  intro R _ ι _ LL n S x
  classical
  refine ⟨restrictSupport R {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree}, ?_, ?_, ?_⟩
  · haveI : Finite {m : ι × Fin n →₀ ℕ | m.degree ≤ x.totalDegree} :=
      (Finsupp.finite_of_degree_le x.totalDegree).to_subtype
    exact Module.Finite.of_basis (basisRestrictSupport R _)
  · rw [mem_restrictSupport_iff]
    intro m hm
    show m.degree ≤ x.totalDegree
    rw [Finsupp.degree_apply]
    exact le_totalDegree hm
  · intro a b y hy
    exact v2con_stable LL S _ a b y hy

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerMonomial
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section ops

variable {K : Type} [Field K] {σ : Type}

def polarizationOperator (K : Type) [Field K] {σ : Type} (v w : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X v)) ∘ₗ (pderiv w).toLinearMap

theorem polarization_monomial (v w : σ) (m : σ →₀ ℕ) (c : K) :
    polarizationOperator K v w (monomial m c) = monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  show X v * pderiv w (monomial m c) = _
  rw [pderiv_monomial, X, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem polarization_pow_monomial (v w : σ) (hvw : v ≠ w) (k : ℕ) (m : σ →₀ ℕ) (c : K) :
    (polarizationOperator K v w ^ k) (monomial m c) =
      monomial (m - Finsupp.single w k + Finsupp.single v k) (c * ((m w).descFactorial k : K)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, polarization_monomial]
    have hw : (m - Finsupp.single w k + Finsupp.single v k : σ →₀ ℕ) w = m w - k := by
      simp [Finsupp.single_apply, hvw]
    have hexp : (m - Finsupp.single w k + Finsupp.single v k - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) = m - Finsupp.single w (k + 1) + Finsupp.single v (k + 1) := by
      ext x
      by_cases hx : x = w
      · rw [hx]
        simp [Finsupp.single_apply, hvw]
        omega
      · by_cases hy : x = v
        · rw [hy]
          simp [Finsupp.single_apply, hvw, Ne.symm hvw]
          omega
        · simp [Finsupp.single_apply, Ne.symm hx, Ne.symm hy]
    rw [hexp, hw, Nat.descFactorial_succ, Nat.cast_mul]
    congr 1
    ring

theorem polarization_divided_power_monomial [CharZero K] (v w : σ) (hvw : v ≠ w) (k : ℕ) (m : σ →₀ ℕ) (c : K) :
    ((k.factorial : K)⁻¹) • (polarizationOperator K v w ^ k) (monomial m c) =
      monomial (m - Finsupp.single w k + Finsupp.single v k) (c * ((m w).choose k : K)) := by
  rw [polarization_pow_monomial v w hvw, MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  congr 1
  have : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [smul_eq_mul]
  field_simp

theorem polarization_commute (v w v' w' : σ) (h1 : w ≠ v') (h2 : w ≠ w') (h3 : w' ≠ v) :
    Commute (polarizationOperator K v w) (polarizationOperator K v' w') := by
  show polarizationOperator K v w * polarizationOperator K v' w' = polarizationOperator K v' w' * polarizationOperator K v w
  refine LinearMap.ext fun f => ?_
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [Module.End.mul_apply, Module.End.mul_apply, polarization_monomial, polarization_monomial,
      polarization_monomial, polarization_monomial]
    have e1 : (m - Finsupp.single w' 1 + Finsupp.single v' 1 : σ →₀ ℕ) w = m w := by
      simp [Finsupp.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]
    have e2 : (m - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) w' = m w' := by
      simp [Finsupp.single_apply, h3, Ne.symm h2, Ne.symm h3, h2]
    have hexp : (m - Finsupp.single w' 1 + Finsupp.single v' 1 - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) =
        m - Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w' 1 + Finsupp.single v' 1 := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases a1 : w = x <;> by_cases a2 : w' = x <;> by_cases a3 : v = x <;>
        by_cases a4 : v' = x <;> (try subst_vars) <;> (try simp_all) <;> omega
    rw [e1, e2, hexp]
    congr 1
    ring
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq]

end ops

section fact

variable {σ : Type}

theorem exponent_factorial_erase_single (m : σ →₀ ℕ) (v : σ) (j : ℕ) :
    expFact (m.erase v + Finsupp.single v j) = expFact (m.erase v) * j.factorial := by
  have hd : Disjoint (m.erase v).support (Finsupp.single v j).support :=
    Finset.disjoint_of_subset_right Finsupp.support_single_subset
      (Finset.disjoint_singleton_right.mpr (by simp))
  unfold expFact
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]

theorem exponent_factorial_add_single (m : σ →₀ ℕ) (v : σ) (k : ℕ) :
    expFact (m + Finsupp.single v k) * (m v).factorial = expFact m * (m v + k).factorial := by
  have h1 : m + Finsupp.single v k = m.erase v + Finsupp.single v (m v + k) := by
    ext x
    by_cases hx : x = v
    · subst hx
      simp
    · simp [Finsupp.erase_ne hx, Finsupp.single_apply, Ne.symm hx]
  have h2 : expFact m = expFact (m.erase v) * (m v).factorial := by
    conv_lhs => rw [← Finsupp.erase_add_single v m]
    exact exponent_factorial_erase_single m v (m v)
  rw [h1, exponent_factorial_erase_single, h2]
  ring

theorem exponent_factorial_ne_zero_of (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

theorem padic_exponent_factorial_bound (p : ℕ) [Fact p.Prime] (m : σ →₀ ℕ) (v w : σ) (hvw : v ≠ w) (k : ℕ) (hk : k ≤ m w) :
    padicValNat p (expFact m) ≤ 2 * padicValNat p ((m w).choose k) +
      padicValNat p (expFact (m - Finsupp.single w k + Finsupp.single v k)) := by
  have hC : (m w).choose k ≠ 0 := (Nat.choose_pos hk).ne'
  set a := m - Finsupp.single w k with ha
  have haw : a w = m w - k := by simp [ha]
  have hav : a v = m v := by simp [ha, Finsupp.single_apply, Ne.symm hvw]
  have hm : a + Finsupp.single w k = m := by
    ext x
    by_cases hx : x = w
    · subst hx
      simp [ha]
      omega
    · simp [ha, Finsupp.single_apply, Ne.symm hx]
  have e1 := exponent_factorial_add_single a w k
  rw [hm, haw, Nat.sub_add_cancel hk] at e1
  have e2 := exponent_factorial_add_single a v k
  rw [hav] at e2
  have f1 : expFact m = expFact a * (m w).choose k * k.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hk
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m w - k))
    rw [e1, ← this]
    ring
  have f2 : expFact (a + Finsupp.single v k) = expFact a * (m v + k).choose k * k.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k (m v))
    rw [Nat.add_sub_cancel] at this
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (m v))
    rw [e2, ← this]
    ring
  have hdvd : expFact m ∣ (m w).choose k ^ 2 * expFact (a + Finsupp.single v k) := by
    rw [f1, f2]
    exact ⟨(m w).choose k * (m v + k).choose k, by ring⟩
  have hne : (m w).choose k ^ 2 * expFact (a + Finsupp.single v k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _)
  have hle := (padicValNat_dvd_iff_le (p := p) hne).mp ((pow_padicValNat_dvd (p := p)).trans hdvd)
  rw [padicValNat.mul (pow_ne_zero _ hC) (exponent_factorial_ne_zero_of _), padicValNat.pow] at hle
  exact hle

end fact

end Formalism.MainNotions.G.GLWeightTheory
end
end

