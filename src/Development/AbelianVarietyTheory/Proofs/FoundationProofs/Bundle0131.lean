import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.coef_of_inv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  intro Ω _ _ ε X l _ _ N w b c hb γ _ hinv
  obtain ⟨hslP, -, -, hev, -⟩ := mon_expand ℤ_[l] w
  have hk : ∀ (u : Fin 2 → ℤ_[l]) (k : Fin (w + 1)),
      (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 ^ (k : ℕ) * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 ^ (w - (k : ℕ)) =
        ∑ i, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) * (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) := by
    intro u k
    rw [← hev, mZl, ← Betti.eval_slP, hslP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hev]
  have key : ∀ u : Fin 2 → ℤ_[l], b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) •
      ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
    intro u
    rw [← congrFun hinv u]
    show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = _
    rw [Betti.toGQ_sl, hb, map_sum]
    simp_rw [map_smul, hk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hz := GlobalTheory.homogeneous_poly_coeff_eq_zero l (X.Khat l)
    (fun a x ha hx => GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree Ω ε X l a x ha hx) w
    (fun i => c i - ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
    (by intro u; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← hb u, ← key u, sub_self])
  intro i
  exact sub_eq_zero.1 (congrFun hz i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob : (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧ (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧ ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  first | exact @GlobalTheory.FN.cmp_props | exact GlobalTheory.FN.cmp_props | (intros; apply GlobalTheory.FN.cmp_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRootStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 → ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  first | exact @GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | exact GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | (intros; apply GlobalTheory.PsRoot.coeff_mem_range_of_isRoot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobeniusStatement
section
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  first | exact @GlobalTheory.normOp_iterate_congr | exact GlobalTheory.normOp_iterate_congr | (intros; apply GlobalTheory.normOp_iterate_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquivStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_H1_H2_equiv_of_continuous_mulEquiv : ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  first | exact @GlobalTheory.contCohomology_transport_mulEquiv | exact GlobalTheory.contCohomology_transport_mulEquiv | (intros; apply GlobalTheory.contCohomology_transport_mulEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundaryStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | exact GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem | (intros; apply GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwine
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem translate_mem_aug_of_not_intertwine {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (J : Set G) (θ : G → ℂ) (u : V) (hu : IsEig π J θ u) (y j : G) (hj : j ∈ J) (hc : y * j * y⁻¹ ∈ J)
    (hne : θ j ≠ θ (y * j * y⁻¹)) : π y u ∈ aug π J θ := by
  have h1 : π (y * j * y⁻¹) (π y u) = θ j • π y u := by
    have : π (y * j * y⁻¹) (π y u) = π y (π j u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [this, hu j hj, map_smul]
  have h2 : (θ j - θ (y * j * y⁻¹)) • π y u ∈ aug π J θ := by
    apply Submodule.subset_span
    exact ⟨_, hc, π y u, by rw [h1, sub_smul]⟩
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h2

theorem eig_eq_zero_of_mem_aug_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ →
    Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) →
    ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ hJ hN hy u hu he
  classical
  obtain ⟨R, h1, hR, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ N _ hN u hu
  simp only [inv_one, one_smul] at hs
  refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ J θ hJ).1 u ?_ he
  rw [← Finset.sum_filter_add_sum_filter_not R (fun y => y ∈ J ∧ θ y = 1)] at hs
  have hA : ∑ y ∈ R.filter (fun y => y ∈ J ∧ θ y = 1), π y u
      = ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro y hy'
    obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hy'
    rw [he y a, b, one_smul]
  have hB : ∑ y ∈ R.filter (fun y => ¬ (y ∈ J ∧ θ y = 1)), π y u ∈ aug π J θ := by
    refine Submodule.sum_mem _ fun y hy' => ?_
    obtain ⟨a, b⟩ := Finset.mem_filter.mp hy'
    obtain ⟨j, hj, hc, hne⟩ := (hy y (hR y a)).resolve_left b
    exact translate_mem_aug_of_not_intertwine π J θ u he y j hj hc hne
  have hc : ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, Finset.mem_filter.mpr ⟨h1, hJ.one, hJ.val_one⟩⟩
  rw [← Submodule.smul_mem_iff _ hc, ← hA, eq_neg_of_add_eq_zero_left hs]
  exact Submodule.neg_mem _ hB

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqUnitMulPowCyclotomicUniformizer
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.UnitPow

theorem eq_unit_mul_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  intro p _ Ω _ _ hclo T b hb hb0
  obtain ⟨n, ι, w, hn, hemb, hw, hmem⟩ := GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq p Ω hclo T b hb
  obtain ⟨hdom, hdvr, hirr⟩ := GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel p n hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hw, map_zero])
  obtain ⟨k, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hirr
  refine ⟨n, k, hn, ι (ε : On p n), hmem _, ι ((ε⁻¹ : (On p n)ˣ) : On p n), hmem _, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← hw, hε, map_mul, map_pow, map_sub, map_one, hemb.1]

end GlobalTheory.K5.UnitPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.DenseAlg

theorem exists_mem_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
    (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a) := by
  intro Ω _ _ _ p _ A Ωl _ _ hclo j hA k e he halg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a, ha, hc⟩ := GlobalTheory.K5.Dense.exists_cong p Ωl hclo Ω j k e he halg
  exact ⟨a, (hA a).2 ha, hc⟩

end GlobalTheory.K5.DenseAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAutAll
section
noncomputable section

namespace GlobalTheory.K5.Rel

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def IsGen (T : Tower p Ω) (m s : ℕ) (τ γ : Gal p Ω) : Prop :=
  (∀ n, τ (T.ζ n) = T.ζ n) ∧ (∀ n, τ (T.qq n) = T.ζ n ^ (p ^ s) * T.qq n) ∧
  (∀ n, γ (T.ζ n) = T.ζ n ^ (1 + p ^ m)) ∧ ∀ n, γ (T.qq n) = T.qq n

def Infl1 (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ G, ∀ t ∈ Hinf T, w (g * t) = w g ∧ t (w g) = w g

def Infl2 (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ G, ∀ h ∈ G, ∀ t ∈ Hinf T, ∀ t' ∈ Hinf T,
    ξ (g * t) (h * t') = ξ g h ∧ t (ξ g h) = ξ g h

def CobI (T : Tower p Ω) (G : Subgroup (Gal p Ω)) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k))
    (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k G w ∧ Infl1 T G w ∧ ∀ g ∈ G, ∀ h ∈ G,
    Cong p k (ξ g h) (((χ g).val : Ω) * g (w h) - w (g * h) + w g)

def relInv (ξ : Gal p Ω → Gal p Ω → Ω) (τ γ : Gal p Ω) (a : ℕ) : Ω :=
  ξ γ τ - ξ (τ ^ a) γ - ∑ i ∈ Finset.Ico 1 a, ξ (τ ^ i) τ

def relD (τ γ : Gal p Ω) (a : ℕ) (x y : Ω) : Ω :=
  (a : Ω) * γ x - ∑ i ∈ Finset.range a, (τ ^ i) x + y - (τ ^ a) y

theorem gal_zeta (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.ζ n) = T.ζ n ^ e := by
  obtain ⟨χ, h⟩ := Basic.exists_isCyc T n
  exact ⟨_, h g⟩

theorem gal_qq (T : Tower p Ω) (g : Gal p Ω) (n : ℕ) : ∃ e : ℕ, g (T.qq n) = T.ζ n ^ e * T.qq n := by
  obtain ⟨a, h⟩ := Basic.exists_isKum_qq T n
  exact ⟨_, h g trivial⟩

theorem conj_mem_Gn (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Gn T n) :
    g⁻¹ * u * g ∈ Gn T n := by
  obtain ⟨e, he⟩ := gal_zeta T g n
  obtain ⟨f, hf⟩ := gal_qq T g n
  have h1 : u (g (T.ζ n)) = g (T.ζ n) := by rw [he, map_pow, (mem_Gn.1 hu).1]
  have h2 : u (g (T.qq n)) = g (T.qq n) := by
    rw [hf, map_mul, map_pow, (mem_Gn.1 hu).1, (mem_Gn.1 hu).2]
  refine mem_Gn.2 ⟨?_, ?_⟩
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1]; exact g.symm_apply_apply _
  · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h2]; exact g.symm_apply_apply _

theorem normal_Gn (T : Tower p Ω) (n : ℕ) : (Gn T n).Normal :=
  ⟨fun u hu g => by simpa using conj_mem_Gn T n g⁻¹ hu⟩

theorem conj_mem_Hinf (T : Tower p Ω) (g : Gal p Ω) {u : Gal p Ω} (hu : u ∈ Hinf T) :
    g⁻¹ * u * g ∈ Hinf T :=
  Subgroup.mem_iInf.2 fun n => conj_mem_Gn T n g (Hinf_le T n hu)

theorem normal_Hinf (T : Tower p Ω) : (Hinf T).Normal :=
  ⟨fun u hu g => by simpa using conj_mem_Hinf T g⁻¹ hu⟩

theorem gal_mem_FixI (T : Tower p Ω) (g : Gal p Ω) {x : Ω} (hx : x ∈ FixI (Hinf T)) :
    g x ∈ FixI (Hinf T) := by
  refine ⟨int_gal g hx.1, fun t ht => ?_⟩
  have := hx.2 _ (conj_mem_Hinf T g ht)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
  conv_rhs => rw [← this]
  exact (g.apply_symm_apply _).symm

theorem Gn_le_Gms (T : Tower p Ω) {m s n : ℕ} (hm : m ≤ n) (hs : s ≤ n) : Gn T n ≤ Gms T m s := by
  intro g hg
  refine (Basic.mem_gms T m s g).2 ⟨?_, ?_⟩
  · rw [← TraceTower.zeta_pow' T hm, map_pow, (mem_Gn.1 hg).1]
  · rw [← TraceTower.qq_pow' T hs, map_pow, (mem_Gn.1 hg).2]

theorem Gn_anti (T : Tower p Ω) {m n : ℕ} (hm : m ≤ n) : Gn T n ≤ Gn T m := Gn_le_Gms T hm hm

theorem Hinf_le_Gms (T : Tower p Ω) (m s : ℕ) : Hinf T ≤ Gms T m s := fun g hg =>
  (Basic.mem_gms T m s g).2 ⟨(mem_Hinf.1 hg m).1, (mem_Hinf.1 hg s).2⟩

theorem FixI_Gms_le (T : Tower p Ω) (m s : ℕ) : FixI (Gms T m s) ≤ FixI (Hinf T) :=
  fun _ hx => ⟨hx.1, fun g hg => hx.2 g (Hinf_le_Gms T m s hg)⟩

theorem cong_fix (hΩ : IsClo p Ω) (G : Subgroup (Gal p Ω)) {k : ℕ} {x y : Ω} (hx : x ∈ FixI G)
    (hy : y ∈ FixI G) (h : Cong p k x y) : ∃ z ∈ FixI G, x - y = (p : Ω) ^ k * z := by
  obtain ⟨z, hz, e⟩ := h
  haveI := Basic.charZero_of_isClo hΩ
  refine ⟨z, ⟨hz, fun g hg => ?_⟩, e⟩
  have h0 : ((p : Ω) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply mul_left_cancel₀ h0
  have := (sub_mem hx hy).2 g hg
  rwa [e, map_mul, map_pow, map_natCast] at this

variable {T : Tower p Ω} {m s : ℕ} {τ γ : Gal p Ω}

theorem IsGen.tau_mem (h : IsGen T m s τ γ) : τ ∈ Gms T m s :=
  (Basic.mem_gms T m s τ).2 ⟨h.1 m, by rw [h.2.1, (T.prim s).pow_eq_one, one_mul]⟩

theorem IsGen.gam_mem (h : IsGen T m s τ γ) : γ ∈ Gms T m s :=
  (Basic.mem_gms T m s γ).2 ⟨by rw [h.2.2.1, pow_add, (T.prim m).pow_eq_one, mul_one, pow_one], h.2.2.2 s⟩

theorem IsGen.tau_pow_zeta (h : IsGen T m s τ γ) (b n : ℕ) : (τ ^ b) (T.ζ n) = T.ζ n := by
  induction b with
  | zero => rfl
  | succ b ih => rw [pow_succ, AlgEquiv.mul_apply, h.1, ih]

theorem IsGen.tau_pow_qq (h : IsGen T m s τ γ) (b n : ℕ) :
    (τ ^ b) (T.qq n) = T.ζ n ^ (p ^ s * b) * T.qq n := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, AlgEquiv.mul_apply, h.2.1, map_mul, map_pow, h.tau_pow_zeta, ih]; ring

theorem IsGen.gam_pow_zeta (h : IsGen T m s τ γ) (c n : ℕ) :
    (γ ^ c) (T.ζ n) = T.ζ n ^ ((1 + p ^ m) ^ c) := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, AlgEquiv.mul_apply, h.2.2.1, map_pow, ih, ← pow_mul, ← pow_succ]

theorem IsGen.gam_pow_qq (h : IsGen T m s τ γ) (c n : ℕ) : (γ ^ c) (T.qq n) = T.qq n := by
  induction c with
  | zero => rfl
  | succ c ih => rw [pow_succ, AlgEquiv.mul_apply, h.2.2.2, ih]

theorem IsGen.rel (h : IsGen T m s τ γ) : (τ ^ (1 + p ^ m) * γ)⁻¹ * (γ * τ) ∈ Hinf T := by
  refine mem_Hinf.2 fun n => ⟨?_, ?_⟩
  · rw [AlgEquiv.mul_apply]
    apply (τ ^ (1 + p ^ m) * γ).injective
    refine ((τ ^ (1 + p ^ m) * γ).apply_symm_apply _).trans ?_
    simp only [AlgEquiv.mul_apply, h.1, h.2.2.1, map_pow, h.tau_pow_zeta]
  · rw [AlgEquiv.mul_apply]
    apply (τ ^ (1 + p ^ m) * γ).injective
    refine ((τ ^ (1 + p ^ m) * γ).apply_symm_apply _).trans ?_
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h.2.1, h.2.2.2, map_mul, map_pow, h.2.2.1, h.2.2.2,
      h.tau_pow_qq, ← pow_mul, mul_comm (p ^ s)]

theorem exists_aut_all (hΩ : IsClo p Ω) (T : Tower p Ω) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ g : Gal p Ω, ∀ n, g (T.ζ n) = T.ζ n ^ a ∧ g (T.qq n) = T.ζ n ^ b * T.qq n := by
  classical
  by_contra hcon
  push_neg at hcon
  choose lv hlv using hcon
  obtain ⟨F, hF⟩ := gal_finite_subcover p Ω hΩ (fun g => {T.ζ (lv g), T.qq (lv g)})
  obtain ⟨σ, h1, h2⟩ := TraceTower.exists_aut hΩ T (F.sup lv + 1) (by omega) a b ha
  obtain ⟨g, hg, hS⟩ := hF σ
  have hle : lv g ≤ F.sup lv + 1 := (Finset.le_sup hg).trans (Nat.le_succ _)
  have e1 : σ (T.ζ (lv g)) = T.ζ (lv g) ^ a := by
    rw [← TraceTower.zeta_pow' T hle, map_pow, h1, ← pow_mul, ← pow_mul, mul_comm]
  have e2 : σ (T.qq (lv g)) = T.ζ (lv g) ^ b * T.qq (lv g) := by
    rw [← TraceTower.zeta_pow' T hle, ← TraceTower.qq_pow' T hle, map_pow, h2, mul_pow, ← pow_mul,
      ← pow_mul, mul_comm b]
  exact hlv g (by rw [← hS _ (by simp), e1]) (by rw [← hS _ (by simp), e2])

theorem exists_isGen (hΩ : IsClo p Ω) (T : Tower p Ω) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ τ γ : Gal p Ω, IsGen T m s τ γ := by
  have hp : p.Prime := Fact.out
  obtain ⟨τ, hτ⟩ := exists_aut_all hΩ T 1 (p ^ s) hp.not_dvd_one
  obtain ⟨γ, hγ⟩ := exists_aut_all hΩ T (1 + p ^ m) 0 (by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h))
  exact ⟨τ, γ, fun n => by simpa using (hτ n).1, fun n => (hτ n).2, fun n => (hγ n).1,
    fun n => by simpa using (hγ n).2⟩

end GlobalTheory.K5.Rel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoboundaryOfSubsingletonContCohomologyThreStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_subsingleton_contCohomology_three : ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  first | exact @GlobalTheory.exists_coboundary_of_subsingleton_Hn_three | exact GlobalTheory.exists_coboundary_of_subsingleton_Hn_three | (intros; apply GlobalTheory.exists_coboundary_of_subsingleton_Hn_three <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImageStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_mul_eq_reparametrization_image : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 → ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  first | exact @GlobalTheory.GeoFix.exists_inR_mul_eq_psi | exact GlobalTheory.GeoFix.exists_inR_mul_eq_psi | (intros; apply GlobalTheory.GeoFix.exists_inR_mul_eq_psi <;> assumption)
end

