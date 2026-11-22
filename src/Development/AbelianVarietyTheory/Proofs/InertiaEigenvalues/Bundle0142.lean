import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrdersStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLattices
section
noncomputable section

namespace GlobalTheory.StableLatCount

open GlobalTheory.UnitLemma Polynomial

theorem card_stable_lattices : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro O _ _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hres M₁ M₂ hM₁ hM₂ hs₁ hs₂
  have hdet : LinearMap.det (adE E g₁ g₂) = resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly :=
    GlobalTheory.T.det_commutator_map_eq_charpoly_resultant E A₁ A₂ (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₂)
  have hdet0 : LinearMap.det (adE E g₁ g₂) ≠ 0 := hdet ▸ hres
  have hunit : IsUnit (adE E g₁ g₂) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet0)
  have hbij : Function.Bijective ((adE E g₁ g₂).restrictScalars O) := by
    have := (Module.End.isUnit_iff _).1 hunit
    simpa only [LinearMap.coe_restrictScalars] using this
  have hN : ∀ x ∈ homLat E M₁ M₂, (adE E g₁ g₂) x ∈ homLat E M₁ M₂ := by
    intro ψ hψ x hx
    rw [adE_apply]
    exact M₁.sub_mem (hs₁ _ (hψ x hx)) (hψ _ (hs₂ x hx))
  have hL := GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top O E A₁ A₂ M₁ M₂ hM₁ hM₂
  have h2 := GlobalTheory.card_kernel_quot_of_bijective O _ (homLat E M₁ M₂) ((adE E g₁ g₂).restrictScalars O) hbij hN
  simp only [LinearMap.coe_restrictScalars] at h2
  rw [GlobalTheory.StableGraph.card_stable_eq_card_hom O A₁ A₂ g₁ g₂ M₁ M₂ hs₂, GlobalTheory.StableLatCount.card_commMaps_eq_card_homQuot O E A₁ A₂ g₁ g₂ M₁ M₂ hM₂ hs₁ hs₂, h2,
    GlobalTheory.LatIndexDet.card_quot_eq_pow_val O E _ (homLat E M₁ M₂) hL.1 hL.2 (adE E g₁ g₂) hdet0 hN, hdet]

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowers
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPowStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_overExt_integral_reduction_pow : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise

namespace GlobalTheory.UnramCocycle

theorem conj_mem_ine_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ

  have hmem : ∀ y : Ω, y ∈ g • A ↔ g⁻¹ y ∈ A := fun y =>
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
  have hgg : ∀ y : Ω, g⁻¹ (g y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine ⟨?_, fun x hx => ?_⟩
  · have h' : σ • (g • A) = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h', inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, hmem, hgg]
      exact (ValuationSubring.valuation_le_one_iff A x).1 hx
    have hy := hval (g x) hx'
    have e : (g⁻¹ * σ * g) x - x = g⁻¹ (σ (g x) - g x) := by
      rw [map_sub, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    rw [e]
    rw [valuation_lt_one_iff'] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨(hmem _).1 hy1, ?_⟩
    rcases hy2 with h0 | h0
    · left
      rw [h0, map_zero]
    · right
      rwa [← map_inv₀, ← hmem]

def kerSub {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : Subgroup Γ where
  carrier := {n | x.1 n = 0 ∧ ∀ m, ρ n m = m}
  one_mem' := ⟨by simpa using x.2.2 1 1, fun m => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [x.2.2, ha, hb]; simp, fun m => ?_⟩
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    · have h := x.2.2 a a⁻¹
      rw [mul_inv_cancel, h1, ha, ha', zero_add] at h
      exact h.symm
    · conv_lhs => rw [← ha' m]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem kerSub_normal {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : (kerSub ρ x).Normal where
  conj_mem := by
    intro n hn g
    obtain ⟨hx, hρ⟩ := hn
    have h1 : x.1 1 = 0 := by simpa using x.2.2 1 1
    refine ⟨?_, fun m => ?_⟩
    ·
      rw [x.2.2, x.2.2, hx, map_zero, add_zero, map_mul, Module.End.mul_apply, hρ, ← x.2.2,
        mul_inv_cancel, h1]
    · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hρ,
        ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem kerSub_isClosed {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (hρ : ContAction ρ) (x : Z1 ρ) :
    IsClosed (kerSub ρ x : Set Γ) := by

  have h1 : IsClosed {n : Γ | x.1 n = 0} := isClosed_eq x.2.1 continuous_const
  have hc : Continuous fun p : Γ × M => ρ p.1 p.2 := hρ
  have h2 : IsClosed {n : Γ | ∀ m, ρ n m = m} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun m =>
      isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact h1.inter h2

theorem vanish_on_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ ρ hρ A S htriv x hx
  have := kerSub_normal ρ x

  have hle : NS Ω S ≤ kerSub ρ x := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ (kerSub_isClosed ρ hρ x)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hσ
    obtain ⟨v, hv, B, hB, hσB⟩ := hσ

    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hB
    have hσ' : σ ∈ Ine (F := F) (g • A.1 v) := by rw [hg, mem_Ine]; exact hσB
    have hc := conj_mem_ine_of_smul (A.1 v) g σ hσ'

    have hzero : x.1 (g⁻¹ * σ * g) = 0 := by
      have hu := hx v hv
      unfold Formalism.GaloisCohomology.unrAt H1ur at hu
      rw [LinearMap.mem_ker] at hu
      unfold resH1 at hu
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hu
      obtain ⟨m, hm⟩ := hu
      have hmem : g⁻¹ * σ * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hc
      have h := hm ⟨⟨g⁻¹ * σ * g, hmem⟩, (Subgroup.mem_subgroupOf).2 hc⟩

      have h' : x.1 (g⁻¹ * σ * g) = ρ (g⁻¹ * σ * g) m - m := h
      rw [htriv v hv (A.1 v) (A.2 v) _ hc, sub_self] at h'
      exact h'
    have hk : g⁻¹ * σ * g ∈ kerSub ρ x := ⟨hzero, htriv v hv (A.1 v) (A.2 v) _ hc⟩
    have h := (kerSub_normal ρ x).conj_mem _ hk g
    have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rwa [e] at h
  exact fun n hn => hle hn

end GlobalTheory.UnramCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapEqOfContinuousAdicCompletionIso
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PlaceOver

open Filter Topology

theorem isOpen_valuation_lt_one {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : P.adicCompletion F | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion F) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem valuation_lt_one_of_continuous {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
    {P : HeightOneSpectrum (𝓞 F)} {P' : HeightOneSpectrum (𝓞 F')}
    (i : P.adicCompletion F →+* P'.adicCompletion F') (hi : Continuous i)
    {x : P.adicCompletion F} (hx : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have hU : {y : P'.adicCompletion F' | Valued.v y < 1} ∈ 𝓝 (i 0) := by
    rw [map_zero]
    exact (isOpen_valuation_lt_one P').mem_nhds (by simp)
  have hV := hi.continuousAt.preimage_mem_nhds hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hV
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by
    simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hγ0)
  have hxn : x ^ n ∈ i ⁻¹' {y : P'.adicCompletion F' | Valued.v y < 1} := by
    apply hγ
    show Valued.v.restrict (x ^ n) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
    exact hn
  have h1 : Valued.v (i x) ^ n < 1 := by simpa [map_pow] using hxn
  by_contra h
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 h)))

end GlobalTheory.PlaceOver

namespace GlobalTheory.PlaceOver

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (P.adicCompletion F) k) = P.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem comap_eq_of_continuous_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  intro E E' _ _ _ _ _ w w' i hi hc
  have hle : w.asIdeal ≤ w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    intro e he
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) (e : E)) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w e).2 he
    have h2 := valuation_lt_one_of_continuous (i : w.adicCompletion E →+* w'.adicCompletion E') hi h1
    have h3 : (i : w.adicCompletion E →+* w'.adicCompletion E') (algebraMap E (w.adicCompletion E) (e : E)) =
        algebraMap E' (w'.adicCompletion E') (algebraMap E E' (e : E)) := hc _
    rw [h3, valued_algebraMap] at h2
    exact h2
  exact (w.isMaximal.eq_of_le (Ideal.comap_ne_top _ w'.isPrime.ne_top) hle).symm

end GlobalTheory.PlaceOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniqueUpToIsoStatement
section
open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_unique_up_to_iso : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  first | exact @GlobalTheory.Pat.isCplAt_unique | exact GlobalTheory.Pat.isCplAt_unique | (intros; apply GlobalTheory.Pat.isCplAt_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_orbit_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjectiveStatement
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_inertia_surjective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ v : ℤ_[l]ˣ, ∃ σ ∈ Ine (F := ℚ) A, cycZ (F := ℚ) (Ω := Ω) l σ = v := by
  first | exact @GlobalTheory.CycInertia.cycZ_Ine_surjective | exact GlobalTheory.CycInertia.cycZ_Ine_surjective | (intros; apply GlobalTheory.CycInertia.cycZ_Ine_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacterPadic_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  first | exact @GlobalTheory.Cyc.cyc_basic | exact GlobalTheory.Cyc.cyc_basic | (intros; apply GlobalTheory.Cyc.cyc_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZeroStatement
section
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | exact GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero | (intros; apply GlobalTheory.UnitLemma.TraceDet.det_trace_pow_mul_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdAllPowOfFrobeniusEqKilledByPerfectPoints
section
open scoped NNReal

namespace GlobalTheory.PointsKey

def oneSubMul {R : Type} [CommRing R] (u : R) : Submonoid R where
  carrier := {x | ∃ r, x = 1 - u * r}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b - u * a * b, by ring⟩
  one_mem' := ⟨0, by simp⟩

theorem dvd_of_one_sub_mul {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by
  have hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m := by
    rw [mul_comm, geom_sum_mul_neg]
  refine ⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩
  calc D = (1 - (u * r) ^ m) * D + (u * r) ^ m * D := by ring
    _ = (∑ i ∈ Finset.range m, (u * r) ^ i) * ((1 - u * r) * D) + (u * r) ^ m * D := by
        rw [← hg]; ring
    _ = _ := by rw [h]; ring

theorem key : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h heq hpts m j
  set S := oneSubMul u with hS
  let R' := Localization S
  let φ : R →+* R' := algebraMap R R'
  have hl' : ((l : ℕ) : R') = 0 := by rw [← map_natCast φ, hl, map_zero]
  have hu' : φ u ∈ nonZeroDivisors R' := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    have hx' : φ u * IsLocalization.mk' R' a s = 0 := by rw [mul_comm]; exact hx
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hta : (t : R) * a = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hu
      exact hu _ (by rw [← ht]; ring)
    exact (IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩
  have hunit : ∀ r', IsUnit (1 - φ u * r') := by
    intro r'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
    obtain ⟨b, hb⟩ := s.2
    have hmem : (s : R) - u * a ∈ S := ⟨b + a, by rw [hb]; ring⟩
    have hsp := IsLocalization.mk'_spec R' a s
    have : (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a) := by
      rw [map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]
    exact isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)
  have heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j) := by
    intro j; simpa [map_sum, map_mul, map_pow] using congrArg φ (heq j)
  have hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0 := by
    intro j O _ _ _ _ _ f h1 h2 h3
    exact hpts O (f.comp φ) h1 h2 h3 j
  have hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n := fun j M =>
    GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M
  obtain ⟨y, hy⟩ := GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h2 : φ (D j * s) = φ (u ^ m * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S R').1 h2
  obtain ⟨r, hr⟩ := (t * s).2
  refine dvd_of_one_sub_mul u r (D j) (t * a) m ?_
  rw [← hr]
  simp only [Submonoid.coe_mul]
  linear_combination ht

end GlobalTheory.PointsKey
end

