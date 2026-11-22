import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveEvalTmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurjTens

variable {O σ ι : Type} [CommRing O]

open Classical in

def pushVars (j : σ → ι) (f : MvPowerSeries σ O) : MvPowerSeries ι O :=
  fun β => if h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β then coeff h.choose f else 0

theorem coeff_pushVars_mapDomain {j : σ → ι} (hj : Function.Injective j) (f : MvPowerSeries σ O)
    (α : σ →₀ ℕ) : coeff (Finsupp.mapDomain j α) (pushVars j f) = coeff α f := by
  have h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α := ⟨α, rfl⟩
  rw [coeff_apply]
  unfold pushVars
  rw [dif_pos h, Finsupp.mapDomain_injective hj h.choose_spec]

theorem coeff_pushVars_of_not {j : σ → ι} (f : MvPowerSeries σ O) (β : ι →₀ ℕ)
    (h : ¬∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β) : coeff β (pushVars j f) = 0 := by
  rw [coeff_apply]
  unfold pushVars
  rw [dif_neg h]

theorem pushVars_add {j : σ → ι} (hj : Function.Injective j) (f g : MvPowerSeries σ O) :
    pushVars j (f + g) = pushVars j f + pushVars j g := by
  ext β
  by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
  · obtain ⟨α, rfl⟩ := h
    simp only [map_add, coeff_pushVars_mapDomain hj]
  · simp only [map_add, coeff_pushVars_of_not _ _ h, add_zero]

theorem pushVars_monomial {j : σ → ι} (hj : Function.Injective j) (α : σ →₀ ℕ) (c : O) :
    pushVars j (monomial α c) = monomial (Finsupp.mapDomain j α) c := by
  classical
  ext β
  by_cases h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β
  · obtain ⟨α', rfl⟩ := h
    rw [coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff]
  · rw [coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]
    rintro rfl
    exact h ⟨α, rfl⟩

theorem pushVars_coe {j : σ → ι} (hj : Function.Injective j) (P : MvPolynomial σ O) :
    pushVars j (P : MvPowerSeries σ O) = ((MvPolynomial.rename j P : MvPolynomial ι O) : MvPowerSeries ι O) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial,
      pushVars_monomial hj]
  | add P Q hP hQ =>
    rw [MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add, MvPolynomial.coe_add]

theorem eval_coe {R A κ : Type} [CommRing R] [CommRing A] [Algebra R A] (z : κ → A)
    (E : MvPowerSeries κ R →ₐ[R] A) (hE : ∀ i, E (X i) = z i) (P : MvPolynomial κ R) :
    E (P : MvPowerSeries κ R) = MvPolynomial.aeval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem exists_eval_pushVars (p : ℕ) {A C : Type} [CommRing A] [CommRing C] [Algebra O A] [Algebra O C]
    [Fintype σ] [IsHausdorff (Ideal.span {(p : C)}) C] (j : σ → ι) (hj : Function.Injective j)
    (x : σ → A) (z : ι → C) (φ : A →ₐ[O] C) (evA : MvPowerSeries σ O →ₐ[O] A)
    (E : MvPowerSeries ι O →ₐ[O] C) (hA : IsEval p x evA) (hE : IsEval p z E)
    (hz : ∀ i, z (j i) = φ (x i)) (f : MvPowerSeries σ O) :
    E (pushVars j f) = φ (evA f) := by
  classical
  have hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P) := by
    intro P
    rw [pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hzj : z ∘ j = fun i => φ (x i) := funext hz
    rw [hzj]
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨N1, hN1⟩ := hE.2 m
  obtain ⟨N2, hN2⟩ := hA.2 m
  set N := max N1 N2
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPolynomial σ O := trunc' O n f
  set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)
  have hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0 := by
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have hgA : (p : A) ^ m ∣ evA g := hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))
  have hgE : (p : C) ^ m ∣ E (pushVars j g) := by
    apply hN1
    intro β hβ
    by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
    · obtain ⟨α, rfl⟩ := h
      rw [coeff_pushVars_mapDomain hj]
      apply hg
      rw [Finsupp.degree_mapDomain] at hβ
      exact lt_of_lt_of_le hβ (le_max_left _ _)
    · exact coeff_pushVars_of_not _ _ h
  have hgφ : (p : C) ^ m ∣ φ (evA g) := by
    have := map_dvd φ hgA
    simpa only [map_pow, map_natCast] using this
  have hf : f = g + (P : MvPowerSeries σ O) := by simp [g]
  have key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g) := by
    rw [hf, pushVars_add hj, map_add, map_add, map_add, hpoly P]
    ring
  rw [key]
  exact dvd_sub hgE hgφ

theorem surjective_eval_tmul : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  intro p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB
  have hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range := by
    intro a
    obtain ⟨f, rfl⟩ := sA a
    refine ⟨pushVars Sum.inl f, ?_⟩
    have := exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft
      evA E hA hE (fun i => by simp) f
    simpa using this
  have hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range := by
    intro b
    obtain ⟨g, rfl⟩ := sB b
    refine ⟨pushVars Sum.inr g, ?_⟩
    have := exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight
      evB E hB hE (fun i => by simp) g
    simpa using this
  intro t
  have : t ∈ E.range := by
    induction t using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      have h := Subalgebra.mul_mem _ (hl a) (hr b)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    | add s t hs ht => exact Subalgebra.add_mem _ hs ht
  exact this

end GlobalTheory.SurjTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInduct
section
namespace GlobalTheory.FinGL

open Formalism.L2.DIV Module

theorem finiteDimensional_coindV_blockTri {F : Type} [Field F] [Fintype F] {r : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) :
    FiniteDimensional ℂ (Representation.coindV (blockTri (κ := F) b).subtype σ) := by
  classical
  have : Finite (GL (Fin r) F) := inferInstance
  infer_instance

theorem nPos_parInd (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ) (ρ k : ℕ) (h : ρ + k + 1 ≤ r) :
    nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  have hfd := finiteDimensional_coindV_blockTri b σ
  induction ρ with
  | zero =>
    rw [GlobalTheory.T.symmetricPositionCharMultiplicity_eq_sum_degenerateWhittaker F ψ hψ r _ (parInd b σ) k (by omega)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal F ψ hψ r V b σ hσ j (Or.inl (by omega)), GlobalTheory.T.levi_whittaker_eq_one_of_cuspidal F ψ hψ r V b σ hσ, mul_one, mul_comm]
  | succ ρ ih =>
    rw [← GlobalTheory.T.symmetricPositionCharMultiplicity_succ_eq F ψ hψ r _ (parInd b σ) ρ k (by omega)]
    exact ih (by omega)

end GlobalTheory.FinGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

section Alg

variable {I R D : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing D] [Algebra R D]

omit [DecidableEq I] in

theorem mvAeval_add_of_mul_eq_zero (t n : I → D) (hn : ∀ i j, n i * n j = 0)
    (P : MvPolynomial I R) :
    MvPolynomial.aeval (fun i ↦ t i + n i) P =
      MvPolynomial.aeval t P + ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * n i := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]; ring
  | mul_X p j hp =>
    have h1 : (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * n j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hn, mul_zero]
    have h2 : ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
        (∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i) * t j +
          MvPolynomial.aeval t p * n j := by
      have h3 : ∀ i, MvPolynomial.aeval t (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * n i =
          MvPolynomial.aeval t (MvPolynomial.pderiv i p) * n i * t j +
            if j = i then MvPolynomial.aeval t p * n i else 0 := by
        intro i
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.aeval_X,
          MvPolynomial.pderiv_X, Pi.single_apply]
        split_ifs <;> simp <;> ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
    rw [map_mul, map_mul, hp, h2, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    linear_combination h1

theorem aeval_truncTotal_succ (N : ℕ) (t : I → D) (F : MvPowerSeries I R) :
    MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) F) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  have h : MvPowerSeries.truncTotal (N + 1) F =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F) := by
    ext d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, Finset.sum_ite_eq,
      Finset.mem_range, Finsupp.degree_eq_sum]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Algebra.smul_def]

omit [Fintype I] [DecidableEq I] in

theorem ideal_pow_eq_bot_of_prod {J : Ideal D} {k : ℕ}
    (h : ∀ s : Fin k → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) : J ^ k = ⊥ := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  rw [List.prod_ofFn]
  exact h _ fun a => (f a).2

omit [DecidableEq I] in

theorem aeval_pderiv_truncTotal_mul {J : Ideal D} {N : ℕ} (hJ : J ^ (N + 1) = ⊥) {t : I → D}
    (ht : ∀ i, t i ∈ J) {x : D} (hx : x ∈ J) (F : MvPowerSeries I R) (i : I) :
    MvPolynomial.aeval t (MvPolynomial.pderiv i (MvPowerSeries.truncTotal (N + 1) F)) * x =
      MvPolynomial.aeval t (MvPowerSeries.truncTotal (N + 1) (MvPowerSeries.pderiv R i F)) * x := by
  classical
  rw [← sub_eq_zero, ← sub_mul, ← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    Finset.sum_mul]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : N ≤ m.degree := by
    by_contra hlt
    refine MvPolynomial.mem_support_iff.1 hm ?_
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_truncTotal _
      (by rw [map_add, Finsupp.degree_single]; omega), MvPowerSeries.coeff_truncTotal _ (by omega),
      MvPowerSeries.coeff_pderiv, sub_self]
  have h1 : ∏ j, t j ^ m j ∈ J ^ N := by
    refine Ideal.pow_le_pow_right hdeg ?_
    rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (ht j) _
  have h2 : (∏ j, t j ^ m j) * x = 0 := by
    rw [← Ideal.mem_bot, ← hJ, pow_succ]
    exact Ideal.mul_mem_mul h1 hx
  rw [mul_assoc, h2, mul_zero]

end Alg

theorem taylor_add_of_mul_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  intro I _ _ D _ _ N t n hs hn f hf
  have key : ∀ (u : I → D) (g : (I → ℂ) → ℂ), AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N u g =
      MvPolynomial.aeval u (MvPowerSeries.truncTotal (N + 1) (GlobalTheory.taylor g)) := fun u g hg => by
    rw [aeval_truncTotal_succ, taylor_eq_sum_coeff_taylor N u g hg]
  rw [key _ _ hf, key _ _ hf, mvAeval_add_of_mul_eq_zero t n hn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key _ _ (GlobalTheory.analyticAt_fderiv_apply hf _), GlobalTheory.taylor_fderiv hf]
  exact aeval_pderiv_truncTotal_mul (ideal_pow_eq_bot_of_prod hs)
    (fun j => Ideal.subset_span (Or.inl ⟨j, rfl⟩)) (Ideal.subset_span (Or.inr ⟨i, rfl⟩)) _ i

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z + g z) = GlobalTheory.PeriodFamily.taylor N t f + GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (c : ℂ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ c * f z) = c • GlobalTheory.PeriodFamily.taylor N t f) ∧ (∀ c : ℂ, GlobalTheory.PeriodFamily.taylor N t (fun _ ↦ c) = algebraMap ℂ D c) ∧ (∀ f g : (I → ℂ) → ℂ, f =ᶠ[𝓝 0] g → GlobalTheory.PeriodFamily.taylor N t f = GlobalTheory.PeriodFamily.taylor N t g) ∧ (∀ (D' : Type) [CommRing D'] [Algebra ℂ D'] (ψ : D →ₐ[ℂ] D') (f : (I → ℂ) → ℂ), ψ (GlobalTheory.PeriodFamily.taylor N t f) = GlobalTheory.PeriodFamily.taylor N (fun i ↦ ψ (t i)) f) ∧ (∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N t f - algebraMap ℂ D (f 0) ∈ Ideal.span (Set.range t)) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_formal_properties | exact GlobalTheory.PeriodFamily.taylor_formal_properties | (intros; apply GlobalTheory.PeriodFamily.taylor_formal_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

section

variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]

theorem exists_prod_dvd_monomial (t : I → D) (k : ℕ) :
    ∀ m : I →₀ ℕ, k ≤ m.degree → ∃ s : Fin k → I, ∏ a, t (s a) ∣ ∏ i, t i ^ m i := by
  induction k with
  | zero => intro m _; exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro m hm
    have h : m ≠ 0 := by rintro rfl; simp at hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    obtain ⟨s, hs⟩ := ih m' (by rw [map_add, Finsupp.degree_single] at hm; omega)
    refine ⟨Fin.cons i s, ?_⟩
    have h1 : ∏ j, t j ^ (Finsupp.single i 1 : I →₀ ℕ) j = t i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finsupp.add_apply, pow_add,
      Finset.prod_mul_distrib, h1]
    exact mul_dvd_mul_left _ hs

variable [Algebra ℂ D]

theorem aeval_eq_zero_of_coeff_eq_zero {N : ℕ} {t : I → D}
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (P : MvPolynomial I ℂ)
    (hP : ∀ m : I →₀ ℕ, m.degree < N + 1 → P.coeff m = 0) : MvPolynomial.aeval t P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have h : N + 1 ≤ m.degree := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hm (hP m (by omega))
  obtain ⟨s, hs⟩ := exists_prod_dvd_monomial t (N + 1) m h
  rw [ht, zero_dvd_iff] at hs
  rw [hs, mul_zero]

omit [Algebra ℂ D] [CommRing D] in

theorem coeff_sum_monomial_finsuppAntidiag (N : ℕ) (F : MvPowerSeries I ℂ) (n : I →₀ ℕ)
    (hn : n.degree < N + 1) :
    MvPolynomial.coeff n (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) = MvPowerSeries.coeff n F := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← Finsupp.degree_eq_sum, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hn)]

theorem aeval_sum_monomial_finsuppAntidiag (N : ℕ) (t : I → D) (F : MvPowerSeries I ℂ) :
    MvPolynomial.aeval t (∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPolynomial.monomial m (MvPowerSeries.coeff m F)) =
      ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m F • ∏ i, t i ^ m i := by
  simp only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (t i))]

end

theorem taylor_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) =
        GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  intro I _ _ D _ _ N t ht f g hf hg
  change GlobalTheory.PeriodFamily.taylor N t (f * g) = _
  rw [GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ (hf.mul hg), GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hf, GlobalTheory.PeriodFamily.taylor_eq_sum_coeff_taylor N t _ hg,
    GlobalTheory.taylor_mul hf hg, ← aeval_sum_monomial_finsuppAntidiag,
    ← aeval_sum_monomial_finsuppAntidiag, ← aeval_sum_monomial_finsuppAntidiag, ← map_mul,
    ← sub_eq_zero, ← map_sub]
  refine aeval_eq_zero_of_coeff_eq_zero ht _ fun m hm => ?_
  rw [MvPolynomial.coeff_sub, coeff_sum_monomial_finsuppAntidiag _ _ _ hm, MvPolynomial.coeff_mul,
    MvPowerSeries.coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, map_add] at hm
  rw [coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega),
    coeff_sum_monomial_finsuppAntidiag _ _ _ (by omega)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlatStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  first | exact @GlobalTheory.PeriodFamily.taylor_remainder_and_flat | exact GlobalTheory.PeriodFamily.taylor_remainder_and_flat | (intros; apply GlobalTheory.PeriodFamily.taylor_remainder_and_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMap
section
open TopologicalSpace TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

section General

variable {R H : Type} [CommRing R] [Algebra ℂ R] [CommRing H] [Algebra ℂ H]

def redCoef (π : R →ₐ[ℂ] ℂ) : R ⊗[ℂ] H →ₐ[ℂ] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ H).comp π) (AlgHom.id ℂ H) (fun _ _ ↦ Commute.all _ _)

theorem redCoef_tmul (π : R →ₐ[ℂ] ℂ) (d : R) (y : H) :
    redCoef π (d ⊗ₜ[ℂ] y) = algebraMap ℂ H (π d) * y := by
  simp [redCoef, Algebra.TensorProduct.lift_tmul]

theorem sub_redCoef_mem (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] H) :
    x - 1 ⊗ₜ[ℂ] redCoef π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d y =>
    rw [redCoef_tmul]
    have e : d ⊗ₜ[ℂ] y - (1 : R) ⊗ₜ[ℂ] (algebraMap ℂ H (π d) * y) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) (d - algebraMap ℂ R (π d)) * ((1 : R) ⊗ₜ[ℂ] y) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  | add x y hx hy =>
    have e : x + y - 1 ⊗ₜ[ℂ] redCoef π (x + y) = (x - 1 ⊗ₜ[ℂ] redCoef π x) + (y - 1 ⊗ₜ[ℂ] redCoef π y) := by
      rw [map_add, TensorProduct.tmul_add]; abel
    rw [e]; exact Ideal.add_mem _ hx hy

end General

theorem fn_redCoef {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {R : Type} [CommRing R]
    [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] Hol W) {p : E} (hp : p ∈ W) :
    (redCoef π x).fn p = π (evT R p hp x) := by
  rw [← Hol.ev_apply p hp]
  change ((Hol.ev p hp).comp (redCoef π)) x = (π.comp (evT R p hp)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun d y ↦ ?_
  simp only [AlgHom.comp_apply, redCoef_tmul, evT, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.commutes,
    AlgHom.id_apply, Algebra.ofId_apply]
  simp

theorem taylor_red {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ)
    (t : I → R) (π : R →ₐ[ℂ] ℂ) (ht : ∀ i, π (t i) = 0) (f : (I → ℂ) → ℂ) :
    π (GlobalTheory.PeriodFamily.taylor N t f) = f 0 := by
  have h := GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t f
  have hle : Ideal.span (Set.range t) ≤ RingHom.ker π := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  have := hle h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  simpa using this

theorem taylor_reduces_to_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  intro I _ _ g R _ _ N t π ht W W₀ _ ρ hρ h h₀ hh₀
  have hq : redCoef π (ρ h) = h₀ := Hol.ext_fn fun p hp ↦ by
    rw [fn_redCoef π _ hp, hρ h p hp, taylor_red N t π ht, hh₀ p hp]
  have := sub_redCoef_mem (H := Hol W₀) π (ρ h)
  rwa [hq] at this

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValuesStatement
section
open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_holomorphic_ext_of_values : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  first | exact @GlobalTheory.tensor_hol_ext_of_values | exact GlobalTheory.tensor_hol_ext_of_values | (intros; apply GlobalTheory.tensor_hol_ext_of_values <;> assumption)
end

