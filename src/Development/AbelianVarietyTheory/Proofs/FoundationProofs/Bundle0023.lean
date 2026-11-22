import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Mathlib
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finset_sum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExceptionalPrimesFiniteCardLe
section
open Finset

namespace GlobalTheory

theorem exceptional_primes_finite_card_le (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Set.Finite {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ∧
      Set.ncard {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ≤ 3 := by
  classical
  set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF
  have hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ) := by
    ext ℓ
    simp only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨⟨hp, ?_, hn⟩, h⟩
      by_contra hd
      rw [padicValNat.eq_zero_of_not_dvd hd] at h
      simp at h
      omega
    · rintro ⟨⟨hp, -, -⟩, h⟩
      exact ⟨hp, h⟩
  rw [hS]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  by_contra hc
  have hc4 : 4 ≤ F.card := by omega
  have h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n := by
    have e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    have hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n := by
      conv_rhs => rw [← e]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) :=
    Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le
  have h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have h4 : m ^ 4 ≤ m ^ F.card := Nat.pow_le_pow_right (by omega) hc4
  have h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left h1 4
  have h6 : n ^ 4 < m ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
  omega

theorem exceptional_set_count : Formalism.CyclotomicNorms.BBCount := by
  intro g hg
  have key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧
      Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3 := by
    intro d hd
    have h1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    exact exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)
  refine ⟨key, fun N => ?_⟩
  induction N with
  | zero =>
    have : Formalism.CyclotomicNorms.BB 0 g = {g} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, -⟩)
        · exact h
        · omega
      · exact Or.inl
    rw [this]
    simp
  | succ N ih =>
    have : Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge N d with h | h
          · obtain rfl : d = N + 1 := by omega
            exact Or.inr h3
          · exact Or.inl (Or.inr ⟨d, h1, h, h3⟩)
      · rintro ((h | ⟨d, h1, h2, h3⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨d, h1, by omega, h3⟩
        · exact Or.inr ⟨N + 1, by omega, le_rfl, h⟩
    rw [this]
    obtain ⟨hf, hc⟩ := key (N + 1) (by omega)
    refine ⟨ih.1.union hf, ?_⟩
    have := Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}
    have := ih.2
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
section
noncomputable section
open Polynomial
namespace GlobalTheory.K5.OnFree

section General

variable {R : Type*} [CommRing R] (f : R[X]) (m : ℕ) (c : R)

abbrev relIdeal : Ideal R[X][X] := Ideal.span {C f, X ^ m - C (C c)}

abbrev topPoly : (AdjoinRoot f)[X] := X ^ m - C (algebraMap R (AdjoinRoot f) c)

def toAdj : (R[X][X] ⧸ relIdeal f m c) →ₐ[R] AdjoinRoot (topPoly f m c) :=
  Ideal.Quotient.liftₐ (relIdeal f m c)
    (Polynomial.eval₂AlgHom
      (Polynomial.aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
      (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) (by
      have h : relIdeal f m c ≤ RingHom.ker (Polynomial.eval₂AlgHom
          (Polynomial.aeval (R := R) (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
          (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        constructor
        · have h1 : aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)) f = 0 := by
            rw [← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
              AdjoinRoot.mk_self, map_zero]
          simpa [RingHom.mem_ker] using h1
        · have h2 := AdjoinRoot.eval₂_root (topPoly f m c)
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h2
          simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow]
          change eval₂ _ _ X ^ m - eval₂ _ _ (C (C c)) = 0
          rw [eval₂_X, eval₂_C, RingHom.coe_coe, aeval_C,
            IsScalarTower.algebraMap_apply R (AdjoinRoot f)]
          exact h2
      exact fun a ha => h ha)

def baseToQuot : AdjoinRoot f →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (Ideal.Quotient.mk (relIdeal f m c) (C X)) (by
    have h : (Ideal.Quotient.mkₐ R (relIdeal f m c)) (C f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have h2 : aeval ((Ideal.Quotient.mkₐ R (relIdeal f m c)) (CAlgHom (R := R) (X : R[X]))) f = 0 := by
      rw [aeval_algHom_apply, aeval_algHom_apply, aeval_X_left_apply]
      exact h
    exact h2)

def toQuot : AdjoinRoot (topPoly f m c) →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom (topPoly f m c) (baseToQuot f m c)
    (Ideal.Quotient.mk (relIdeal f m c) X) (by
    have h : (Ideal.Quotient.mk (relIdeal f m c)) (X ^ m - C (C c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, AlgHom.commutes]
    rw [map_sub, map_pow] at h
    exact h)

theorem toQuot_root : toQuot f m c (AdjoinRoot.root _) = Ideal.Quotient.mk (relIdeal f m c) X := by
  simp [toQuot]

theorem toQuot_of_root : toQuot f m c (AdjoinRoot.of _ (AdjoinRoot.root f)) =
    Ideal.Quotient.mk (relIdeal f m c) (C X) := by
  have h : baseToQuot f m c (AdjoinRoot.root f) = Ideal.Quotient.mk (relIdeal f m c) (C X) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← h]
  simp [toQuot]

theorem toAdj_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) X) = AdjoinRoot.root _ := by
  change eval₂ _ _ X = _
  rw [eval₂_X]

theorem toAdj_C_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) (C X)) =
    AdjoinRoot.of _ (AdjoinRoot.root f) := by
  change eval₂ _ _ (C X) = _
  rw [eval₂_C, RingHom.coe_coe, aeval_X]

def adjEquiv : AdjoinRoot (topPoly f m c) ≃ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AlgEquiv.ofAlgHom (toQuot f m c) (toAdj f m c)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      refine Polynomial.algHom_ext' ?_ ?_
      · refine Polynomial.algHom_ext ?_
        have := toQuot_of_root f m c
        rw [← toAdj_C_X] at this
        exact this
      · have := toQuot_root f m c
        rw [← toAdj_X] at this
        exact this)
    (by
      refine AdjoinRoot.algHom_ext' ?_ ?_
      · refine AdjoinRoot.algHom_ext ?_
        have := toAdj_C_X f m c
        rw [← toQuot_of_root] at this
        exact this
      · have := toAdj_X f m c
        rw [← toQuot_root] at this
        exact this)

theorem exists_basis [Nontrivial R] (hf : f.Monic) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (hm : m ≠ 0) :
    ∃ b : Module.Basis (Fin d × Fin m) R (R[X][X] ⧸ relIdeal f m c),
      ∀ i j, b (i, j) = (Ideal.Quotient.mk (relIdeal f m c) (C X)) ^ (i : ℕ) *
        (Ideal.Quotient.mk (relIdeal f m c) X) ^ (j : ℕ) := by
  let b₁ : Module.Basis (Fin d) R (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr hd)
  have hb₁ : ∀ i, b₁ i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b₁, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _ (b₁.ne_zero ⟨0, hd0⟩)
  have hg : (topPoly f m c).Monic := monic_X_pow_sub_C _ hm
  have hgd : (topPoly f m c).natDegree = m := natDegree_X_pow_sub_C
  let b₂ : Module.Basis (Fin m) (AdjoinRoot f) (AdjoinRoot (topPoly f m c)) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hgd)
  have hb₂ : ∀ j, b₂ j = AdjoinRoot.root (topPoly f m c) ^ (j : ℕ) := by
    intro j
    simp only [b₂, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  refine ⟨(b₁.smulTower b₂).map (adjEquiv f m c).toLinearEquiv, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.smulTower_apply, hb₁, hb₂, Algebra.smul_def,
    AdjoinRoot.algebraMap_eq, ← toQuot_of_root, ← toQuot_root, ← map_pow (toQuot f m c),
    ← map_pow (toQuot f m c), ← map_mul, map_pow]
  rfl

end General

theorem on_free (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
      ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  rcases subsingleton_or_nontrivial (O0 p) with h | h
  · haveI : Subsingleton (On p n) := Module.subsingleton (O0 p) _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun _ _ => Subsingleton.elim _ _⟩
  · have hpos : 0 < p ^ n := pow_pos hp.out.pos n
    exact exists_basis (cyclotomic (p ^ n) (O0 p)) (p ^ n) (qO p) (cyclotomic.monic _ _) _
      (natDegree_cyclotomic _ _) (Nat.totient_pos.2 hpos) hpos.ne'

end GlobalTheory.K5.OnFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharParityMulNeOneMulInvNeOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dirichletCharacter_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  first | exact @GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | exact GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one | (intros; apply GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsChooseSmallPadicValAxInductionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_choose_small_padicVal_ax_induction : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N → ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  first | exact @GlobalTheory.exists_choose_small_valuation_ax | exact GlobalTheory.exists_choose_small_valuation_ax | (intros; apply GlobalTheory.exists_choose_small_valuation_ax; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspForms
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame.DualFrame

theorem mdiff_det {n : ℕ} {M : ℍ → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, MDiff fun τ => M τ a b) :
    MDiff fun τ => (M τ).det := by
  have : (fun τ => (M τ).det) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ a, (fun τ => M τ (σ a) a) := by
    ext τ; simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact MDifferentiable.sum fun σ _ => (MDifferentiable.prod fun a _ => hM _ _).const_smul _

variable {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)

def dualEntry (i j : Fin r) : ℍ → ℂ := fun τ => ModularForm.discriminant τ * (evM s w F τ)⁻¹ j i

variable {s w F}

theorem evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ}
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (i k : Fin r) :
    evM s w F (y • τ) i k = c i * evM s w F τ (π i) k * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  simp only [evM, Matrix.of_apply]
  calc (F k ∣[w k] s i) (y • τ)
      = (F k ∣[w k] s i) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w k) * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [mul_assoc, ← zpow_add₀ hJ]; simp
    _ = c i * (F k ∣[w k] s (π i)) τ * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [← slash_mul_apply, hc]; simp [smul_eq_mul]

theorem inv_evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (hA : (evM s w F τ).det ≠ 0)
    (i j : Fin r) :
    (evM s w F (y • τ))⁻¹ j i = denom (y : GL (Fin 2) ℝ) τ ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i) := by
  set J := denom (y : GL (Fin 2) ℝ) τ with hJdef
  have hJ : J ≠ 0 := denom_ne_zero _ _
  have key : (Matrix.of fun j i => J ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i)) * evM s w F (y • τ) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, evM_smul hc, ← hJdef]
    have h1 : ∀ l, J ^ (-w j) * c l * (evM s w F τ)⁻¹ j (π l) * (c l * evM s w F τ (π l) k * J ^ w k)
        = (J ^ (-w j) * J ^ w k) * ((evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k) := by
      intro l
      linear_combination (J ^ (-w j) * (evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k * J ^ w k) * hcc l
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, Equiv.sum_comp π (fun l => (evM s w F τ)⁻¹ j l * evM s w F τ l k), ← Matrix.mul_apply,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
    rcases eq_or_ne j k with rfl | hjk
    · rw [← zpow_add₀ hJ]; simp
    · simp [Matrix.one_apply_ne hjk]
  rw [Matrix.inv_eq_left_inv key]; rfl

theorem discriminant_smul (y : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (y • τ) = ModularForm.discriminant τ * denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant y) τ
  rw [ModularForm.SL_slash_apply] at h
  rw [← h, mul_assoc, ← zpow_add₀ hJ]; simp

theorem dualEntry_slash {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (i j : Fin r) : dualEntry s w F i j ∣[12 - w j] y = c i • dualEntry s w F (π i) j := by
  ext τ
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply]
  simp only [dualEntry, Pi.smul_apply, smul_eq_mul, discriminant_smul, inv_evM_smul hcc hc τ (hA τ)]
  have hJJ : denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w j) *
      denom (y : GL (Fin 2) ℝ) τ ^ (-(12 - w j)) = 1 := by
    rw [← zpow_add₀ hJ, ← zpow_add₀ hJ, show (12 : ℤ) + -w j + -(12 - w j) = 0 by ring, zpow_zero]
  linear_combination (c i * ModularForm.discriminant τ * (evM s w F τ)⁻¹ j (π i)) * hJJ

theorem dualEntry_slash_of_eq {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    {y γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {i i' : Fin r} (hy : s i * y = γ * s i') (j : Fin r) :
    dualEntry s w F i j ∣[12 - w j] y = dualEntry s w F i' j := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm y
  choose g hg hdec using hπ
  let c : Fin r → ℂ := fun l => if s l * y = g l * s (π l) then 1 else -1
  have hcc : ∀ l, c l * c l = 1 := by
    intro l; simp only [c]; split_ifs <;> norm_num
  have hc : ∀ l j, F j ∣[w j] (s l * y) = c l • F j ∣[w j] s (π l) := by
    intro l j
    by_cases hp : s l * y = g l * s (π l)
    · simp only [c, if_pos hp]
      rw [hp, (hF j).2.slash_mul (hg l), one_smul]
    · simp only [c, if_neg hp]
      rw [(hdec l).resolve_left hp, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul (hg l), neg_one_smul]
  have hπi : π i = i' := by
    apply hs.2 (π i) i' ((g i)⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem (hg i)) hγ)
    rcases hdec i with h | h
    · left; rw [mul_assoc, ← hy, h, inv_mul_cancel_left]
    · right; rw [mul_assoc, ← hy, h, mul_neg, neg_neg, inv_mul_cancel_left]
  have hp : s i * y = g i * s (π i) := by
    by_contra hp
    have h := (hdec i).resolve_left hp
    rw [hy, hπi, ← neg_mul] at h
    have h2 : γ = -g i := mul_right_cancel h
    apply hΓ
    have h3 : (-1 : SL(2, ℤ)) = γ * (g i)⁻¹ := by rw [h2, neg_mul, mul_inv_cancel]
    rw [h3]
    exact Γ.mul_mem hγ (Γ.inv_mem (hg i))
  rw [dualEntry_slash hcc hc hA, hπi]
  simp only [c, if_pos hp, one_smul]

theorem mdiff_dualEntry (hF : ∀ j, MDiff (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0) (i j : Fin r) :
    MDiff (dualEntry s w F i j) := by
  have e : dualEntry s w F i j = ModularForm.discriminant * ((fun τ => (evM s w F τ).det)⁻¹ *
      fun τ => ((evM s w F τ).updateRow i (Pi.single j 1)).det) := by
    ext τ
    simp [dualEntry, Matrix.inv_def, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine CuspForm.discriminant.holo'.mul (((mdiff_det_evM s w hF).inv hA).mul (mdiff_det fun a b => ?_))
  by_cases h : a = i
  · simp only [Matrix.updateRow_apply, if_pos h]
    exact mdifferentiable_const
  · simp only [Matrix.updateRow_apply, if_neg h]
    exact mdiff_slash (hF b) _ _

theorem exists_dual_cuspForms (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (hT : Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0)) :
    ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  let G : Fin r → ℍ → ℂ := fun j => dualEntry s w F j j ∣[12 - w j] (s j)⁻¹
  have hodd : ∀ j, Odd (12 - w j) := fun j => by
    obtain ⟨k, hk⟩ := (hF j).1
    exact ⟨5 - k, by omega⟩
  have hpos : ∀ j i, ∀ γ ∈ Γ, G j ∣[12 - w j] (γ * s i) = dualEntry s w F i j := by
    intro j i γ hγ
    simp only [G]
    rw [← SlashAction.slash_mul]
    exact dualEntry_slash_of_eq hΓ hs hF hA hγ (mul_inv_cancel_left _ _) j
  have hzero : ∀ i j, IsZeroAtImInfty (dualEntry s w F i j) := fun i j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT j) i
  refine ⟨G, fun j => ⟨fun γ hγ => ?_, mdiff_slash (mdiff_dualEntry (fun j => (hF j).2.2.1) hA j j) _ _,
    fun x => ?_⟩, fun τ => ?_⟩
  · obtain ⟨i, g, hg, h | h⟩ := hs.1 1
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (γ * g * s i) := by rw [mul_assoc, ← h, mul_one]
        _ = G j ∣[12 - w j] (g * s i) := by rw [hpos j i _ (Γ.mul_mem hγ hg), hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (-(γ * g * s i)) := by
            rw [mul_assoc, ← mul_neg, ← h, mul_one]
        _ = G j ∣[12 - w j] (-(g * s i)) := by
            rw [slash_neg_of_odd (hodd j), slash_neg_of_odd (hodd j), hpos j i _ (Γ.mul_mem hγ hg),
              hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
  · obtain ⟨i, g, hg, rfl | rfl⟩ := hs.1 x
    · rw [hpos j i g hg]; exact hzero i j
    · rw [slash_neg_of_odd (hodd j), hpos j i g hg]; exact (hzero i j).neg
  · have e : evM s (fun j => 12 - w j) G τ = (ModularForm.discriminant τ • (evM s w F τ)⁻¹).transpose := by
      ext i j
      have h := hpos j i 1 Γ.one_mem
      rw [one_mul] at h
      change (G j ∣[12 - w j] s i) τ = _
      rw [h]; rfl
    rw [e, Matrix.det_transpose, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) (inv_ne_zero (hA τ))

end GlobalTheory.OddFrame.DualFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCusps
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorValuationPrimeDvdPowSubOfFinitePaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  first | exact @GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | exact GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | (intros; apply GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntGeneratorsCardEqOfIsLatticePiStatement
section
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_span_generators_of_isLattice_pi : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E, (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | exact GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | (intros; apply GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (K : Subfield Ω), (∀ x ∈ K, x ≠ 0 → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k) → ∀ (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) → ∀ u ∈ A, (∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, x ∈ K) ∧ Q.eval ζ = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ x ∈ K) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified | exact GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified | (intros; apply GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified <;> assumption)
end

