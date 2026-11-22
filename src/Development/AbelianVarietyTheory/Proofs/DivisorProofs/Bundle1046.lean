import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MarkEll

theorem star_mulVec_dot {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (A *ᵥ (M *ᵥ b)) = star a ⬝ᵥ ((Mᴴ * A * M) *ᵥ b) := by
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem normSq_eq_of_form {n : ℕ} (Γ A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hΓ : Γᴴ * A * Γ = (c : ℂ) • A)
    (x : Fin n → ℂ) (w : ℂ) (hx : Γ *ᵥ x = w • x) (h0 : star x ⬝ᵥ (A *ᵥ x) ≠ 0) : ‖w‖ ^ 2 = c := by
  have h := star_mulVec_dot Γ A x x
  rw [hΓ, hx] at h
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  rw [← mul_assoc] at h
  have h2 : w * star w = (c : ℂ) := mul_right_cancel₀ h0 h
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h3

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := Polynomial.aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem eigA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : G.C) (v : InfinitePlace G.F) (z : ℂ),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).eval₂ v.embedding z = 0 →
    ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v g *ᵥ x = z • x := by
  intro p _ G g v z hdeg hz
  letI alg : Algebra G.F ℂ := v.embedding.toAlgebra
  have halg : ∀ a : G.F, algebraMap G.F ℂ a = v.embedding a := fun a => rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun a => by
        change G.psi v (algebraMap G.F G.C a) = _
        rw [G.psi_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply, halg] }
  let Θ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  have hinj : Function.Injective Θ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Θ.toRingHom).resolve_right
      (by haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩; exact not_subsingleton _)
  set x : ℂ ⊗[G.F] G.C := (1 : ℂ) ⊗ₜ[G.F] g with hx
  have hxi : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  have hge := natDegree_minpoly_le_tmul ℂ g hxi
  have hΘx : Θ x = G.psi v g := by
    rw [hx]
    first
      | (erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl)
      | (show (Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)) 1 * ψF g = G.psi v g
         rw [map_one, one_mul]; rfl)
      | simp [Θ, ψF]
  have hmin : minpoly ℂ (G.psi v g) = minpoly ℂ x := by rw [← hΘx]; exact minpoly.algHom_eq Θ hinj x
  have hgi : IsIntegral G.F g := IsIntegral.of_finite G.F g
  have hdvd : minpoly ℂ (G.psi v g) ∣ (minpoly G.F g).map (algebraMap G.F ℂ) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (ψF g) (minpoly G.F g) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmon : ((minpoly G.F g).map (algebraMap G.F ℂ)).Monic := (minpoly.monic hgi).map _
  have heq : (minpoly G.F g).map (algebraMap G.F ℂ) = minpoly ℂ (G.psi v g) := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ?_) hmon hdvd ?_
    · exact IsIntegral.of_finite ℂ _
    · rw [Polynomial.natDegree_map, hmin]; exact hge
  have hroot : (minpoly ℂ (Matrix.toLin' (G.psi v g))).IsRoot z := by
    rw [Matrix.minpoly_toLin', ← heq, Polynomial.IsRoot, Polynomial.eval_map]
    exact hz
  obtain ⟨y, hy⟩ := (Module.End.hasEigenvalue_iff_isRoot.mpr hroot).exists_hasEigenvector
  refine ⟨y, hy.2, ?_⟩
  have := hy.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem normSq_of_eigenvector {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ) (ha : G.a = 1)
    (hm : P.Mark μ) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx0 : x ≠ 0) (w : ℂ)
    (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  obtain ⟨-, -, hΓ⟩ := GlobalTheory.LKMid.pair_form_laws p G P v
  obtain ⟨Z, hZ⟩ := GlobalTheory.LKMid.Pair.gram_psi_inv_congr p G P v
  set A := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hAdef
  set Γ := G.psi v P.γ with hΓdef
  have hΓ' : Γᴴ * A * Γ = ((((P.c : ℚ) : ℝ)) : ℂ) • A := by rw [hΓ]; push_cast; rfl
  have cong : ∀ a b : Fin G.n → ℂ, star a ⬝ᵥ (A *ᵥ b) =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a) ⬝ᵥ (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b)) := by
    intro a b; rw [star_mulVec_dot, ← hZ]
  have Zne : ∀ a : Fin G.n → ℂ, a ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a ≠ 0 := by
    intro a ha h
    apply ha
    have := congrArg (fun y => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  have hc0 : ((((P.c : ℚ) : ℝ)) : ℂ) ≠ 0 := by
    have : ((P.c : ℚ)) ≠ 0 := P.c.ne_zero
    exact_mod_cast this
  rcases G.sig v with ⟨h1, -⟩ | ⟨h0, -⟩
  · obtain ⟨v0, hv0, x0, hx0e, hpos⟩ := hm
    have hv : v = v0 := by
      have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := by
        have := ha; unfold HTGroup.a at this; omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hcard
      exact congrArg Subtype.val (Subsingleton.elim (⟨v, h1⟩ : {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1})
        ⟨v0, hv0⟩)
    subst hv
    have hS0 : star x0 ⬝ᵥ (A *ᵥ x0) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hμ : ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := normSq_eq_of_form Γ A _ hΓ' x0 μ hx0e hS0
    by_cases hw : w = μ
    · rw [hw]; exact hμ
    · have hS : star x0 ⬝ᵥ (A *ᵥ x) = 0 := by
        by_contra hne
        have h := star_mulVec_dot Γ A x0 x
        rw [hΓ', hx0e, hx] at h
        simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul] at h
        rw [← mul_assoc] at h
        have h2 := mul_right_cancel₀ hne h
        have hμ2 : μ * star μ = ((((P.c : ℚ) : ℝ)) : ℂ) := by
          rw [← hμ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hμ0 : star μ ≠ 0 := by
          intro h0; apply hc0; rw [← hμ2, h0, mul_zero]
        apply hw
        apply mul_right_cancel₀ hμ0
        rw [hμ2]
        first | exact h2 | (rw [mul_comm]; exact h2)
      apply normSq_eq_of_form Γ A _ hΓ' x w hx
      intro h
      have hneg := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _
        (by rw [← cong]; exact hpos) (by rw [← cong]; exact hS) (Zne x hx0)
      rw [← cong, h] at hneg; simp at hneg
  · apply normSq_eq_of_form Γ A _ hΓ' x w hx
    intro h
    have hneg := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (Zne x hx0)
    rw [← cong, h] at hneg; simp at hneg

theorem mark_ell : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ ha hm φ z hz
  have hdeg : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) z hdeg (by rw [h]; exact hz)
    exact normSq_of_eigenvector G P μ ha hm _ x hx0 z hx
  · have hz' : (minpoly G.F (P.γ : G.C)).eval₂ (InfinitePlace.mk φ).embedding (star z) = 0 := by
      have e : (InfinitePlace.mk φ).embedding = (starRingEnd ℂ).comp φ := by
        rw [h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := Polynomial.hom_eval₂ P.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      rw [e]; exact this.symm
    obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) (star z) hdeg hz'
    have := normSq_of_eigenvector G P μ ha hm _ x hx0 (star z) hx
    rwa [norm_star] at this

end GlobalTheory.LKMid.MarkEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntRing
section
noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.TauNorm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum ℤ)

abbrev Av : Type := v.adicCompletion ℚ ⊗[ℚ] K

abbrev bas : Module.Basis (Fin (Module.finrank ℚ K)) (v.adicCompletion ℚ) (Av K v) :=
  Algebra.TensorProduct.basis (v.adicCompletion ℚ) (Module.finBasis ℚ K)

def IsInt (x : Av K v) : Prop := ∀ i, (bas K v).repr x i ∈ v.adicCompletionIntegers ℚ

abbrev sig (τ : K ≃ₐ[ℚ] K) : Av K v →ₐ[ℚ] Av K v :=
  Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) (τ : K →ₐ[ℚ] K)

variable {K v}

theorem isInt_zero : IsInt K v 0 := fun i => by simp

theorem isInt_add {x y : Av K v} (hx : IsInt K v x) (hy : IsInt K v y) : IsInt K v (x + y) :=
  fun i => by simpa only [map_add, Finsupp.add_apply] using add_mem (hx i) (hy i)

theorem isInt_neg {x : Av K v} (hx : IsInt K v x) : IsInt K v (-x) :=
  fun i => by simpa only [map_neg, Finsupp.neg_apply] using neg_mem (hx i)

variable (K v)

def intRing (h1 : IsInt K v 1) (hm : ∀ x y, IsInt K v x → IsInt K v y → IsInt K v (x * y)) :
    Subring (Av K v) where
  carrier := {x | IsInt K v x}
  mul_mem' hx hy := hm _ _ hx hy
  one_mem' := h1
  add_mem' hx hy := isInt_add hx hy
  zero_mem' := isInt_zero
  neg_mem' hx := isInt_neg hx

end GlobalTheory.TauNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPowOfPsiAtTrivial
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus

namespace GlobalTheory.GaussModulus

theorem mem_pow_of_psiAt_trivial {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ)
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) (δ : 𝓞 E)
    (hδ : ∀ r : 𝓞 E, psiAt w (algebraMap E (w.adicCompletion E) ((δ : E) * r / c)) = 1) : δ ∈ w.asIdeal ^ a := by
  set t : w.adicCompletion E := algebraMap E (w.adicCompletion E) ((δ : E) / c) with ht
  have hc0 : w.valuation E (c : E) ≠ 0 := by rw [hc]; exact WithZero.exp_ne_zero
  have hδ1 : w.valuation E (δ : E) ≤ 1 := w.valuation_le_one δ
  have hvt : Valued.v t ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) := by
    rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    simpa using hδ1
  have key : ∀ s ∈ w.adicCompletionIntegers E, psiAt w (t * s) = 1 := by
    intro s hs
    have hs1 : Valued.v s ≤ 1 := hs
    obtain ⟨r, hr⟩ := exists_int_approx w hs1 (a + diffExp w)
    have e : t * s = algebraMap E (w.adicCompletion E) ((δ : E) * r / c) +
        t * (s - algebraMap E (w.adicCompletion E) (r : E)) := by
      have ha : algebraMap E (w.adicCompletion E) ((δ : E) * r / c) =
          algebraMap E (w.adicCompletion E) ((δ : E) / c) * algebraMap E (w.adicCompletion E) (r : E) := by
        rw [← (algebraMap E (w.adicCompletion E)).map_mul]; congr 1; ring
      rw [ha, ht]
      ring
    rw [e, psiAt_add, hδ r, one_mul]
    refine psiAt_eq_one ?_
    rw [map_mul]
    calc Valued.v t * Valued.v (s - algebraMap E (w.adicCompletion E) (r : E))
        ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) * WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) :=
          mul_le_mul' hvt hr
      _ = 1 := by rw [← WithZero.exp_add]; simp
      _ ≤ WithZero.exp (diffExp w : ℤ) := by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hvt' := (psiAt_conductor w t).1 key
  rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add] at hvt'
  have h2 : w.valuation E (δ : E) ≤ WithZero.exp (-(a : ℤ)) := by
    refine hvt'.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  rw [w.valuation_of_algebraMap] at h2
  exact (w.intValuation_le_pow_iff_mem δ a).1 (by simpa using h2)

end GlobalTheory.GaussModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosetsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModPSquaredStalkSurjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI.StalkKer

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma natCast_eq_zero_stalk_of_over_zmod (n : ℕ) {X : Scheme} (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod n)) (x : X) :
    ((n : ℕ) : X.presheaf.stalk x) = 0 := by
  have := map_natCast ((X.presheaf.germ ⊤ x trivial).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ZMod n))).inv.hom)) n
  rw [← this, ZMod.natCast_self, map_zero]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma stalk_hom_eq_zero_of_stalkMap_eq_zero {X Y : Scheme} (π : X ⟶ Y) (y : X) {R : CommRingCat}
    [IsLocalRing R] (h : Spec R ⟶ X) (hy : h (IsLocalRing.closedPoint R) = y)
    (q : Y.presheaf.stalk (π y) ⟶ R) (hh : h ≫ π = Spec.map q ≫ Y.fromSpecStalk (π y))
    (z : Y.presheaf.stalk (π y)) (hz : (π.stalkMap y).hom z = 0) : q.hom z = 0 := by
  subst hy
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (h ≫ π)
  have h2 : Scheme.stalkClosedPointTo (h ≫ π) = q :=
    Spec.map_injective ((cancel_mono (Y.fromSpecStalk _)).1 (h1.trans hh))
  rw [← h2, Scheme.stalkClosedPointTo_comp]
  simp [hz]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0})
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod (p ^ 2))) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p)) (π : X ⟶ Y),
    IsPullback π f g (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) →
    ∀ y : X, Function.Surjective (π.stalkMap y).hom ∧
      ∀ z, (π.stalkMap y).hom z = 0 ↔ ∃ w, z = p * w := by
  intro p hp Y X g f π hPB y
  have hci : IsClosedImmersion π :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hPB.flip
      (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _))
  refine ⟨π.stalkMap_surjective y, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · let O := Y.presheaf.stalk (π y)
    let I : Ideal O := Ideal.span {((p : ℕ) : O)}
    have hsq : ((p : ℕ) : O) ^ 2 = 0 := by
      rw [← Nat.cast_pow]; exact natCast_eq_zero_stalk_of_over_zmod (p ^ 2) g (π y)
    have hI : I ≠ ⊤ := by
      intro hT
      have hu : IsUnit ((p : ℕ) : O) := Ideal.span_singleton_eq_top.1 hT
      have h0 : IsUnit (0 : O) := hsq ▸ hu.pow 2
      exact zero_ne_one (isUnit_zero_iff.1 h0)
    haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (O ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI hloc : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hpQ : ((p : ℕ) : O ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    haveI : CharP (O ⧸ I) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpQ)
    let q : O ⟶ CommRingCat.of (O ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    haveI : IsLocalHom q.hom := hloc
    let a : Spec (CommRingCat.of (O ⧸ I)) ⟶ Y := Spec.map q ≫ Y.fromSpecStalk (π y)
    let b : Spec (CommRingCat.of (O ⧸ I)) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p) :=
      Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) (O ⧸ I)))
    have hcomm : a ≫ g = b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) := by
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ g)
      rw [← hφ]
      change Spec.map φ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext_zmod _ _
    let h := hPB.lift a b hcomm
    have hh : h ≫ π = a := hPB.lift_fst a b hcomm
    have hy : h (IsLocalRing.closedPoint (O ⧸ I)) = y := by
      apply π.isClosedEmbedding.injective
      change (h ≫ π) _ = _
      rw [hh]
      change Y.fromSpecStalk (π y) ((Spec.map q) (IsLocalRing.closedPoint (O ⧸ I))) = π y
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    have hq := stalk_hom_eq_zero_of_stalkMap_eq_zero π y h hy q hh z hz
    have hmem : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 hq
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_natCast, natCast_eq_zero_stalk_of_over_zmod p f y, zero_mul]

end GlobalTheory.DI.StalkKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEquiv

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Datum.InfFam D} {M : DSModel V S}
  {J : Set (GA D V)} {χ : GA D V → ℂ}

open Classical in

theorem list_equiv {U : MMap M} (hU : IsMultMap θ M J χ U)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (v w : M.Vec) (h : ∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) (l : List D.what₂.Tau) (hl : l.Nodup) :
    U (fun ρ => if ρ ∈ l then w ρ else v ρ) = rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v) := by
  induction l with
  | nil =>
    funext x
    simp [rTr]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have e := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
      simp only [if_neg hl.1]; exact h a)
    rw [ih hl.2] at e
    have e2 : rTr V ((a :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
        rTr V (atTau θ V a (g a)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
      funext x
      simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
    rw [e2, ← e]
    congr 1
    funext ρ
    by_cases hρ : ρ = a
    · subst hρ
      simp
    · rw [Function.update_of_ne hρ]
      simp [hρ]

theorem mult_realElt : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : Datum.InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) → ∀ v w : M.Vec, (∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) → U w = rTr V (realElt θ V g) (U v) := by
  intro D V S θ M J χ U hU g hg v w h
  classical
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have e := list_equiv hU g hg v w h (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [realElt, ← e]
    congr 1
    funext ρ
    simp
  | zero => funext x; simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have a := congrFun h1 x
    have b := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at a b ⊢
    rw [a, b]
  | smul c U _ h1 =>
    funext x
    have a := congrFun h1 x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at a ⊢
    rw [a]

end GlobalTheory.RealEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePowStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (Ω : Set (GA D V)), IsCompact Ω → ∃ N : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ u ∈ GinfC V, ∀ y : GA D V, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.Finite ∧ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.ncard : ℕ) : ℝ) ≤ C * normInf θ V u ^ N := by
  first | exact @GlobalTheory.RatCount.ncard_rational_le | exact GlobalTheory.RatCount.ncard_rational_le | (intros; apply GlobalTheory.RatCount.ncard_rational_le <;> assumption)
end

