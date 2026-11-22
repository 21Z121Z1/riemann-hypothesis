import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProductInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvd
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem toGQ_mul_pos' (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dif_pos hmm, dif_pos h, dif_pos h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem sl_trans_of_lev {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : X.K)
    (hf : Lev X M f) (t : ℕ) : X.sl (toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1]) f = f := by
  let γ : SL(2, ℤ) := ⟨!![1, ((t * M : ℕ) : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [γ]
  have e : toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1] = ofSL γ := Betti.toGQ_sl γ
  rw [e]; exact hf γ hγ

theorem Nq_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  intro Ω _ _ _ ε X M M' q f hq hdvd hcop hlev
  obtain ⟨e, rfl⟩ := hdvd
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e M) hcop
  set g : ℕ → X.K := fun i => X.sl (toGQ !![1, ((i : ℤ) * (M : ℤ)); 0, (q : ℤ)]) f with hg
  have step : ∀ j : ℕ, X.sl (toGQ !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)]) f = g (j * e % q) := by
    intro j
    have hm : !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)] =
        !![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] * !![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] := by
      have hd := Nat.mod_add_div (j * e) q
      generalize j * e % q = a at hd ⊢
      generalize j * e / q = b at hd ⊢
      have hdz : (a : ℤ) + (q : ℤ) * (b : ℤ) = (j : ℤ) * (e : ℤ) := by exact_mod_cast hd
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M : ℤ) * hdz.symm
    have h1 : (0 : ℤ) < (!![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]
    have h2 : (0 : ℤ) < (!![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]; exact_mod_cast hq
    rw [hm, toGQ_mul_pos' _ _ h1 h2, X.sl_mul, sl_trans_of_lev X M f hlev]
  have hinj : Set.InjOn (fun j => j * e % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : a * e ≡ b * e [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hqe) h'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have himg : (Finset.range q).image (fun j => j * e % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  unfold Nq
  simp_rw [step]
  show ∏ j ∈ Finset.range q, g j = _
  rw [← Finset.prod_image (f := g) hinj, himg]

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1Statement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulSq_old | exact GlobalTheory.HeckeFamilyMatrices.ulSq_old | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulSq_old <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ), (∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := by
  first | exact @GlobalTheory.KZ.PolAct.act_mem_pol | exact GlobalTheory.KZ.PolAct.act_mem_pol | (intros; apply GlobalTheory.KZ.PolAct.act_mem_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentativesStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrix_prime_det_coset_representatives : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q → (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨ ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  first | exact @GlobalTheory.cosetPrimeDet | exact GlobalTheory.cosetPrimeDet | (intros; apply GlobalTheory.cosetPrimeDet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLaws
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.CjLaws

end GlobalTheory.KZ.CjLaws

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_of_exists {m : Matrix (Fin 2) (Fin 2) ℤ} {δ : SL(2, ℤ)}
    (h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m := by
  unfold _root_.GlobalTheory.KZ.H3.cj
  rw [dif_pos h]
  exact h.choose_spec

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma eq_of_mul_eq_mul_of_det_ne_zero {m δ₁ δ₂ : Matrix (Fin 2) (Fin 2) ℤ} (hm : m.det ≠ 0)
    (h : δ₁ * m = δ₂ * m) : δ₁ = δ₂ := by
  have h2 : δ₁ * m * adjugate m = δ₂ * m * adjugate m := by rw [h]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one] at h2
  exact smul_right_injective _ hm h2

open Matrix in
open scoped MatrixGroups TensorProduct in
private lemma mul_eq_cj_mul_and_cj_mem_gamma (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ) (hm : 0 < m.det)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs)) :
    m * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
      _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M := by
  set d := m.det with hd
  have hd0 : d ≠ 0 := hm.ne'
  have hN : ((M * d.natAbs : ℕ) : ℤ) = (M : ℤ) * d := by
    push_cast
    rw [abs_of_pos hm]
  have hdvd : ∀ i j, ((M : ℤ) * d) ∣
      (δ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [CongruenceSubgroup.Gamma_mem] at hδ
    obtain ⟨h00, h01, h10, h11⟩ := hδ
    intro i j
    rw [← hN, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp_all
  choose X hX using hdvd
  set D : Matrix (Fin 2) (Fin 2) ℤ := 1 + (M : ℤ) • (m * Matrix.of X * adjugate m) with hD
  have hδX : (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + ((M : ℤ) * d) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]
    ring
  have hDm : D * m = m * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hD, hδX, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      adjugate_mul, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, smul_smul]
  have hdetD : D.det = 1 := by
    have h := congrArg Matrix.det hDm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact mul_right_cancel₀ hd0 (by rw [h, one_mul])
  have hex : ∃ δ' : SL(2, ℤ),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m :=
    ⟨⟨D, hdetD⟩, hDm.symm⟩
  have h1 := mul_eq_cj_mul_of_exists hex
  refine ⟨h1, ?_⟩
  have h2 : (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) = D :=
    eq_of_mul_eq_mul_of_det_ne_zero hd0 (by rw [← h1, hDm])
  rw [CongruenceSubgroup.Gamma_mem, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    push_cast <;> simp

open Matrix in
open scoped MatrixGroups TensorProduct in
theorem _root_.GlobalTheory.KZ.cj_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det →
    ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs),
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (_root_.GlobalTheory.KZ.H3.cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧
        _root_.GlobalTheory.KZ.H3.cj m δ ∈ CongruenceSubgroup.Gamma M) ∧
    (∀ γ δ : SL(2, ℤ), _root_.GlobalTheory.KZ.H3.cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det →
      m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m →
        ∀ z ∈ _root_.GlobalTheory.KZ.Hs,
          _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ) z) =
            _root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.ofSL δ')
              (_root_.GlobalTheory.KZ.mob (_root_.GlobalTheory.KZ.toGQ m) z)) := by
  refine ⟨mul_eq_cj_mul_and_cj_mem_gamma, fun γ δ => ?_, fun m δ δ' hm h => ?_⟩
  · have hex : ∃ δ' : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ' : Matrix (Fin 2) (Fin 2) ℤ) * γ :=
      ⟨γ * δ * γ⁻¹, by simp [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h1 := mul_eq_cj_mul_of_exists hex
    apply Subtype.ext
    refine eq_of_mul_eq_mul_of_det_ne_zero (m := (γ : Matrix (Fin 2) (Fin 2) ℤ)) (by simp) ?_
    rw [← h1]
    simp [Matrix.mul_assoc, Matrix.adjugate_mul]
  · intro z hz
    obtain ⟨-, hmul, -, -, hcoe, hhom⟩ := _root_.GlobalTheory.KZ.mob_laws
    have hδ : (0 : ℤ) < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    have hδ' : (0 : ℤ) < (δ' : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
    rw [← hmul _ _ z hz, ← hmul _ _ z hz, ← hcoe, ← hcoe, ← hhom _ _ hm hδ, ← hhom _ _ hδ' hm, h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbit
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add, map_natCast, map_add, map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffine
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixChosenDiamondMatrixGamma1Gamma0Statement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiamondMatrix_chosenDiamondMatrixGamma1Gamma0 : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N → IsDiam N l d (sgD N l d) := by
  first | exact @GlobalTheory.KZ.isDiam_sgD_of_prime | exact GlobalTheory.KZ.isDiam_sgD_of_prime | (intros; apply GlobalTheory.KZ.isDiam_sgD_of_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduceStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ → Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_succ_reduce | exact GlobalTheory.KZ.H3.kum_succ_reduce | (intros; apply GlobalTheory.KZ.H3.kum_succ_reduce <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.DlRescale

def mulN (N : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (N : ℚ)

theorem mulN_le (N : ℕ) (hN : 0 < N) (g g' : ℚ) : mulN N g ≤ mulN N g' ↔ g ≤ g' := by
  have : (0:ℚ) < N := by exact_mod_cast hN
  simp [mulN, mul_le_mul_iff_of_pos_left this]

theorem mulN_inj (N : ℕ) (hN : 0 < N) : Function.Injective (mulN N) := fun g g' h =>
  le_antisymm ((mulN_le N hN g g').1 h.le) ((mulN_le N hN g' g).1 h.ge)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def resc (N : ℕ) (hN : 0 < N) : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω :=
  HahnSeries.embDomainRingHom (mulN N) (mulN_inj N hN) (mulN_le N hN)

theorem resc_coeff (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) (r : ℚ) :
    (resc N hN ψ).coeff r = ψ.coeff (r / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : r = mulN N (r / N) := by simp [mulN]; field_simp
  conv_lhs => rw [e]
  simp only [resc, HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (f := ⟨⟨mulN N, mulN_inj N hN⟩, mulN_le N hN _ _⟩)

theorem forall_div (N : ℕ) (hN : 0 < N) (Q : ℚ → Prop) : (∀ r : ℚ, Q (r / N)) ↔ ∀ r, Q r := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun h r => ?_, fun h r => h _⟩
  have := h (N * r)
  rwa [mul_div_cancel_left₀ r hN'] at this

theorem theta_resc (N : ℕ) (hN : 0 < N) (s : ℚ) (ψ : HahnSeries ℚ Ω) :
    theta (s / N) (resc N hN ψ) = resc N hN (theta s ψ) := by
  ext r
  simp only [theta, resc_coeff]
  congr 2
  ring

theorem prim_resc (A : ValuationSubring Ω) (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) :
    Prim A (resc N hN ψ) ↔ Prim A ψ := by
  unfold Prim
  simp only [resc_coeff]
  rw [forall_div N hN (fun r => ψ.coeff r ∈ A)]
  constructor
  · rintro ⟨h1, r, h2, h3⟩; exact ⟨h1, r / N, h2, h3⟩
  · rintro ⟨h1, r, h2, h3⟩
    have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨h1, N * r, ?_⟩
    rw [mul_div_cancel_left₀ r hN']; exact ⟨h2, h3⟩

theorem eOm_zero (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

theorem exp_sl_diag (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) (hN : 0 < N) (u : X.K) :
    X.exp (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) u) = resc N hN (X.exp u) := by
  have hdet : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hN
  have e00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  rw [resc_coeff]
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) e10 u (r / N)
  rw [e00, e01, e11, mul_zero, zero_div, eOm_zero, one_mul, div_one, div_mul_cancel₀ r hN'] at h
  exact h

end GlobalTheory.DlRescale

end

open GlobalTheory.DlRescale in
theorem GlobalTheory.Glue.isDl_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  intro Ω _ _ _ ε X _ l _ A _ n N s f φ φ' hN hφ
  have hφ' : φ' = resc N hN φ := by ext r; rw [hφ, resc_coeff]
  subst hφ'
  have hexp := exp_sl_diag ε X N hN
  set g := toGQ !![(N : ℤ), 0; 0, 1]
  have key : ∀ a b : X.K, (∀ r, CgA A l n ((resc N hN φ * X.exp (X.sl g a) * X.exp (X.sl g b)).coeff r)
      ((theta (s / N) (X.exp (X.sl g a)) * X.exp (X.sl g b) - X.exp (X.sl g a) * theta (s / N) (X.exp (X.sl g b))).coeff r)) ↔
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r) := by
    intro a b
    simp only [hexp, theta_resc, ← map_mul, ← map_sub, resc_coeff]
    exact forall_div N hN (fun r => CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r))
  have hA : (∀ r, (resc N hN φ).coeff r ∈ A) ↔ ∀ r, φ.coeff r ∈ A := by
    simp only [resc_coeff]; exact forall_div N hN (fun r => φ.coeff r ∈ A)
  constructor
  · rintro ⟨h0, a, b, κ, hκ, hfb, pa, pb, hc⟩
    refine ⟨hA.2 h0, X.sl g a, X.sl g b, κ, hκ, ?_, ?_, ?_, (key a b).2 hc⟩
    · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
    · rw [hexp]; exact (prim_resc A N hN _).2 pa
    · rw [hexp]; exact (prim_resc A N hN _).2 pb
  · rintro ⟨h0, a', b', κ, hκ, hfb, pa, pb, hc⟩
    obtain ⟨a, rfl⟩ := (X.sl g).surjective a'
    obtain ⟨b, rfl⟩ := (X.sl g).surjective b'
    refine ⟨hA.1 h0, a, b, κ, hκ, ?_, ?_, ?_, (key a b).1 hc⟩
    · apply (X.sl g).injective
      rw [map_mul, map_mul, AlgEquiv.commutes]; exact hfb
    · rw [hexp] at pa; exact (prim_resc A N hN _).1 pa
    · rw [hexp] at pb; exact (prim_resc A N hN _).1 pb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevel
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.kronecker_product_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ ε X M q σ f hM hq hqM hf hσ γ hγ
  exact GlobalTheory.hecke_product_invariant ε X M q f hM hq hqM hf σ hσ γ hγ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruenceStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  first | exact @GlobalTheory.KZ.H3.kum_near_zero_eval | exact GlobalTheory.KZ.H3.kum_near_zero_eval | (intros; apply GlobalTheory.KZ.H3.kum_near_zero_eval <;> assumption)
end

