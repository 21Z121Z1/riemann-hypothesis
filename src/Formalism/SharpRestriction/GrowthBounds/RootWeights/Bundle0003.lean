import Formalism.SharpRestriction.GrowthBounds.RootWeights.MulLaurentSup
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IdentityEvaluationGenericMatrix
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem mapRingHom_laurent_C' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  first
  | simp [LaurentPolynomial.C_apply, AddMonoidAlgebra.mapRingHom_single]
  | simp [LaurentPolynomial.C_apply, Finsupp.mapRange_single]
  | (ext k; simp [LaurentPolynomial.C_apply, Finsupp.single_apply]; split_ifs <;> simp)
  | (ext k; simp [LaurentPolynomial.C_apply, AddMonoidAlgebra.coeff_single]; split_ifs <;> simp)
  | rfl

private theorem mapRingHom_laurent_T {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (k : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T k : LaurentPolynomial A) = LaurentPolynomial.T k := by
  first
  | (simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T]; done)
  | (ext j
     simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.T, -LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.T_apply]
     split_ifs <;> simp; done)
  | (ext j
     simp [LaurentPolynomial.coeff_T]
     split_ifs <;> simp; done)

theorem mul_Psi_support {σ A R' : Type*} [CommRing A] [CommRing R'] (φ0 : A →+* R') (x : σ → R')
    (P : MvPolynomial σ (LaurentPolynomial A)) :
    ((eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ φ0) (fun v => LaurentPolynomial.C (x v))) P).coeff.support ⊆
      mul_degs P := by
  have key : (eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ φ0) (fun v => LaurentPolynomial.C (x v)) :
      MvPolynomial σ (LaurentPolynomial A) →+* LaurentPolynomial R') =
      (AddMonoidAlgebra.mapRingHom ℤ (eval₂Hom φ0 x)).comp (mul_Phi σ A) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      ext k
      simp [mul_Phi]
    · intro i
      simp [mul_Phi, mapRingHom_laurent_C']
  rw [key, mul_degs_eq]
  intro k hk
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro h
  apply hk
  simp [h]

def identityEvaluation (R : Type*) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R →+* R :=
  MvPolynomial.eval (fun ab => if ab.1 = ab.2 then (1 : R) else 0)

theorem identity_evaluation_generic_matrix (R : Type*) [CommRing R] (n : ℕ) : (identityEvaluation R n).mapMatrix (genMat R n) = 1 := by
  ext a b
  simp [identityEvaluation, genMat, Matrix.one_apply]

theorem identity_evaluation_generic_det (R : Type*) [CommRing R] (n : ℕ) : identityEvaluation R n (genMat R n).det = 1 := by
  rw [RingHom.map_det, identity_evaluation_generic_matrix, Matrix.det_one]

def mul_ev (R : Type*) [CommRing R] (n : ℕ) : GLCoord R n →+* R :=
  IsLocalization.Away.lift (genMat R n).det (g := identityEvaluation R n) (by rw [identity_evaluation_generic_det]; exact isUnit_one)

theorem mul_ev_alg (R : Type*) [CommRing R] (n : ℕ) (a : MvPolynomial (Fin n × Fin n) R) :
    mul_ev R n (algebraMap _ (GLCoord R n) a) = identityEvaluation R n a := by
  first
  | simp [mul_ev]
  | exact IsLocalization.Away.lift_eq _ _ a
  | (unfold mul_ev; exact IsLocalization.lift_eq _ a)

theorem mul_ev_inv (R : Type*) [CommRing R] (n : ℕ) :
    mul_ev R n (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) = 1 := by
  have h := congrArg (mul_ev R n)
    (IsLocalization.Away.mul_invSelf (S := GLCoord R n) (genMat R n).det)
  rw [map_mul, map_one, mul_ev_alg, identity_evaluation_generic_det, one_mul] at h
  exact h

def mul_ph (R : Type*) [CommRing R] (n : ℕ) : GLLaurent R n →+* LaurentPolynomial R :=
  AddMonoidAlgebra.mapRingHom ℤ (mul_ev R n)

theorem mul_ph_C (R : Type*) [CommRing R] (n : ℕ) (a : GLCoord R n) :
    mul_ph R n (LaurentPolynomial.C a) = LaurentPolynomial.C (mul_ev R n a) := by
  simp only [mul_ph]
  exact mapRingHom_laurent_C' _ _

theorem mul_ph_T (R : Type*) [CommRing R] (n : ℕ) (k : ℤ) :
    mul_ph R n (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  simp only [mul_ph]
  exact mapRingHom_laurent_T _ _

theorem mul_ph_gL (R : Type*) [CommRing R] (n : ℕ) : (mul_ph R n).mapMatrix (gL R n) = 1 := by
  ext a b
  simp only [gL, RingHom.mapMatrix_apply, Matrix.map_apply, genMat, Matrix.of_apply, mul_ph_C,
    mul_ev_alg, identityEvaluation, MvPolynomial.eval_X, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_ph_gLinv (R : Type*) [CommRing R] (n : ℕ) : (mul_ph R n).mapMatrix (gLinv R n) = 1 := by
  have hadj : (identityEvaluation R n).mapMatrix (genMat R n).adjugate = 1 := by
    rw [RingHom.map_adjugate, identity_evaluation_generic_matrix, Matrix.adjugate_one]
  ext a b
  have hab := congrFun (congrFun hadj a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  simp only [gLinv, RingHom.mapMatrix_apply, Matrix.map_apply, mul_ph_C, map_mul, mul_ev_inv,
    mul_ev_alg, one_mul, hab, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_ph_twist (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    (mul_ph R n).mapMatrix (twistMat R n j k) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T k else 1) := by
  rw [twistMat, map_mul, map_mul, mul_ph_gL, mul_ph_gLinv, one_mul, mul_one]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [mul_ph_T]

open Classical in
theorem mul_valS_detA_le {R : Type} [Field R] {ι : Type} (LL : Letters ι) {r : ℕ} [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true) (S' : Set ι) :
    valS LL S' (detA (R := R) A) ≤ ((1 : ℤ) : WithTop ℤ) := by
  set Ψ : MvPolynomial (ι × Fin r) (GLLaurent R r) →+* LaurentPolynomial R :=
    eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (mul_ev R r))
      (fun v => LaurentPolynomial.C (if v.1 = A v.2 then (1 : R) else 0)) with hΨ
  have hC : ∀ b, Ψ (C b) = mul_ph R r b := fun b => by rw [hΨ, coe_eval₂Hom, eval₂_C]; rfl
  have hX : ∀ i b, Ψ (X (A i, b)) = if i = b then 1 else 0 := by
    intro i b
    rw [hΨ, coe_eval₂Hom, eval₂_X]
    by_cases h : i = b
    · simp [h]
    · have : A i ≠ A b := fun h' => h (hA h')
      simp [h, this]
  have key : Ψ (twistSub LL S' (lastIdx r) (detA (R := R) A)) =
      (Matrix.diagonal (fun i : Fin r =>
        if A i ∈ S' ∧ i = lastIdx r then (LaurentPolynomial.T 1 : LaurentPolynomial R) else 1)).det := by
    rw [detA, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    have ht := fun b => congrFun (congrFun (mul_ph_twist R r (lastIdx r) 1) b) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at ht
    by_cases hS : A i ∈ S'
    · have : twistSub LL S' (lastIdx r) (X (A i, j) : MvPolynomial (ι × Fin r) R) =
          ∑ b : Fin r, C (twistMat R r (lastIdx r) 1 b j) * X (A i, b) := by
        simp [twistSub, hS, hv]
      rw [this, map_sum]
      simp only [map_mul, hC, hX, ht]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hij : i = j
      · subst hij; simp [hS]
      · simp [hij]
    · have : twistSub LL S' (lastIdx r) (X (A i, j) : MvPolynomial (ι × Fin r) R) = X (A i, j) := by
        simp [twistSub, hS]
      rw [this, hX]
      by_cases hij : i = j
      · subst hij; simp [hS]
      · simp [hij]
  rw [Matrix.det_diagonal, Finset.prod_eq_single (lastIdx r) (fun b _ hb => by simp [hb]) (by simp)] at key
  have hsub := mul_Psi_support (mul_ev R r) (fun v : ι × Fin r => if v.1 = A v.2 then (1 : R) else 0)
    (twistSub LL S' (lastIdx r) (detA (R := R) A))
  by_cases hS : A (lastIdx r) ∈ S'
  · have hm : (1 : ℤ) ∈ sDegs LL S' (lastIdx r) (detA (R := R) A) := by
      apply hsub
      rw [← hΨ, key]
      simp [hS]
    exact Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hm
  · have hm : (0 : ℤ) ∈ sDegs LL S' (lastIdx r) (detA (R := R) A) := by
      apply hsub
      rw [← hΨ, key]
      simp [hS]
    refine (Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hm).trans ?_
    exact_mod_cast (zero_le_one : (0 : ℤ) ≤ 1)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesSubmodule
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  obtain ⟨w, _, p_mem, p_ne, _⟩ := S
  haveI : CharZero O := by
    obtain ⟨q, hq⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O q with hqp | hq0
    · exfalso
      by_cases hdvd : q ∣ p
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
        subst hqp'
        exact p_ne (CharP.cast_eq_zero O q)
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))
        have hu : IsUnit (p : ZMod q) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
        have hu' : IsUnit (p : O) := by
          have h5 := hu.map (ZMod.castHom (dvd_refl q) O)
          simpa using h5
        exact (IsLocalRing.mem_maximalIdeal _).mp p_mem hu'
    · subst hq0
      exact CharP.charP_to_charZero O
  unfold KK
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem
    rw [map_add, map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def binomialDiagonalSubring (E : GLOps n K V) : Subring (Module.End K V) :=
  Subring.closure {u | ∃ a k, u = binomE E a k}

def OperatorsShiftWeightsByRoots (E : GLOps n K V) : Prop :=
  ∀ a b ν, ∀ x ∈ weightSp E ν, E a b x ∈ weightSp E (ν + rootW a b)

def WeightsBounded (E : GLOps n K V) : Prop :=
  ∃ m : ℕ, ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)

def WeightProjectionsIntegralBinomial (E : GLOps n K V) : Prop :=
  ∃ Θ : (Fin n → ℤ) → Module.End K V, (∀ μ, Θ μ ∈ binomialDiagonalSubring E) ∧
    ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0

def IsotypicComponentsSpanModule (E : GLOps n K V) : Prop := (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def TrivialIsotypicIsInvariant (E : GLOps n K V) : Prop :=
  ∀ x ∈ isoSub E 0, x ∈ weightSp E 0 ∧ ∀ a b : Fin n, a < b → E a b x = 0

def NontrivialIsotypicWeightZeroKilled (E : GLOps n K V) : Prop :=
  ∀ (P π : Module.End K V), IsWtProj E 0 π → (∀ w ∈ weightSp E 0, w ∈ nMinus E → P w = 0) →
    ∀ mu, mu ≠ 0 → ∀ x ∈ isoSub E mu, P (π x) = 0

end Formalism.MainNotions.G.GLWeightTheory
end
end

