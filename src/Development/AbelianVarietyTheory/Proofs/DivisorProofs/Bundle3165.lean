import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GdegMetric

theorem coeff_eq_zero_of_const (N : ℕ) (γ : ℕ → ℝ) (K : ℝ)
    (h : ∀ c : ℕ, ∑ m ∈ Finset.range (N + 1), (c : ℝ) ^ m * γ m = K) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    γ m = 0 := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (N + 1), Polynomial.C (γ j) * Polynomial.X ^ j
  have hP : P = Polynomial.C K := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℕ => (c : ℝ)) Nat.cast_injective fun c => ?_
    simp only [Set.mem_ofPred_eq, P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h c]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at e
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) m, if_pos (Finset.mem_range.2 (by omega)),
    if_neg (by omega)] at e
  exact e

theorem map_mul_add_pow {ι : Type} (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (A x y : MvPolynomial ι ℝ) (c : ℝ) (n : ℕ) :
    Φ (A * (MvPolynomial.C c * x + y) ^ n) =
      ∑ m ∈ Finset.range (n + 1), c ^ m * ((n.choose m : ℝ) * Φ (A * x ^ m * y ^ (n - m))) := by
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : A * ((MvPolynomial.C c * x) ^ m * y ^ (n - m) * (n.choose m : MvPolynomial ι ℝ)) =
      (c ^ m * (n.choose m : ℝ)) • (A * x ^ m * y ^ (n - m)) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow, ← map_pow]
    ring
  rw [e, map_smul, smul_eq_mul]
  ring

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem lin_single' {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (lin fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

theorem isConj_const_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_sum {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem icls_fnB_zsmul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_sum (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y)
    (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _)
    (isConj_const_mul hc _) fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_sum (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem chInt_raise_const (N : HermLB p) (t : ℝ) (hu : ∀ σ (y : CxPts p σ), CInfAt (fun _ => t) y) (hc) (D : ℕ)
    (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) :
    chInt (N.raise (fun _ _ => t) hu hc) D f = chInt N D f := by
  simp only [chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

theorem gdeg_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  intro HC k _ S _ p D hX L u
  classical
  let one : ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun _ _ => 1
  have h1 : ∀ σ (y : CxPts p σ), CInfAt (one σ) y := fun σ y => cInfAt_const 1 y
  have hc1 : ∀ σ σ', (Weight.ofFun (one σ)).IsConj (Weight.ofFun (one σ')) := fun _ _ _ _ _ _ _ => rfl
  let T : HermLB p := fnB one h1 hc1
  let U : HermLB p := fnB u.u u.cInf u.conj
  let G : Fin 3 → HermLB p := ![T, L, U]
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k S p D hX).2 _ G).1
  let eA : Option (Fin 3) → Fin 3 := fun o => o.elim 2 id
  have hA : IsArFun (fun o : Option (Fin 3) => o.elim U G) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eA o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 3)) (fun o => o.elim U G)
      (fun o => Pi.single (eA o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 2
        · exact isometric_comb_single G j
    simpa only [lin_single'] using this
  let eB : Option (Fin 2) → Fin 3 := fun o => o.elim 0 Fin.succ
  have hB : IsArFun (fun o : Option (Fin 2) => o.elim T ![L, U]) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eB o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 2)) (fun o => o.elim T ![L, U])
      (fun o => Pi.single (eB o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 0
        · fin_cases j
          · exact isometric_comb_single G 1
          · exact isometric_comb_single G 2
    simpa only [lin_single'] using this
  have chA : ∀ c b : ℤ, Φ (X 2 * (C (c : ℝ) * X 0 + (X 1 + C (b : ℝ) * X 2)) ^ D) =
      1 / 2 * chInt (comb G ![c, 1, b]) D u.u := by
    intro c b
    have := HC.arChange k S p D hX (Fin 3) G u.u u.cInf u.conj _ hA ![c, 1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [← this]
    congr 1
    simp [lin, Fin.sum_univ_three, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eA]
    ring
  have chB : ∀ b : ℤ, Φ (X 0 * (X 1 + C (b : ℝ) * X 2) ^ D) = 1 / 2 * gdeg (comb ![L, U] ![1, b]) D := by
    intro b
    have := HC.arChange k S p D hX (Fin 2) ![L, U] one h1 hc1 _ hB ![1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [gdeg, ← this]
    congr 1
    simp [lin, Fin.sum_univ_two, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eB]

  have iso : ∀ c b : ℤ, (comb G ![c, 1, b]).Isometric ((comb ![L, U] ![1, b]).raise (fun _ _ => (c : ℝ) * 1)
      (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl)) := by
    intro c b
    refine Isometric.trans (icls_eq_iff.1 ?_) (isometric_tens_fnB _ _ _ _)
    rw [icls_tens]
    have e : (fnB (p := p) (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y)
        (fun _ _ _ _ _ _ _ => rfl)).icls = c • T.icls := icls_fnB_zsmul h1 hc1 c
    rw [e, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_two]
    simp [G]
    abel
  have hind : ∀ c b : ℤ, chInt (comb G ![c, 1, b]) D u.u = chInt (comb G ![0, 1, b]) D u.u := by
    intro c b
    rw [(iso c b).chInt_eq, (iso 0 b).chInt_eq]
    exact (chInt_raise_const _ _ _ _ _ _).trans (chInt_raise_const _ _ _ _ _ _).symm
  have i1 : (comb ![L, U] ![1, 1]).Isometric (up L u) := icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB L u.u u.cInf u.conj), icls_tens, icls_comb, Fin.sum_univ_two]
    simp [U])
  have i0 : (comb ![L, U] ![1, 0]).Isometric L := icls_eq_iff.1 (by
    rw [icls_comb, Fin.sum_univ_two]
    simp)
  rw [← i1.gdeg_eq, ← i0.gdeg_eq]
  have e1 := chB 1
  have e0 := chB 0
  cases D with
  | zero =>
    simp only [pow_zero, mul_one] at e1 e0
    linarith
  | succ d =>
    have s1 : ∀ b : ℤ, Φ (X 2 * X 0 * (X 1 + C (b : ℝ) * X 2) ^ d) = 0 := by
      intro b
      have h := coeff_eq_zero_of_const (d + 1)
        (fun m => ((d + 1).choose m : ℝ) * Φ (X 2 * X 0 ^ m * (X 1 + C (b : ℝ) * X 2) ^ (d + 1 - m)))
        (1 / 2 * chInt (comb G ![0, 1, b]) (d + 1) u.u) (fun c => by
          beta_reduce
          rw [← map_mul_add_pow, ← hind c b, ← chA c b]
          push_cast
          rfl) (le_refl 1) (by omega)
      simp only [Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by positivity)
      · exact h
    have s2 : ∀ m ≤ d, Φ (X 2 * X 0 * X 2 ^ m * X 1 ^ (d - m)) = 0 := by
      intro m hm
      have hs : ∀ c : ℕ, ∑ j ∈ Finset.range (d + 1),
          (c : ℝ) ^ j * ((d.choose j : ℝ) * Φ (X 2 * X 0 * X 2 ^ j * X 1 ^ (d - j))) = 0 := by
        intro c
        rw [← map_mul_add_pow]
        have := s1 c
        rw [add_comm] at this
        push_cast at this
        exact this
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have := hs 0
        rw [Finset.sum_range_succ'] at this
        simpa using this
      · have h := coeff_eq_zero_of_const d _ 0 hs hm0 hm
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h (by exact_mod_cast (Nat.choose_pos hm).ne')
        · exact h
    have ex := map_mul_add_pow Φ (X 0) (X 2) (X 1) 1 (d + 1)
    rw [Finset.sum_range_succ'] at ex
    have hz : ∀ i ∈ Finset.range (d + 1), (1 : ℝ) ^ (i + 1) * (((d + 1).choose (i + 1) : ℝ) *
        Φ (X 0 * X 2 ^ (i + 1) * X 1 ^ (d + 1 - (i + 1)))) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Nat.add_sub_add_right, show (X 0 * X 2 ^ (i + 1) * X 1 ^ (d - i) : MvPolynomial (Fin 3) ℝ) =
        X 2 * X 0 * X 2 ^ i * X 1 ^ (d - i) by ring, s2 i hi', mul_zero, mul_zero]
    rw [Finset.sum_eq_zero hz, zero_add] at ex
    have e1' : Φ (X 0 * (C 1 * X 2 + X 1) ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 1]) (d + 1) := by
      rw [← e1, add_comm]
      push_cast
      rfl
    have e0' : Φ (X 0 * X 1 ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 0]) (d + 1) := by
      rw [← e0]
      simp
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at ex
    linarith

end GlobalTheory.GdegMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependent
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.HomInj

theorem aeval_mul_hom {σ R A : Type} [CommRing R] [CommRing A] [Algebra R A] {P : MvPolynomial σ R} {q : ℕ} (hP : P.IsHomogeneous q)
    (c : A) (z : σ → A) : aeval (fun i => c * z i) P = c ^ q * aeval z P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hP (mem_support_iff.mp hm)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m) := by
    simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
  rw [this]; ring

def dehom (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin D) ℤ :=
  aeval (Fin.cons 1 X)

theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℤ A] {D : ℕ} (w : Fin D → A) (P : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval w (dehom D P) = aeval (Fin.cons 1 w : Fin (D + 1) → A) P := by
  rw [dehom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem dehom_eq_zero {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ} (hP : P.IsHomogeneous q)
    (h : dehom D P = 0) : P = 0 := by
  let R := MvPolynomial (Fin (D + 1)) ℤ
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  set c : F := algebraMap R F (X 0) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ← map_zero (algebraMap R F)]
    exact fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)
  let z : Fin (D + 1) → F := fun i => algebraMap R F (X i) / c
  have hz : (fun i => algebraMap R F (X i)) = fun i => c * z i := by
    funext i; exact (mul_div_cancel₀ _ hc0).symm
  have hz0 : z = Fin.cons 1 (fun j => z j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show algebraMap R F (X 0) / c = 1
      exact div_self hc0
    · simp
  have key : algebraMap R F P = c ^ q * aeval z P := by
    have e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P := by
      rw [← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [e1, hz]
    exact aeval_mul_hom hP c z
  have hzP : aeval z P = 0 := by
    have e2 := aeval_dehom (fun j => z j.succ) P
    rw [h, map_zero] at e2
    rw [hz0]; exact e2.symm
  apply hinj
  rw [key, hzP, mul_zero, map_zero]

end GlobalTheory.HSAmp.HomInj

namespace GlobalTheory.HSAmp

open GlobalTheory.HSAmp.HomInj in

theorem homogComb_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ)
    (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  intro K _ _ D x hx hind _ ι _ g hg q T hT hsum
  let y : Fin (D + 1) → K := fun j => x j / x 0
  have hy : ∀ j, y j ∈ ratF x := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [y, div_self (hx 0)]; exact (ratF x).one_mem
    · exact Subfield.subset_closure ⟨j, rfl⟩
  let y' : Fin (D + 1) → ratF x := fun j => ⟨y j, hy j⟩
  have hxy : x = fun j => x 0 * y j := by
    funext j; exact (mul_div_cancel₀ _ (hx 0)).symm
  have hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K) := by
    intro i
    show _ = algebraMap (ratF x) K _
    rw [← aeval_algebraMap_apply]
    rfl
  have h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i) := by
    intro i
    rw [← aeval_mul_hom (hT i) (x 0) y]
    exact congrArg (fun v => aeval v (T i)) hxy
  have hsum' : ∑ i, aeval y' (T i) • g i = 0 := by
    have hq : x 0 ^ q ≠ 0 := pow_ne_zero _ (hx 0)
    have : x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1, hval, Subfield.smul_def, smul_eq_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have h0 : ∀ i, aeval y (T i) = 0 := by
    intro i
    rw [hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]; rfl
  have hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [y, div_self (hx 0)]
    · simp [y]
  funext i
  apply dehom_eq_zero (hT i)
  apply (algebraicIndependent_iff_injective_aeval.1 hind)
  rw [aeval_dehom, ← hy0, h0, map_zero]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecMonomialOfConeCombinatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Arith

theorem idlAlong_monomial : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  intro o _ ζ g n F Z i φ J d hV X _ _ _ m ga δ M hcone hδ b hb T W _ _ σ c e' x s hσ hcomm hs hβ
  obtain ⟨a, ha, hid⟩ := hV T (spMap σ ≫ x) hcomm
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at hid
  have hlin : φ.LinearOn δ := by
    have := hcone.linearOn_smul M
    rwa [show δ = fun k => (M : ℤ) • ga k from funext hδ]
  have hev : φ.evalZ T.β = ∑ k, (c k : ℝ) * φ.evalZ (δ k) := by
    refine InvFun.LinearOn.eval_eq_sum (X := X) hlin (r := e'.symm.toIntLinearEquiv.toLinearMap)
      e'.symm.surjective (fun k => Nat.cast_nonneg _) ?_
    intro u v
    simp [hβ]
  have haN : a = ∑ k, c k * b k := by
    have : (a : ℝ) = ∑ k, (c k : ℝ) * b k := by
      rw [ha, hev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k]; ring
    exact_mod_cast this
  have hassoc : Associated (∏ k, σ (s k) ^ b k) (T.ϖ ^ a) := by
    rw [haN, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun k _ => ?_
    rw [pow_mul]
    exact (hs k).pow_pow
  have hmap : (idlAlong J x).map σ = (Ideal.span {∏ k, s k ^ b k}).map σ := by
    rw [hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
    exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
  rw [← Ideal.comap_map_of_bijective σ hσ (I := idlAlong J x), hmap, Ideal.comap_map_of_bijective σ hσ]

end GlobalTheory.Poinc.Arith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormBlPrincipal

theorem idlAlong_comap_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J →
    ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  intro S Z π J h R _ _ ξ
  obtain ⟨-, S₀, π₀, ν, -, hbl, hc, -⟩ := h
  obtain ⟨U, f, hx, -, hU⟩ := hbl.1 ((ξ ≫ ν) (closedPoint R))
  have hle : ⊤ ≤ (ξ ≫ ν) ⁻¹ᵁ U.1 := (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ ν) hx).ge
  refine ⟨((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom f, ?_⟩
  have e : idlAlong (J.comap π) ξ = idlAlong (J.comap π₀) (ξ ≫ ν) := by
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hc, Category.assoc]
  rw [e, GlobalTheory.TraitOrder.idlAlong_eq_map _ _ U hle, hU, Ideal.map_span, Set.image_singleton]

end GlobalTheory.NormBlPrincipal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableAgainstMixedChernForm_iff_pull_iso : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = Mix.int L f := by
  first | exact @GlobalTheory.MixIso.intg_int_pull | exact GlobalTheory.MixIso.intg_int_pull | (intros; apply GlobalTheory.MixIso.intg_int_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteEtaleOriginKeyLemmaEssFinitStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  first | (exact @GlobalTheory.GoodEtale.closure_finiteEtale) | (exact GlobalTheory.GoodEtale.closure_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.closure_finiteEtale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralRelation_uniformisedHom_convolution_expansionTerms : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F), (∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) → (∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ)) → ∀ α : D₁.toPre.X, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  first | exact @GlobalTheory.Mum.Two.Mix.core | exact GlobalTheory.Mum.Two.Mix.core | (intros; apply GlobalTheory.Mum.Two.Mix.core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAddStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  first | exact @GlobalTheory.AV.isAmpleCls_add | exact GlobalTheory.AV.isAmpleCls_add | (intros; apply GlobalTheory.AV.isAmpleCls_add <;> assumption)
end

