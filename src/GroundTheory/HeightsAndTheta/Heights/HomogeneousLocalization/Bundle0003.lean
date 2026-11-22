import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPolySections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh
  GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra algebraOfOver

noncomputable section

namespace SectionsLatticeFS.PolySections

variable {A : Type u} [CommRing A] {N : ℕ}

lemma degree_eq_of_weight {e : Fin (N + 1) →₀ ℕ} {n : ℕ} (h : Finsupp.weight 1 e = n) :
    e.degree = n := by
  rw [← h, Finsupp.degree_eq_weight_one]
  rfl

lemma toLaurent_mem_LDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (s : Set (Fin (N + 1))) : toLaurent A N P ∈ LDeg A s n := by
  intro m hm
  by_cases hr : m ∈ Set.range (expHom N)
  · obtain ⟨e, rfl⟩ := hr
    rw [coeff_toLaurent_expHom] at hm
    refine ⟨?_, fun j _ => ?_⟩
    · rw [sum_expHom]
      exact_mod_cast degree_eq_of_weight ((mem_homogeneousSubmodule n P).mp hP hm)
    · simp [expHom]
  · exact (hm (coeff_toLaurent_eq_zero hr)).elim

lemma exists_toLaurent_eq {n : ℕ} {ℓ : Laurent A N} (hℓ : ∀ j, ℓ ∈ LDeg A {j} (n : ℤ)) :
    ∃ P ∈ grading A N n, toLaurent A N P = ℓ := by
  classical
  have hnn : ∀ m, ℓ.coeff m ≠ 0 → ∀ i, 0 ≤ m i := by
    intro m hm i
    by_cases h : ∃ j, j ≠ i
    · obtain ⟨j, hj⟩ := h
      exact (hℓ j m hm).2 i (by simpa [eq_comm] using hj)
    · push Not at h
      have hs : ∑ j, m j = m i :=
        Finset.sum_eq_single i (fun j _ hj => absurd (h j) hj) (by simp)
      have := (hℓ i m hm).1
      omega
  have hrange : ∀ m, ℓ.coeff m ≠ 0 → m ∈ Set.range (expHom N) := by
    intro m hm
    refine ⟨Finsupp.equivFunOnFinite.symm fun i => (m i).toNat, funext fun i => ?_⟩
    simp [expHom, Int.toNat_of_nonneg (hnn m hm i)]
  let S : Finset (Fin (N + 1) →₀ ℕ) :=
    ℓ.coeff.support.preimage (expHom N) expHom_injective.injOn
  let P : MvPolynomial (Fin (N + 1)) A := ∑ e ∈ S, monomial e (ℓ.coeff (expHom N e))
  have hcoeff : ∀ e, P.coeff e = ℓ.coeff (expHom N e) := by
    intro e
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with he
    · rfl
    · simp only [S, Finset.mem_preimage, Finsupp.mem_support_iff, not_not] at he
      exact he.symm
  refine ⟨P, (mem_homogeneousSubmodule n P).mpr fun e he => ?_, ?_⟩
  · rw [hcoeff] at he
    have h1 := (hℓ 0 _ he).1
    rw [sum_expHom] at h1
    have h2 : e.degree = n := by exact_mod_cast h1
    rw [← h2, Finsupp.degree_eq_weight_one]
    rfl
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    by_cases hm : m ∈ Set.range (expHom N)
    · obtain ⟨e, rfl⟩ := hm
      rw [coeff_toLaurent_expHom, hcoeff]
    · rw [coeff_toLaurent_eq_zero hm]
      by_contra h
      exact hm (hrange m (Ne.symm h))

variable (A N) in

def lpoly (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) : Laurent A N :=
  lval (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => 0)

lemma isCocycle (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) :
    d _ _ 0 (globalCocycle (twistAb A N n) (cover A N) s).1 = 0 :=
  (mem_cocycles _).1 (globalCocycle (twistAb A N n) (cover A N) s).2

lemma lpoly_mem (n : ℕ) (s : (ProjScheme.self A N).H0 (ProjScheme.twistN A N n)) (j : Fin (N + 1)) :
    lpoly A N n s ∈ LDeg A {j} (n : ℤ) := by
  have h := lval_mem (globalCocycle (twistAb A N n) (cover A N) s).1 (fun _ => j)
  rw [lpoly, lval_eq_of_cocycle _ (isCocycle n s) (fun _ => 0) (fun _ => j)]
  rwa [range_const_fin_one] at h

lemma lpoly_injective (n : ℕ) : Function.Injective (lpoly A N n) := by
  intro s t h
  apply globalCocycle_injective (twistAb A N n) (cover A N)
    (modulesAb (twistingSheaf (grading A N) (n : ℤ))).property iSup_stdOpen
  apply Subtype.ext
  apply cochain_ext
  intro i
  rw [lval_eq_of_cocycle _ (isCocycle n s) i (fun _ => 0),
    lval_eq_of_cocycle _ (isCocycle n t) i (fun _ => 0)]
  exact h

lemma algebraMap_mem_awayDeg {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (i : Fin 1 → Fin (N + 1)) :
    algebraMap (MvPolynomial (Fin (N + 1)) A) (Localization.Away (xprod (A := A) i)) P ∈
      ProjTwist.awayDeg (grading A N) (xprod_mem i) (Nat.succ_pos 0) (n : ℤ) := by
  have h := ProjTwist.mk_mem_awayDeg (xprod_mem i) (Nat.succ_pos 0) (k := (n : ℤ)) (n := 0) (j := n)
    (a := P) hP (by simp)
  have e : ProjTwist.fpow (xprod (A := A) i) 0 = 1 := Subtype.ext (pow_zero _)
  rwa [e, Localization.mk_one_eq_algebraMap] at h

lemma lpoly_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n) :
    lpoly A N n (ProjScheme.polySection hP) = toLaurent A N P := by
  have hz : (awayDegEquiv (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)).symm
      ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ = ⟨_, algebraMap_mem_awayDeg hP _⟩ := by
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [awayDegEquiv_apply, awayToLaurent_algebraMap]
  have key : (globalCocycle (twistAb A N n) (cover A N) (ProjScheme.polySection hP)).1
      (fun _ => 0) = theta (fun _ : Fin 1 => (0 : Fin (N + 1))) (n : ℤ)
        ⟨toLaurent A N P, toLaurent_mem_LDeg hP _⟩ := by
    apply ProjTwist.ext
    funext x
    rw [val_theta, hz]
    refine Eq.trans ?_ (ProjTwist.locMap_algebraMap (𝒜 := grading A N) x.1 _ P).symm
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  rw [lpoly, lval, key, AddEquiv.symm_apply_apply]

lemma polySection_add {n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (hQ : Q ∈ grading A N n) (hPQ : P + Q ∈ grading A N n) :
    ProjScheme.polySection hPQ = ProjScheme.polySection hP + ProjScheme.polySection hQ := by
  apply ProjTwist.ext
  funext x
  exact (Localization.add_mk_self P 1 Q).symm

lemma polySection_smul {n : ℕ} (a : A) {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ grading A N n)
    (haP : a • P ∈ grading A N n) :
    ProjScheme.polySection haP = a • ProjScheme.polySection hP := by
  apply ProjTwist.ext
  funext x
  change Localization.mk (a • P) 1 =
    projValue (grading A N) (algebraMap A Γ(projectiveSpace A N, ⊤) a) x.1 trivial *
      Localization.mk P 1
  rw [projValue_algebraMap, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one,
    smul_eq_C_mul]

theorem proof : SectionsLatticeFS.PolySections.Statement.{u} := by
  intro A _ N n
  let f : grading A N n →ₗ[A] (ProjScheme.self A N).H0 (ProjScheme.twistN A N n) :=
    { toFun := fun P => ProjScheme.polySection P.2
      map_add' := fun P Q => polySection_add P.2 Q.2 _
      map_smul' := fun a P => polySection_smul a P.2 _ }
  have hinj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply toLaurent_injective
    rw [← lpoly_polySection P.2, ← lpoly_polySection Q.2]
    exact congrArg (lpoly A N n) h
  have hsurj : Function.Surjective f := by
    intro s
    obtain ⟨P, hP, hPs⟩ := exists_toLaurent_eq (lpoly_mem n s)
    exact ⟨⟨P, hP⟩, lpoly_injective n (by rw [← hPs]; exact lpoly_polySection hP)⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

end SectionsLatticeFS.PolySections

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PSupMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry NumberField TensorProduct GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma SupMonomial.pow_mul_prod_le {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    ((∑ i, a i : ℕ) : ℝ) ^ (∑ i, a i) * ∏ i, q i ^ a i ≤
      (∑ i, q i) ^ (∑ i, a i) * ∏ i, (a i : ℝ) ^ a i := by
  rcases Nat.eq_zero_or_pos (∑ i, a i) with h0 | hpos
  · have ha : ∀ i, a i = 0 := fun i => Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)
    simp [ha]
  set n := ∑ i, a i with hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  set w : ι → ℝ := fun i => (a i : ℝ) / n
  set z : ι → ℝ := fun i => q i / a i
  have hz : ∀ i, 0 ≤ z i := fun i => div_nonneg (hq i) (Nat.cast_nonneg _)
  have hw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div]
    rw [← Nat.cast_sum, ← hn, div_self hnR.ne']
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ w z
    (fun i _ => div_nonneg (Nat.cast_nonneg _) hnR.le) hw (fun i _ => hz i)
  have hsum : ∑ i, w i * z i ≤ (∑ i, q i) / n := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [w, z]
    rcases eq_or_ne (a i : ℝ) 0 with h | h
    · rw [h]; simpa using div_nonneg (hq i) hnR.le
    · rw [div_mul_div_comm, mul_comm (a i : ℝ), mul_div_mul_right _ _ h]
  have key : (∏ i, z i ^ w i) ^ n = ∏ i, z i ^ a i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hz i), div_mul_cancel₀ _ hnR.ne', Real.rpow_natCast]
  have h1 : ∏ i, z i ^ a i ≤ (∑ i, q i) ^ n / (n : ℝ) ^ n := by
    rw [← key, ← div_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _)
      (hamgm.trans hsum) n
  have h2 : ∏ i, q i ^ a i = (∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [z]
    rcases eq_or_ne (a i) 0 with h | h
    · simp [h]
    · rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr h))]
  have hA : 0 ≤ ∏ i, (a i : ℝ) ^ a i := Finset.prod_nonneg fun i _ => by positivity
  have hN : 0 < (n : ℝ) ^ n := pow_pos hnR n
  rw [h2]
  calc (n : ℝ) ^ n * ((∏ i, z i ^ a i) * ∏ i, (a i : ℝ) ^ a i)
      ≤ (n : ℝ) ^ n * ((∑ i, q i) ^ n / (n : ℝ) ^ n * ∏ i, (a i : ℝ) ^ a i) := by gcongr
    _ = (∑ i, q i) ^ n * ∏ i, (a i : ℝ) ^ a i := by field_simp

lemma SupMonomial.sq_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) :
    (‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree) ^ 2 =
      (∏ i, (‖v i‖ ^ 2) ^ a i) / (∑ i, ‖v i‖ ^ 2) ^ a.degree := by
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 v ^ a.degree) ^ 2 = (norm2 v ^ 2) ^ a.degree by ring, euclideanNorm_sq, norm_prod,
    ← Finset.prod_pow]
  simp only [norm_pow, ← pow_mul, mul_comm (a _) 2]
  rfl

lemma SupMonomial.le {N : ℕ} (a : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx]
  refine Real.sqrt_le_sqrt ?_
  rw [SupMonomial.sq_eq]
  have hS : 0 < (∑ i, ‖v i‖ ^ 2) ^ a.degree := pow_pos (normSq2_pos hv) _
  have hN : 0 < (a.degree : ℝ) ^ a.degree := by
    rcases Nat.eq_zero_or_pos a.degree with h | h
    · simp [h]
    · exact pow_pos (by exact_mod_cast h) _
  rw [div_le_div_iff₀ hS hN]
  have := SupMonomial.pow_mul_prod_le (fun i => a i) (fun i => ‖v i‖ ^ 2) (fun i => by positivity)
  rw [← Finsupp.degree_eq_sum] at this
  linarith

lemma SupMonomial.exists_eq {N : ℕ} (a : Fin (N + 1) →₀ ℕ) :
    ∃ v : Fin (N + 1) → ℂ, v ≠ 0 ∧
      ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ a.degree =
        √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) := by
  rcases Nat.eq_zero_or_pos a.degree with h0 | hpos
  · have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).mp h0
    subst ha
    refine ⟨Pi.single 0 1, by simp [funext_iff, Pi.single_apply], ?_⟩
    simp
  set n := a.degree
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ i, a i ≠ 0 by rw [← Finsupp.degree_eq_sum]; exact hpos.ne')
  set v : Fin (N + 1) → ℂ := fun i => ((√((a i : ℝ) / n) : ℝ) : ℂ)
  have hvi : ∀ i, ‖v i‖ ^ 2 = (a i : ℝ) / n := fun i => by
    simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hnR.le)
  have hv : v ≠ 0 := fun h => by
    have := hvi j
    rw [h, Pi.zero_apply, norm_zero, zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at this
    exact this.elim (fun h' => hj (by exact_mod_cast h')) hnR.ne'
  refine ⟨v, hv, ?_⟩
  have hx : 0 ≤ ‖MvPolynomial.eval v (MvPolynomial.monomial a (1 : ℂ))‖ / norm2 v ^ n :=
    div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos hv).le _)
  rw [← Real.sqrt_sq hx, SupMonomial.sq_eq]
  congr 1
  simp only [hvi]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← Finsupp.degree_eq_sum, div_self hnR.ne', one_pow, div_one,
    Finset.prod_congr rfl fun i _ => div_pow (a i : ℝ) n (a i), Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]

theorem SupMonomial.proof (h : FSValue.Statement.{0}) : SupMonomial.Statement := by
  intro K _ _ N σ a
  have hval : ∀ x : (self (𝓞 K) N).complexPoints (intEmb σ),
      fsFibreNorm a.degree (intEmb σ) x ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl))) =
      CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) x.1 := by
    intro x
    rw [evalFibre_tmul, map_one, one_smul, h, MvPolynomial.map_monomial, map_one]
  have hle : ∀ y : CP N, CP.fsNormPoly a.degree (MvPolynomial.monomial a (1 : ℂ)) y ≤
      √((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree) :=
    fun y => SupMonomial.le a y.rep y.rep_nonzero
  obtain ⟨v, hv, hveq⟩ := SupMonomial.exists_eq a
  let x₀ : (self (𝓞 K) N).complexPoints (intEmb σ) := selfPoint (intEmb σ) (Projectivization.mk ℂ v hv)
  have : Nonempty ((self (𝓞 K) N).complexPoints (intEmb σ)) := ⟨x₀⟩
  simp only [fsSupNorm, hval]
  refine le_antisymm (ciSup_le fun x => hle x.1)
    (le_ciSup_of_le ⟨√((∏ i, ((a i : ℝ) ^ a i)) / (a.degree : ℝ) ^ a.degree), ?_⟩ x₀ (le_of_eq ?_))
  · rintro _ ⟨x, rfl⟩
    exact hle x.1
  · rw [← hveq]
    exact (CP.fsNormPoly_mk (MvPolynomial.isHomogeneous_monomial 1 rfl) v hv).symm

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

