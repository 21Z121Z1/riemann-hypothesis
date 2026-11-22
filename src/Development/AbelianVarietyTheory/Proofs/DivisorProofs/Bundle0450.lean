import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfCompatibleFractions
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial

namespace GlobalTheory

theorem weightedHomogeneousComponent_one_int {σ A : Type*} [CommRing A] (F : MvPolynomial σ A)
    (m : ℤ) : weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) m F =
      if 0 ≤ m then homogeneousComponent m.toNat F else 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent, weight_one_int]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, coeff_homogeneousComponent]
    by_cases h : (a.degree : ℤ) = m
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hm, if_neg (by omega), coeff_zero]

theorem isHomogeneous_polyGrading_of_component {ι A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A))
    (hJ : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) :
    (J : Submodule (MvPolynomial ι A) (MvPolynomial ι A)).IsHomogeneous (polyGrading ι A) := by
  intro m F hF
  have e : (decompose (polyGrading ι A) F m : MvPolynomial ι A) =
      weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) m F :=
    weightedDecomposition.decompose'_apply A _ F m
  rw [e, weightedHomogeneousComponent_one_int]
  split_ifs
  · exact hJ F hF _
  · exact zero_mem _

theorem sum_cubeSign_pair {ι : Type} [LinearOrder ι] {t : Finset ι} (ht : t.card = 2) :
    ∑ i ∈ t, cubeSign t i = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hab]
  have h := cubeSign_mul_erase (t := {a, b}) (by simp) (by simp) hab
  rw [Finset.erase_insert (by simpa using hab), Finset.pair_comm,
    Finset.erase_insert (by simpa using hab.symm), cubeSign_singleton, cubeSign_singleton,
    mul_one, mul_one, Finset.pair_comm] at h
  rw [h]; ring

theorem exists_form_of_compatible_fractions : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous d ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) A) ^ L * (F i - X i ^ N * G) ∈ J := by
  intro A _ _ n J hJ
  letI : Decomposition (grQuot (polyGrading (Fin (n + 1)) A) J) :=
    grQuotDecomposition _ (isHomogeneous_polyGrading_of_component J hJ)
  obtain ⟨n₀, hn₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A (MvPolynomial (Fin (n + 1)) A ⧸ J)
    (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hc => ?_⟩
  have hd' : n₀ ≤ (d : ℤ) := by omega
  have hb := (grAug_bijective_iff (ι := Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J)
    (d : ℤ)).2 ⟨hn₀ d hd' 0, hn₀ d hd' 1⟩
  have hmem : ∀ i, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd A {i}) N
      (Submodule.Quotient.mk (F i)) ∈ homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) {i} d :=
    fun i => awayFrac_mem_homLoc (d := ((d + N : ℕ) : ℤ))
      ⟨F i, mem_polyGrading_natCast.2 (hF i), rfl⟩ (by simp)
  let y : ∀ i, (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d).obj {i} :=
    fun i => (⟨_, hmem i⟩ : homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) {i} d)
  let x := Cube.termOneEquiv (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) y

  have hres : ∀ (s : {s : Finset (Fin (n + 1)) // s.card = 1}) (T : Finset (Fin (n + 1)))
      (h : s.1 ⊆ T), ∃ j ∈ s.1, (show homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) T d from
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) h (x s)).1 =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd A T) N
          (xProd A (T.erase j) ^ N • Submodule.Quotient.mk (F j)) := by
    rintro ⟨s, hs⟩ T h
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
    refine ⟨j, Finset.mem_singleton_self j, ?_⟩
    have hj : j ∈ T := h (Finset.mem_singleton_self j)
    have e : x ⟨{j}, hs⟩ = y j := Cube.termOneEquiv_apply _ y j
    simp only [e, res_grCube]
    erw [coe_homLocRes]
    exact locRes_awayFrac X h (by rw [Finset.prod_singleton, Finset.prod_erase_mul _ _ hj]) N _

  have hx : Cube.d (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) 1 x = 0 := by
    funext t
    obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 t.2
    have hv : ∀ j ∈ t.1, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd A t.1) N
        (xProd A (t.1.erase j) ^ N • Submodule.Quotient.mk (F j)) =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd A t.1) N
        (xProd A (t.1.erase a) ^ N • Submodule.Quotient.mk (F a)) := by
      intro j hj
      rw [hab'] at hj ⊢
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rfl
      · rw [Finset.mem_singleton] at hj
        subst hj
        have e1 : ({a, j} : Finset (Fin (n + 1))).erase j = {a} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        have e2 : ({a, j} : Finset (Fin (n + 1))).erase a = {j} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        rw [e1, e2]
        simp only [xProd, Finset.prod_singleton, Finset.prod_pair hab]
        rw [awayFrac_eq_iff]
        obtain ⟨L, hL⟩ := hc a j
        refine ⟨L, ?_⟩
        rw [smul_smul, smul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq]
        have := J.mul_mem_left (-((X a * X j) ^ N)) hL
        convert this using 1
        simp only [Finset.prod_pair hab, smul_eq_mul]
        ring
    rw [Cube.d_apply]
    have hbt : b ∈ t.1 := by rw [hab']; simp
    have key : ∀ i : t.1, Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) =
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset b t.1) (x (Cube.eraseIdx t ⟨b, hbt⟩)) := by
      intro i
      obtain ⟨j, hj, e⟩ := hres (Cube.eraseIdx t i) t.1 (Finset.erase_subset i.1 t.1)
      obtain ⟨j', hj', e'⟩ := hres (Cube.eraseIdx t ⟨b, hbt⟩) t.1 (Finset.erase_subset b t.1)
      exact Subtype.ext (e.trans (((hv j (Finset.mem_of_mem_erase hj)).trans
        (hv j' (Finset.mem_of_mem_erase hj')).symm).trans e'.symm))
    rw [Finset.sum_congr rfl fun i _ => by rw [key i], ← Finset.sum_smul,
      Finset.sum_coe_sort t.1 (cubeSign t.1), sum_cubeSign_pair t.2, zero_smul]
    rfl

  obtain ⟨m, hm⟩ := hb.2 ((cechHomologyZeroIso
    (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩)
  obtain ⟨G, hG, hGm⟩ := m.2
  refine ⟨G, mem_polyGrading_natCast.1 hG, fun i => ?_⟩
  have e := cechHomologyZeroIso_grAug (grQuot (polyGrading (Fin (n + 1)) A) J) (d : ℤ) m
    ⟨{i}, Finset.card_singleton i⟩
  have e2 : (cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).hom.hom
      ((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩) =
      ⟨x, hx⟩ :=
    congr(($((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv_hom_id)).hom ⟨x, hx⟩)
  rw [hm, e2] at e
  have e3 : x ⟨{i}, Finset.card_singleton i⟩ = y i := Cube.termOneEquiv_apply _ y i
  have e4 := congrArg Subtype.val (e3.symm.trans e)
  erw [coe_toHomLoc] at e4
  rw [← hGm, awayFrac_eq_iff] at e4
  obtain ⟨l, hl⟩ := e4
  refine ⟨l, ?_⟩
  simp only [xProd, Finset.prod_singleton, LinearMap.coe_restrictScalars, Submodule.mkQ_apply] at hl
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul (p := J) (X i ^ (l + N)),
    Submodule.Quotient.eq] at hl
  convert hl using 1
  simp only [smul_eq_mul]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.LogJacobian

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def substSecondBlockZero (d : ℕ) : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C :=
  Sum.elim (fun b => X b) (fun _ => 0)

theorem constantCoeff_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : constantCoeff (substSecondBlockZero (C := C) d s) = 0 := by
  cases s <;> simp [substSecondBlockZero]

theorem hasSubst_substSecondBlockZero (d : ℕ) : HasSubst (substSecondBlockZero (C := C) d) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_substSecondBlockZero d)

def jacEntry (G : LogFGL v d) (k l : Fin d) : MvPowerSeries (Fin d) C :=
  subst (substSecondBlockZero d) (pderiv C (Sum.inr k) (G.F l))

theorem natCast_int (n : ℕ) : IsIntV v (n : C) := by
  induction n with
  | zero => simp [IsIntV]
  | succ n ih =>
    unfold IsIntV at *
    push_cast
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

theorem mvIsInt_pderiv {σ : Type} {f : MvPowerSeries σ C} (hf : MvIsInt v f) (i : σ) :
    MvIsInt v (pderiv C i f) := by
  intro n
  unfold IsIntV
  rw [coeff_pderiv, v.map_mul]
  have h2 : ((n i : C) + 1) = ((n i + 1 : ℕ) : C) := by push_cast; ring
  rw [h2]
  exact add_nonneg (hf _) (natCast_int _)

theorem mvIsInt_substSecondBlockZero (d : ℕ) (s : Fin d ⊕ Fin d) : MvIsInt v (substSecondBlockZero (C := C) d s) := by
  intro n
  unfold IsIntV
  cases s with
  | inl b => simp only [substSecondBlockZero, Sum.elim_inl]; rw [coeff_X]; split_ifs <;> simp
  | inr b => simp [substSecondBlockZero]

theorem jacEntry_int (G : LogFGL v d) (k l : Fin d) : MvIsInt v (jacEntry G k l) :=
  ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (mvIsInt_pderiv (G.F_int l) _) (mvIsInt_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d)

theorem subst_zero_eq (g : MvPowerSeries (Fin d) C) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) g = MvPowerSeries.C (constantCoeff g) := by
  have : (fun _ : Fin d => (0 : MvPowerSeries (Fin d) C)) = ((0 : Fin d → C) • X) := by
    funext i; simp
  rw [this, ← rescale_eq_subst, rescale_zero_apply]

theorem subst_substSecondBlockZero_firstBlock_log (G : LogFGL v d) (a : Fin d) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a))
      = G.lg a := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun b => X b := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_self]; rfl

theorem subst_substSecondBlockZero_secondBlock (G : LogFGL v d) (g : MvPowerSeries (Fin d) C) :
    subst (substSecondBlockZero (C := C) d) (subst (fun b => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) g)
      = MvPowerSeries.C (constantCoeff g) := by
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (fun b => constantCoeff_X _)) (hasSubst_substSecondBlockZero d)]
  have : (fun b : Fin d => subst (substSecondBlockZero (C := C) d) (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C))
      = fun _ => 0 := by
    funext b; rw [subst_X (hasSubst_substSecondBlockZero d)]; rfl
  rw [this, subst_zero_eq]

theorem formalGroupLaw_subst_secondBlock_zero (G : LogFGL v d) (l : Fin d) : subst (substSecondBlockZero (C := C) d) (G.F l) = (X l : MvPowerSeries (Fin d) C) := by
  obtain ⟨⟨hE0, hlgE⟩, hElg, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hF0c : ∀ l, constantCoeff (subst (substSecondBlockZero (C := C) d) (G.F l)) = 0 := fun l =>
    constantCoeff_subst_eq_zero (hasSubst_substSecondBlockZero d) (constantCoeff_substSecondBlockZero d) (G.F_const l)
  have hF0 : HasSubst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) := hasSubst_of_constantCoeff_zero hF0c
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have key : ∀ a, subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (G.lg a) = G.lg a := by
    intro a
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), G.lg_F a,
      subst_add (hasSubst_substSecondBlockZero d), subst_substSecondBlockZero_firstBlock_log, subst_substSecondBlockZero_secondBlock G, G.lg_const a, map_zero, add_zero]
  have e1 : subst (fun l => subst (substSecondBlockZero (C := C) d) (G.F l)) (X l : MvPowerSeries (Fin d) C)
      = subst (substSecondBlockZero d) (G.F l) := subst_X hF0 l
  rw [← e1, ← hElg l, subst_comp_subst_apply hlg hF0]
  simp only [key, hElg]

theorem jac_lg_mul_jacEntry (G : LogFGL v d) (a k : Fin d) :
    ∑ l, pderiv C l (G.lg a) * jacEntry G k l = if a = k then 1 else 0 := by
  classical
  have h := congrArg (pderiv C (Sum.inr k)) (G.lg_F a)
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst G.F_const, map_add,
    ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (fun b => constantCoeff_X _),
    ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (fun b => constantCoeff_X _)] at h
  simp only [pderiv_X, Pi.single_apply, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero,
    zero_add, Sum.inr.injEq, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have h2 := congrArg (subst (substSecondBlockZero (C := C) d)) h
  rw [subst_substSecondBlockZero_secondBlock G, ← coe_substAlgHom (hasSubst_substSecondBlockZero d), map_sum] at h2
  simp only [map_mul, coe_substAlgHom] at h2
  simp only [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) (hasSubst_substSecondBlockZero d), formalGroupLaw_subst_secondBlock_zero,
    subst_self, id] at h2
  have hc : constantCoeff (pderiv C k (G.lg a)) = if a = k then 1 else 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, G.lg_lin]; simp
  simp only [jacEntry]
  rw [h2, hc]
  split_ifs <;> simp

theorem pderiv_expOf (G : LogFGL v d) (l k : Fin d) :
    pderiv C k (expOf G l) = subst (expOf G) (jacEntry G k l) := by
  classical
  obtain ⟨⟨hE0, hlgE⟩, -, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  let J : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun a l => subst (expOf G) (pderiv C l (G.lg a))
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => pderiv C k (expOf G l)
  let N : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) C) :=
    Matrix.of fun l k => subst (expOf G) (jacEntry G k l)
  have hJM : J * M = 1 := by
    ext a k
    have h := congrArg (pderiv C k) (hlgE a)
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hE0, pderiv_X, Pi.single_apply] at h
    simp only [J, M, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
  have hJN : J * N = 1 := by
    refine Matrix.ext fun a k => ?_
    have h := congrArg (subst (expOf G)) (jac_lg_mul_jacEntry G a k)
    rw [← coe_substAlgHom hE, map_sum] at h
    simp only [map_mul, coe_substAlgHom] at h
    simp only [J, N, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, h]
    split_ifs
    · rw [← substAlgHom_apply hE, map_one]
    · rw [← substAlgHom_apply hE, map_zero]
  have hNJ : N * J = 1 := mul_eq_one_comm.mp hJN
  have hMN : M = N := by
    calc M = (N * J) * M := by rw [hNJ, Matrix.one_mul]
      _ = N * (J * M) := Matrix.mul_assoc _ _ _
      _ = N := by rw [hJM, Matrix.mul_one]
  exact congrFun (congrFun hMN l) k

end

theorem exists_integral_invariant_derivation : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  intro C _ _ v d G
  refine ⟨jacEntry G, jacEntry_int G, fun f k α => ?_⟩
  obtain ⟨⟨hE0, -⟩, -, -⟩ := GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hP : ∀ l, (show MvPowerSeries (Fin d) C from
      fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f) = pderiv C l f := by
    intro l; ext β; rw [coeff_pderiv, mul_comm]; rfl
  simp only [hP]
  rw [mul_comm, ← coeff_pderiv, ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hE0]
  simp only [pderiv_expOf]
  congr 1
  rw [← substAlgHom_apply hE, map_sum]
  simp only [map_mul, substAlgHom_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.LogJacobian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem lift_linear_of_injective {S : Type*} [Ring S] {N A B C : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C]
    (hN : Module.Baer S N)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C) (hex : ∀ b, v b = 0 → ∃ a, u a = b)
    (f : B →ₗ[S] N) (hf : f ∘ₗ u = 0) : ∃ g : C →ₗ[S] N, g ∘ₗ v = f := by
  have hle : LinearMap.ker v ≤ LinearMap.ker f := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    simpa using LinearMap.congr_fun hf a
  let f₁ : (B ⧸ LinearMap.ker v) →ₗ[S] N := (LinearMap.ker v).liftQ f hle
  let f₂ : LinearMap.range v →ₗ[S] N := f₁ ∘ₗ (v.quotKerEquivRange).symm.toLinearMap
  obtain ⟨g, hg⟩ := hN.extension_property (LinearMap.range v).subtype (LinearMap.range v).injective_subtype f₂
  refine ⟨g, LinearMap.ext fun b => ?_⟩
  have h1 := LinearMap.congr_fun hg ⟨v b, b, rfl⟩
  have h2 : (v.quotKerEquivRange).symm ⟨v b, b, rfl⟩ = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h1
  rw [LinearMap.comp_apply, h1]
  simp only [f₂, f₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem lift_homSh : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  intro R _ J X hinj A B C u v hex f hf
  obtain ⟨e, hnat, -⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  have he0 : ∀ M : ModuleCat.{1} (ULift.{1} R), e X M 0 = 0 := by
    intro M
    have := hnat X M M 0 0
    rw [zero_comp, ModuleCat.hom_zero, LinearMap.comp_zero] at this
    exact this
  have hf' : e X B f ∘ₗ u.hom = 0 := by rw [← hnat, hf, he0]
  obtain ⟨g', hg'⟩ := lift_linear_of_injective (Module.Baer.of_injective hinj) u.hom v.hom hex (e X B f) hf'
  refine ⟨(e X C).symm g', (e X B).injective ?_⟩
  rw [hnat, Equiv.apply_symm_apply, hg']
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparate
section
namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodCohomologyClassOfRichBased
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_perCl {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hR : K.Rich) (hB : K.Based) (c : H1 K.Oc) : ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective K.Oc c
  obtain ⟨G, hG⟩ := GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based K hR hB f.1 (fun T T' T'' φ ψ _ _ ↦ f.2 φ ψ)
  let f' : Z1 K.Oc := f - ⟨d0 K.Oc G, commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc G⟩
  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), f'.1 T T' φ = f.1 T T' φ - (G T' - φ.φ (G T)) :=
    fun _ _ _ ↦ rfl
  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → f'.1 T T' φ = 0 := by
    intro T T' φ hφ
    rw [hv, hG T T' φ hφ, sub_self]
  have hc : ∀ {T T' T'' : K.Obj} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f'.1 T T'' (φ ≫ ψ) = ψ.φ (f'.1 T T' φ) + f'.1 T' T'' ψ := fun φ ψ ↦ f'.2 φ ψ
  have hp : ∀ l : Λ, ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l →
      f'.1 T T' φ = algebraMap (Hol F.V) T'.C p :=
    fun l ↦ GlobalTheory.T.invariant_cochainOne_const_on_degree K hR f'.1 l
      (fun T T' T'' φ ψ _ hψ ↦ by rw [hc, h0 _ _ ψ hψ, add_zero])
      (fun T T' T'' φ ψ hφ _ ↦ by rw [hc, h0 _ _ φ hφ, map_zero, zero_add])
  choose p hp using hp
  have hcom : ∀ {T T' : K.Obj} (ψ : T ⟶ T') (x : Hol F.V),
      ψ.φ (algebraMap (Hol F.V) T.C x) = algebraMap (Hol F.V) T'.C x := fun ψ x ↦ ψ.φ.commutes x
  have hadd : ∀ l m, p (l + m) = p l + p m := by
    intro l m
    rw [← sub_eq_zero]
    refine GlobalTheory.T.parameter_function_eq_zero_of_composable K hR l m _ fun k k' k'' hl hm ↦ ?_
    let φ : K.triv k ⟶ K.triv k' := ptHom (K.triv k') hl
    let ψ : K.triv k' ⟶ K.triv k'' := ptHom (K.triv k'') hm
    have e := hc φ ψ
    rw [hp (l + m) _ _ (φ ≫ ψ) rfl, hp l _ _ φ rfl, hp m _ _ ψ rfl, hcom ψ] at e
    change K.cst k'' (p (l + m)) = K.cst k'' (p l) + K.cst k'' (p m) at e
    rw [map_sub, map_add, e, sub_self]
  refine ⟨AddMonoidHom.mk' p hadd, ?_⟩
  rw [perCl, H1.mk_eq_mk]
  refine ⟨G, ?_⟩
  funext T T' φ
  have e := hp φ.deg T T' φ rfl
  rw [hv] at e
  change G T' - φ.φ (G T) = f.1 T T' φ - algebraMap (Hol F.V) T'.C (p φ.deg)
  rw [← e]
  ring

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackMulPOfPTorsionInvariant
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_tensor_map_eq_of_exact {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by
  obtain ⟨F', rfl⟩ := (Module.Flat.lTensor_exact N h F).1 h₂
  have h₃ : g.rTensor M F' = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) f hf
    rw [map_zero, ← h₁, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  obtain ⟨c, rfl⟩ := (Module.Flat.rTensor_exact M h F').1 h₃
  exact ⟨c, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩

theorem PDivGroup.exists_tensorSquare_mulP_eq {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1))
    (h₁ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0)
    (h₂ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0) :
    ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  refine exists_tensor_map_eq_of_exact (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) _
    (Test.mulP_injective G n) (fun a => ⟨fun ha => ?_, ?_⟩) F h₁ h₂
  · exact GlobalTheory.T.exists_mulP_eq_of_transl_invariant G n a (sub_eq_zero.1 ha)
  · rintro ⟨e, rfl⟩
    exact sub_eq_zero.2 (G.transl_mulP n e)

end GlobalTheory
end

