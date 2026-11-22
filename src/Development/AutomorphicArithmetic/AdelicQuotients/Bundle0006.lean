import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsLowerEntryNeZeroOfNormCharpolyIrreducible
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

section BlockTri

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (Q : ι → Prop) [DecidablePred Q]

private def LowZero (M : Matrix ι ι R) : Prop := ∀ j, ¬ Q j → ∀ i, Q i → M j i = 0

private theorem lowZero_mul {A B : Matrix ι ι R} (hA : LowZero Q A) (hB : LowZero Q B) :
    LowZero Q (A * B) := by
  intro j hj i hi
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : Q k
  · rw [hA j hj k hk, zero_mul]
  · rw [hB k hk i hi, mul_zero]

private theorem toSq_mul {A B : Matrix ι ι R} (hB : LowZero Q B) :
    (A * B).toSquareBlockProp Q = A.toSquareBlockProp Q * B.toSquareBlockProp Q := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  change (A * B) i l = ∑ k : {x // Q x}, A i k * B k l
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype Q]
  have h0 : ∑ k : {x // ¬ Q x}, A i k * B k l = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hB k k.2 l hl, mul_zero]
  rw [h0, add_zero]

private theorem charpoly_toSq_dvd {M : Matrix ι ι R} (hM : LowZero Q M) :
    (M.toSquareBlockProp Q).charpoly ∣ M.charpoly := by
  have hz : ∀ i, ¬ Q i → ∀ j, Q j → M.charmatrix i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Matrix.charmatrix_apply_ne M i j hij, hM i hi j hj]
    simp
  have hsq : (M.charmatrix).toSquareBlockProp Q = (M.toSquareBlockProp Q).charmatrix := by
    ext1 ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      change M.charmatrix i i = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨i, hi⟩
      rw [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]
      rfl
    · have hne : (⟨i, hi⟩ : {x // Q x}) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
      change M.charmatrix i j = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.charmatrix_apply_ne M i j hij, Matrix.charmatrix_apply_ne _ _ _ hne]
      rfl
  have h := Matrix.twoBlockTriangular_det (M.charmatrix) Q hz
  rw [hsq] at h
  exact ⟨_, h⟩

end BlockTri

theorem UpperTheory.exists_lower_entry_ne_zero_of_norm_charpoly_irreducible :
    ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
          (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ : GL (Fin n) E) (p : F[X]), Irreducible p →
          p.map (algebraMap F E) = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly →
          ∀ r : ℕ, 0 < r → r < n → ∃ i j : Fin n, (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (δ : Matrix (Fin n) (Fin n) E) j i ≠ 0 := by
  intro F E _ _ _ _ _ σ hgen n δ p hp hpc r hr0 hrn
  by_contra hcon
  push_neg at hcon
  let Q : Fin n → Prop := fun i => (i : ℕ) < r
  have hL : LowZero Q (δ : Matrix (Fin n) (Fin n) E) :=
    fun j hj i hi => hcon i j hi (not_lt.mp hj)
  have hdet : ((δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q).det ≠ 0 := by
    intro h0
    have h := Matrix.twoBlockTriangular_det (δ : Matrix (Fin n) (Fin n) E) Q hL
    rw [h0, zero_mul] at h
    have hu : IsUnit (δ : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit
    exact hu.ne_zero h
  let δ₁ : GL {i // Q i} E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hδ₁ : (δ₁ : Matrix {i // Q i} {i // Q i} E) =
      (δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q := rfl
  have key : ∀ m : ℕ,
      LowZero Q ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∧
      ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q =
        ((twNorm (sigmaGL σ) m δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E) := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro j hj i hi
        have hij : j ≠ i := fun h => hj (h ▸ hi)
        simp [hij]
      · ext ⟨i, hi⟩ ⟨l, hl⟩
        simp [Matrix.toSquareBlockProp, Matrix.one_apply]
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hpow : ((((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) δ : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) = (δ : Matrix (Fin n) (Fin n) E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hpow₁ : ((((sigmaGL σ : Monoid.End (GL {i // Q i} E)) ^ m) δ₁ : GL {i // Q i} E) :
          Matrix {i // Q i} {i // Q i} E) =
            (δ₁ : Matrix {i // Q i} {i // Q i} E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hLm : LowZero Q ((δ : Matrix (Fin n) (Fin n) E).map (σ ^ m)) := by
        intro j hj i hi
        simp [hL j hj i hi]
      rw [twNorm_succ, twNorm_succ, Units.val_mul, Units.val_mul, hpow, hpow₁]
      refine ⟨lowZero_mul Q ih1 hLm, ?_⟩
      rw [toSq_mul Q hLm, ih2, hδ₁]
      rfl
  have hdvd : ((normGL σ δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E).charpoly ∣
      ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    have h := charpoly_toSq_dvd Q (key (Module.finrank F E)).1
    rw [(key (Module.finrank F E)).2] at h
    exact h
  obtain ⟨P₁, hP₁⟩ := charpoly_normGL_lifts σ hgen δ₁
  have hdvd' : P₁ ∣ p := by
    rw [← Polynomial.map_dvd_map' (algebraMap F E), hP₁, hpc]
    exact hdvd
  have hdegP : P₁.natDegree = Fintype.card {i // Q i} := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := P₁), hP₁, Matrix.charpoly_natDegree_eq_dim]
  have hdegp : p.natDegree = n := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := p), hpc, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hpos : 0 < Fintype.card {i // Q i} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, hr0⟩⟩
  have hlt : Fintype.card {i // Q i} < n := by
    have h := Fintype.card_subtype_lt (p := Q) (x := (⟨r, hrn⟩ : Fin n)) (by simp [Q])
    simpa using h
  rcases hp.dvd_iff.mp hdvd' with hu | ha
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have h1 := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated ha)
    omega
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroDvdCharpolyLeInfinitePlace
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma norm_multiset_prod_le_pow (B : ℝ) (hB : 1 ≤ B) (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ B) : ‖s.prod‖ ≤ B ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (hs a (Multiset.mem_cons_self ..))
      (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)) (norm_nonneg _) (by linarith)

private lemma norm_root_charpoly_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (z : ℂ) (hz : M.charpoly.IsRoot z) :
    ‖z‖ ≤ max 1 (n : ℝ) * R := by
  have hdet : ((Matrix.scalar (Fin n)) z - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) ⟨i0, Finset.mem_univ _⟩
  have hvi : 0 < ‖v i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hi i0 (Finset.mem_univ _))
  have hrow : z * v i = ∑ j, M i j * v j := by
    have h1 := congrFun hMv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
    have h2 : ((Matrix.scalar (Fin n)) z).mulVec v i = z * v i := by
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [h2] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  have hle : ‖z‖ * ‖v i‖ ≤ n * R * ‖v i‖ := by
    rw [← norm_mul, hrow]
    calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, R * ‖v i‖ := Finset.sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (hM i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) (by linarith))
      _ = n * R * ‖v i‖ := by simp [Finset.sum_const, mul_assoc]
  have h3 : ‖z‖ ≤ n * R := le_of_mul_le_mul_right hle hvi
  exact h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

private lemma norm_coeff_zero_le_complex {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hM : ∀ i j, ‖M i j‖ ≤ R) (p : ℂ[X]) (hp : p.Monic) (hd : p ∣ M.charpoly) :
    ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  have hB : 1 ≤ max 1 (n : ℝ) * R := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hR
  have hs : p.Splits := IsAlgClosed.splits p
  have hc : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  rw [hs.coeff_zero_eq_prod_roots_of_monic hp, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  have hroots : ∀ z ∈ p.roots, ‖z‖ ≤ max 1 (n : ℝ) * R := fun z hz =>
    norm_root_charpoly_le M R hR hM z ((Polynomial.isRoot_of_mem_roots hz).dvd hd)
  refine (norm_multiset_prod_le_pow _ hB _ hroots).trans ?_
  rw [← hs.natDegree_eq_card_roots]
  refine pow_le_pow_right₀ hB ?_
  have h := natDegree_le_of_dvd hd hc
  simpa [Matrix.charpoly_natDegree_eq_dim] using h

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E) (n : ℕ) (M : Matrix (Fin n) (Fin n) w.Completion) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : w.Completion[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ (max 1 (n : ℝ) * R) ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  have hn : ∀ x, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
  have h := norm_coeff_zero_le_complex (M.map (InfinitePlace.Completion.extensionEmbedding w)) R hR
    (fun i j => by simpa [hn] using hM i j)
    (p.map (InfinitePlace.Completion.extensionEmbedding w))
    (hp.map _)
    (by rw [Matrix.charpoly_map]; exact Polynomial.map_dvd _ hd)
  rwa [coeff_map, hn] at h
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroFactorCharpolyIwahoriDiagPowLe
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private lemma nrm_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (h : ValuativeRel.valuation (w.adicCompletion E) x ≤ 1) : ‖x‖ ≤ 1 :=
  norm_le_one_of_mem w ((mem_valuationInteger_iff w x).1 ((Valuation.mem_integer_iff _ _).2 h))

private lemma nrm_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x y : w.adicCompletion E}
    (h : ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.valuation (w.adicCompletion E) y) :
    ‖x‖ = ‖y‖ := by
  have key : ∀ a b : w.adicCompletion E, b ≠ 0 →
      ValuativeRel.valuation (w.adicCompletion E) a = ValuativeRel.valuation (w.adicCompletion E) b →
      ‖a‖ ≤ ‖b‖ := by
    intro a b hb hab
    have hb' : ValuativeRel.valuation (w.adicCompletion E) b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
    have h1 : ValuativeRel.valuation (w.adicCompletion E) (a / b) ≤ 1 := by
      rw [map_div₀, hab, div_self hb']
    have h2 := nrm_le w _ h1
    rw [norm_div] at h2
    exact (div_le_one (norm_pos_iff.2 hb)).1 h2
  by_cases hy : y = 0
  · subst hy
    have hx : x = 0 := (Valuation.zero_iff _).1 (by rw [h, map_zero])
    rw [hx]
  have hx : x ≠ 0 := by
    intro hx
    exact hy ((Valuation.zero_iff _).1 (by rw [← h, hx, map_zero]))
  exact le_antisymm (key x y hy h) (key y x hx h.symm)

private lemma nrm_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ‖((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E)‖ ≤ 1 / 2 := by
  have hlt : ValuativeRel.valuation (w.adicCompletion E)
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) < 1 :=
    GLnLocal.valuation_uniformizer_lt_one _
  have hne : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = x at hlt hne
  have hv : Valued.v x < 1 := by
    by_contra hge
    have hge' : 1 ≤ Valued.v x := not_lt.1 hge
    have hinv : Valued.v x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge'
    have hm : x⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers E w :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hinv
    have h3 := (Valuation.mem_integer_iff _ _).1 ((mem_valuationInteger_iff w _).2 hm)
    rw [map_inv₀] at h3
    have h0 : ValuativeRel.valuation (w.adicCompletion E) x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    exact absurd h3 (not_le.2 ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 hlt))
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hne
  have hN : 1 < Ideal.absNorm w.asIdeal := HeightOneSpectrum.one_lt_absNorm w
  have hN2 : (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast hN
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by exact_mod_cast hN
  have hlt1 : ‖x‖ < 1 := by
    rw [FinitePlace.norm_def]
    exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff h1).2 hv
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hvne] at hlt1 ⊢
  generalize (WithZero.unzero hvne).toAdd = m at hlt1 ⊢
  have hm : m ≤ -1 := by
    by_contra hc
    have hm0 : 0 ≤ m := by omega
    have h5 : (1 : NNReal) ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ m := one_le_zpow₀ h1.le hm0
    have h6 : (1 : ℝ) ≤ (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) := by exact_mod_cast h5
    exact absurd hlt1 (not_lt.2 h6)
  have h6 : (Ideal.absNorm w.asIdeal : NNReal) ^ m ≤ (Ideal.absNorm w.asIdeal : NNReal) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ h1.le hm
  have h7 : (((Ideal.absNorm w.asIdeal : NNReal) ^ m : NNReal) : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
    have := NNReal.coe_le_coe.2 h6
    simpa using this
  refine h7.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) hN2

private lemma prod_zp {n : ℕ} {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : Fin n → ℤ) (J : Finset (Fin n)) :
    ∏ i ∈ J, x ^ e i = x ^ ∑ i ∈ J, e i := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

private lemma fin_real (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1 / 2) (j m : ℕ) (hm : 1 ≤ m) :
    r ^ (j * m) * 2 ^ j ≤ 1 := by
  have hr1 : r ≤ 1 := by linarith
  have ha : r ^ (j * m) ≤ r ^ j := pow_le_pow_of_le_one h0.le hr1 (Nat.le_mul_of_pos_right j hm)
  have hb : r ^ j * 2 ^ j ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right ha (by positivity)).trans hb

theorem UpperTheory.norm_coeff_zero_factor_charpoly_iwahori_diagPow_le :
    A1 → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ν : Fin n → ℤ), Function.Injective ν → ∑ i, ν i = 0 →
        (∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0) → ∀ j : ℕ, 0 < j →
        ∀ a ∈ GLnLocal.iwahori (w.adicCompletion E) n, ∀ b ∈ GLnLocal.iwahori (w.adicCompletion E) n,
        ∀ p₁ p₂ : (w.adicCompletion E)[X], p₁.Monic → p₂.Monic → 0 < p₁.natDegree → 0 < p₂.natDegree →
        p₁ * p₂ = ((a * Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly →
        ‖p₁.coeff 0‖ * 2 ^ j ≤ 1 ∨ ‖p₂.coeff 0‖ * 2 ^ j ≤ 1 := by
  intro hA E _ _ w n ν hν hsum hJ j hj a ha b hb p₁ p₂ hm₁ hm₂ hd₁ hd₂ hp
  classical
  have hϖ : ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ≠ 0 :=
    GLnLocal.uniformizer_ne_zero _
  have hr := nrm_unif w
  have hdiag : ∀ J : Finset (Fin n), ∏ i ∈ J, ((Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) :
      GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i =
      ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    intro J
    rw [Finset.mul_sum, ← prod_zp _ hϖ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  generalize ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) = ϖ at hϖ hr hdiag
  have hr0 : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ
  have hinj : Function.Injective (fun i => (j : ℤ) * ν i) := fun x y h =>
    hν (mul_left_cancel₀ (by exact_mod_cast hj.ne') h)
  obtain ⟨J, hJc, hJv⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb p₁ hm₁ ⟨p₂, hp.symm⟩
  have hcp : (p₁ * p₂).natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨J', hJ'c, hJ'v⟩ := hA (w.adicCompletion E) n _ hinj a ha b hb (p₁ * p₂) (hm₁.mul hm₂) (hp ▸ dvd_rfl)
  have hJ'u : J' = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hJ'c, hcp, Fintype.card_fin]
  have hdeg : p₁.natDegree + p₂.natDegree = n := by
    rw [← hm₁.natDegree_mul hm₂]; exact hcp
  have hne : J.Nonempty := Finset.card_pos.1 (by omega)
  have hnu : J ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hJc
    omega
  have hs := hJ J hne hnu
  have h1 : ‖p₁.coeff 0‖ = ‖ϖ‖ ^ ((j : ℤ) * ∑ i ∈ J, ν i) := by
    rw [nrm_eq w (hJv.trans (by rw [hdiag])), norm_zpow]
  have h2 : ‖p₁.coeff 0‖ * ‖p₂.coeff 0‖ = 1 := by
    rw [← norm_mul, ← mul_coeff_zero, nrm_eq w (hJ'v.trans (congrArg _ (hdiag J'))), hJ'u, hsum]
    simp
  generalize (∑ i ∈ J, ν i) = s at hs h1
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · right
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -s)
    have hs' : s = -(m : ℤ) := by omega
    have hm1 : 1 ≤ m := by omega
    have h3 : ‖p₂.coeff 0‖ = ‖ϖ‖ ^ (j * m) := by
      have h4 : ‖p₁.coeff 0‖ = (‖ϖ‖ ^ (j * m))⁻¹ := by
        rw [h1, hs', mul_neg, zpow_neg, ← Nat.cast_mul, zpow_natCast]
      rw [h4] at h2
      exact (inv_mul_eq_one₀ (pow_ne_zero _ hr0.ne')).1 h2 |>.symm
    rw [h3]
    exact fin_real _ hr0 hr j m hm1
  · left
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hgt.le
    have hm1 : 1 ≤ m := by omega
    rw [h1, hm, ← Nat.cast_mul, zpow_natCast]
    exact fin_real _ hr0 hr j m hm1
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem continuous_infMap {M M' : Type} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact NumberField.LiesOver.continuous_completionMap

private theorem norm_algebraMap_of_smul_eq (σ : E ≃ₐ[F] E) (u w : HeightOneSpectrum (𝓞 E))
    (h : σ • u = w) (l : E) :
    ‖algebraMap E (w.adicCompletion E) (σ l)‖ = ‖algebraMap E (u.adicCompletion E) l‖ := by
  subst h
  exact norm_algebraMap_smul σ u l

private theorem norm_finMap (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E))
    (y : (comapPrime (σ : E ≃+* E) w).adicCompletion E) :
    ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine (HeightOneSpectrum.denseRange_algebraMap E (comapPrime (σ : E ≃+* E) w)).induction_on
    (p := fun y => ‖finiteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖) y
    (isClosed_eq (continuous_norm.comp (continuous_finiteCompletionMap _ w)) continuous_norm)
    fun l => ?_
  rw [finiteCompletionMap_algebraMap]
  exact norm_algebraMap_of_smul_eq σ _ w (by rw [comapPrime_eq_inv_smul, smul_inv_smul]) l

private theorem norm_algebraMap_completion (w : InfinitePlace E) (x : E) :
    ‖algebraMap E w.Completion x‖ = w x :=
  InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ x)

private theorem norm_infMap (σ : E ≃ₐ[F] E) (w : InfinitePlace E)
    (y : (w.comap ((σ : E ≃+* E) : E →+* E)).Completion) :
    ‖infiniteCompletionMap (σ : E ≃+* E) w y‖ = ‖y‖ := by
  refine InfinitePlace.Completion.induction_on _ y
    (isClosed_eq (continuous_norm.comp (continuous_infMap _ w)) continuous_norm) fun a => ?_
  change ‖infiniteCompletionMap (σ : E ≃+* E) w (algebraMap E _ a.ofAbs)‖ =
    ‖algebraMap E (w.comap ((σ : E ≃+* E) : E →+* E)).Completion a.ofAbs‖
  rw [infiniteCompletionMap_algebraMap, norm_algebraMap_completion, norm_algebraMap_completion,
    InfinitePlace.comap_apply]
  rfl

private theorem norm_snd_congr (a : 𝔸[E]) {w₁ w₂ : HeightOneSpectrum (𝓞 E)} (h : w₁ = w₂) :
    ‖a.2 w₁‖ = ‖a.2 w₂‖ := by
  subst h
  rfl

private theorem norm_fst_congr (a : 𝔸[E]) {w₁ w₂ : InfinitePlace E} (h : w₁ = w₂) :
    ‖a.1 w₁‖ = ‖a.1 w₂‖ := by
  subst h
  rfl

end

theorem UpperTheory.norm_galois_smul_adele_component_at_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (a : 𝔸[E]),
        (∀ w : HeightOneSpectrum (𝓞 E), ‖(galAd σ a).2 (σ • w)‖ = ‖a.2 w‖) ∧
        ∀ w : InfinitePlace E, ‖(galAd σ a).1 (σ • w)‖ = ‖a.1 w‖ := by
  intro F E _ _ _ _ _ σ a
  rw [galAd_apply]
  constructor
  · intro w
    rw [smul_snd, norm_finMap]
    exact norm_snd_congr a (by rw [comapPrime_eq_inv_smul, inv_smul_smul])
  · intro w
    rw [smul_fst, norm_infMap]
    exact norm_fst_congr a (by rw [comap_eq_inv_smul, inv_smul_smul])
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.QuotientIntegralLtTopOfInvariantClosedEmbedding
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.quotientIntegral_lt_top_of_invariant_closedEmbedding :
    Q1 → Q2 → ∀ (G T : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (H : Subgroup G) [LocallyCompactSpace H], IsClosed (H : Set G) →
        ∀ (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] [ν.IsMulRightInvariant]
          (i : T →* H), Topology.IsClosedEmbedding i → ∀ Φ : H → ℂ, Continuous Φ → (∀ t x, Φ (i t * x) = Φ x) →
          (∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) →
          quotInt μ (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν Φ = quotInt μ id i ν Φ := by
  intro q1 q2 G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ hH μ _ ν _ _ _ i hi Φ hΦ hinv hfin
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨ρ, hρc, hρ, -⟩ := q2 H T ν i hi
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  have hex : ∃ ρ', IsNormAlong (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν ρ' := by
    refine ⟨Function.extend (Subtype.val : H → G) (fun x => (ρ x : ℝ≥0∞)) 0,
      hemb.measurable_extend hρ.1 measurable_zero, fun x => ?_⟩
    rw [← hρ.2 x]
    refine lintegral_congr fun t => ?_
    exact Subtype.val_injective.extend_apply (fun x => (ρ x : ℝ≥0∞)) 0 (i t * x)
  have hn : IsNormAlong id i ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => hex.choose_spec.2 x⟩
  have h1 := q1 H H T μ ν (MonoidHom.id H) i measurable_id hi.continuous Φ
    (fun x : H => hex.choose (x : G)) hΦ.measurable hinv hn (hfin _ hn)
  refine Eq.trans ?_ h1.symm
  unfold quotInt
  rw [dif_pos hex]
  rfl
end

