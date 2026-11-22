import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdicNormProdLeProdOfInjectiveClasses
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.adicNorm_prod_le_prod_of_injective_classes :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (O S R : Type) [Fintype O] [Fintype S] (f : O → S → ℂ), (∀ o s, IsIntegral ℤ (f o s)) → ∀ (X : O → Finset R) (cl : ∀ o, ↥(X o) → S), (∀ o, Function.Injective (cl o)) → ‖ι.symm (∏ o, ∏ s, f o s)‖ ≤ ∏ o, ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖ := by
  intro l _ ι O S R _ _ f hf X cl hcl
  classical
  have h1 : ∀ o s, ‖ι.symm (f o s)‖ ≤ 1 := fun o s =>
    GlobalTheory.norm_le_one_of_isIntegral_int (map_isIntegral_int ι.symm (hf o s))
  rw [map_prod, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun o _ => ?_)
  rw [map_prod, norm_prod]
  have h2 : ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖
      = ∏ s ∈ Finset.univ.map ⟨cl o, hcl o⟩, ‖ι.symm (f o s)‖ := by
    rw [Finset.prod_map]; rfl
  rw [h2]
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
    (fun _ _ => norm_nonneg _) (fun s _ _ => h1 o s)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleOfNewformAttached
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.admissible_of_newform_attached :
    NewformAut → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ), 1 ≤ e → ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W → (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) → Level l M ![(e : ℤ), -(e : ℤ)] W → IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → AdmR ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  intro hN Ω _ _ _ l _ ι e M he W hirr hf hlev hcyc
  obtain ⟨f, hf⟩ := hf
  refine ⟨hirr, hN (2 * e + 1) (by omega) f l Ω ι W _ hf, hlev, ⟨_, hcyc, ?_⟩,
    Or.inr fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]), fun s => ?_⟩
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  generalize ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.vecMul, dotProduct] <;> ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockConjugateRankThreeRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private def gl2ToGL3BlockMatrix {k : Type} [Field k] (a : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) k :=
  !![a 0 0, 0, a 0 1; 0, 1, 0; a 1 0, 0, a 1 1]

private theorem gl2ToGL3BlockMatrix_mul {k : Type} [Field k] (a b : Matrix (Fin 2) (Fin 2) k) :
    gl2ToGL3BlockMatrix (a * b) = gl2ToGL3BlockMatrix a * gl2ToGL3BlockMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2ToGL3BlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_embedding_one {k : Type} [Field k] :
    gl2ToGL3BlockMatrix (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2ToGL3BlockMatrix]

private def gl2ToGL3BlockHom {k : Type} [Field k] : GL (Fin 2) k →* GL (Fin 3) k :=
  Units.map ({ toFun := gl2ToGL3BlockMatrix, map_one' := block_embedding_one, map_mul' := gl2ToGL3BlockMatrix_mul } :
    Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 3) (Fin 3) k)

theorem UpperTheory.block_conjugate_rank_three_rep :
    ∀ (Γ Δ k : Type) [Group Γ] [Group Δ] [Field k] (φ : Γ → Δ) (W W' : Δ →* GL (Fin 2) k) (ρ ρ' : Γ →* GL (Fin 3) k) (g g' : GL (Fin 3) k), (∀ s, ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W (φ s) 0 0, 0, W (φ s) 0 1; 0, 1, 0; W (φ s) 1 0, 0, W (φ s) 1 1]) → (∀ s, ((g' * ρ' s * g'⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W' (φ s) 0 0, 0, W' (φ s) 0 1; 0, 1, 0; W' (φ s) 1 0, 0, W' (φ s) 1 1]) → RepIso W W' → RepIso ρ ρ' := by
  intro Γ Δ k _ _ _ φ W W' ρ ρ' g g' hρ hρ' hWW
  obtain ⟨h, hh⟩ := hWW
  let H : GL (Fin 3) k := gl2ToGL3BlockHom h
  have c : ∀ s, g' * ρ' s * g'⁻¹ = H * (g * ρ s * g⁻¹) * H⁻¹ := by
    intro s
    apply Units.ext
    have e1 : ((H * (g * ρ s * g⁻¹) * H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (H : Matrix (Fin 3) (Fin 3) k) * ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          ((H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [Units.val_mul, Units.val_mul]
    rw [e1, hρ s, hρ' s]
    change gl2ToGL3BlockMatrix ((W' (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      gl2ToGL3BlockMatrix (h : Matrix (Fin 2) (Fin 2) k) * gl2ToGL3BlockMatrix ((W (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        gl2ToGL3BlockMatrix ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [hh (φ s), Units.val_mul, Units.val_mul, gl2ToGL3BlockMatrix_mul, gl2ToGL3BlockMatrix_mul]
  refine ⟨g'⁻¹ * H * g, fun s => ?_⟩
  calc ρ' s = g'⁻¹ * (g' * ρ' s * g'⁻¹) * g' := by group
    _ = g'⁻¹ * (H * (g * ρ s * g⁻¹) * H⁻¹) * g' := by rw [c s]
    _ = g'⁻¹ * H * g * ρ s * (g'⁻¹ * H * g)⁻¹ := by group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinTraceDifferenceLogBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.eisenstein_trace_difference_log_bound :
    ∀ (q e k : ℕ), 7 ≤ q → 1 ≤ e → 0 < k → ∀ z t : ℂ, z ^ k = 1 → ‖t‖ ≤ 3 → IsIntegral ℤ ((q : ℂ) ^ e * t) → t ≠ eis3 q e z ∧ IsIntegral ℤ ((q : ℂ) ^ e * (t - eis3 q e z)) ∧ Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1 := by
  intro q e k hq he hk z t hz ht hI
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hk.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzn
  have hQN : 7 ≤ q ^ e := le_trans hq (Nat.le_self_pow (by omega) q)
  have hlogQ : Real.log ((q ^ e : ℕ) : ℝ) = e * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hcast : (q : ℂ) ^ e = ((q ^ e : ℕ) : ℂ) := by push_cast; rfl
  unfold eis3
  rw [hcast] at hI ⊢
  generalize q ^ e = N at hQN hlogQ hI
  have hN : (7 : ℝ) ≤ N := by exact_mod_cast hQN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hexp : (N : ℂ) * (t - ((N : ℂ)⁻¹ * z + 1 + (N : ℂ) * z⁻¹)) =
      (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ := by
    field_simp
    ring
  have hnA : ‖(N : ℂ) * t - z - N‖ ≤ 4 * N + 1 := by
    have h1 : ‖(N : ℂ) * t‖ ≤ 3 * N := by
      rw [norm_mul, Complex.norm_natCast]
      nlinarith
    have h2 := norm_sub_le ((N : ℂ) * t - z) (N : ℂ)
    have h3 := norm_sub_le ((N : ℂ) * t) z
    rw [Complex.norm_natCast] at h2
    linarith
  have hnB : ‖(N : ℂ) * N * z⁻¹‖ = N * N := by
    simp [hzn]
  have hne : (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, hnB] at hnA
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hexp, ← h, sub_self, mul_zero]
  · rw [hexp]
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_one)
    have hzI' : IsIntegral ℤ z⁻¹ :=
      IsIntegral.of_pow hk (by rw [inv_pow, hz, inv_one]; exact isIntegral_one)
    have hNI : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact ((hI.sub hzI).sub hNI).sub ((hNI.mul hNI).mul hzI')
  · rw [hexp]
    have hb : ‖(N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹‖ ≤ 2 * ((N : ℝ) * N) := by
      have := norm_sub_le ((N : ℂ) * t - z - N) ((N : ℂ) * N * z⁻¹)
      nlinarith
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 := Real.log_le_log (norm_pos_iff.mpr hne) hb
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hNpos.ne' hNpos.ne', hlogQ] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntEqProdOfGaloisPermutedIntegral
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_int_eq_prod_of_galois_permuted_integral :
    ∀ (T : Type) [Fintype T] (f : T → ℂ), (∀ t, IsIntegral ℤ (f t)) → (∀ σ : ℂ ≃+* ℂ, ∃ u : T ≃ T, ∀ t, f (u t) = σ (f t)) → ∃ n : ℤ, (n : ℂ) = ∏ t, f t := by
  intro T _ f hf hσ
  have hfix : ∀ σ : ℂ ≃+* ℂ, σ (∏ t, f t) = ∏ t, f t := by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    rw [map_prod, ← Equiv.prod_comp u f]
    exact Finset.prod_congr rfl (fun t _ => (hu t).symm)
  have hint : IsIntegral ℤ (∏ t, f t) := IsIntegral.prod f (fun t _ => hf t)
  obtain ⟨q, hq⟩ := GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed _ hfix
  have hq' : algebraMap ℚ ℂ q = ∏ t, f t := by simpa using hq.symm
  rw [← hq'] at hint
  have hqi : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := ℚ) hqi
  refine ⟨n, ?_⟩
  rw [← hq', ← hn]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_normV_eq_prime_pow_le_finrank :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ∃ h : ℕ, 1 ≤ h ∧ h ≤ Module.finrank ℚ K ∧ normV w = p ^ h := by
  intro K _ _ p w hp hpw
  have hcard : normV w = Ideal.absNorm w.asIdeal := by
    unfold normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hdvd : Ideal.absNorm w.asIdeal ∣ p ^ Module.finrank ℚ K := by
    rw [← hspan]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpw)
  obtain ⟨h, hle, heq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨h, ?_, hle, hcard.trans heq⟩
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · exfalso
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at heq
    exact w.isPrime.ne_top heq
  · exact h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    IsAdmissible π → ∀ y : Jacquet π (unipB k (Fin N)), y ≠ 0 →
    (∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y) →
    fixed π (GlobalTheory.CentralExponent.cong (Fin N) γ hγ) ≠ ⊥ := by
  intro k _ _ _ _ N V _ _ π γ hγ hπ y hy0 hy hbot
  have hmem : ∀ d : Fin N → kˣ, diagT k (Fin N) d ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ ↔
      ∀ i, valuation k ((d i : k) - 1) < γ := by
    intro d
    constructor
    · intro h i
      have := h i i
      simpa [val_diagT] using this
    · intro h i j
      by_cases hij : i = j
      · subst hij
        simpa [val_diagT] using h i
      · simp [val_diagT, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  obtain ⟨v, hv, e⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq hπ
    (GlobalTheory.CentralExponent.isOpen_cong γ hγ) (GlobalTheory.CentralExponent.isCompact_cong γ hγ) (diagT k (Fin N))
    (N := unipB k (Fin N)) (fun _ => leviEmb_mem_normalizer k (points (Fin N)) _)
    ((GlobalTheory.CentralExponent.cong (Fin N) γ hγ).comap (diagT k (Fin N)))
    (fun _ h => h) (GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N))
    (fun g hg => by
      obtain ⟨d, hd, x, hx, c, hc, e⟩ := UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori k N γ hγ g hg
      exact ⟨d, (hmem d).2 hd, x, hx, c, hc, e⟩)
    (GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract k (Fin N)) y
    (fun d => by
      have := hy d ((hmem d).1 d.2)
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact this)
  rw [hbot, Submodule.mem_bot] at hv
  exact hy0 (by rw [← e, hv, map_zero])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowResDegPlaceNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qh11.pow_cong A ha hb h m

private theorem dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) : IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

private theorem dec_lt {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x < 1) : A.valuation (g x) < 1 := by
  by_contra hc
  have h1 : 1 ≤ A.valuation (g x) := not_lt.1 hc
  have h2 : A.valuation (g x⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_le_one_of_one_le₀ h1
  have h3 := dec_le (inv_mem hg) h2
  have e : g⁻¹ (g x⁻¹) = x⁻¹ := g.symm_apply_apply _
  rw [e, map_inv₀] at h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h1
  have h0 : 0 < A.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  exact absurd hx (not_lt.2 ((inv_le_one₀ h0).1 h3))

private theorem inv_mul_ine {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g h : G K Ω} (hg : IsFrob (F := K) A q g) (hh : IsFrob (F := K) A q h) : h⁻¹ * g ∈ Ine (F := K) A := by
  refine ⟨mul_mem (inv_mem hh.1) hg.1, fun x hx => ?_⟩
  have h3 := Valuation.map_sub_lt A.valuation (hg.2 _ hx) (hh.2 _ hx)
  rw [sub_sub_sub_cancel_right] at h3
  have h4 := dec_lt (inv_mem hh.1) h3
  have e : h⁻¹ (h x) = x := h.symm_apply_apply x
  rw [map_sub, e] at h4
  exact h4

private theorem asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  have hpr : Prime (p : 𝓞 ℚ) := by
    have h : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm

private theorem normV_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    normV v = p := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h, asIdeal_eq hp v hv, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

theorem UpperTheory.frobenius_pow_resDeg_place_norm :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (p h : ℕ) (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (p : 𝓞 ℚ) ∈ v.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (p ^ h) σ → IsPlaceOver B v ∧ ∃ τ : G ℚ Ω, IsFrob B (normV v) τ ∧ (τ ^ h)⁻¹ * σ.restrictScalars ℚ ∈ Ine (F := ℚ) B := by
  intro K Ω _ _ _ _ _ _ _ p h w v hp hw hv B hB σ hσ
  have hcl : IsAlgClosure ℚ Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }
  have hu : (p : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    show algebraMap (𝓞 ℚ) (𝓞 K) (p : 𝓞 ℚ) ∈ w.asIdeal
    rwa [map_natCast]
  have hvw : v = w.under (𝓞 ℚ) :=
    HeightOneSpectrum.ext ((asIdeal_eq hp v hv).trans (asIdeal_eq hp _ hu).symm)
  have hBv : IsPlaceOver B v := by
    rw [hvw]
    intro x
    rw [IsScalarTower.algebraMap_apply ℚ K Ω]
    exact hB (algebraMap (𝓞 ℚ) (𝓞 K) x)
  refine ⟨hBv, ?_⟩
  obtain ⟨τ, hτ⟩ := exists_isFrob hBv
  refine ⟨τ, hτ, ?_⟩
  rw [normV_eq hp v hv] at hτ
  have hσ' : IsFrob (F := ℚ) B (p ^ h) (σ.restrictScalars ℚ) := ⟨hσ.1, hσ.2⟩
  exact inv_mul_ine hσ' (isFrob_pow hτ h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsIrrTwistAndRepIsoOfTwistRepIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.isIrr_twist_and_repIso_of_twist_repIso :
    ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (χ : Γ →* kˣ), (∀ r : Γ →* GL (Fin n) k, IsIrr r → IsIrr (tw r χ)) ∧ ∀ r r' : Γ →* GL (Fin n) k, RepIso (tw r χ) (tw r' χ) → RepIso r r' := by
  intro Γ k _ _ n χ
  have key : ∀ (r : Γ →* GL (Fin n) k) W, IsInv (tw r χ) W ↔ IsInv r W := fun r W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  refine ⟨fun r hr => ?_, fun r r' ⟨g, hg⟩ => ⟨g, fun s => ?_⟩⟩
  · unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
  · have h := congrArg Units.val (hg s)
    apply Units.ext
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul] at h ⊢
    exact smul_right_injective _ (Units.ne_zero (χ s)) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetExistsLeviCongruenceFixedOfCharSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem UpperTheory.smooth_gl_one_cuspidal {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i

private theorem UpperTheory.fixed_vectors_nonzero_character {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y : IrrRep (GL (Fin 1) k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h : IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar χ hχ)
    (h1 : ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) :
    fixed y.ρ (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
  have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) χ) (isCuspidal_detRep_one hχ).1
      (isIrreducible_ofChar _) := h
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv⟩
  have hg : valuation k ((g.1.val - 1) 0 0) < γ := g.2 0 0
  have h2 : χ (Matrix.GeneralLinearGroup.det g.1) = 1 := by
    refine h1 _ ?_
    simpa [Matrix.det_unique] using hg
  refine φ.toLinearEquiv.injective ?_
  have h3 := φ.toIntertwiningMap.isIntertwining _ _ g.1 v
  refine h3.trans ?_
  simp only [detRep, ofChar_apply, detChar_apply, h2, MonoidHom.one_apply, Units.val_one, one_mul, one_smul]
  rfl

theorem UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    ∀ e : (Σ _ : Fin N, Fin 1) ≃ Fin N, Nontrivial (Jacquet π (unipRad k e)) →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ g : Levi k fun _ : Fin N => Fin 1,
      (∀ a, g a ∈ GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) → jac e π g y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ e hJ
  have hjs : IsSmooth (jac e π) := isSmooth_jac e hs.isSmooth
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hjs
  have hsm : ∀ j : Fin N, IsSmooth (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun _ : Fin N => GL (Fin 1) k) j)
  have hy : ∀ j : Fin N, ∃ y : IrrRep (GL (Fin 1) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) : Representation ℂ (GL (Fin 1) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac (d := fun _ : Fin N => 1) hG hZ hs e hτ hτs y hy
  have hfix : ∀ j : Fin N, fixed (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
    intro j
    have hc : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp :=
      ⟨Nat.one_pos, UpperTheory.smooth_gl_one_cuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hc ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    obtain ⟨χ, hχs, h2, h3⟩ := hχ (IrrGL.of (y j).ρ (y j).smooth (y j).irr)
      (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, by rw [h1]; exact Multiset.mem_singleton_self _⟩)
    exact UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ (hsm j) (hy j) (GlobalTheory.CentralExponent.isCompact_cong γ hγ)
      (UpperTheory.fixed_vectors_nonzero_character (y j) γ hγ χ hχs h2 h3)
  have hcomm : ∀ (_ : Fin N) (x z : GL (Fin 1) k), x * z = z * x := by
    intro _ x z
    ext i j
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
  have htriv := UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot (Fin N) (fun _ => GL (Fin 1) k) hcomm Y τ
    (fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) hτ hfix
  let H : Subgroup (Levi k fun _ : Fin N => Fin 1) :=
    Subgroup.pi Set.univ fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ
  have hH : IsCompact (H : Set (Levi k fun _ : Fin N => Fin 1)) :=
    isCompact_univ_pi fun _ => GlobalTheory.CentralExponent.isCompact_cong γ hγ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hτf : fixed τ H ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
    rw [htriv g.1 fun a => g.2 a trivial]
    simp, hv⟩
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ τ (jac e π) H hjs hτs hH hτf)
  refine ⟨w, hw0, fun g hg => ?_⟩
  simpa using hw ⟨g, fun a _ => hg a⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapTraceEqSumRootsOfCharpolyMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.map_trace_eq_sum_roots_of_charpoly_map :
    ∀ (k : Type) [Field k] (φ : k →+* ℂ) (B : Multiset ℂ), (∀ M : Matrix (Fin 3) (Fin 3) k, M.charpoly.map φ = (B.map fun b => X - C b).prod → φ M.trace = B.sum) ∧ ∀ M : Matrix (Fin 2) (Fin 2) k, M.charpoly.map φ = (B.map fun b => X - C b).prod → ∀ h : ℕ, φ (M ^ h).trace = (B.map (· ^ h)).sum := by
  intro k _ φ B
  refine ⟨fun M hM => ?_, fun M hM => ?_⟩
  · rw [AddMonoidHom.map_trace, Matrix.trace_eq_sum_roots_charpoly, Matrix.charpoly_map, hM,
      Polynomial.roots_multiset_prod_X_sub_C]
  · have hN : (M.map φ).charpoly = (B.map fun b => X - C b).prod := by rw [Matrix.charpoly_map, hM]
    have ht : (M.map φ).trace = B.sum := by
      rw [Matrix.trace_eq_sum_roots_charpoly, hN, Polynomial.roots_multiset_prod_X_sub_C]
    have hc : B.card = 2 := by
      have := Matrix.charpoly_natDegree_eq_dim (M.map φ)
      rw [hN, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
      simpa using this
    obtain ⟨b1, b2, rfl⟩ := Multiset.card_eq_two.mp hc
    have h0 := Matrix.aeval_self_charpoly (M.map φ)
    rw [hN] at h0
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
    set N := M.map φ with hNdef
    have hCH : N * N = (b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      have e : N * N - ((b1 + b2) • N - (b1 * b2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
        rw [← h0]
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
        module
      exact sub_eq_zero.mp e
    have key : ∀ h : ℕ, (N ^ h).trace = b1 ^ h + b2 ^ h ∧
        (N ^ (h + 1)).trace = b1 ^ (h + 1) + b2 ^ (h + 1) := by
      intro h
      induction h with
      | zero =>
        refine ⟨?_, ?_⟩
        · simp [Matrix.trace_one]
          norm_num
        · simpa [add_comm] using ht
      | succ h ih =>
        refine ⟨ih.2, ?_⟩
        have e : N ^ (h + 1 + 1) = (b1 + b2) • N ^ (h + 1) - (b1 * b2) • N ^ h := by
          rw [pow_succ, pow_succ, mul_assoc, hCH, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
            ← pow_succ]
        rw [e, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih.1, ih.2, smul_eq_mul,
          smul_eq_mul]
        ring
    intro h
    rw [AddMonoidHom.map_trace, Matrix.map_pow, (key h).1]
    simp [add_comm]
end

