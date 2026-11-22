import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0050
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0045
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0030

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_centre_of_bdd :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → Centre (ctSp r S) := by
  intro K _ _ n r S hS z hz
  obtain ⟨p, hp, hpS⟩ := hS.centre z hz
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  refine ⟨p, hp, fun x hx => ?_⟩
  have hle : ctSp r S ≤ LinearMap.ker (Polynomial.aeval (uAction z : Module.End ℂ (archSmooth K n)) p) := by
    refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, hψ⟩
    have hA : φ.1 ∈ automorphicForms K n := mem_automorphicForms.2 (UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ)
    let incl : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
      Submodule.inclusion automorphicForms_le_archSmooth
    have h1 := map_aeval_apply_of_intertwine incl (A := uActionAF K n z) (B := uAction z) (fun _ => rfl) p ⟨φ.1, hA⟩
    have h2 : Polynomial.aeval (uActionAF K n z) p ⟨φ.1, hA⟩ = 0 := by
      apply Submodule.inclusion_injective automorphicForms_le_archSmooth
      rw [map_zero]
      exact h1.trans ((Submodule.mem_bot ℂ).1 (hpS φ hφ))
    have h3 := map_aeval_apply_of_intertwine f (A := uActionAF K n z) (B := uAction z) (hfu z) p ⟨φ.1, hA⟩
    have h4 : ψ = f ⟨φ.1, hA⟩ := Subtype.ext (hψ.trans (hf ⟨φ.1, hA⟩).symm)
    refine LinearMap.mem_ker.2 ?_
    rw [h4, ← h3, h2, map_zero]
  exact (Submodule.mem_bot ℂ).2 (hle hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_types_of_bdd :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → Types (ctSp r S) := by
  intro K _ _ n r S hS
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, fun ψ hψ g => ?_⟩
  unfold ctSp at hψ
  induction hψ using Submodule.span_induction with
  | mem ψ h =>
    obtain ⟨φ, hφ, he⟩ := h
    have hc : Continuous φ.1 := (UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ).continuous
    rw [he]
    refine @UpperTheory.locallyFinite_of_algMod_criterion _ (archCompact K n) (_) _ V hV
      (fun X k => φ.1 (unipGL X * (g * infEmb K n k.1))) (fun X => ?_)
      (fun k => integrableOn_constantTerm hc _)
    simpa only [mul_assoc] using hmem φ hφ (unipGL X * g)
  | zero => exact V.zero_mem
  | add x y _ _ hx hy => exact V.add_mem hx hy
  | smul c x _ hx => exact V.smul_mem c hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfBddCuspidal
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_bdd_cuspidal :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → (∀ φ ∈ S, IsCuspidal φ.1) → FiniteDimensional ℂ S := by
  intro K _ _ n S hS hcusp
  classical
  have hle : cuspForms K n ≤ archSmooth K n :=
    cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
  let j : cuspForms K n →ₗ[ℂ] archSmooth K n := Submodule.inclusion hle
  have hj : Function.Injective j := Submodule.inclusion_injective hle
  have hju : ∀ (u : UEnv K n) (ψ : cuspForms K n), j (uActionCusp K n u ψ) = uAction u (j ψ) :=
    fun u ψ => rfl
  have hjf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (ψ : cuspForms K n),
      j (finRepCusp K n h ψ) = rtFin h (j ψ) := fun h ψ => rfl
  obtain ⟨d, b, P, hPm, hP⟩ := UpperTheory.exists_basis_algMod_laplacian_of_types_centre K n S hS.types hS.centre
  set Z := UnitaryAdmissible.centralZ K n with hZdef
  have hZc : UniversalEnvelopingAlgebra.ι ℝ Z ∈ (isExpLieAlgebra K n).centerU := by
    apply mem_center_of_forall_ι_commute
    intro x
    have h1 := UnitaryAdmissible.lie_centralZ (K := K) (n := n) x
    have h2 : UniversalEnvelopingAlgebra.ι ℝ ⁅Z, x⁆ = UniversalEnvelopingAlgebra.ι ℝ Z * UniversalEnvelopingAlgebra.ι ℝ x - UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ Z := by
      rw [LieHom.map_lie, Ring.lie_def]
    rw [h1, map_zero] at h2
    exact (sub_eq_zero.mp h2.symm).symm
  obtain ⟨Q, hQm, hQ⟩ := hS.centre _ hZc
  obtain ⟨L, hLo, hL⟩ := hS.level
  let U : Subgroup (AdelicGLn.integralFiniteGL K n) := L.subgroupOf _
  have hUo : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := hLo.preimage continuous_subtype_val
  have hP'm : (Polynomial.X * P).Monic := Polynomial.monic_X.mul hPm
  have hP'd : 0 < (Polynomial.X * P).natDegree := by
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X hPm, Polynomial.natDegree_X]
    omega
  let N : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P)) ⊓
      ⨅ u : U, LinearMap.ker (finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) - LinearMap.id)
  have hmemN : ∀ ψ, ψ ∈ N ↔ Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P) ψ = 0 ∧
      ∀ u : U, finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) ψ = ψ := by
    intro ψ
    simp only [N, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hTA : ∀ m, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (uActionCusp K n (laplacianU K n b) m) =
      uActionCusp K n (laplacianU K n b) (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro m
    have hc := (Subalgebra.mem_center_iff.mp hZc) (laplacianU K n b)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc]
  have hTf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) m,
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (finRepCusp K n h m) =
        finRepCusp K n h (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro h m
    apply hj
    rw [hju, hjf, hjf, hju, uAction_rtFin]
  have hTN : ∀ x ∈ N, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    refine ⟨?_, fun u => ?_⟩
    · rw [← map_aeval_apply_of_intertwine _ hTA, hx.1, map_zero]
    · rw [← hTf, hx.2 u]
  have hE : ∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)).eigenspace c) := by
    intro c
    refine UnitaryAdmissible.finiteDimensional_of_eigen b _ hP'm hP'd c U hUo _ ?_
    intro φ hφ
    rw [Submodule.mem_inf, hmemN, Module.End.mem_eigenspace_iff] at hφ
    exact ⟨hφ.1.1, hφ.2, fun u hu => hφ.1.2 ⟨u, hu⟩⟩
  have hfin := UpperTheory.finiteDimensional_inf_ker_aeval_monic _ _ N hTN hE Q hQm
  refine Submodule.finiteDimensional_of_le (S₂ := (N ⊓ LinearMap.ker (Polynomial.aeval
    (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)) Q)).map j) ?_
  intro φ hφ
  have hφc : (φ : AdelicGLn.AdelicGL K n → ℂ) ∈ cuspForms K n :=
    ⟨UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ, hcusp φ hφ⟩
  have hjψ : j ⟨φ.1, hφc⟩ = φ := rfl
  refine ⟨⟨φ.1, hφc⟩, ?_, hjψ⟩
  refine Submodule.mem_inf.mpr ⟨(hmemN _).mpr ⟨?_, fun u => ?_⟩, ?_⟩
  · apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, (Submodule.mem_bot ℂ).mp (hP φ hφ), map_zero]
  · apply hj
    rw [hjf, hjψ]
    apply Subtype.ext
    funext g
    exact hL φ hφ _ (Subgroup.mem_subgroupOf.mp u.2) g
  · rw [LinearMap.mem_ker]
    apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ]
    exact (Submodule.mem_bot ℂ).mp (hQ φ hφ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfCmEigensystemCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem not_mem_of_distinct_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem admissible_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3 ι e N ρ) :
    AdmK ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  refine ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, ?_, by decide⟩
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  rw [zpow_neg_one] at h1
  convert h1 using 1
  funext i
  fin_cases i <;> simp <;> ring

theorem UpperTheory.frobenius_trace_count_bound_of_cm_eigensystem_count :
    CountK → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], ∃ c A : ℕ, ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K → ∃ D : TrData (normV w) e, Nat.card D.S ≤ c * (N * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (normV w) σ → D.Classifies ι σ⁻¹ (Adm3 ι e N) := by
  intro hC K _ _ _
  obtain ⟨c, A, hK⟩ := hC K 3 (by norm_num)
  refine ⟨c * 2 ^ A, A, fun e he N hN p w hp hw hpN hpd => ?_⟩
  have hN' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : 1 ≤ normV w := by
    rw [← hN']
    exact Nat.one_le_iff_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : normV w ≠ 0)
  obtain ⟨D, hcard, hcl⟩ := hK ![(e : ℤ) - 1, -1, -(e : ℤ) - 1]
    (by
      refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      fin_cases i <;> simp <;> omega)
    (by
      intro i
      fin_cases i <;> simp [Fin.rev] <;> ring)
    (e + 1)
    (by
      intro i
      rw [abs_le]
      fin_cases i <;> simp <;> omega)
    N hN p w hp hw hpN hpd
  obtain ⟨T, u, hT⟩ := UpperTheory.traces_from_eigenvalues_rank3 (normV w) e hq D
  refine ⟨T, ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ => ?_⟩
  · rw [← Nat.card_congr u, mul_assoc, ← mul_pow]
    refine hcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    nlinarith
  · obtain ⟨cl, h1, h2⟩ := hcl l hl2 hlp Ω ι
    refine ⟨fun r => u (cl ⟨_, admissible_twist_cyclotomic ι e N r.1 r.2⟩), fun r r' H => ?_, fun r => ?_⟩
    · exact (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).2 _ _ (h1 _ _ (u.injective H))
    · have hl := not_mem_of_distinct_prime w hp (Fact.out : l.Prime) hlp hw
      have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hB hσ
      have e3 : ((cycBar K Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
        change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ K Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
        rw [e2]; simp
      have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map _ ι.toRingHom _).1 _ ((h2 ⟨_, admissible_twist_cyclotomic ι e N r.1 r.2⟩ B hB).2 σ hσ)
      rw [tw_val, Matrix.trace_smul, MonoidHom.inv_apply, map_inv (cycBar K Ω l), inv_inv, e3, smul_eq_mul, map_mul,
        map_natCast] at h3
      rw [hT, eq_comm, RingEquiv.symm_apply_eq]
      simp only [mul_inv]
      rw [Multiset.sum_map_mul_left, ← h3, inv_mul_cancel_left₀ hqC]
      rfl
end

