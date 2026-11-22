import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameInteger
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPath
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameIntegerStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acts_by_same_integer_statement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  first | exact @GlobalTheory.PrimeOrderScalar.acts_by_same_integer | exact GlobalTheory.PrimeOrderScalar.acts_by_same_integer | (intros; apply GlobalTheory.PrimeOrderScalar.acts_by_same_integer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPowerStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  first | exact @GlobalTheory.NormCompat.chi_artin_restrict | exact GlobalTheory.NormCompat.chi_artin_restrict | (intros; apply GlobalTheory.NormCompat.chi_artin_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPointsStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) → ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  first | exact @GlobalTheory.UDense.eval_eq_zero_of_rat | exact GlobalTheory.UDense.eval_eq_zero_of_rat | (intros; apply GlobalTheory.UDense.eval_eq_zero_of_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplex
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem exists_isBEig_of_isPolyRep :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
      IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  intro n ι _ _ _ Φ hΦ
  obtain ⟨μ₀, hμ₀⟩ := GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex n ι Φ hΦ
  obtain ⟨μ, ⟨v, hv0, hvw⟩, hmax⟩ := GlobalTheory.T.exists_torusWeight_maximizing_weighted_sum n ι Φ μ₀ hμ₀
  refine ⟨v, μ, hv0, fun B hB => ?_⟩
  have hU : ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → Φ U *ᵥ v = v := by
    refine GlobalTheory.T.unitriangular_induction_on_transvections n (fun U => Φ U *ᵥ v = v) (by simp [hΦ.one]) (fun A C hA hC => ?_) ?_
    · show Φ (A * C) *ᵥ v = v
      rw [hΦ.mul, ← mulVec_mulVec, hC, hA]
    · intro i j hij s C hC
      show Φ C *ᵥ v = v
      obtain ⟨K, w, hw0, hww, hsum⟩ := GlobalTheory.T.exists_transvection_weightVec_expansion n ι Φ hΦ i j (ne_of_lt hij) μ v hvw
      have hz : ∀ k, k ≠ 0 → w k = 0 := by
        intro k hk
        by_contra hne
        have := hmax _ ⟨w k, hne, hww k⟩
        have hk' : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        have hij' : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
        have key : ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l)
            = ∑ l : Fin n, ((n : ℤ) - ((l : ℕ) : ℤ)) * μ l + k * (((n : ℤ) - ((i : ℕ) : ℤ)) - ((n : ℤ) - ((j : ℕ) : ℤ))) := by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          ring
        rw [key] at this
        nlinarith
      rw [hsum s C hC, Finset.sum_eq_single 0 (fun k _ hk => by rw [hz k hk, smul_zero]) (by simp), hw0, pow_zero, one_smul]
  obtain ⟨D, U, rfl, hD, hDd, hUb, hU1⟩ := GlobalTheory.T.GL_upperTriangular_eq_diagonal_mul_unitriangular' n B hB
  rw [hΦ.mul, ← mulVec_mulVec, hU U hUb hU1, hvw D hD]
  simp only [hDd]

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.SplitComplHomeo

open scoped WithZeroTopology in

theorem exists_complEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (NumberField.maximalRealSubfield L) ≃+* s.w.adicCompletion L,
      Continuous i ∧ Continuous i.symm ∧ ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro E _ _ _ s
  have : s.w.asIdeal.LiesOver s.v.asIdeal := ⟨s.w_under.symm⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (maximalRealSubfield E) E s.v s.w).continuous
  let φ : s.v.adicCompletion (maximalRealSubfield E) →+* s.w.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E s.w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv (maximalRealSubfield E) s.v).toRingHom
  have hφ : ∀ x : maximalRealSubfield E, φ (algebraMap (maximalRealSubfield E) _ x) =
      algebraMap E _ (algebraMap (maximalRealSubfield E) E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E s.w).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (s.v.valuation (maximalRealSubfield E))) (WithVal (s.w.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion (maximalRealSubfield E) s.v))
  have hi : ∀ x : E, φ (s.i x) = algebraMap E (s.w.adicCompletion E) x := fun x => by
    have key : ∀ y, Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x) := fun y =>
      (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).induction_on
        (p := fun y => Valued.v (φ y - algebraMap E (s.w.adicCompletion E) x) = Valued.v (y - s.i x)) y
        (isClosed_eq
          ((Valued.continuous_valuation_of_surjective (s.w.valuedAdicCompletion_surjective E)).comp
            (hcont.sub continuous_const))
          ((Valued.continuous_valuation_of_surjective (s.v.valuedAdicCompletion_surjective _)).comp
            (continuous_id.sub continuous_const))) fun k => by
        rw [hφ, ← map_sub, ← PI.CompAtExist.stepA s, map_sub, AlgHom.commutes]
    have h0 := key (s.i x)
    rw [sub_self, map_zero, map_eq_zero, sub_eq_zero] at h0
    exact h0
  letI : Algebra (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hcont
  letI : NontriviallyNormedField (s.v.adicCompletion (maximalRealSubfield E)) :=
    Valued.toNontriviallyNormedField _ _
  have hs : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E)) := Submodule.closed_of_finiteDimensional _
    intro y
    exact (HeightOneSpectrum.denseRange_algebraMap E s.w).induction_on
      (p := fun y => y ∈ (LinearMap.range (Algebra.linearMap (s.v.adicCompletion (maximalRealSubfield E))
        (s.w.adicCompletion E)) : Set (s.w.adicCompletion E))) y hcl fun x => ⟨s.i x, hi x⟩
  let e : s.v.adicCompletion (maximalRealSubfield E) ≃ₗ[s.v.adicCompletion (maximalRealSubfield E)]
      s.w.adicCompletion E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) ⟨φ.injective, hs⟩
  haveI : FiniteDimensional (s.v.adicCompletion (maximalRealSubfield E)) (s.w.adicCompletion E) :=
    e.finiteDimensional
  have hinv : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hs⟩, hcont, hinv.congr fun y => ?_, hi⟩
  exact (RingEquiv.symm_apply_eq _).2 (e.apply_symm_apply y).symm |>.symm

end GlobalTheory.SplitComplHomeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by
  have key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N =
      c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k) := by
    intro μ k
    have h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V))) := by
      rw [sub_mul, h, mul_sub, smul_sub]
      simp [smul_smul]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ', ← pow_succ]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [End.iSup_maxGenEigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    have h1 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc
      hs.isFinitelySemisimple hn
    have h2 : N v ∈ f.maxGenEigenspace (c * μ) := by
      rw [End.mem_maxGenEigenspace] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      refine ⟨k, ?_⟩
      have := LinearMap.congr_fun (key μ k) v
      simpa [hk] using this
    have h3 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc
      hs.isFinitelySemisimple hn
    simp [h1, h3, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

end Lin

theorem isNilpotent_pow_sub_one {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)

theorem commute_of_commute_pow {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]

theorem exists_frobenius_semisimplification : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob h))
  set f := ρ (frob h) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob h)).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob h)
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob h) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob h) (τ * frob h * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob h) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob h) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueEmbeddingEigenspaceSumStatement
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embedding_eigenspace_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  first | exact @GlobalTheory.EigDecomp.exists_unique_eigen_sum | exact GlobalTheory.EigDecomp.exists_unique_eigen_sum | (intros; apply GlobalTheory.EigDecomp.exists_unique_eigen_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOscillatorIntegralSymplecticPathStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorIntegral_symplecticPath : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, omJ J (a t x) (a t y) = omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (omJ J) X c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t : ℝ => ∫ w, ρ (a t w) (∫ u, gau u • ρ (a t u) (proj h (ρ (-w) f)))) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | exact GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc | (intros; apply GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  first | exact @GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | exact GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | (intros; apply GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemSpanLowerWeightsOfBorelEigenvectorStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulVec_mem_span_lower_weights_of_borelEigenvector : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig | exact GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_sle_of_isBEig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_localValues_global_over_places_above : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (B : Type) [CommGroup B] (ψ1 : Ideles K →* B) (ψ2 : Ideles E →* B) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v ∉ S, ∀ x, IsUnitAt v x → ψ2 (localIdele E v x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x, IsUnitAt w x → ψ1 (localIdele K w x) = 1) → (∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → ψ1 (localIdele K w x) = ψ2 (localIdele E v ϖ) ^ w.asIdeal.inertiaDeg (𝓞 E)) → ∀ a : Kˣ, ∃ (TK : Finset (HeightOneSpectrum (𝓞 K))) (TE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ TK, ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) ∧ (∀ w ∉ TK, (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) → ψ1 (locUnit K w a) = 1) ∧ (∀ v ∈ TE, v ∉ S) ∧ (∀ v ∉ TE, v ∉ S → ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) = 1) ∧ ∏ w ∈ TK, ψ1 (locUnit K w a) = ∏ v ∈ TE, ψ2 (locUnit E v (Units.map (Algebra.norm E (S := K)) a)) := by
  first | exact @GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | exact GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm | (intros; apply GlobalTheory.NormCompat.prod_locUnit_eq_prod_locUnit_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLNonvanishingAtOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_L_nonvanishing_at_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | exact GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | (intros; apply GlobalTheory.Mem.rayLSeries_entire_ne_zero_one <;> assumption)
end

