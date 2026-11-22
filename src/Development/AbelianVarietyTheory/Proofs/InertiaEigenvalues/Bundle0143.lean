import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0131
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFractionFieldAddValNormUnramifiedLocalExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormValU.val_norm | exact GlobalTheory.UnitLemma.Unr.NormValU.val_norm | (intros; apply GlobalTheory.UnitLemma.Unr.NormValU.val_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | exact GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure | (intros; apply GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
section
noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLatDVR

theorem isReduced_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_aeval_eq_of_charpoly_separable g hP a
  obtain ⟨m, hm⟩ := ha
  have hf : aeval (LinearMap.mulLeft E g) (f ^ m) = 0 := by
    have h2 : aeval g (f ^ m) = 0 := by rw [map_pow, hm]
    have := aeval_algHom_apply (Algebra.lmul E A) g (f ^ m)
    rw [h2, map_zero] at this
    exact this
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  rw [← pow_mul] at h1
  obtain ⟨q, hq⟩ := hP.squarefree.isRadical _ _ h1
  have hc : aeval g (LinearMap.mulLeft E g).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g)
    have h' : Algebra.lmul E A (aeval g (LinearMap.mulLeft E g).charpoly) = 0 := by
      rw [← aeval_algHom_apply]; exact h
    simpa using congrArg (fun F : Module.End E A => F 1) h'
  rw [hq, map_mul, hc, zero_mul]

theorem isPrincipalIdealRing_integralClosure_field {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by
  haveI : IsDedekindDomain (integralClosure O L) :=
    GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne E
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O E L]
    exact (algebraMap E L).injective.comp (IsFractionRing.injective O E)
  haveI : Module.IsTorsionFree O (integralClosure O L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => hinj (congrArg Subtype.val h)
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal O) (integralClosure O L)
  refine (hfin.insert ⊥).subset ?_
  intro P hP
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    haveI : P.IsPrime := hP
    have hne : P.comap (algebraMap O (integralClosure O L)) ≠ ⊥ := fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
    have hmax : (P.comap (algebraMap O (integralClosure O L))).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    refine ⟨hP, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal hmax).symm

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact isPrincipalIdealRing_integralClosure_field (E := E)
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (PrincipalLat.isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep N hN hst
  haveI := isReduced_of_charpoly_separable g hsep
  haveI := isPrincipalIdealRing_integralClosure (O := O) (E := E) (A := A)
  exact PrincipalLat.eq_mulLat_of_isPrincipalIdealRing N hN hst

end GlobalTheory.UnitLemma.PrincipalLatDVR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLatticeStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNormStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHermitianPair_structure_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  first | exact @GlobalTheory.JR.EtFacts.main | exact GlobalTheory.JR.EtFacts.main | (intros; apply GlobalTheory.JR.EtFacts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseNearOfDecompositionFixed
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise

namespace GlobalTheory

theorem exists_base_near_of_dec_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  intro E Ω _ _ _ _ _ A w h z hz r hr
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hint : ∀ x : Ω, IsIntegral ℤ x → A.valuation x ≤ 1 := fun x hx =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hx)
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x => by
    have : IsIntegral ℚ x := isIntegral_trans (R := ℚ) (A := E) x (Algebra.IsIntegral.isIntegral x)
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr this.isAlgebraic

  obtain ⟨b, hb0, hbz⟩ := (halg z).exists_integral_multiple

  obtain ⟨b', hb'0, hb'r⟩ := (halg r⁻¹).exists_integral_multiple

  set m : ℕ := Ideal.absNorm w.asIdeal with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hmA : A.valuation (m : Ω) < 1 := by
    have h1 := (h ((m : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
    simpa using h1
  have hbv : A.valuation (b : Ω) ≠ 0 := by simpa using hb0
  have hrv : A.valuation r ≠ 0 := by simpa using hr
  have hb'v : A.valuation (b' : Ω) ≤ A.valuation r := by
    have h1 := hint _ hb'r
    rw [zsmul_eq_mul, Valuation.map_mul, map_inv₀] at h1
    have := mul_le_mul_left h1 (A.valuation r)
    rwa [mul_assoc, inv_mul_cancel₀ hrv, mul_one, one_mul] at this
  set c : ℕ := b'.natAbs * b.natAbs * m with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr hb'0) (Int.natAbs_ne_zero.mpr hb0)) hm0
  have hnat : ∀ n : ℤ, A.valuation ((n.natAbs : ℕ) : Ω) = A.valuation (n : Ω) := by
    intro n
    rcases Int.natAbs_eq n with e | e
    · conv_rhs => rw [e]
      simp
    · conv_rhs => rw [e]
      simp

  have hcv : A.valuation (c : Ω) < A.valuation r * A.valuation (b : Ω) := by
    rw [hc, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul, hnat, hnat]
    have h1 : A.valuation (b' : Ω) * A.valuation (b : Ω) ≤ A.valuation r * A.valuation (b : Ω) :=
      mul_le_mul_left hb'v _
    have hpos : 0 < A.valuation (b' : Ω) * A.valuation (b : Ω) := by
      rw [zero_lt_iff, ← Valuation.map_mul]; simpa using ⟨hb'0, hb0⟩
    calc A.valuation (b' : Ω) * A.valuation (b : Ω) * A.valuation (m : Ω)
        < A.valuation (b' : Ω) * A.valuation (b : Ω) * 1 := mul_lt_mul_of_pos_left hmA hpos
      _ ≤ A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact h1
  have hbz' : IsIntegral ℤ ((b : Ω) * z) := by rwa [zsmul_eq_mul] at hbz
  have key : ∀ x u : Ω, A.valuation x ≤ A.valuation (c : Ω) → IsIntegral ℤ ((b : Ω) * u) →
      A.valuation (x * u) < A.valuation r := by
    intro x u hx hu
    refine lt_of_mul_lt_mul_right' (a := A.valuation (b : Ω)) ?_
    calc A.valuation (x * u) * A.valuation (b : Ω) = A.valuation x * A.valuation ((b : Ω) * u) := by
          rw [Valuation.map_mul, Valuation.map_mul, mul_assoc, mul_comm (A.valuation u)]
      _ ≤ A.valuation (c : Ω) * 1 := mul_le_mul' hx (hint _ hu)
      _ < A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact hcv
  set K := IntermediateField.adjoin E ({z} : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hzK : z ∈ K := IntermediateField.mem_adjoin_simple_self E z
  have hfix : ∀ σ : G E Ω, σ z = z → ∀ x ∈ K, σ x = x := by
    intro σ hσ x hx
    have e1 : ((σ : Ω →ₐ[E] Ω).comp K.val) = K.val :=
      IntermediateField.adjoin_algHom_ext E (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy; simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ ⟨x, hx⟩) e1
  have hsame : ∀ σ : G E Ω, (∀ x ∈ K, IsIntegral ℤ x → (A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
      σ z = z := by
    intro σ hall
    obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_conj_valuationSubring_of_same_below E Ω K A (σ⁻¹ • A) (fun x hx hxi => by
      rw [smul_valuation_lt_one_iff, inv_inv]; exact (hall x hx hxi).symm)
    have hD : σ * ρ ∈ Dec (F := E) A := by
      rw [mem_Dec, mul_smul, hρ, smul_inv_smul]
    have := hz _ hD
    rw [AlgEquiv.mul_apply, hρK z hzK] at this
    exact this
  obtain ⟨t, htK, htint, ht1, htσ⟩ := GlobalTheory.T.exists_integral_near_one_small_off_decomposition E Ω K A c hc0
  obtain ⟨e, s, hs, he⟩ := GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' E Ω (t * z)
  refine ⟨e, ?_⟩
  have hyz : A.valuation (t * z - z) < A.valuation r := by
    have : t * z - z = (t - 1) * z := by ring
    rw [this]; exact key _ _ ht1 hbz'
  have hsum : ∀ x ∈ s, A.valuation x < A.valuation r := by
    intro x hx
    obtain ⟨hxy, σ, rfl⟩ := hs x hx
    have hσz : σ z ≠ z := by
      intro hσz
      apply hxy
      rw [map_mul, hfix σ hσz t htK, hσz]
    have hex : ∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1) := by
      by_contra hne
      exact hσz (hsame σ (fun x hx hxi => by
        by_contra hn
        exact hne ⟨x, hx, hxi, hn⟩))
    rw [map_mul]
    refine key _ _ (htσ σ hex) ?_
    have : (b : Ω) * σ z = σ ((b : Ω) * z) := by simp
    rw [this]
    exact hbz'.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)
  have e2 : algebraMap E Ω e - z = (∑ x ∈ s, x) + (t * z - z) := by rw [← he]; ring
  rw [e2]
  exact Valuation.map_add_lt _ (Valuation.map_sum_lt _ hrv hsum) hyz

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisTraceInvolutionDetUnitUnramified
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ h hd
  refine ⟨w, ?_⟩
  obtain ⟨π, π', hππ, hm, hm'⟩ := GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h
  obtain ⟨u, hu, hue⟩ := GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt K K' d φ h π π' hππ hm hm' w hw
  obtain ⟨v, hv, hve⟩ := GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis K K' d φ h.2.1 w hw
  have key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← w.sum_repr (K'.c (w l))]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v) := by
    rw [key, Matrix.det_mul, ← hue, ← hve, map_mul]
  rw [hdet]
  refine ⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
  exact (hu.mul hv).ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitian
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NormSec

theorem normsec : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := GlobalTheory.T.exists_isotropic_idempotent_centralizer_hermitian E r A₀ hA hsep
  have hcomm := GlobalTheory.T.matrix_commute_of_commute_separable_charpoly E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_right e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_right e)
  have hT₁ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₁ hB₁
  have hT₂ := GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2

end GlobalTheory.NormSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConductorMulMemAdjoinOfSeparableStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g → ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u → algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  first | exact @GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | exact GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | (intros; apply GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetCosetsIntegralNormUnitsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_cosets_integral_norm_units : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ F : Finset B.Aˣ, ∀ u : B.Aˣ, (∃ w ∈ intUnits K.O B.A, (w : B.A) = u * B.σ u) → ∃ f ∈ F, ∃ t ∈ B.T, u * f⁻¹ * t⁻¹ ∈ intUnits K.O B.A := by
  first | exact @GlobalTheory.NormUnits.exists_finset_normUnits | exact GlobalTheory.NormUnits.exists_finset_normUnits | (intros; apply GlobalTheory.NormUnits.exists_finset_normUnits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  first | exact @GlobalTheory.UnitLemma.TorusPts.torus_points | exact GlobalTheory.UnitLemma.TorusPts.torus_points | (intros; apply GlobalTheory.UnitLemma.TorusPts.torus_points <;> assumption)
end

