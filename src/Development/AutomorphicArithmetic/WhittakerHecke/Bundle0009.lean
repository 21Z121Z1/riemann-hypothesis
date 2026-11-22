import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsNumberFieldExtensionPlaceFrobeniusDegree
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.exists_numberField_extension_place_frobenius_degree :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
        (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (n : ℕ), 2 ≤ n → ∀ (φ : G E Ω), IsFrob A (normV w) φ →
        ∀ (c : 𝓞 E), c ∉ w.asIdeal ^ 2 →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra E L) (_ : Algebra L Ω) (_ : IsScalarTower E L Ω)
          (_ : IsAlgClosure L Ω) (u : HeightOneSpectrum (𝓞 L)) (_ : IsPlaceOver A u) (s : L ≃ₐ[E] L),
          (∀ x : L, φ (algebraMap L Ω x) = algebraMap L Ω (s x)) ∧
          (∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x) ∧
          algebraMap (𝓞 E) (𝓞 L) c ∉ u.asIdeal ^ 2 ∧ normV u = normV w ^ n := by
  classical
  intro E Ω _ _ _ _ _ A w h n hn φ hφ c hc
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hfinw : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hq2 : 2 ≤ normV w := Finite.one_lt_card (α := 𝓞 E ⧸ w.asIdeal)
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = normV w := ⟨_, rfl⟩
  rw [← hqdef] at hφ hq2 ⊢
  have hqw : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    DiscreteGroups.sglob.DzType.natCast_mem_of_normV w q 1 one_pos (by rw [pow_one, hqdef])
  have hqΩ : A.valuation ((q : ℕ) : Ω) < 1 := by
    have := (h ((q : ℕ) : 𝓞 E)).mpr hqw
    simpa using this
  have hQ4 : 4 ≤ q ^ n := by
    have h2 : q ^ 2 ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
    nlinarith
  have hQΩ : A.valuation ((q ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, Valuation.map_pow]
    exact pow_lt_one₀ zero_le hqΩ (by omega)
  have hN1 : A.valuation (((q ^ n - 1 : ℕ)) : Ω) = 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg,
      Valuation.map_one_sub_of_lt _ hQΩ]
  have hN' : ¬ A.valuation (((q ^ n - 1 : ℕ)) : Ω) < 1 := by
    rw [hN1]; exact lt_irrefl 1
  haveI : NeZero (((q ^ n - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast (show q ^ n - 1 ≠ 0 by omega)⟩
  haveI : NeZero (q ^ n - 1) := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)
  have hζ1 : A.valuation ζ = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (by omega) hζ.pow_eq_one
  have hζA : A.valuation ζ ≤ 1 := hζ1.le
  let f : ℤ[X] := X ^ (q ^ n - 1) - C 1
  have hf : f.Monic := monic_X_pow_sub_C 1 (by omega)
  have hfζ : aeval ζ f = 0 := by simp [f, hζ.pow_eq_one]
  have hder : ¬ A.valuation (aeval ζ (derivative f)) < 1 := by
    simp only [f]
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C, map_pow, aeval_X,
      Valuation.map_mul, Valuation.map_pow, hζ1, one_pow, mul_one]
    have e : algebraMap ℤ Ω (((q ^ n - 1 : ℕ) : ℤ)) = (((q ^ n - 1 : ℕ)) : Ω) := by simp
    rw [e, hN1]
    exact lt_irrefl 1
  have hζE : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  let L := IntermediateField.adjoin E ({ζ} : Set Ω)
  have hfd : FiniteDimensional E L := IntermediateField.adjoin.finiteDimensional hζE
  have : FiniteDimensional ℚ L := Module.Finite.trans E L
  haveI hNF : NumberField L := ⟨⟩
  haveI hAC' : IsAlgClosure L Ω := ⟨hAC, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  haveI hcyc : IsCyclotomicExtension {q ^ n - 1} E L := hζ.intermediateField_adjoin_isCyclotomicExtension E
  haveI hgal : IsGalois E L := IsCyclotomicExtension.isGalois {q ^ n - 1} E L

  have hroot : ∀ τ : Ω ≃ₐ[E] Ω, τ ∈ ReciprocityTheory.Gal.Dec (F := E) A → A.valuation (τ ζ - ζ) < 1 → τ ζ = ζ := by
    intro τ hτ hlt
    have hτA : A.valuation (τ ζ) ≤ 1 := by
      rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hτ, ← A.valuation_le_one_iff]
      exact hζA
    refine (GlobalTheory.T.eq_of_roots_congr_of_derivative_unit A f ζ (τ ζ) hζA hτA hfζ (GlobalTheory.UnrCycExt.aeval_apply_eq_zero τ f hfζ) hder ?_).symm
    rw [Valuation.map_sub_swap]; exact hlt
  have hine : ∀ t ∈ Ine (F := E) A, ∀ x : L, t (algebraMap L Ω x) = algebraMap L Ω x := by
    intro t ht e
    have htζ : t ζ = ζ := hroot t ht.1 (ht.2 ζ hζA)
    exact GlobalTheory.UnrCycExt.fix_adjoin ζ hζE t htζ _ e.2
  have hφn : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((φ ^ n) x - x ^ (q ^ n)) < 1 :=
    GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one A q φ hφ n
  have hφD : φ ^ n ∈ ReciprocityTheory.Gal.Dec (F := E) A := Subgroup.pow_mem _ hφ.1 n
  have hζQ : ζ ^ (q ^ n) = ζ := by
    rw [show q ^ n = (q ^ n - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  have hφζ : (φ ^ n) ζ = ζ := by
    refine hroot _ hφD ?_
    have := hφn ζ hζA
    rwa [hζQ] at this
  have hfix : ∀ x ∈ L, (φ ^ n) x = x := GlobalTheory.UnrCycExt.fix_adjoin ζ hζE (φ ^ n) hφζ
  have hpowq : ∀ y : 𝓞 L, A.valuation (algebraMap L Ω ((y : L) ^ (q ^ n) - (y : L))) < 1 := by
    intro y
    have hyA := GlobalTheory.UnrCycExt.val_le_one_of_int A y
    have := hφn _ hyA
    have hy2 : (φ ^ n) (algebraMap L Ω (y : L)) = algebraMap L Ω (y : L) := hfix _ (y : L).2
    rw [hy2] at this
    rw [map_sub, map_pow, Valuation.map_sub_swap]
    exact this

  have hq0 : ((q : ℕ) : 𝓞 L) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hqv : A.valuation (algebraMap L Ω (((q : ℕ) : 𝓞 L) : L)) < 1 := by
    simpa using hqΩ
  let u := GlobalTheory.UnrCycExt.placeBelow L A ((q : ℕ) : 𝓞 L) hq0 hqv
  have hu : IsPlaceOver A u := GlobalTheory.UnrCycExt.isPlaceOver_placeBelow L A _ hq0 hqv
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζL : IsPrimitiveRoot ζL (q ^ n - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) hζ (algebraMap L Ω).injective
  have hζint : IsIntegral ℤ ζL := hζL.isIntegral (by omega)
  let ζ' : 𝓞 L := ⟨ζL, hζint⟩
  refine ⟨L, inferInstance, hNF, inferInstance, inferInstance, inferInstance, hAC', u, hu,
    AlgEquiv.restrictNormal φ L, ?_, hine, ?_, ?_⟩
  · intro x
    exact (AlgEquiv.restrictNormal_commutes φ L x).symm
  · have hmap : ∀ p : ℤ[X], algebraMap L Ω ((aeval ζ' p : 𝓞 L) : L) = aeval ζ p := by
      intro p
      have h1 : ((aeval ζ' p : 𝓞 L) : L) = aeval (ζ' : L) p :=
        (Polynomial.aeval_algebraMap_apply L ζ' p).symm
      rw [h1, ← Polynomial.aeval_algebraMap_apply]
      rfl
    have hfζ' : aeval ζ' f = 0 := by
      have h2 := hmap f
      rw [hfζ, ← map_zero (algebraMap L Ω)] at h2
      exact_mod_cast (algebraMap L Ω).injective h2
    have hover : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 L) x ∈ u.asIdeal ↔ x ∈ w.asIdeal := by
      intro x
      rw [← h x]
      show A.valuation (algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L)) < 1 ↔ _
      rw [show ((algebraMap (𝓞 E) (𝓞 L) x : 𝓞 L) : L) = algebraMap E L (x : E) from rfl,
        ← IsScalarTower.algebraMap_apply]
    have hder' : aeval ζ' (derivative f) ∉ u.asIdeal := fun hm => hder (by
      rw [← hmap]; exact hm)
    exact GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem E L w u ζ' f hf hfζ' (GlobalTheory.UnrCycExt.adjoin_gen_eq_top E ζ hζE) hover hder' c hc
  · show Nat.card (𝓞 L ⧸ u.asIdeal) = q ^ n
    haveI : u.asIdeal.IsMaximal := u.isMaximal
    refine GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' u.asIdeal (q ^ n) ζ' (by omega) ?_ ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 L) L
      rw [map_pow, map_one]
      exact hζL.pow_eq_one
    · intro j hj0 hjq hm
      have hm1 : A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (ζ' ^ j - 1))) < 1 := hm
      rw [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at hm1
      have hm' : A.valuation (ζ ^ j - 1) < 1 := hm1
      have := ReciprocityTheory.Gal.eq_of_pow_eq_one A hN'
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hm'
      have hd := hζ.dvd_of_pow_eq_one j this
      exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
    · intro y
      have := hpowq y
      show A.valuation (algebraMap L Ω (((y ^ (q ^ n) - y : 𝓞 L)) : L)) < 1
      simpa using this
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FunctionalQdetEqAevalShiftedPolynomial
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.functional_qdet_eq_aeval_shifted_polynomial :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (j : A) (l : A →ₗ[ℂ] ℂ) (p : Polynomial ℂ),
          (∀ i k, Commute (X i k) j) → (∀ (c : ℂ) (a : A), l (Formalism.REAL.qdet (fun i k => X i k - if i = k then j else 0) c * a) = p.eval c * l a) →
          ∀ v : ℂ, l (Formalism.REAL.qdet X v) = l (Polynomial.aeval j (p.comp (Polynomial.X + Polynomial.C v))) := by
  intro A _ _ n X j l p hc h v
  classical
  let B : Subalgebra ℂ A := Subalgebra.centralizer ℂ {j}
  have hB : ∀ i k, (X i k - if i = k then j else 0) ∈ B := fun i k => by
    rintro _ rfl
    refine (Commute.sub_left (hc i k) ?_).symm
    split_ifs
    · exact Commute.refl _
    · exact Commute.zero_left _
  let X' : Fin n → Fin n → B := fun i k => ⟨_, hB i k⟩
  let Q : Polynomial B := Formalism.REAL.qdet (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
  have hev : ∀ (b : A) (hb : ∀ a : B, Commute (B.val a) b), Q.eval₂ (B.val : B →+* A) b =
      Formalism.REAL.qdet (fun i k => (X i k - if i = k then j else 0) + if i = k then b else 0) v := fun b hb => by
    have := UpperTheory.V.Fb.map_qdet (Polynomial.eval₂AlgHom B.val b hb)
      (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
    refine Eq.trans ?_ (this.trans ?_)
    · rfl
    · congr 1
      funext i k
      rw [map_add, apply_ite (Polynomial.eval₂AlgHom B.val b hb), map_zero]
      congr 1
      · exact Polynomial.eval₂_C _ _
      · congr 1
        exact Polynomial.eval₂_X _ _
  have h1 : Q.eval₂ (B.val : B →+* A) j = Formalism.REAL.qdet X v := by
    rw [hev j (fun a => (a.2 j rfl).symm)]
    simp
  set q := p.comp (Polynomial.X + Polynomial.C v) with hq
  have h2 : ∀ (a : A) (k : ℕ), l ((Q.coeff k : A) * a) = q.coeff k * l a := fun a k => by
    have e : (∑ m ∈ Q.support, Polynomial.monomial m (l ((Q.coeff m : A) * a))) = q * Polynomial.C (l a) := by
      refine Polynomial.funext fun c => ?_
      have := h (v + c) a
      rw [← GlobalTheory.CuspRep.qdet_shift, ← hev _ (fun a => (Algebra.commutes c _).symm), Polynomial.eval₂_eq_sum, Polynomial.sum,
        Finset.sum_mul, map_sum] at this
      rw [Polynomial.eval_mul, Polynomial.eval_C, hq, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, add_comm c v, ← this, Polynomial.eval_finset_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Polynomial.eval_monomial, ← map_pow, mul_assoc, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul,
        mul_comm]
      rfl
    have e2 := congrArg (fun r => Polynomial.coeff r k) e
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_mul_C, Finset.sum_ite_eq'] at e2
    rw [← e2]
    split_ifs with hk
    · rfl
    · rw [Polynomial.notMem_support_iff.1 hk]
      simp
  let N := max Q.natDegree q.natDegree + 1
  rw [← h1, Polynomial.eval₂_eq_sum_range' _ (show Q.natDegree < N from Nat.lt_succ_of_le (le_max_left _ _)),
    Polynomial.aeval_eq_sum_range' (show q.natDegree < N from Nat.lt_succ_of_le (le_max_right _ _)), map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]
  exact h2 _ m
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FunctionalVanishesInvariant
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem zt_eq (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (t : ℝ) :
    zt E r t = GlobalTheory.UnitaryBC.splitCentre E r (t * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r
    (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)
  rw [Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t] at h
  exact h

theorem UpperTheory.functional_vanishes_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (f : Sm E r), (∀ t g, f.1 (zt E r t * g) = f.1 g) → j0 E r f = 0 := by
  intro E _ _ _ r f hf
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [j0]
  have hd : ((r * Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hr.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  have h : ∀ t g, f.1 (GlobalTheory.UnitaryBC.splitCentre E r t * g) = f.1 g := fun t g => by
    have := hf (t * (r * Module.finrank ℚ E : ℝ)) g
    rwa [zt_eq, mul_inv_cancel_right₀ hd] at this
  have h0 : lie E r (oneL E r) f = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    have h1 := GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E r f g 0
    have h2 : (fun t : ℝ => f.1 (g * GlobalTheory.UnitaryBC.splitCentre E r t)) = fun _ => f.1 g := by
      funext t
      rw [← CuspidalL2GL.splitCentre_comm, h]
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (f.1 g))
    rw [CuspidalL2GL.splitCentre_zero, mul_one] at h3
    exact h3
  have h4 : lie E r (oneL E r) = ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i := by
    rw [UpperTheory.V.Cm.lie_eq_sum]
    have hc : ∀ (τ : E →+* ℂ) (i k : Fin r), coord τ (oneL E r i k) = if i = k then 1 else 0 := fun τ i k => by
      have : oneL E r i k = (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k := rfl
      rw [this, Matrix.one_apply]
      split_ifs <;> simp
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [j0, LinearMap.smul_apply, ← h4, h0, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralQuotientDerivativeOneParameterEqZero
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem flow_abs {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [SFinite ν] (T : ℝ → Y → Y) (hT : Continuous fun p : Y × ℝ => T p.2 p.1)
    (hm : ∀ u, MeasurePreserving (T u) ν ν) (he : ∀ u, MeasurableEmbedding (T u)) (H D : Y → ℂ) (hD : Continuous D)
    (iH : Integrable H ν) (iD : Integrable D ν) (hd : ∀ y u, HasDerivAt (fun s => H (T s y)) (D (T u y)) u) :
    ∫ y, D y ∂ν = 0 := by
  have hc : Continuous fun p : Y × ℝ => D (T p.2 p.1) := hD.comp hT
  have h1 : ∀ y, ∫ u in Set.Ioc (0 : ℝ) 1, D (T u y) = H (T 1 y) - H (T 0 y) := fun y => by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd y u)
      ((hc.comp (Continuous.prodMk_right y)).intervalIntegrable _ _)
  have hi : Integrable (Function.uncurry fun y u => D (T u y)) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨.of_forall fun u => ((hm u).integrable_comp_emb (he u)).2 iD, ?_⟩
    have : (fun u => ∫ y, ‖D (T u y)‖ ∂ν) = fun _ => ∫ y, ‖D y‖ ∂ν := funext fun u => (hm u).integral_comp (he u) fun y => ‖D y‖
    exact this ▸ integrable_const _
  have h2 := integral_integral_swap hi
  simp only [h1, fun u => (hm u).integral_comp (he u) D] at h2
  have i : ∀ u, Integrable (fun x => H (T u x)) ν := fun u => ((hm u).integrable_comp_emb (he u)).2 iH
  rw [integral_sub (i 1) (i 0),
    (hm 1).integral_comp (he 1) H, (hm 0).integral_comp (he 0) H] at h2
  simpa using h2.symm

private theorem flow_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) (c : ℝ → G)
    (hc : Continuous c) : Continuous fun p : RightCosetSpace Γ × ℝ => rightMul Γ (c p.2) p.1 :=
  (continuous_rightMul_prod Γ).comp (f := fun p : RightCosetSpace Γ × ℝ => (p.1, c p.2))
    (continuous_fst.prodMk (hc.comp continuous_snd))

theorem UpperTheory.integral_quotient_derivative_oneParameter_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h D : GA E r → ℂ) (c : ℝ → GA E r),
          AutomorphicForm.IsLeftInvariant h → AutomorphicForm.IsLeftInvariant D → Continuous D → Continuous c → c 0 = 1 →
          (∀ s t, c (s + t) = c s * c t) → (∀ s, c s ∈ normOneGL E r) → (∀ g, HasDerivAt (fun s => h (g * c s)) (D g) 0) →
          Integrable (onQ h) (muQ E r) → Integrable (onQ D) (muQ E r) → ∫ y, onQ D y ∂muQ E r = 0 := by
  intro E _ _ r h D c hh hD cD cc _ cadd c1 hd ih iD
  have e : ∀ {f : GA E r → ℂ} (hf : AutomorphicForm.IsLeftInvariant f), onQ f = CuspidalSpectrum.cuspQuot hf := fun hf => by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  rw [e hh] at ih
  rw [e hD] at iD ⊢
  haveI : IsFiniteMeasure (muQ E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  haveI : SigmaFinite (muQ E r) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (muQ E r) := instSFiniteOfSigmaFinite
  refine flow_abs (muQ E r) (fun u => rightMul (rationalGLOne E r) ⟨c u, c1 u⟩) ?_
    (fun u => measurePreserving_rightMul (Γ := rationalGLOne E r) (mu1 E r) _)
    (fun u => (rightMulHomeomorph (rationalGLOne E r) _).measurableEmbedding) _ _ ?_ ih iD fun y u => ?_
  · exact flow_cont (rationalGLOne E r) (fun u => ⟨c u, c1 u⟩) (cc.subtype_mk c1)
  · exact (isOpenQuotientMap_mk (rationalGLOne E r)).isQuotientMap.continuous_iff.2 (cD.comp continuous_subtype_val)
  · obtain ⟨g, rfl⟩ := mk_surjective (rationalGLOne E r) y
    have h1 := (hd (g * c u)).scomp_of_eq u ((hasDerivAt_id u).sub_const u) (by simp)
    rw [one_smul] at h1
    refine h1.congr_of_eventuallyEq (.of_forall fun s => ?_)
    change h (g * c s) = h (g * c u * c (s - u))
    rw [mul_assoc, ← cadd, add_sub_cancel]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LocGLEqLocalEmbeddingAndKGLEqIntegralGL
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)),
          (∀ g, GlobalTheory.CuspRep.locGL E n w g = AdelicGLn.localEmbedding w g) ∧
          GlobalTheory.LFun.KGL w n = GLnLocal.integralGL (w.adicCompletion E) n := by
  intro E _ _ n w
  refine ⟨fun g => ?_, ?_⟩
  · obtain ⟨-, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
    have key : ∀ v, Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (GlobalTheory.CuspRep.locGL E n w g) =
        Matrix.GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc E v) (AdelicGLn.localEmbedding w g) := fun v => by
      by_cases h : v = w
      · subst h
        rw [GlobalTheory.CuspRep.pLoc_locGL]
        exact (h1 g).symm
      · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne h]
        exact (h2 v h g).symm
    refine Units.ext (Matrix.ext fun i j => ?_)
    refine DFunLike.ext _ _ fun v => ?_
    exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (key v)
  · have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
        Formalism.UG.GLint (Fin n) O = GLnLocal.integralGL (w.adicCompletion E) n := by
      rintro _ rfl
      rfl
    exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.OneParameterSubgroupNormOne
section
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Global
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem cv_mod (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w => by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, hm]

private theorem cv_sum (x : Cinf E) : ∑ τ : E →+* ℂ, coord τ x = ∑ w : InfinitePlace E, (x w + starRingEnd ℂ (x w)) := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun τ : E →+* ℂ => InfinitePlace.mk τ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 h)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (ComplexEmbedding.involutive_conjugate E τ).symm
    · rintro (rfl | rfl) <;> simp
  rw [hf, Finset.sum_pair hne.symm]
  unfold coord
  simp [hne.symm]

private theorem cv_det {m : ℝ → Matrix (Fin a) (Fin a) ℂ} {Y : Matrix (Fin a) (Fin a) ℂ} (h0 : m 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun s => m s i j) (Y i j) 0) : HasDerivAt (fun s => (m s).det) (∑ i, Y i i) 0 :=
  _root_.UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det h0 hd

end

theorem UpperTheory.one_parameter_subgroup_norm_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (X : Lie E r), ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0 →
          ∃ c : ℝ → GL (Fin r) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous (fun s => infGL E r (c s)) ∧
            HasDerivAt (fun s => toL (c s).val) X 0 ∧ ∀ s, infGL E r (c s) ∈ normOneGL E r := by
  intro E _ _ _ r X hX
  classical
  obtain ⟨c, h0, hadd, hc, hd, -⟩ := UpperTheory.V.Lit.Bor.oneParam E r X
  refine ⟨c, h0, hadd, hc, hd, fun s => ?_⟩
  have hD : ∀ w : InfinitePlace E, HasDerivAt (fun s => (c s).val.det w) (∑ i, X i i w) 0 := fun w => by
    have h1 := cv_det (m := fun s => (c s).val.map fun x => x w) (Y := fun i j => X i j w)
      (by rw [h0]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h])
      fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hd i) j) w
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    exact RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (c s).val
  let Q : ℝ → ℂ := fun s => ∏ w : InfinitePlace E, ((c s).val.det w * starRingEnd ℂ ((c s).val.det w))
  have hQ0 : Q 0 = 1 := by simp [Q, h0]
  have hQm : ∀ s t, Q (s + t) = Q s * Q t := fun s t => by
    simp only [Q, hadd, Units.val_mul, Matrix.det_mul, Pi.mul_apply, map_mul, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by ring
  have hQd : HasDerivAt Q 0 0 := by
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ) fun (w : InfinitePlace E) _ => (hD w).fun_mul (hD w).star
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_comm] at hX
    simp only [cv_sum] at hX
    rw [Finset.sum_comm] at hX
    refine hX.symm.trans ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [h0, Finset.sum_add_distrib]
  have hall : ∀ t, HasDerivAt Q 0 t := fun t => by
    have h1 : HasDerivAt (fun u => Q (u - t)) 0 t := by
      have := HasDerivAt.scomp t (g₁ := Q) (h := fun u => u - t) (by simpa using hQd) ((hasDerivAt_id t).sub_const t)
      simpa [Function.comp_def] using this
    have h2 := h1.const_mul (Q t)
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    change Q u = Q t * Q (u - t)
    rw [← hQm, add_sub_cancel]
  have hQ : Q s = 1 := (is_const_of_deriv_eq_zero (fun t => (hall t).differentiableAt) (fun t => (hall t).deriv) s 0).trans hQ0
  refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
  refine (cv_mod (c s)).trans ?_
  simp only [Q, Complex.mul_conj'] at hQ
  exact_mod_cast hQ
end

