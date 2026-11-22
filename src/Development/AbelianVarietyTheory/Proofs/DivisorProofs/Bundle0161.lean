import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityAsSumExpMinusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
section
open MvPolynomial

namespace GlobalTheory

namespace PowLinSpan

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem sum_C_mul_X_pow (u : σ → ℝ) (d : ℕ) :
    (∑ x, C (u x) * X x : MvPolynomial σ ℝ) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, u x ^ k x) •
          monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul, map_natCast, C_1, one_mul,
    Finsupp.coe_equivFunOnFinite_symm]
  ring

noncomputable def polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.piAntidiag Finset.univ d,
    monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) * φ (monomial (Finsupp.equivFunOnFinite.symm k) 1))

theorem eval_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (u : σ → ℝ) :
    eval u (polOf φ d) = φ ((∑ x, C (u x) * X x) ^ d) := by
  rw [sum_C_mul_X_pow, map_sum, polOf, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, eval_monomial, smul_eq_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

theorem coeff_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (m : σ →₀ ℕ) (hm : ∑ x, m x = d) :
    coeff m (polOf φ d) = (Nat.multinomial Finset.univ m : ℝ) * φ (monomial m 1) := by
  rw [polOf, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (⇑m)]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [← h]
    simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    simp [hm]

theorem degreeOf_polOf_le (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (x : σ) :
    (polOf φ d).degreeOf x ≤ d := by
  refine (degreeOf_le_totalDegree _ _).trans ?_
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k hk => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finset.mem_piAntidiag] at hk
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simpa [Finsupp.coe_equivFunOnFinite_symm] using hk.1.le

theorem monomial_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (m : σ →₀ ℕ) (hm : ∑ x, m x = d) : φ (monomial m 1) = 0 := by
  have h := coeff_polOf φ d m hm
  rw [hP, coeff_zero] at h
  have hne : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem homog_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsHomogeneous d) : φ Q = 0 := by
  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : ∑ x, m x = d := by
    have := hQ (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : monomial m (coeff m Q) = coeff m Q • monomial m (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, monomial_kill φ d hP m hdeg, smul_zero]

theorem span_pow_linRoot : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N d : ℕ) (Q : MvPolynomial (ι × Fin N) ℝ),
    Q.IsHomogeneous d →
    Q ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) '' {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := by
  intro ι _ _ N d Q hQ
  by_contra hnot
  obtain ⟨φ, hφQ, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ u : ι → Fin N → ℝ, (∀ τ, StrictAnti (u τ)) →
      φ ((∑ x : ι × Fin N, C (u x.1 x.2) * X x) ^ d) = 0 := by
    intro u hu
    have hmem : Formalism.DegreeFormula.linRoot u ^ d ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) ''
        {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := Submodule.subset_span ⟨u, hu, rfl⟩
    have h0 : φ (Formalism.DegreeFormula.linRoot u ^ d) = 0 := by
      have := Submodule.mem_map_of_mem (f := φ) hmem
      rw [hφ] at this
      simpa using this
    rw [Formalism.DegreeFormula.linRoot, neg_pow] at h0
    rcases neg_one_pow_eq_or (MvPolynomial (ι × Fin N) ℝ) d with h | h <;> rw [h] at h0
    · simpa using h0
    · simpa using h0
  have hP : polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (polOf φ d)
      (fun x => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ) - (x.2 : ℝ) * (d + 1))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective]
      · simpa using Nat.lt_succ_of_le (degreeOf_polOf_le φ d x)
      · intro a b hab
        simpa using hab
    · intro v hv
      rw [eval_polOf]
      have := hkill (fun τ i => v (τ, i)) ?_
      · simpa using this
      intro τ i j hij
      obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp (hv (τ, i))
      obtain ⟨b, hb, hvb⟩ := Finset.mem_image.mp (hv (τ, j))
      simp only [Finset.mem_range] at ha hb
      have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
        exact_mod_cast this
      have hb' : (b : ℝ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.mp hb
      have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      show v (τ, j) < v (τ, i)
      rw [← hva, ← hvb]
      simp only
      nlinarith
  exact hφQ (homog_kill φ d hP Q hQ)

end PowLinSpan
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ] (f g : MvPolynomial σ Ω) (D : ℕ), f ≠ 0 → f.totalDegree ≤ D → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  first | exact @GlobalTheory.hypersurface_diff_isPreirreducible | exact GlobalTheory.hypersurface_diff_isPreirreducible | (intros; apply GlobalTheory.hypersurface_diff_isPreirreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdeals
section
namespace GlobalTheory

theorem iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormEquationFromLocalAssociatesStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_norm_equation_from_local_associates : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  first | exact @GlobalTheory.CmIdealGlue.glue | exact GlobalTheory.CmIdealGlue.glue | (intros; apply GlobalTheory.CmIdealGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_affineOpen_of_isAffine {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens) :
    (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  haveI : IsAffine (W.1 : Scheme) := W.2
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (K.comap f) W.1.ι
    ⟨⊤, isAffineOpen_top _⟩
  rw [← Scheme.IdealSheafData.comap_comp, IdealSheafData.ideal_comap_top_of_isAffine] at h1
  have hc : (W.1.ι ≫ f).appTop ≫ (W.1.ι.appIso ⊤).inv = f.appLE ⊤ (W.1.ι ''ᵁ ⊤) (by simp) := by
    simp [Scheme.Hom.appLE]; exact Category.comp_id _
  have hs : Function.Surjective (W.1.ι.appIso ⊤).inv.hom :=
    (W.1.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective
  have h2 : (K.comap f).ideal ⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ =
      Ideal.map (f.appLE ⊤ (Subtype.val (⟨W.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens)) (by simp)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rw [← hc, CommRingCat.hom_comp, ← Ideal.map_map, h1, Ideal.map_comap_of_surjective _ hs]
  have hW : (⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  have key : ∀ V : X.affineOpens, V = W →
      (K.comap f).ideal V = Ideal.map (f.appLE ⊤ V.1 (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) →
      (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rintro V rfl h; exact h
  exact key _ hW h2

example : ∀ {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens), (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
  fun f K W => IdealSheafData.ideal_comap_affineOpen_of_isAffine f K W

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffineStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | exact @GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | exact GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataExtOfOpenCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

theorem idealSheafData_ext_of_openCover {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨(f p.1) ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (f p.1)⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    have hy : y ∈ (⊤ : (V i).Opens) := trivial
    rw [← iSup_affineOpens_eq_top (V i)] at hy
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, ⟨y, hW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun J => J.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersionsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions : (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) → ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X), (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) → ∀ (K : ∀ i, (P i).IdealSheafData), (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j → (K i).comap a = (K j).comap b) → ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  first | (exact @GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (exact GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (intros; apply GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEqStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_eq_of_basicOpen_eq' : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' → X.basicOpen e = X.basicOpen e' → e = e' := by
  first | exact @GlobalTheory.idempotent_eq_of_basicOpen_eq | exact GlobalTheory.idempotent_eq_of_basicOpen_eq | (intros; apply GlobalTheory.idempotent_eq_of_basicOpen_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityAsSumExpMinusOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identity_as_sum_exp_minus_one : ∃ (n : ℕ) (a : Fin n → ℝ) (A : Fin n → ℝ → ℂ), (∀ j, Function.HasTemperateGrowth (A j)) ∧
    ∀ t : ℝ, (t : ℂ) = ∑ j, (Complex.exp (Complex.I * ((a j * t : ℝ) : ℂ)) - 1) * A j t := by
  first | exact @GlobalTheory.ExpDivision.exists_division | exact GlobalTheory.ExpDivision.exists_division | (intros; apply GlobalTheory.ExpDivision.exists_division <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtalePrimeComparison
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_prime_comparison : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  first | (exact @GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (exact GlobalTheory.eq_of_le_of_comap_eq_of_indEtale) | (intros; apply GlobalTheory.eq_of_le_of_comap_eq_of_indEtale  <;> assumption)
end

