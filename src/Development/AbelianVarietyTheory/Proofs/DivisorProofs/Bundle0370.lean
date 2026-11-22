import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitSectionAvoid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerThree
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem colGram_three_unitLower : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  intro M hd hu
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h01 : M 0 1 = 0 := hu 0 1 (by decide)
  have h02 : M 0 2 = 0 := hu 0 2 (by decide)
  have h12 : M 1 2 = 0 := hu 1 2 (by decide)
  have e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  have e2 : lminor (Mᴴ * M) 2 =
      (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0 := by
    unfold lminor
    exact Matrix.det_fin_two _
  have g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have g2 : lminor (Mᴴ * M) 2 =
      ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      <;> ring
  have pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · unfold colGram
    rw [g1, add_assoc, pos _ (by positivity), ← add_assoc]
  · unfold colGram
    rw [g2, add_assoc, pos _ (by positivity), ← add_assoc]

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosetsStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_covered_by_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  first | exact @GlobalTheory.compact_finite_leftCoset_reps | exact GlobalTheory.compact_finite_leftCoset_reps | (intros; apply GlobalTheory.compact_finite_leftCoset_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCohomology_commutes_with_filteredColimits : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (exact GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (intros; apply GlobalTheory.EtC.ContFin.cohomology_filteredColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_contracting_homotopy : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ), (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b), ε a b (bop α β) = 1) ∧ (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧ ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)), cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  first | (exact @GlobalTheory.EZ.Cone.coneContraction) | (exact GlobalTheory.EZ.Cone.coneContraction) | (intros; apply GlobalTheory.EZ.Cone.coneContraction  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegralStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice k a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  first | exact @GlobalTheory.RankFibreKer.nhds_one_slice_invariant | exact GlobalTheory.RankFibreKer.nhds_one_slice_invariant | (intros; apply GlobalTheory.RankFibreKer.nhds_one_slice_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasureStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_slice_section_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  first | exact @GlobalTheory.RankFibreKer.exists_isCompact_of_slice | exact GlobalTheory.RankFibreKer.exists_isCompact_of_slice | (intros; apply GlobalTheory.RankFibreKer.exists_isCompact_of_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGramSize
section
set_option autoImplicit false
noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TrBasisQuot

theorem isTranscendenceBasis_quot_polynomial {k : Type} [Field k] {m : ℕ}
    (p : Polynomial (MvPolynomial (Fin m) k)) (hp : Prime p) (hdeg : 0 < p.natDegree) :
    IsTranscendenceBasis k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
  classical
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let φ : MvPolynomial (Fin m) k →ₐ[k] Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p} :=
    (Ideal.Quotient.mkₐ k (Ideal.span {p})).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k) _)
  have hφ : ∀ b, φ b = Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C b) := fun b => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    by_contra hb0
    have := Polynomial.natDegree_le_of_dvd hb (Polynomial.C_ne_zero.2 hb0)
    rw [Polynomial.natDegree_C] at this
    omega
  have haev : MvPolynomial.aeval (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) = φ :=
    MvPolynomial.algHom_ext fun j => by simp [hφ]
  have hind : AlgebraicIndependent k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    rw [algebraicIndependent_iff_injective_aeval, haev]
    exact hinj
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  have hS : ∀ b, φ b ∈ Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    intro b
    rw [Algebra.adjoin_range_eq_range_aeval, haev]
    exact AlgHom.mem_range_self φ b
  let ψ := RingHom.codRestrict φ.toRingHom (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j)))) (fun b => hS b)
  have hψ : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
  have hr : IsAlgebraic (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      (Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X) := by
    refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hp.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hc : (algebraMap _ (Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p})).comp ψ =
        (Ideal.Quotient.mk (Ideal.span {p})).comp Polynomial.C := RingHom.ext fun b => rfl
    rw [hc, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self p
  have htop : Algebra.adjoin (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      {Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X} = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Polynomial.induction_on q (fun b => ?_) (fun f g hf hg => ?_) (fun n b ih => ?_)
    · exact Subalgebra.algebraMap_mem _ (⟨φ b, hS b⟩ : Algebra.adjoin k _)
    · rw [map_add]
      exact add_mem hf hg
    · rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem ih (Algebra.subset_adjoin rfl)
  have h1 := (Algebra.isAlgebraic_adjoin_singleton_iff).2 hr
  exact ⟨fun z => h1 z (by rw [htop]; trivial)⟩

theorem trBasis_mod_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F),
    AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) →
    ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A,
      IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  intro k F _ _ _ d u hu A hA t ht
  subst hA
  classical
  have ht0 : Irreducible (hu.aevalEquiv.symm t) :=
    (MulEquiv.irreducible_iff hu.aevalEquiv.symm.toMulEquiv).2 ht
  cases d with
  | zero =>
    exfalso
    have h := MvPolynomial.eq_C_of_isEmpty (hu.aevalEquiv.symm t)
    apply ht0.not_isUnit
    rw [h]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
    rw [h, hc, map_zero]
  | succ m =>
    obtain ⟨i, hi⟩ : ∃ i, (hu.aevalEquiv.symm t).degreeOf i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : (hu.aevalEquiv.symm t).totalDegree = 0 := by
        rw [MvPolynomial.totalDegree_eq_zero_iff]
        intro mm hmm x
        have := MvPolynomial.monomial_le_degreeOf x hmm
        rw [hcon x] at this
        omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
      apply ht0.not_isUnit
      rw [h0]
      refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
      rw [h0, hc, map_zero]
    let E := hu.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin (m + 1)) i)).trans
      (MvPolynomial.finSuccEquiv k m))
    have hdeg : 0 < (E t).natDegree := by
      have h1 : (E t).natDegree = ((MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) i))
          (hu.aevalEquiv.symm t)).degreeOf 0 :=
        MvPolynomial.natDegree_finSuccEquiv _
      have h2 := MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (0 : Fin (m + 1)) i).injective
        (p := hu.aevalEquiv.symm t) i
      rw [Equiv.swap_apply_right] at h2
      rw [h1, h2]
      omega
    have hpE : Prime (E t) :=
      ((MulEquiv.irreducible_iff E.toMulEquiv).2 ht).prime
    have hpt : Prime t := (MulEquiv.prime_iff E.toMulEquiv).1 hpE
    refine ⟨hpt, m, rfl, fun j => E.symm (Polynomial.C (MvPolynomial.X j)), ?_⟩
    have hI : Ideal.span {E t} = (Ideal.span {t}).map (E : _ →+* _) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    have hb := (Ideal.quotientEquivAlg (Ideal.span {t}) (Ideal.span {E t}) E hI).symm.isTranscendenceBasis
      (GlobalTheory.TrBasisQuot.isTranscendenceBasis_quot_polynomial (E t) hpE hdeg)
    have hfun : (⇑((Ideal.span {t}).quotientEquivAlg (Ideal.span {E t}) E hI).symm ∘ fun j : Fin m =>
        (Ideal.Quotient.mk (Ideal.span {E t})) (Polynomial.C (MvPolynomial.X j))) =
        fun j => Ideal.Quotient.mk (Ideal.span {t}) (E.symm (Polynomial.C (MvPolynomial.X j))) := by
      funext j
      simp only [Function.comp_apply, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    rw [hfun] at hb
    exact hb

end GlobalTheory.TrBasisQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicPrimitiveRootsFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit : ∀ (q : ℕ) (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ ζ : Prim q c.pt, ∃ (j : J) (ξ : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = ζ) ∧ ∀ (j : J) (ξ ξ' : Prim q (D.obj j)), Prim.map (c.ι.app j).hom ξ = Prim.map (c.ι.app j).hom ξ' → ∃ (k : J) (f : j ⟶ k), Prim.map (D.map f).hom ξ = Prim.map (D.map f).hom ξ' := by
  first | (exact @GlobalTheory.EtC.prim_filtered_colimit) | (exact GlobalTheory.EtC.prim_filtered_colimit) | (intros; apply GlobalTheory.EtC.prim_filtered_colimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTCompDTStatement
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero : ∀ a b c d : ℕ, c + d + 2 = a + b → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  first | (exact @GlobalTheory.EZ.TotSq.dT_sq) | (exact GlobalTheory.EZ.TotSq.dT_sq) | (intros; apply GlobalTheory.EZ.TotSq.dT_sq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DadjCombination
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem dadj_combination : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (n : ℕ) (u : Fin n → F), ∀ v ∈ Algebra.adjoin k (Set.range u), ∃ c : Fin n → F, (∀ j, c j ∈ Algebra.adjoin k (Set.range u)) ∧ D k K (algebraMap F K v) = ∑ j, algebraMap F K (c j) • D k K (algebraMap F K (u j)) := by
  intro k F K _ _ _ _ _ _ _ n u v hv
  induction hv using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simpa using Subalgebra.one_mem _
      · simpa [Pi.single_apply, h] using Subalgebra.zero_mem _
    · simp [Pi.single_apply]
  | algebraMap r =>
    refine ⟨0, fun _ => Subalgebra.zero_mem _, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
    simp
  | add x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨cx + cy, fun j => add_mem (hcx j) (hcy j), ?_⟩
    simp only [map_add, ex, ey, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | mul x y hx hy ihx ihy =>
    obtain ⟨cx, hcx, ex⟩ := ihx
    obtain ⟨cy, hcy, ey⟩ := ihy
    refine ⟨fun j => x * cy j + y * cx j, fun j => add_mem (mul_mem hx (hcy j)) (mul_mem hy (hcx j)), ?_⟩
    rw [map_mul, Derivation.leibniz, ex, ey]
    simp only [Finset.smul_sum, smul_smul, map_add, map_mul, add_smul, Finset.sum_add_distrib]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalDifferentialEval
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  first | (exact @GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (exact GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (intros; apply GlobalTheory.EZ.ev_map_dD_eq_diagCx_d <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialsSpanOfUniformizerBasis
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential IsLocalRing TensorProduct

namespace GlobalTheory

theorem span_D_uniformizer_transcendenceBasis : ∀ (k R : Type) [Field k] [CharZero k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Algebra.EssFiniteType k R] (s : R),
    Irreducible s → ∀ (m : ℕ) (y : Fin m → R),
    IsTranscendenceBasis k (fun j => IsLocalRing.residue R (y j)) →
    Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) = ⊤ := by
  intro k R _ _ _ _ _ _ _ s hs m y hy
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := residue_surjective
  haveI := hy.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun j => residue R (y j)))
      (ResidueField R) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hy.1
  have hmax : maximalIdeal R = Ideal.span {s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer s).1 hs
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := ker_residue
  have hs0 : algebraMap R (ResidueField R) s = 0 := by
    rw [← RingHom.mem_ker, hker, hmax]; exact Ideal.mem_span_singleton_self s
  haveI : Module.Finite R Ω[R⁄k] := inferInstance
  set N := Submodule.span R (insert (D k R s) (Set.range fun j => D k R (y j))) with hN
  have hmb : ∀ x : R, mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] D k R x) =
      D k (ResidueField R) (algebraMap R (ResidueField R) x) :=
    fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
  have key : ∀ ω : Ω[R⁄k], ∃ n ∈ N, (1 : ResidueField R) ⊗ₜ[R] ω = (1 : ResidueField R) ⊗ₜ[R] n := by
    intro ω
    let c := b.repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))
    let c' : Fin m → R := fun i => Function.surjInv hsurj (c i)
    have hc' : ∀ i, algebraMap R (ResidueField R) (c' i) = c i := fun i => Function.surjInv_eq hsurj _
    have h0 : mapBaseChange k R (ResidueField R)
        ((1 : ResidueField R) ⊗ₜ[R] (ω - ∑ i, c' i • D k R (y i))) = 0 := by
      rw [tmul_sub, map_sub, tmul_sum, map_sum, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] ω))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, tmul_smul, ← algebraMap_smul (ResidueField R) (c' i), map_smul, hmb, hc']
      rfl
    obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) hsurj _).mp h0
    obtain ⟨⟨a, ha⟩, rfl⟩ := Ideal.toCotangent_surjective _ t
    have ha' := ha
    rw [hker, hmax, Ideal.mem_span_singleton'] at ha'
    obtain ⟨r, rfl⟩ := ha'
    rw [kerCotangentToTensor_toCotangent] at ht
    have e1 : (1 : ResidueField R) ⊗ₜ[R] D k R (r * s) = (1 : ResidueField R) ⊗ₜ[R] (r • D k R s) := by
      rw [Derivation.leibniz, tmul_add, add_eq_left]
      have : (1 : ResidueField R) ⊗ₜ[R] (s • D k R r) = (algebraMap R (ResidueField R) s) • ((1 : ResidueField R) ⊗ₜ[R] D k R r) := by
        rw [algebraMap_smul, tmul_smul]
      rw [this, hs0, zero_smul]
    refine ⟨r • D k R s + ∑ i, c' i • D k R (y i), ?_, ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)))
    · have e2 : ω = (ω - ∑ i, c' i • D k R (y i)) + ∑ i, c' i • D k R (y i) := (sub_add_cancel _ _).symm
      rw [e2, tmul_add, ← ht, e1, ← tmul_add]
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, eq_top_iff]
  intro z _
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c ω =>
    obtain ⟨c₀, rfl⟩ := hsurj c
    obtain ⟨n, hn, hω⟩ := key ω
    refine ⟨c₀ • n, N.smul_mem _ hn, ?_⟩
    rw [LinearMap.map_smul, TensorProduct.mk_apply, ← hω, ← algebraMap_smul (ResidueField R) c₀,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x z hx hz => exact add_mem (hx trivial) (hz trivial)

end GlobalTheory
end
end

