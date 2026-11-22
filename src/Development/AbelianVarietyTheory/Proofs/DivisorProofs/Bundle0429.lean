import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLocDIffSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOneStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧ (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧ ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  first | exact @GlobalTheory.QFam.levelPoly_conj | exact GlobalTheory.QFam.levelPoly_conj | (intros; apply GlobalTheory.QFam.levelPoly_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPos
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscRep
variable {R : Type} [CommRing R]

def asum (m : ℕ) : ℤ := ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ)

theorem asum_succ (k : ℕ) : asum (k + 1) = asum k + (-1) ^ (k + 1) := by
  rw [asum, Fin.sum_univ_castSucc]
  simp [asum]

theorem asum_even (m : ℕ) : asum m = if Even m then 1 else 0 := by
  induction m with
  | zero => simp [asum]
  | succ k ih =>
    rw [asum_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h' : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', (h.add_one).neg_one_pow]
    · have h' : Even (k + 1) := h.add_one
      have h'' : ¬ Even k := Nat.not_even_iff_odd.mpr h
      simp [h', h'', h'.neg_one_pow]

variable (R) in
abbrev C (F : PSh) : ChainComplex (Shv R) ℕ := (chainsN R).obj (disc.obj F)

theorem C_d (F : PSh) (p : ℕ) :
    (C R F).d (p + 1) p = (asum (p + 1)) • (𝟙 ((free R).obj F) : (C R F).X (p + 1) ⟶ (C R F).X p) := by
  rw [show (C R F).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((disc.obj F).δ i) from
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ p]
  simp only [asum, Finset.sum_smul, SimplicialObject.δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (disc.obj F).map (SimplexCategory.δ i).op = 𝟙 F from rfl]
  exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f) ((free R).map_id F)

def idX (F : PSh) (i j : ℕ) : (C R F).X i ⟶ (C R F).X j := 𝟙 ((free R).obj F)

theorem idX_comp (F : PSh) (i j k : ℕ) : idX (R := R) F i j ≫ idX F j k = idX F i k := Category.id_comp _

theorem C_d' (F : PSh) (p : ℕ) : (C R F).d (p + 1) p = (asum (p + 1)) • idX F (p + 1) p := C_d F p

def piC (F : PSh) : C R F ⟶ C R F where
  f i := if i = 0 then 𝟙 _ else 0
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [if_neg (Nat.succ_ne_zero j), zero_comp, C_d']
    rcases j with _ | j
    · rw [asum_even, if_neg (by decide), zero_smul, zero_comp]
    · rw [if_neg (Nat.succ_ne_zero j), comp_zero]

def htpC (F : PSh) : Homotopy (𝟙 (C R F)) (piC F) where
  hom i j := if i + 1 = j ∧ Odd i then idX F i j else 0
  zero i j w := by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact w h
  comm i := by
    rcases i with _ | k
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, C_d']
      simp [piC, asum_even]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, C_d', C_d']
      simp only [piC, if_neg (Nat.succ_ne_zero k), add_zero, true_and, asum_even]
      rcases Nat.even_or_odd k with h | h
      · have h1 : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using h
        have h2 : Even (k + 1 + 1) := h1 |> fun _ => (h.add_one).add_one
        have h3 : Odd (k + 1) := h.add_one
        have h4 : ¬ Odd k := Nat.not_odd_iff_even.mpr h
        simp only [h1, h2, h3, h4, if_true, if_false, one_smul, zero_smul, comp_zero, zero_comp, zero_add, idX_comp]
        rfl
      · have h1 : Even (k + 1) := h.add_one
        have h3 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.mpr h1
        simp only [h1, h, h3, if_true, if_false, one_smul, comp_zero, zero_comp, add_zero, idX_comp]
        rfl

def piZ (F : PSh) : (chains R).obj (disc.obj F) ⟶ (chains R).obj (disc.obj F) :=
  HomologicalComplex.extendMap (piC F) ComplexShape.embeddingDownNat

def htpZ (F : PSh) : Homotopy (𝟙 ((chains R).obj (disc.obj F))) (piZ F) :=
  (Homotopy.ofEq (HomologicalComplex.extendMap_id (C R F) ComplexShape.embeddingDownNat).symm).trans
    ((htpC F).extend ComplexShape.embeddingDownNat)

theorem piZ_f (F : PSh) (p : ℕ) (hp : 0 < p) : (piZ (R := R) F).f (-(p : ℤ)) = 0 := by
  have h1 := HomologicalComplex.extendMap_f (piC (R := R) F) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  simp only [piC, if_neg hp.ne', zero_comp, comp_zero] at h1
  exact h1

end GlobalTheory.EtC.DiscRep

open GlobalTheory.EtC.DiscRep in

theorem GlobalTheory.EtC.discRep : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ)
    (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n,
      CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  intro R _ F I n x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  refine ⟨zcomp (Cocycle.ofHom (piZ F)) α (zero_add n), ?_, ?_⟩
  · rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-(n.negOnePow • (Cochain.ofHomotopy (htpZ F)).comp α.1 (by omega)), ?_⟩
    rw [δ_neg, δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  · intro p hp s h
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) _ _ s (add_zero _) h, piZ_f F p hp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_divisor) | (exact GlobalTheory.KeyOriginCut.exists_stage_divisor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_divisor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J), (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n), ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
  first | (exact @GlobalTheory.EtC.SemiMap.op_image_spec) | (exact GlobalTheory.EtC.SemiMap.op_image_spec) | (intros; apply GlobalTheory.EtC.SemiMap.op_image_spec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndependentBasisCoprime
section
open NumberField

namespace GlobalTheory.CoprimeBasis

theorem isTorsionFree_of_addTorsionFree {F : Type} [Field F] [NumberField F]
    (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [IsAddTorsionFree M] :
    Module.IsTorsionFree (𝓞 F) M where
  isSMulRegular r hr x y hxy := by
    have hxy' : r • x = r • y := hxy
    have hr0 : r ≠ 0 := hr.ne_zero
    have hn : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hr0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    have h1 : (Ideal.absNorm (Ideal.span {r})) • (x - y) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F), ← hb, mul_smul, smul_sub, hxy', sub_self, smul_zero]
    exact sub_eq_zero.1 (nsmul_right_injective hn (h1.trans (nsmul_zero _).symm))

theorem isCoprime_of_mem_primeTo {R : Type} [CommRing R] {s d : R}
    (hs : s ∈ GlobalTheory.Mass.primeTo d) : IsCoprime s d := by
  by_cases hI : Ideal.span {s, d} = ⊤
  · obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 hI)
    exact ⟨a, b, h⟩
  · obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
    exact absurd (hle (Ideal.subset_span (by simp))) (hs P hP (hle (Ideal.subset_span (by simp))))

theorem exists_coprime_basis : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  intro F _ _ M _ _ _ _ N hN
  classical
  set S : Submonoid (𝓞 F) := GlobalTheory.Mass.primeTo (N : 𝓞 F) with hSdef
  have hSle : S ≤ nonZeroDivisors (𝓞 F) := GlobalTheory.Mass.SemiBasis.primeTo_le hN
  haveI : Module.IsTorsionFree (𝓞 F) M := isTorsionFree_of_addTorsionFree M
  haveI : Module.Finite (𝓞 F) M := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) M
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hSle
  haveI : IsPrincipalIdealRing (Localization S) := by
    haveI := GlobalTheory.Mass.SemiBasis.isPID (K := F) hN
    haveI : IsLocalization S (GlobalTheory.Mass.SemiBasis.A F hN) :=
      Localization.subalgebra.isLocalization_ofField F _ _
    exact IsPrincipalIdealRing.of_surjective
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).toRingHom
      (IsLocalization.algEquiv S (GlobalTheory.Mass.SemiBasis.A F hN) (Localization S)).surjective
  haveI : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := Localization S) (M := LocalizedModule S M)
  have hb : ∀ i, ∃ (m : M) (s : S), b i = LocalizedModule.mk m s := fun i => by
    exact LocalizedModule.induction_on (β := fun y => ∃ (m : M) (s : S), y = LocalizedModule.mk m s)
      (fun m s => ⟨m, s, rfl⟩) (b i)
  choose x s hxs using hb
  have key : ∀ i, (s i : 𝓞 F) • b i = LocalizedModule.mk (x i) 1 := by
    intro i
    rw [hxs i, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel]
  refine ⟨r, x, ?_, ?_⟩
  · let u : Fin r → (Localization S)ˣ := fun i => (IsLocalization.map_units (Localization S) (s i)).unit
    have hu : LinearIndependent (Localization S) (u • ⇑b) := b.linearIndependent.units_smul u
    have hfx : (u • ⇑b) = LocalizedModule.mkLinearMap S M ∘ x := by
      funext i
      simp only [Pi.smul_apply', Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← key i]
      rw [Units.smul_def, IsUnit.unit_spec, algebraMap_smul]
    rw [hfx] at hu
    have hinj : Function.Injective fun a : 𝓞 F => a • (1 : Localization S) := by
      intro a a' h
      simp only [Algebra.smul_def, mul_one] at h
      exact IsLocalization.injective (Localization S) hSle h
    exact (hu.restrict_scalars hinj).of_comp _
  · set P : Submodule (𝓞 F) M := Submodule.span (𝓞 F) (Set.range x) with hP
    have hloc : ∀ y : LocalizedModule S M, ∃ t : S, ∃ m' ∈ P, (t : 𝓞 F) • y = LocalizedModule.mk m' 1 := by
      intro y
      have hy : y ∈ Submodule.span (Localization S) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨s i, x i, Submodule.subset_span ⟨i, rfl⟩, key i⟩
      | zero => exact ⟨1, 0, P.zero_mem, by simp [LocalizedModule.zero_mk]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨t', m', hm', h'⟩ := hz
        refine ⟨t * t', (t' : 𝓞 F) • m + (t : 𝓞 F) • m', P.add_mem (P.smul_mem _ hm) (P.smul_mem _ hm'), ?_⟩
        calc ((t * t' : S) : 𝓞 F) • (y + z) = (t' : 𝓞 F) • ((t : 𝓞 F) • y) + (t : 𝓞 F) • ((t' : 𝓞 F) • z) := by
              rw [Submonoid.coe_mul, smul_add, smul_smul, smul_smul, mul_comm (t' : 𝓞 F)]
          _ = _ := by
              rw [h, h', LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_add_mk]
              simp
      | smul a y _ hy =>
        obtain ⟨t, m, hm, h⟩ := hy
        obtain ⟨⟨r0, u⟩, hr⟩ := IsLocalization.surj S a
        have hua : (u : 𝓞 F) • a = algebraMap (𝓞 F) (Localization S) r0 := by
          rw [Algebra.smul_def, mul_comm]; exact hr
        refine ⟨u * t, r0 • m, P.smul_mem r0 hm, ?_⟩
        calc ((u * t : S) : 𝓞 F) • (a • y) = ((u : 𝓞 F) • a) • ((t : 𝓞 F) • y) := by
              rw [Submonoid.coe_mul, mul_smul, smul_comm (t : 𝓞 F) a y, smul_assoc]
          _ = LocalizedModule.mk (r0 • m) 1 := by
              rw [hua, h, algebraMap_smul, LocalizedModule.smul'_mk]
    have hgen : ∀ m : M, ∃ t : S, (t : 𝓞 F) • m ∈ P := by
      intro m
      obtain ⟨t, m', hm', h⟩ := hloc (LocalizedModule.mk m 1)
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      simp only [one_smul, Submonoid.smul_def] at hu
      refine ⟨u * t, ?_⟩
      rw [Submonoid.coe_mul, mul_smul, hu]
      exact P.smul_mem _ hm'
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 F) (M := M)
    choose t ht using fun j => hgen (g j)
    refine ⟨((∏ j, t j : S) : 𝓞 F), ?_, ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero (hSle (∏ j, t j).2)
    · exact isCoprime_of_mem_primeTo (∏ j, t j).2
    · intro m
      have hle : Submodule.span (𝓞 F) (Set.range g) ≤
          P.comap (LinearMap.lsmul (𝓞 F) M ((∏ j, t j : S) : 𝓞 F)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show ((∏ j, t j : S) : 𝓞 F) • g j ∈ P
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Submonoid.coe_mul, mul_smul]
        exact P.smul_mem _ (ht j)
      rw [hg] at hle
      exact hle Submodule.mem_top

end GlobalTheory.CoprimeBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepthStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unimodular_matrix_for_depth : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  first | exact @GlobalTheory.powRow_matrix | exact GlobalTheory.powRow_matrix | (intros; apply GlobalTheory.powRow_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEqStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ), IsUnif ϖ → ∀ t : n ⊕ Fin c, ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) = (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  first | exact @GlobalTheory.DiagVol.invVol_diag_one | exact GlobalTheory.DiagVol.invVol_diag_one | (intros; apply GlobalTheory.DiagVol.invVol_diag_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibre
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem comp_trivV (N : ℕ) {E E' : Spc} (f : E' ⟶ E) : f ≫ trivV N E = trivV N E' := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

theorem hom_ext_invertibleLocus (q : ℕ) {E : Spc} (f g : E ⟶ disc.obj (invP q)) : f = g := by
  ext n U x
  exact Subsingleton.elim (α := PLift _) _ _

def toInvP (q : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) : disc.obj F ⟶ disc.obj (invP q) :=
  disc.map
    { app := fun U => TypeCat.ofHom fun x => ⟨hF U.unop ⟨x⟩⟩
      naturality := fun _ _ _ => by ext x; rfl }

def fibQ.snd (q N : ℕ) : fibQ q N ⟶ PGL N := pullback.snd _ _

theorem fibQ.cond (q N : ℕ) : trivV N (fibQ q N) = fibQ.snd q N ≫ PGL.pr N := by
  show trivV N (pullback (trivV N (disc.obj (invP q))) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N
  rw [← comp_trivV N (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N))]
  exact pullback.condition

def fibQ.lift {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N) (h : trivV N X = b ≫ PGL.pr N) :
    X ⟶ fibQ q N :=
  pullback.lift a b (by rw [comp_trivV]; exact h)

@[simp] theorem fibQ.lift_snd {q N : ℕ} {X : Spc} (a : X ⟶ disc.obj (invP q)) (b : X ⟶ PGL N)
    (h : trivV N X = b ≫ PGL.pr N) : fibQ.lift a b h ≫ fibQ.snd q N = b :=
  pullback.lift_snd _ _ _

theorem fibQ.hom_ext {q N : ℕ} {X : Spc} {f g : X ⟶ fibQ q N} (h : f ≫ fibQ.snd q N = g ≫ fibQ.snd q N) : f = g :=
  pullback.hom_ext (hom_ext_invertibleLocus q _ _) h

theorem trivProj_iso (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N),
      θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  have h1 : prod.fst ≫ trivV N (disc.obj F) = (prod.snd ≫ fibQ.snd q N) ≫ PGL.pr N := by
    rw [comp_trivV, Category.assoc, ← fibQ.cond, comp_trivV]
  have h2 : trivV N (pullback (trivV N (disc.obj F)) (PGL.pr N)) = pullback.snd _ _ ≫ PGL.pr N := by
    rw [← comp_trivV N (pullback.fst (trivV N (disc.obj F)) (PGL.pr N))]
    exact pullback.condition
  let hom : disc.obj F ⨯ fibQ q N ⟶ pullback (trivV N (disc.obj F)) (PGL.pr N) :=
    pullback.lift prod.fst (prod.snd ≫ fibQ.snd q N) h1
  let inv : pullback (trivV N (disc.obj F)) (PGL.pr N) ⟶ disc.obj F ⨯ fibQ q N :=
    prod.lift (pullback.fst _ _) (fibQ.lift (pullback.fst _ _ ≫ toInvP q F hF) (pullback.snd _ _) h2)
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_, ?_⟩
  · apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, pullback.lift_fst, Category.id_comp]
    · apply fibQ.hom_ext
      rw [Category.assoc, Category.assoc, ← Category.assoc inv, prod.lift_snd, fibQ.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, prod.lift_snd, fibQ.lift_snd, Category.id_comp]
  · exact pullback.lift_fst _ _ _
  · rw [← Category.assoc, pullback.lift_snd, Category.assoc]
    rfl

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycleStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_agree_of_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | exact GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | (intros; apply GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariantStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulP_eq_of_transl_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (a : G.A (n + 1)), G.transl n a = a ⊗ₜ[R] 1 → ∃ e : G.A n, G.mulP n e = a := by
  first | exact @GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | exact GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroClosureEtaleAtStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (exact GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_ne_zero_closureEtaleAt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringLeValuationSubringAStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_le_valuationSubring' : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ), (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) → (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) → ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R), ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring <;> assumption)
end

