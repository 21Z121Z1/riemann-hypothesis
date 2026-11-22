import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  first | (exact @GlobalTheory.EtC.DiscSupp.bijective_disc) | (exact GlobalTheory.EtC.DiscSupp.bijective_disc) | (intros; apply GlobalTheory.EtC.DiscSupp.bijective_disc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexXStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_projBundleModelCochainComplex_X : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) → ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  first | (exact @GlobalTheory.EtC.Jcx_X_injective) | (exact GlobalTheory.EtC.Jcx_X_injective) | (intros; apply GlobalTheory.EtC.Jcx_X_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in

theorem integralClosure_projective_rA : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K]
    [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F),
    IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  intro k _ _ F K _ _ _ _ _ _ d x h i
  obtain ⟨hfin, -, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x h {i} (Finset.singleton_nonempty i)
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x h.pd i
  haveI : IsRegularRing (rA k x {i}) := IsRegularRing.of_ringEquiv e.toRingEquiv
  haveI : IsNoetherianRing (rA k x {i}) := inferInstance
  haveI : IsDomain (rA k x {i}) := inferInstance
  haveI : IsIntegrallyClosed (rA k x {i}) :=
    haveI : UniqueFactorizationMonoid (MvPolynomial (Fin d) k) := inferInstance
    haveI : UniqueFactorizationMonoid (rA k x {i}) :=
      (MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance)
    inferInstance
  haveI : IsRegularRing (rB k K x {i}) := GlobalTheory.isRegularRing_of_smooth k _
  haveI hB : IsRegularRing (integralClosure (rA k x {i}) K) := ‹IsRegularRing (rB k K x {i})›
  haveI : IsNoetherianRing (integralClosure (rA k x {i}) K) := inferInstance
  haveI : IsDomain (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Algebra.IsIntegral (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : FaithfulSMul (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have := congrArg (fun y : integralClosure (rA k x {i}) K => (y : K)) hab
    exact Subtype.ext ((algebraMap F K).injective this)
  haveI : Algebra.HasGoingDown (rA k x {i}) (integralClosure (rA k x {i}) K) := inferInstance
  haveI : Module.Flat (rA k x {i}) (integralClosure (rA k x {i}) K) := by
    refine GlobalTheory.flat_of_isRegularRing_of_isRegularRing fun q hq => ?_
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under (rA k x {i})) q]
    · exact le_self_add
    all_goals first | assumption | infer_instance
  haveI : Module.FinitePresentation (rA k x {i}) (integralClosure (rA k x {i}) K) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
section
open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DenClear

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (c : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem intSmul_eq {r : ℕ} (a : 𝓞 E) (w : Fin r → E) : a • w = (a : E) • w := by
  rw [← algebraMap_smul E a w]

theorem exists_natSmul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))) : ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : ((n * m : ℕ) : E) • (x + y) = m • ((n : E) • x) + n • ((m : E) • y) := by
      simp only [Nat.cast_mul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem hnx m) (Λ.nsmul_mem hmy n)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_natMul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, (a : E) = (m : E) * c := ⟨⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩, rfl⟩
    have e : ((m * n : ℕ) : E) • (c • x) = a • ((n : E) • x) := by
      rw [intSmul_eq, ha, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact Λ.smul_mem _ hnx

variable [IsCMField E]

theorem exists_natSmul_mem_lieLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 →
    (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  intro E _ _ _ r G Λ hfg hspan X htr hskew
  obtain ⟨S, hS⟩ := hfg
  have hv : ∀ s : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • (X *ᵥ s) ∈ Λ := fun s =>
    exists_natSmul_mem Λ _ (by rw [hspan]; trivial)
  choose n hn hnX using hv
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_, ?_, ?_⟩
  · rw [trace_smul, htr, smul_zero]
  · intro x y
    have h := hskew x y
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at h ⊢
    have e1 : ∀ a b, (↑(∏ s ∈ S, n s) * (X *ᵥ x) a) * G a b * (IsCMField.complexConj E) (y b) =
        (↑(∏ s ∈ S, n s) : E) * ((X *ᵥ x) a * G a b * (IsCMField.complexConj E) (y b)) := fun a b => by ring
    have e2 : ∀ a b, x a * G a b * ((↑(∏ s ∈ S, n s) : E) * (IsCMField.complexConj E) ((X *ᵥ y) b)) =
        (↑(∏ s ∈ S, n s) : E) * (x a * G a b * (IsCMField.complexConj E) ((X *ᵥ y) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h, mul_zero]
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [smul_mulVec]
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hs
      rw [hk, Nat.cast_mul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
      exact Λ.nsmul_mem (hnX s) k
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [intSmul_eq, mulVec_smul, ← intSmul_eq]
      exact Λ.smul_mem a hx

end GlobalTheory.DenClear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  first | exact @GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | exact GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | (intros; apply GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwiseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Spc) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ContCone R F (((evaluation _ PSh).obj k ⋙ disc).mapCone c)) → ContCone R F c := by
  first | (exact @GlobalTheory.EtC.contCone_of_levelwise) | (exact GlobalTheory.EtC.contCone_of_levelwise) | (intros; apply GlobalTheory.EtC.contCone_of_levelwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

theorem exists_comp_eq_of_injective {R : Type} [CommRing R] {A B K : Shv R} [Injective K] (g : A ⟶ B) (φ : A ⟶ K)
    (h : ∀ U (a : Sec A U), Sec.map g a = 0 → Sec.map φ a = 0) : ∃ ψ : B ⟶ K, g ≫ ψ = φ := by
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel g)
  have hf : S.f ≫ φ = 0 := by
    refine (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R (S.f ≫ φ)).2.2.2 0 fun U a => ?_
    have h0 : Sec.map g (Sec.map (kernel.ι g) a) = 0 := by
      rw [← sec_map_comp, kernel.condition]; rfl
    change Sec.map φ (Sec.map (kernel.ι g) a) = Sec.map (0 : kernel g ⟶ K) a
    rw [h U _ h0]; rfl
  exact ⟨hS.descToInjective φ hf, hS.comp_descToInjective φ hf⟩

theorem kernel_local (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (h : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := GlobalTheory.T.kummerRelation_boundary_kernel_generator_sum_zero q V c h

theorem exists_isKum (q : ℕ) [NeZero q] : ∃ t, IsKum q t := by
  have hinj : Injective ((res (ZMod q) (tw q 1)).X 0) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q 1)).2.1 0
  have hu := free_hom_sections (ZMod q) unitsP ((free (ZMod q)).obj unitsP)
  obtain ⟨G, hG⟩ := (free_hom_sections (ZMod q) (tripP q) ((free (ZMod q)).obj unitsP)).1
    (fun U x => freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP U (unitsP.mk (tripP.get x).src))
    (fun V U g x => by
      rw [res_sub, hu.2.2.1, hu.2.2.1]
      rfl)
  obtain ⟨Φ, hΦ⟩ := (free_hom_sections (ZMod q) (tripP q) ((res (ZMod q) (tw q 1)).X 0)).1
    (fun U x => resGen 1 (tripP.get x).root)
    (fun V U g x => by
      unfold resGen
      rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
      rfl)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective G Φ (fun U a ha => by
    apply sec_eq_zero_of_loc
    refine loc_calculus.2.1 U _ _ ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) (tripP q) U).1 a) ?_
    rintro V g ⟨c, hc⟩
    have hc' := congrArg (Sec.map G) hc
    rw [← sec_res_map, ha, res_zero', smap_sum] at hc'
    rw [sec_res_map, hc, smap_sum]
    simp only [hG] at hc'
    simp only [hΦ]
    exact kernel_local q V c hc'.symm)
  refine ⟨fun U v => Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)), ?_, ?_⟩
  · intro V U g v _
    rw [sec_res_map, hu.2.2.1]
    rfl
  · intro U ζ v w hw
    have e := congrArg (Sec.map ψ) (hG U (tripP.mk ⟨ζ, v, w, hw⟩))
    rw [← sec_map_comp, hψ, hΦ, smap_sub] at e
    change resGen 1 ζ = Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) -
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) at e
    show Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk w)) =
      Sec.map ψ (freeGen (ZMod q) unitsP U (unitsP.mk v)) + resGen 1 ζ
    rw [e]
    exact (add_sub_cancel _ _).symm

theorem isKum_kumT : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := fun q _ => pick_spec (exists_isKum q)

end GlobalTheory.EtC.KummerSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRadStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  first | exact @GlobalTheory.RatCrit.isRat_of_adelic | exact GlobalTheory.RatCrit.isRat_of_adelic | (intros; apply GlobalTheory.RatCrit.isRat_of_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterDEqOfEventuallyEq
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem iterD_eventuallyEq (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ) (h : f =ᶠ[nhds z] g) :
    iterD u f =ᶠ[nhds z] iterD u g := by
  induction u with
  | nil => exact h
  | cons i u ih =>
    have h2 := ih.eventuallyEq_nhds
    filter_upwards [h2] with w hw
    exact Filter.EventuallyEq.lineDeriv_eq hw

theorem iterD_eq_of_eventuallyEq : ∀ (I : Type) [Fintype I] [DecidableEq I] (u : List I)
    (f g : (I → ℂ) → ℂ) (z : I → ℂ), f =ᶠ[nhds z] g → iterD u f z = iterD u g z :=
  fun I _ _ u f g z h => (iterD_eventuallyEq I u f g z h).eq_of_nhds

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivZeroEqLaguerreDerivativePolynomialV
section
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.HilbFam.LagDeriv

set_option autoImplicit false in
open Filter Topology in
private lemma hasDerivAt_inv_pow_mul_exp_div_one_add_mul (c y : ℂ) (j : ℕ) {z : ℂ} (hz : 1 + z * c ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j * Complex.exp (y * w / (1 + w * c)))
      (-(j * c) * ((1 + z * c)⁻¹ ^ (j + 1) * Complex.exp (y * z / (1 + z * c))) +
        y * ((1 + z * c)⁻¹ ^ (j + 2) * Complex.exp (y * z / (1 + z * c)))) z := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 + w * c) c z := by
    simpa using ((hasDerivAt_id z).mul_const c).const_add 1
  have hinv : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹) (-c / (1 + z * c) ^ 2) z := hu.inv hz
  have hpow : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j)
      (j * (1 + z * c)⁻¹ ^ (j - 1) * (-c / (1 + z * c) ^ 2)) z := hinv.pow j
  have hq : HasDerivAt (fun w : ℂ ↦ y * w / (1 + w * c)) (y / (1 + z * c) ^ 2) z := by
    refine (((hasDerivAt_id z).const_mul y).div hu hz).congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  refine (hpow.mul hq.cexp).congr_deriv ?_
  rcases j with _ | j
  · simp [div_eq_mul_inv]
    ring
  · simp only [Nat.cast_succ, Nat.add_sub_cancel, inv_pow]
    field_simp
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_eq_zero_of_lt (k n m : ℕ) (hm : n < m) :
    _root_.GlobalTheory.HilbFam.rco k n m = 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp [Nat.choose_eq_zero_of_lt hm]

set_option autoImplicit false in
open Filter Topology in
private lemma ascFactorial_succ_eq_mul_succ_ascFactorial (a e : ℕ) :
    a.ascFactorial (e + 1) = a * (a + 1).ascFactorial e := by
  induction e with
  | zero => simp [Nat.ascFactorial_succ]
  | succ e ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_succ (k n m : ℕ) (hm : m ≤ n) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℤ) =
      -((k + n + m + 1 : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n (m + 1) +
        _root_.GlobalTheory.HilbFam.rco k n m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold _root_.GlobalTheory.HilbFam.rco
  rcases d with _ | e
  · simp
  · have h1 : m + (e + 1) + 1 - (m + 1) = e + 1 := by omega
    have h2 : m + (e + 1) - (m + 1) = e := by omega
    have h3 : m + (e + 1) - m = e + 1 := by omega
    rw [h1, h2, h3]
    have hc := Nat.choose_succ_right_eq (m + (e + 1)) m
    have hc' : m + (e + 1) - m = e + 1 := by omega
    rw [hc'] at hc
    have hs : (m + (e + 1) + 1).choose (m + 1) = (m + (e + 1)).choose m + (m + (e + 1)).choose (m + 1) :=
      Nat.choose_succ_succ' _ _
    have ha1 : (k + (m + 1)).ascFactorial (e + 1) = (k + (m + 1) + e) * (k + (m + 1)).ascFactorial e :=
      Nat.ascFactorial_succ
    have ha2 := ascFactorial_succ_eq_mul_succ_ascFactorial (k + m) e
    rw [hs, ha1, ha2]
    have hkm : k + m + 1 = k + (m + 1) := by omega
    rw [hkm]
    push_cast
    have hcz : ((m + (e + 1)).choose (m + 1) : ℤ) * (m + 1) = ((m + (e + 1)).choose m : ℤ) * (e + 1) := by
      exact_mod_cast hc
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ e * ((k + (m + 1)).ascFactorial e : ℤ)) * hcz

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_succ (k n m : ℕ) (hm : m ≤ n) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℂ) * c ^ (n + 1 - (m + 1)) * y ^ (m + 1) =
      -(((k + n + (m + 1) : ℕ) : ℂ) * c) *
          ((_root_.GlobalTheory.HilbFam.rco k n (m + 1) : ℂ) * c ^ (n - (m + 1)) * y ^ (m + 1)) +
        y * ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_succ k n m hm)
  push_cast at hZ
  rw [hZ]
  rcases hm.lt_or_eq with hlt | rfl
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e1 : m + t + 1 + 1 - (m + 1) = t + 1 := by omega
    have e2 : m + t + 1 - (m + 1) = t := by omega
    have e3 : m + t + 1 - m = t + 1 := by omega
    rw [e1, e2, e3]
    push_cast
    ring
  · rw [rco_eq_zero_of_lt k m (m + 1) (Nat.lt_succ_self m)]
    simp only [Nat.sub_self, pow_zero]
    push_cast
    ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_zero (k n : ℕ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℤ) =
      -((k + n : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero, Nat.ascFactorial_succ]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_zero (k n : ℕ) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℂ) * c ^ (n + 1 - 0) * y ^ 0 =
      -(((k + n + 0 : ℕ) : ℂ) * c) *
        ((_root_.GlobalTheory.HilbFam.rco k n 0 : ℂ) * c ^ (n - 0) * y ^ 0) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_zero k n)
  push_cast at hZ
  rw [hZ]
  simp only [Nat.sub_zero, pow_zero, add_zero]
  push_cast
  ring

set_option autoImplicit false in
open Filter Topology in
private lemma iteratedDeriv_inv_pow_mul_exp_eq_sum_rco (c y : ℂ) (n : ℕ) :
    ∀ k : ℕ, ∀ z : ℂ, 1 + z * c ≠ 0 →
      iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) z =
        ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + z * c)⁻¹ ^ (k + n + m) * Complex.exp (y * z / (1 + z * c))) := by
  induction n with
  | zero =>
    intro k z _
    simp [_root_.GlobalTheory.HilbFam.rco]
  | succ n ih =>
    intro k z hz
    have hopen : IsOpen {w : ℂ | 1 + w * c ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hev : iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) =ᶠ[𝓝 z]
        fun w ↦ ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + w * c)⁻¹ ^ (k + n + m) * Complex.exp (y * w / (1 + w * c))) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw ↦ ih k w hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun m _ ↦
      (hasDerivAt_inv_pow_mul_exp_div_one_add_mul c y (k + n + m) hz).const_mul
        ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m))
    rw [hd.deriv]
    set H : ℕ → ℂ := fun j ↦ (1 + z * c)⁻¹ ^ j * Complex.exp (y * z / (1 + z * c)) with hH
    set C : ℕ → ℕ → ℂ := fun n m ↦
      (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m with hC
    change ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1) +
        y * H (k + n + m + 2)) = ∑ m ∈ Finset.range (n + 1 + 1), C (n + 1) m * H (k + (n + 1) + m)
    have hA : ∑ m ∈ Finset.range (n + 1 + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [Finset.sum_range_succ]
      simp [hC, rco_eq_zero_of_lt k n (n + 1) (Nat.lt_succ_self n)]
    have hT : ∀ m ∈ Finset.range (n + 1), C (n + 1) (m + 1) * H (k + (n + 1) + (m + 1)) =
        -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) * H (k + n + (m + 1) + 1) +
          C n m * (y * H (k + n + m + 2)) := by
      intro m hm
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_succ k n m hmn c y]
      have e1 : k + (n + 1) + (m + 1) = k + n + (m + 1) + 1 := by omega
      have e2 : k + n + m + 2 = k + n + (m + 1) + 1 := by omega
      rw [e1, e2]
      ring
    have h0 : C (n + 1) 0 * H (k + (n + 1) + 0) = -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) := by
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_zero k n c y]
      have e1 : k + (n + 1) + 0 = k + n + 0 + 1 := by omega
      rw [e1]
    have hS : ∑ m ∈ Finset.range (n + 1), -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) *
          H (k + n + (m + 1) + 1) + -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [← Finset.sum_range_succ' (fun m ↦ -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1))]
      exact hA
    have hB : ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1)) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) :=
      Finset.sum_congr rfl fun m _ ↦ by ring
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_congr rfl hT, Finset.sum_add_distrib, h0]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hB, ← hS]
    ring

set_option autoImplicit false in
open Filter Topology in

theorem _root_.GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag : ∀ (k n : ℕ) (c y : ℂ),
    iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 =
      _root_.GlobalTheory.HilbFam.lag k n c y := by
  intro k n c y
  rw [iteratedDeriv_inv_pow_mul_exp_eq_sum_rco c y n k 0 (by simp)]
  unfold _root_.GlobalTheory.HilbFam.lag
  simp

end GlobalTheory.HilbFam.LagDeriv
end
end

