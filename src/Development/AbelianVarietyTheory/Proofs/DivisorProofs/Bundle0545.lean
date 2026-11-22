import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvari
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem pullHQ_galoisCover_inv : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  obtain ⟨tr, h1, h2⟩ := GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic l f G a ha hiso n i
  set F := pullHQ l (sch.map f) n i with hF
  set T := tr.baseChange ℚ_[l] with hT
  have pqc : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C),
      pullHQ l (sch.map (u ≫ v)) n i = (pullHQ l (sch.map u) n i).comp (pullHQ l (sch.map v) n i) := by
    intro A B C u v
    rw [pullHQ, pullHQ, pullHQ, ← LinearMap.baseChange_comp, ← pullHl_comp, ← Functor.map_comp]
  have pqi : ∀ A : Scheme.{0}, pullHQ l (sch.map (𝟙 A)) n i = LinearMap.id := by
    intro A
    rw [pullHQ, CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  have key1 : ∀ x, T (F x) = (Fintype.card G : ℚ_[l]) • x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h1, Nat.cast_smul_eq_nsmul]
      exact TensorProduct.tmul_smul _ _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  have key2 : ∀ y, F (T y) = ∑ g, pullHQ l (sch.map (a g)) n i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h2, TensorProduct.tmul_sum]
      simp only [pullHQ, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add]
  have comp : ∀ g, (pullHQ l (sch.map (a g)) n i).comp F = F := by
    intro g
    rw [hF, ← pqc, ha g]
  by_cases hG : Fintype.card G = 0
  ·
    haveI : IsEmpty G := Fintype.card_eq_zero_iff.mp hG
    have hS : IsEmpty ↥(∐ (fun _ : G => Y)) := by
      constructor
      intro p
      obtain ⟨j, _⟩ := (sigmaOpenCover (fun _ : G => Y)).exists_eq p
      exact isEmptyElim (show G from j)
    haveI hYe : IsEmpty Y :=
      ⟨fun y => hS.false ((pullback.lift (𝟙 Y) (𝟙 Y) rfl ≫ inv (Sigma.desc (fun g =>
        pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f)).base y)⟩
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨y, _⟩ := (inferInstance : Surjective f).surj x
      exact hYe.false y⟩
    haveI : IsIso f := isIso_of_isEmpty f
    have e1 : (pullHQ l (sch.map (inv f)) n i).comp F = LinearMap.id := by
      rw [hF, ← pqc, IsIso.inv_hom_id, pqi]
    have e2 : F.comp (pullHQ l (sch.map (inv f)) n i) = LinearMap.id := by
      rw [hF, ← pqc, IsIso.hom_inv_id, pqi]
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have := congrArg (pullHQ l (sch.map (inv f)) n i) hxy
      rwa [← LinearMap.comp_apply, e1, ← LinearMap.comp_apply, e1] at this
    · rw [iInf_of_empty, LinearMap.range_eq_top]
      intro y
      exact ⟨pullHQ l (sch.map (inv f)) n i y, by rw [← LinearMap.comp_apply, e2, LinearMap.id_apply]⟩
  have hc : (Fintype.card G : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hG
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := congrArg T hxy
    rw [key1, key1] at this
    exact smul_right_injective _ hc this
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      intro g
      rw [← LinearMap.comp_apply, comp g, sub_self]
    · intro y hy
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
      refine ⟨(Fintype.card G : ℚ_[l])⁻¹ • T y, ?_⟩
      rw [map_smul, key2]
      simp only [hy, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hc, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from (Arrow.mk f).augmentedCechNerve.hom)) := by
  first | exact @GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective | exact GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective | (intros; apply GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCover
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_isBundle : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e he hr
  have hstab : ∀ I, ∀ c ∈ rB k K x I, ∀ w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W),
      (c : K) • w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W) := by
    intro I c hc w hw
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hw ⊢
    rw [map_smul]
    exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K _ p p).2.1 _ hw).2.2.2 c hc
  have key : ∀ i, Module.Finite (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) ∧
      Module.Projective (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) := by
    intro i
    obtain ⟨hf1, hf2, hf3⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
    haveI := hf2
    haveI := hf3
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.span_regularForms_finite_projective_smooth k K (rB k K x {i}) p W e he hr
    exact GlobalTheory.T.finite_projective_span_of_integralClosure' k F K (rA k x {i}) (rB k K x {i}) (fun y => Iff.rfl) hf1 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hx i) W _
      (hstab {i}) hB1 hB2
  refine ⟨fun i => ?_, fun i => (key i).2, fun I i hi => GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization k F K d x hx p W e I i hi⟩
  obtain ⟨hfin, -⟩ := key i
  obtain ⟨-, hf2, -⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
  haveI := hf2
  haveI : FiniteDimensional F K := hx.fin
  set S : Set W := ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) with hSdef
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hA : ∀ a : rA k x {i}, ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rw [Subalgebra.smul_def, ← algebraMap_smul K (a : F) w]
    exact hstab {i} _ (Subalgebra.algebraMap_mem (integralClosure (rA k x {i}) K) a) w hw
  have hspan : (Submodule.span (rA k x {i}) S).restrictScalars k =
      (omB k K (rB k K x {i}) p).comap (e.restrictScalars k) := by
    apply le_antisymm
    · intro y hy
      change y ∈ Submodule.span (rA k x {i}) S at hy
      change y ∈ S
      induction hy using Submodule.span_induction with
      | mem z hz => exact hz
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul a z _ hz => exact hA a z hz
    · exact fun y hy => Submodule.subset_span hy
  refine ⟨s, by rw [hs, hspan], ?_⟩
  have hK := GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top k K (rB k K x {i}) p W e he hr
  have hF := GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' k F K (rB k K x {i}) W S (hstab {i}) hK
  rw [eq_top_iff, ← hF, Submodule.span_le]
  intro w hw
  have : w ∈ Submodule.span (rA k x {i}) (s : Set W) := by rw [hs]; exact Submodule.subset_span hw
  exact Submodule.span_le_restrictScalars (rA k x {i}) F (s : Set W) this

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndexStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex : GlobalTheory.SatakeWeyl.UnimodFin → GlobalTheory.SatakeWeyl.Unimod := by
  first | exact @GlobalTheory.SatakeWeyl.unimod_of_unimodFin | exact GlobalTheory.SatakeWeyl.unimod_of_unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimod_of_unimodFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalars_injective_sheaf_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I] (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  first
  | exact @GlobalTheory.EtC.restr_injective_acyclic
  | exact GlobalTheory.EtC.restr_injective_acyclic
  | (intros; apply GlobalTheory.EtC.restr_injective_acyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMinorSupportStatement
section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_minor_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  first | exact @GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | exact GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | (intros; apply GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

open scoped nonZeroDivisors

theorem GlobalTheory.UCls.selfDual_latOf_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  intro E _ _ _ r G Λ g0 hΛ hua
  obtain ⟨hG, hdet, hfg, hspan, hsd⟩ := hΛ
  obtain ⟨hunit, hpres⟩ := hua
  let g : GL (Fin r) (RA (maximalRealSubfield E) E) := Matrix.nonsingInvUnit g0 hunit
  have hg : (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) = g0 := rfl
  obtain ⟨L, hL, hLfg, hLspan, hLhat⟩ :=
    GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E r Λ g hfg hspan
  rw [hg] at hL hLhat
  have hmem : ∀ x : E, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsd' : ∀ v : Fin r → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * G a b * (IsCMField.complexConj E) (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ Λ := by
    intro v
    simp only [hmem]
    exact hsd v
  have key := GlobalTheory.AdLat.latOf_selfDual (maximalRealSubfield E) E r Λ (IsCMField.complexConj E) G 1 g
    hfg hspan (IsCMField.complexConj_apply_apply E) hG hdet one_ne_zero hsd' (by rw [hg]; exact hpres)
  rw [hg] at key
  refine ⟨L, hL, hLhat, hG, hdet, hLfg, hLspan, fun x => ?_⟩
  have := key x
  rw [← hL] at this
  simp only [hmem, SetLike.mem_coe] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolutionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwist
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.CliffTwo

def twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) : Representation ℂ H V where
  toFun x := ((ν x : ℂˣ) : ℂ) • ρ x
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistRep_apply {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) (x : H) : twistRep ρ ν x = ((ν x : ℂˣ) : ℂ) • ρ x := rfl

theorem isIrreducible_twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (h : ρ.IsIrreducible) (ν : H →* ℂˣ) :
    (twistRep ρ ν).IsIrreducible := by
  let f : Subrepresentation (twistRep ρ ν) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((ν g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [twistRep_apply, smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder_iff.2 h

theorem isIrrChar_mul_char {H : Type} [Group H] {χ : H → ℂ} (hχ : IsIrrChar ℂ ℂ χ) (ν : H →* ℂˣ) :
    IsIrrChar ℂ ℂ (fun x => χ x * ((ν x : ℂˣ) : ℂ)) := by
  obtain ⟨n, ρ, hρ, hc⟩ := hχ
  refine ⟨n, twistRep ρ ν, isIrreducible_twistRep hρ ν, fun g => ?_⟩
  simp only [hc, Representation.character, twistRep_apply, map_smul, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end GlobalTheory.CliffTwo

open GlobalTheory.CliffTwo in

theorem GlobalTheory.Shin.coset_pair_eq_zero_or_twist :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' →
    ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨
      ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  intro G Γ _ _ _ _ φ s hp hs χ χ' hχ hχ'
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, hη1, -, hsum⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  have hS := (hsum χ χ').2
  by_cases h0 : ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0
  · exact Or.inl h0
  right
  have hne : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := by
    rw [← hS]; exact mul_ne_zero (by exact_mod_cast hp.ne_zero) h0
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hT : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := right_ne_zero_of_mul ha
  have hpow : ∀ x, ((η ^ a) x : ℂ) = (η x : ℂ) ^ a := fun x => by simp
  have hψ : IsIrrChar ℂ ℂ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) := isIrrChar_mul_char hχ' (η ^ a)
  refine ⟨η ^ a, fun g => by simp [hη1], fun x => ?_⟩
  by_contra hx
  have hne' : χ ≠ fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ) := fun e => hx (congrFun e x)
  have hpair : pair χ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) = 0 := by
    first | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne (G ⋊[φ] Γ) χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne hχ hψ hne'
  have hvirt : (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    obtain ⟨n, ρ, -, hc⟩ := hψ
    exact AddSubgroup.subset_closure ⟨n, ρ, hc⟩
  have hstar : ∀ g, star ((fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g) = (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g⁻¹ := by
    first | exact GlobalTheory.CuspGL.star_virt_eq_inv (G ⋊[φ] Γ) _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv hvirt
  apply hT
  have hcard : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) =
      ∑ᶠ x, χ x * (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) x⁻¹ := by
    congr 1; ext x; have hx := hstar x; simp only [hpow] at hx ⊢; rw [← hx]
  rw [this]
  unfold pair at hpair
  exact (mul_eq_zero.1 hpair).resolve_left (inv_ne_zero hcard)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesDifferentiable
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum.Series

theorem series_differentiable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ s : ℕ, 2 ≤ s → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out) (∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out) z (Pi.single i 1) := by
  intro E _ _ _ I _ _ φ hφ s hs c y hc m z hz

  have hz1 : ‖z‖ < 1 := by
    rcases isEmpty_or_nonempty I with hI | hI
    · simp [Subsingleton.elim z 0]
    · exact (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1

  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(s : ℝ)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (s : ℝ) hc (by exact_mod_cast (by omega : 1 < s))
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s m r hr1
  have hsum : ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => dTerm φ (2 * s) m w q.1.out) := fun w hw =>
    Summable.of_norm_bounded (hNs.mul_left C0) fun q => hC0 w (hUle w hw) _ (hne q)
  choose C hC using fun j : I => GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform E I φ hφ s (m + Pi.single j 1) r hr1
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℂ] ℂ) := fun q w =>
    ∑ j, dTerm φ (2 * s) (m + Pi.single j 1) w q.1.out • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j, C j * N q * ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j‖ with hu
  have hus : Summable u := summable_sum fun j _ => ((hNs.mul_left (C j)).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => dTerm φ (2 * s) m w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_deformedProductDerivativeTerm E I φ (2 * s) m q.1.out (hne q) w (hUpd w hw)
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC j w (hUle w hw) _ (hne q)) (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), dTerm φ (2 * s) m w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum z hzU) hzU
  refine ⟨hsum z hzU, hF.differentiableAt, fun i => ?_⟩
  have hL := hF.hasLineDerivAt (Pi.single i 1)
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hev : (∑' q, f' q z) (Pi.single i 1) = ∑' q : modUnits (lattice c y), dTerm φ (2 * s) (m + Pi.single i 1) z q.1.out := by
    have hm := (ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : I → ℂ)).map_tsum hcs
    simp only [ContinuousLinearMap.apply_apply] at hm
    rw [hm]
    refine tsum_congr fun q => ?_
    simp [hf', ContinuousLinearMap.sum_apply, Pi.single_apply]
  rwa [hev] at hL

end GlobalTheory.DeformedSum.Series
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts : GlobalTheory.SatakeWeyl.EmbMem := by
  first | exact @GlobalTheory.SatakeWeyl.embMem | exact GlobalTheory.SatakeWeyl.embMem | (intros; apply GlobalTheory.SatakeWeyl.embMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebraStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spread_torsor_to_etale_algebra : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  first | (exact @GlobalTheory.LocAcyc.spread_torsor_to_etale) | (exact GlobalTheory.LocAcyc.spread_torsor_to_etale) | (intros; apply GlobalTheory.LocAcyc.spread_torsor_to_etale  <;> assumption)
end

