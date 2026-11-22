import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalCompactCoverByUnits
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.CoverS

section Split

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU NumberField IsDedekindDomain
open scoped TensorProduct NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {M : ℕ}

def comp (τ : E →ₐ[F] Fv F v) (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : Fin 1 → Fin M → Fv F v :=
  fun p k => splitProj τ (X p k)

theorem continuous_comp (τ : E →ₐ[F] Fv F v) : Continuous (comp (M := M) τ) :=
  continuous_pi fun p => continuous_pi fun k =>
    (continuous_splitProj τ).comp ((continuous_apply k).comp (continuous_apply p))

def glue (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    Fin 1 → Fin M → Fv F v ⊗[F] E :=
  fun p k => (splitAlgEquiv h τ).symm (Y p k, Z p k)

theorem continuous_glue (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous fun W : (Fin 1 → Fin M → Fv F v) × (Fin 1 → Fin M → Fv F v) => glue h τ W.1 W.2 :=
  continuous_pi fun p => continuous_pi fun k => (continuous_splitAlgEquiv_symm h τ).comp (by fun_prop)

theorem comp_glue_left (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    comp τ (glue h τ Y Z) = Y := by
  funext p k
  simp [comp, glue]

theorem comp_glue_right (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    comp (τ.comp σ) (glue h τ Y Z) = Z := by
  funext p k
  simp [comp, glue]

theorem glue_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Fin 1 → Fin M → Fv F v ⊗[F] E) :
    glue h τ (comp τ X) (comp (τ.comp σ) X) = X := by
  funext p k
  exact split_ext h τ (by simp [comp, glue]) (by simp [comp, glue])

def unitVecs (σ : E →ₐ[F] E) (τ : E →ₐ[F] Fv F v) : Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {X | ‖comp τ X‖ = 1 ∧ ‖comp (τ.comp σ) X‖ = 1}

theorem isOpen_unitVecs (τ : E →ₐ[F] Fv F v) : IsOpen (unitVecs (M := M) σ τ) := by
  have hS : IsOpen {Y : Fin 1 → Fin M → Fv F v | ‖Y‖ = 1} := by
    have := IsUltrametricDist.isOpen_sphere (0 : Fin 1 → Fin M → Fv F v) (r := 1) one_ne_zero
    have e : {Y : Fin 1 → Fin M → Fv F v | ‖Y‖ = 1} = Metric.sphere 0 1 := Set.ext fun Y => by simp
    rw [e]
    exact this
  exact (hS.preimage (continuous_comp τ)).inter (hS.preimage (continuous_comp (τ.comp σ)))

theorem isCompact_unitVecs (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : IsCompact (unitVecs (M := M) σ τ) := by
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have hS : IsCompact (Metric.sphere (0 : Fin 1 → Fin M → Fv F v) 1) := isCompact_sphere _ _
  have := (hS.prod hS).image (continuous_glue h τ)
  convert this using 1
  ext X
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(comp τ X, comp (τ.comp σ) X), ⟨by simpa using h1, by simpa using h2⟩, glue_comp h τ X⟩
  · rintro ⟨⟨Y, Z⟩, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [comp_glue_left]; simpa using h1
    · rw [comp_glue_right]; simpa using h2

theorem comp_ne_zero_of_free (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    {X : Fin 1 → Fin M → Fv F v ⊗[F] E} (hX : LinearIndependent (Fv F v ⊗[F] E) X) : comp τ X ≠ 0 := by
  intro h0
  have h1 := Fintype.linearIndependent_iff.1 hX (fun _ => splitIdem h τ) (by
    funext k
    have e : splitProj τ (X 0 k) = 0 := congrFun (congrFun h0 0) k
    simpa using (splitProj_eq_zero_iff h τ _).1 e) 0
  simpa using congrArg (splitProj τ) h1

theorem proj_eq_zero_of_smul (ρ : E →ₐ[F] Fv F v) {X : Fin 1 → Fin M → Fv F v ⊗[F] E}
    {c : Fv F v ⊗[F] E} (hc : ∀ k, c * X 0 k = 0) (hρ : comp ρ X ≠ 0) : splitProj ρ c = 0 := by
  by_contra hne
  refine hρ ?_
  funext p k
  obtain rfl : p = 0 := Subsingleton.elim _ _
  have := congrArg (splitProj ρ) (hc k)
  rw [map_mul, map_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hne

theorem free_of_comp_ne_zero (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    {X : Fin 1 → Fin M → Fv F v ⊗[F] E} (h1 : comp τ X ≠ 0) (h2 : comp (τ.comp σ) X ≠ 0) :
    LinearIndependent (Fv F v ⊗[F] E) X := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hc : ∀ k, g 0 * X 0 k = 0 := fun k => by simpa using congrFun hg k
  exact split_ext h τ (by simpa using proj_eq_zero_of_smul τ hc h1)
    (by simpa using proj_eq_zero_of_smul (τ.comp σ) hc h2)

theorem unitVecs_subset_free (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    unitVecs (M := M) σ τ ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
  rintro X ⟨h1, h2⟩
  refine free_of_comp_ne_zero h τ (fun e => ?_) (fun e => ?_)
  · rw [e, norm_zero] at h1; exact zero_ne_one h1
  · rw [e, norm_zero] at h2; exact zero_ne_one h2

theorem exists_entry_norm (hM : 0 < M) (Y : Fin 1 → Fin M → Fv F v) : ∃ p k, ‖Y p k‖ = ‖Y‖ := by
  haveI : Nonempty (Fin M) := Fin.pos_iff_nonempty.1 hM
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun b => ‖Y b‖₊)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun b => ‖Y p b‖₊)
  refine ⟨p, k, ?_⟩
  have e1 : ‖Y‖₊ = ‖Y p‖₊ := by rw [Pi.nnnorm_def]; exact hp
  have e2 : ‖Y p‖₊ = ‖Y p k‖₊ := by rw [Pi.nnnorm_def]; exact hk
  exact congrArg NNReal.toReal (e1.trans e2).symm

theorem exists_scale {ϖ : Fv F v} (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (hM : 0 < M)
    {Y : Fin 1 → Fin M → Fv F v} (hY : Y ≠ 0) :
    ∃ (j : ℤ) (Y' : Fin 1 → Fin M → Fv F v), ‖Y'‖ = 1 ∧ ‖Y‖ = ‖ϖ‖ ^ j ∧ ∀ p k, Y p k = ϖ ^ j * Y' p k := by
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, norm_zero] at hϖ
    exact inv_ne_zero hq0 hϖ.symm
  obtain ⟨p, k, hpk⟩ := exists_entry_norm hM Y
  have ha : Y p k ≠ 0 := fun e => hY (norm_eq_zero.1 (by rw [← hpk, e, norm_zero]))
  obtain ⟨m, hm⟩ := GlobalTheory.NormFvFacts.norm_eq_zpow F v (Y p k) ha
  refine ⟨-m, ϖ ^ m • Y, ?_, ?_, fun p k => ?_⟩
  · rw [norm_smul, norm_zpow, hϖ, ← hpk, hm, inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
  · rw [← hpk, hm, hϖ, zpow_neg, inv_zpow, inv_inv]
  · simp only [Pi.smul_apply, smul_eq_mul, zpow_neg]
    rw [inv_mul_cancel_left₀ (zpow_ne_zero _ hϖ0)]

def mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) : (Fv F v ⊗[F] E)ˣ where
  val := (splitAlgEquiv h τ).symm ((a : Fv F v), (b : Fv F v))
  inv := (splitAlgEquiv h τ).symm (((a⁻¹ : (Fv F v)ˣ) : Fv F v), ((b⁻¹ : (Fv F v)ˣ) : Fv F v))
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv, Prod.mk_one_one, map_one]
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, Units.inv_mul, Prod.mk_one_one, map_one]

theorem splitProj_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    splitProj τ (mkU h τ a b : Fv F v ⊗[F] E) = a := splitProj_symm h τ _

theorem splitProj_comp_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    splitProj (τ.comp σ) (mkU h τ a b : Fv F v ⊗[F] E) = b := splitProj_comp_symm h τ _

theorem nnnorm_norm_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    ‖Algebra.norm (Fv F v) (mkU h τ a b : Fv F v ⊗[F] E)‖₊ = ‖(a : Fv F v)‖₊ * ‖(b : Fv F v)‖₊ := by
  rw [GlobalTheory.SplitInterDet.norm_eq_split h τ, splitProj_mkU, splitProj_comp_mkU, nnnorm_mul]

theorem summable_pow {t : ℝ≥0} (ht0 : t ≠ 0) (ht : t < 1) (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    Summable fun i : ℕ × ℕ => (t ^ ((i.1 : ℤ) - k) * t ^ ((i.2 : ℤ) - k)) ^ n := by
  rw [← NNReal.summable_coe]
  have h0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
  have h1 : (t : ℝ) < 1 := by exact_mod_cast ht
  have hp : 0 ≤ (t : ℝ) := t.2
  have g : Summable fun a : ℕ => ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a :=
    (summable_geometric_of_lt_one (by positivity) (pow_lt_one₀ hp h1 hn)).mul_left _
  have hg : 0 ≤ fun a : ℕ => ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a := fun a => by
    show 0 ≤ ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a
    positivity
  refine (Summable.mul_of_nonneg g g hg hg).congr fun i => ?_
  have e : ∀ a : ℕ, (t : ℝ) ^ ((a : ℤ) - k) = (t : ℝ) ^ a * (t : ℝ) ^ (-(k : ℤ)) := fun a => by
    rw [sub_eq_add_neg, zpow_add₀ h0, zpow_natCast]
  simp only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_zpow]
  rw [e, e]
  ring

theorem neg_lt_of_norm_lt {ϖ : Fv F v} (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) {x : ℝ} {j : ℤ} {k : ℕ}
    (e : x = ‖ϖ‖ ^ j) (hx : x < (Ideal.absNorm v.asIdeal : ℝ) ^ k) : -(k : ℤ) < j := by
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  rw [e, hϖ, inv_zpow', ← zpow_natCast] at hx
  have := (zpow_lt_zpow_iff_right₀ hq).1 hx
  omega

theorem cover (h : IsCMExt F E σ) (hM : 2 ≤ M) (τ : E →ₐ[F] Fv F v)
    {A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)} (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} ∧
      Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
      A ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
          (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.NormFvFacts.exists_norm_eq_inv F v
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, norm_zero] at hϖ
    exact inv_ne_zero hq0 hϖ.symm
  have hlt : ‖ϖ‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, hϖ, NNReal.coe_one]
    exact inv_lt_one_of_one_lt₀ hq
  obtain ⟨C1, hC1⟩ := hA.exists_bound_of_continuousOn (continuous_comp (M := M) τ).continuousOn
  obtain ⟨C2, hC2⟩ := hA.exists_bound_of_continuousOn (continuous_comp (M := M) (τ.comp σ)).continuousOn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max C1 C2) hq
  let w : (Fv F v)ˣ := Units.mk0 ϖ hϖ0
  refine ⟨ℕ × ℕ, inferInstance, unitVecs σ τ, fun i => mkU h τ (w ^ ((i.1 : ℤ) - k)) (w ^ ((i.2 : ℤ) - k)),
    isCompact_unitVecs h τ, isOpen_unitVecs τ, unitVecs_subset_free h τ, ?_, ?_⟩
  · refine (summable_pow (nnnorm_ne_zero_iff.2 hϖ0) hlt k (n := M - 1) (by omega)).congr fun i => ?_
    rw [nnnorm_norm_mkU]
    simp [w, Units.val_zpow_eq_zpow_val, nnnorm_zpow]
  · rintro X ⟨hXA, hXf⟩
    obtain ⟨j1, Y1, n1, e1, f1⟩ := exists_scale hϖ (by omega) (comp_ne_zero_of_free h τ hXf)
    obtain ⟨j2, Y2, n2, e2, f2⟩ := exists_scale hϖ (by omega) (comp_ne_zero_of_free h (τ.comp σ) hXf)
    have b1 := neg_lt_of_norm_lt hϖ e1 ((hC1 X hXA).trans_lt ((le_max_left _ _).trans_lt hk))
    have b2 := neg_lt_of_norm_lt hϖ e2 ((hC2 X hXA).trans_lt ((le_max_right _ _).trans_lt hk))
    have c1 : (((j1 + k).toNat : ℤ) - k) = j1 := by omega
    have c2 : (((j2 + k).toNat : ℤ) - k) = j2 := by omega
    refine Set.mem_iUnion.2 ⟨((j1 + k).toNat, (j2 + k).toNat), glue h τ Y1 Y2, ⟨?_, ?_⟩, ?_⟩
    · rw [comp_glue_left]; exact n1
    · rw [comp_glue_right]; exact n2
    · funext p m
      refine split_ext h τ ?_ ?_
      · have := congrFun (congrFun (comp_glue_left h τ Y1 Y2) p) m
        simp only [map_mul, splitProj_mkU, c1]
        refine Eq.trans ?_ (f1 p m).symm
        rw [← this]
        simp [w, comp, Units.val_zpow_eq_zpow_val]
      · have := congrFun (congrFun (comp_glue_right (σ := σ) h τ Y1 Y2) p) m
        simp only [map_mul, splitProj_comp_mkU, c2]
        refine Eq.trans ?_ (f2 p m).symm
        rw [← this]
        simp [w, comp, Units.val_zpow_eq_zpow_val]

end Split

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem exists_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v), ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ hE M hM v τ A hA
  exact cover hE hM τ hA

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.Free.CoverS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdQuot

section Theta

variable {k : Type} [Field k] {N : ℕ}

theorem thetaW_apply (g : GL (Fin N) k) (i j : Fin N) :
    (thetaW k N g).val i j = (g⁻¹).val (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply]

theorem thetaW_mem_unipB {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) : thetaW k N u ∈ unipB k (Fin N) := by
  have hi := (mem_unipB k).1 (inv_mem hu)
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thetaW_apply]
    exact hi.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [thetaW_apply]
    exact hi.2 _

theorem whitChar_thetaW (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ N ⟨thetaW k N u, thetaW_mem_unipB u.2⟩ = whitChar ψ N u⁻¹ := by
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  refine congrArg (fun s => Circle.toUnits (ψ s)) ?_
  refine Finset.sum_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [thetaW_apply]
    rfl

theorem whitChar_inv (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ⁻¹ N u = whitChar ψ N u⁻¹ := by
  rw [map_inv]
  show Circle.toUnits (ψ⁻¹ _) = (Circle.toUnits (ψ _))⁻¹
  rw [AddChar.inv_apply', map_inv]

end Theta

section Main

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k}

variable (k)

end Main

end GlobalTheory.CompanionTheory.StdQuot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralAbsoluteBound
section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
open scoped FourierTransform

noncomputable section
namespace GlobalTheory.CompanionTheory.TateFunctionalEquationComplex

theorem integrable_chR (F : ℝ → ℂ) (e : Bool) (s : ℂ) (hm : AEStronglyMeasurable F volume)
    (h : Integrable (fun x : ℝ => F x * ((|x| ^ (s.re - 1) : ℝ) : ℂ))) :
    Integrable (fun a : ℝˣ => F a * chR e s a) mulR := by
  let g : ℝ → ℂ := fun x => F x * ((if e = true ∧ x < 0 then -1 else 1) * (((|x| : ℝ) : ℂ) ^ s))
  have hs1 : Measurable fun x : ℝ => (if e = true ∧ x < 0 then (-1 : ℂ) else 1) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    show MeasurableSet {x : ℝ | e = true ∧ x < 0}
    by_cases he : e = true
    · have hI : {x : ℝ | e = true ∧ x < 0} = Set.Iio 0 := by
        ext x
        simp [he]
      rw [hI]
      exact measurableSet_Iio
    · have hI : {x : ℝ | e = true ∧ x < 0} = ∅ := by
        ext x
        simp [he]
      rw [hI]
      exact MeasurableSet.empty
  have hs2 : Measurable fun x : ℝ => (((|x| : ℝ) : ℂ) ^ s) :=
    (Complex.measurable_ofReal.comp measurable_abs).pow_const s
  have hm' : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ • g x) volume :=
    (measurable_abs.inv).aestronglyMeasurable.smul
      (hm.mul (hs1.mul hs2).aestronglyMeasurable)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    refine h.mono hm' ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hpos : 0 < |x| := abs_pos.2 hx0
    have hsg : ‖(if e = true ∧ x < 0 then (-1 : ℂ) else 1)‖ = 1 := by split_ifs <;> simp
    have hp : 0 ≤ |x| ^ (s.re - 1) := Real.rpow_nonneg hpos.le _
    have h1 : ‖|x|⁻¹ • g x‖ = ‖F x‖ * |x| ^ (s.re - 1) := by
      simp only [g]
      rw [norm_smul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hsg,
        Real.rpow_sub_one hpos.ne', Real.norm_eq_abs, abs_inv, abs_abs]
      field_simp
    have h2 : ‖F x * ((|x| ^ (s.re - 1) : ℝ) : ℂ)‖ = ‖F x‖ * |x| ^ (s.re - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    rw [h1, h2]
  exact (RealTateConv.integrable_mulR_iff g).2 key

theorem fourier_scaled_swap (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    ∫ x : ℝ, g x * 𝓕 f (t * x) = ∫ x : ℝ, f x * 𝓕 g (t * x) := by
  have hL : Continuous fun p : ℝ × ℝ => (t • LinearMap.mul ℝ ℝ) p.1 p.2 := by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    fun_prop
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := t • LinearMap.mul ℝ ℝ)
    (f := f) (g := g) Real.continuous_fourierChar hL hf hg
  have hF : ∀ (h : ℝ → ℂ) (y : ℝ), 𝓕 h (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ) h y := by
    intro h y
    rw [Real.fourier_real_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  have hF' : ∀ (h : ℝ → ℂ) (y : ℝ), 𝓕 h (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ).flip h y := by
    intro h y
    rw [Real.fourier_real_eq, VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  simp only [hF f, hF' g]
  simp only [smul_eq_mul] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem tate_zeta_symmetric (f : ℝ → ℂ) (g : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hf : Integrable f) (hw : Integrable (fun w => f w * ((|w| ^ (s.re - 1) : ℝ) : ℂ)))
    (hF : Integrable (fun r => 𝓕 f r * ((|r| ^ (-s.re) : ℝ) : ℂ))) :
    z1 (𝓕 f) e (1 - s) * z1 g e s
      = z1 (SchwartzMap.fourierTransformCLM ℂ g) e (1 - s) * z1 f e s := by
  have h1' : 0 < (1 - s).re := by simpa using h1
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  have hre : (1 - s).re - 1 = -s.re := by simp
  have A : Integrable (fun a : ℝˣ => 𝓕 f a * chR e (1 - s) a) mulR :=
    integrable_chR _ e _ hcont.aestronglyMeasurable (by rw [hre]; exact hF)
  have B : Integrable (fun a : ℝˣ => f a * chR e s a) mulR :=
    integrable_chR _ e _ hf.aestronglyMeasurable hw
  have hc : ((SchwartzMap.fourierTransformCLM ℂ g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (g : ℝ → ℂ) := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  rw [TateR.tate_zeta_product _ _ e s A (RealTateConv.tateInt g e s h0),
    TateR.tate_zeta_product _ _ e s (RealTateConv.tateInt _ e _ h1') B, hc]
  simp only [fourier_scaled_swap f g hf g.integrable]

theorem main : TateFunctionalEquationComplex := by
  intro f e s h0 h1 hf hw hF
  have h1' : 0 < (1 - s).re := by simpa using h1
  cases e
  · obtain ⟨g, hg⟩ := TateR.gaussEven
    have key := tate_zeta_symmetric f g false s h0 h1 hf hw hF
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne := Gammaℝ_ne_zero_of_re_pos h0
    simp only [gT, Bool.false_eq_true, if_false, add_zero, one_mul]
    field_simp
    linear_combination key
  · obtain ⟨g, hg⟩ := TateR.gaussOdd
    have key := tate_zeta_symmetric f g true s h0 h1 hf hw hF
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    simp only [gT, if_true]
    field_simp
    linear_combination key

end GlobalTheory.CompanionTheory.TateFunctionalEquationComplex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
section
namespace GlobalTheory.CompanionTheory.Exhaustion

open Filter Topology

variable {α E : Type*} [NormedAddCommGroup E]

theorem exists_subset_of_exhaustion {C : ℕ → Finset α} (hC : Monotone C) (hex : ∀ a, ∃ k, a ∈ C k)
    (s : Finset α) : ∃ k, s ⊆ C k :=
  ((tendsto_atTop_finset_of_monotone hC hex).eventually (eventually_ge_atTop s)).exists

theorem summable_norm_of_exhaustion {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable fun a => ‖f a‖ := by
  refine summable_of_sum_le (c := K) (fun a => norm_nonneg _) fun s => ?_
  obtain ⟨k, hk⟩ := exists_subset_of_exhaustion hC hex s
  exact (Finset.sum_le_sum_of_subset_of_nonneg hk fun _ _ _ => norm_nonneg _).trans (hK k)

theorem tsum_exhaust [CompleteSpace E] {f : α → E} {C : ℕ → Finset α} (hC : Monotone C)
    (hex : ∀ a, ∃ k, a ∈ C k) {K : ℝ} (hK : ∀ k, ∑ a ∈ C k, ‖f a‖ ≤ K) :
    Summable f ∧ Tendsto (fun k => ∑ a ∈ C k, f a) atTop (𝓝 (∑' a, f a)) := by
  have hs : Summable f := (summable_norm_of_exhaustion hC hex hK).of_norm
  exact ⟨hs, hs.hasSum.comp (tendsto_atTop_finset_of_monotone hC hex)⟩

theorem tsum_exhaust_prop : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  intro α f C hC hex ⟨K, hK⟩
  exact ⟨summable_norm_of_exhaustion hC hex hK, (tsum_exhaust hC hex hK).2⟩

end GlobalTheory.CompanionTheory.Exhaustion
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_finite_integral : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.finInt | exact GlobalTheory.CompanionTheory.Gunr.finInt | (intros; apply GlobalTheory.CompanionTheory.Gunr.finInt <;> assumption)
end

