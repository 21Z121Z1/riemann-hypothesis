import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSm_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') : IsSm σ J (f + f') :=
  fun k γ hγ g => (h k γ hγ g).add (h' k γ hγ g)

theorem isSm_smul (a : ℂ) {f : GAd σ J → ℂ} (h : IsSm σ J f) : IsSm σ J (a • f) :=
  fun k γ hγ g => (h k γ hγ g).const_smul a

theorem differentiable_of_isSm {f : GAd σ J → ℂ} (h : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (g : GAd σ J) : Differentiable ℝ fun t : ℝ => f (g * γ t) := by
  have h1 := h 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem lineDer_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : lineDer γ (f + f') = lineDer γ f + lineDer γ f' := by
  funext g
  exact deriv_fun_add (differentiable_of_isSm h hγ g 0) (differentiable_of_isSm h' hγ g 0)

omit [NumberField E] in
theorem lineDer_smul (a : ℂ) (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) : lineDer γ (a • f) = a • lineDer γ f := by
  funext g
  simp only [lineDer, Pi.smul_apply, smul_eq_mul, deriv_const_mul_field']

theorem isSm_lineDer {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ f) := by
  intro k γs h g
  have h1 := hf (k + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) γs γ)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hγ
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      f (g * (List.ofFn fun i => γs i (t i)).prod * γ s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem isSm_foldr {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f : GAd σ J → ℂ}
    (hf : IsSm σ J f) : IsSm σ J (l.foldr lineDer f) := by
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    exact isSm_lineDer (ih fun δ hδ => hl δ (by simp [hδ])) (hl γ (by simp))

theorem foldr_add {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f f' : GAd σ J → ℂ}
    (hf : IsSm σ J f) (hf' : IsSm σ J f') : l.foldr lineDer (f + f') = l.foldr lineDer f + l.foldr lineDer f' := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (by simp [hδ])
    simp only [List.foldr_cons]
    rw [ih hl', lineDer_add (isSm_foldr hl' hf) (isSm_foldr hl' hf') (hl γ (by simp))]

omit [NumberField E] in
theorem foldr_smul (l : List (ℝ → GAd σ J)) (a : ℂ) (f : GAd σ J → ℂ) :
    l.foldr lineDer (a • f) = a • l.foldr lineDer f := by
  induction l with
  | nil => rfl
  | cons γ l ih => simp only [List.foldr_cons, ih, lineDer_smul]

theorem dop_add {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ)
    {f f' : GAd σ J → ℂ} (hf : IsSm σ J f) (hf' : IsSm σ J f') : dop z (f + f') = dop z f + dop z f' := by
  funext g
  simp only [dop, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_add (hz l hl) hf hf', Pi.add_apply, mul_add]

omit [NumberField E] in
theorem dop_smul (z : List (ℝ → GAd σ J) →₀ ℂ) (a : ℂ) (f : GAd σ J → ℂ) : dop z (a • f) = a • dop z f := by
  funext g
  simp only [dop, Finsupp.sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, foldr_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isAutOn_add_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (H K : Subgroup (GAd σ J)) (φ ψ : GAd σ J → ℂ) (a : ℂ), IsAutOn σ J H K φ → IsAutOn σ J H K ψ →
    IsAutOn σ J H K (φ + ψ) ∧ IsAutOn σ J H K (a • φ) := by
  intro F E _ _ _ _ _ σ _ n J _ H K φ ψ a h h'
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont, isSm_add h.smooth h'.smooth, ?_, h.kfin.add h'.kfin, ?_⟩,
    ⟨fun γ hγ g => ?_, ?_, h.cont.const_smul a, isSm_smul a h.smooth, ?_, ?_, ?_⟩⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    refine ⟨max N N', fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    obtain ⟨C', hC'⟩ := hN' l hl
    refine ⟨|C| + |C'|, fun g => ?_⟩
    have h1 : (1 : ℝ) ≤ height σ J g := by exact_mod_cast one_le_height σ J g
    have h0 : (0 : ℝ) ≤ height σ J g := zero_le_one.trans h1
    rw [foldr_add hl h.smooth h'.smooth, Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hC g).trans ?_) ((hC' g).trans ?_))
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_left _ _)) (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_right _ _)) (pow_nonneg h0 _) (abs_nonneg _)
  · haveI := h.zfin
    haveI := h'.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ} ⊔
      Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z ψ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [dop_add hz.1 h.smooth h'.smooth]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨‖a‖ * C, fun g => ?_⟩
    rw [foldr_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)
  · obtain ⟨W, hW, e⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h.kfin
    exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => W.smul_mem a (e k hk)⟩
  · haveI := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [dop_smul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz, rfl⟩)

end GlobalTheory.UAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormulaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_sum_degree_formula : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (f : (k →+* ℂ) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  first | exact @GlobalTheory.finrank_mul_sum_embeddings_comp | exact GlobalTheory.finrank_mul_sum_embeddings_comp | (intros; apply GlobalTheory.finrank_mul_sum_embeddings_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeCard

theorem encard_smallSec_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  intro k _ X _ p A B hBA
  obtain ⟨P, rfl, rfl, h1⟩ := hBA
  have hrep := Pair.rep_base k X p P
  have eL : P.L.smallSec.encard = (P.Bl 1 0 1).encard :=
    SmallBall.encard_eq_Bl P hrep.1 P.L.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have eA : P.A.smallSec.encard = (P.Bl 0 1 1).encard :=
    SmallBall.encard_eq_Bl P hrep.2.1 P.A.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  rw [eL, eA]
  refine Set.encard_le_encard fun f hf => ?_
  have e := NuMul.mul_mem_H_and_nu_mul k X p P 1 (-1) 0 1 1 f h1.1 hf.1
  rw [one_mul, add_zero, neg_add_cancel] at e
  refine ⟨e.1, fun σ y => ?_⟩
  rw [e.2 σ y]
  calc P.nu 1 (-1) σ y 1 * P.nu 0 1 σ y f ≤ 1 * 1 :=
        mul_le_mul (h1.2 σ y) (hf.2 σ y) (SmallBall.nu_nonneg P 0 1 σ y f) zero_le_one
    _ = 1 := one_mul 1

end GlobalTheory.HSNef.LeCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

open Classical in

def lieRep (R : RealPoints θ V) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (SmF θ V) :=
  DirectSum.toLieAlgebra _ (fun τ => (envRep R τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change (envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)) * envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) * envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(envRep_comm R h _ _).eq, sub_self]

def envRepAll (R : RealPoints θ V) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (SmF θ V) :=
  UniversalEnvelopingAlgebra.lift ℂ (lieRep R)

open Classical in

def envIncl (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] GlobalTheory.AutFinLit.Env V :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (DirectSum.lieAlgebraOf ℂ D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ))

open Classical in
theorem envIncl_ι (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x) := by
  simp [envIncl]

theorem envRepAll_envIncl (R : RealPoints θ V) (τ : D.what₂.Tau) (u : EnvAt V τ) :
    envRepAll R (envIncl V τ u) = envRep R τ u := by
  classical
  have : (envRepAll R).comp (envIncl V τ) = envRep R τ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envRepAll R (envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x)) = envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [envIncl_ι, envRepAll, UniversalEnvelopingAlgebra.lift_ι_apply, lieRep]
    exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x
  exact congrArg (fun f : EnvAt V τ →ₐ[ℂ] _ => f u) this

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodConj

theorem eventually_mem_integers {E : Type} [Field E] [NumberField E] (a : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w n := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w →
      ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  intro E _ _ _ _ n _ γ hsep
  have hint : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) ((γ.1 : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E ∧
      algebraMap E (w.adicCompletion E) (((γ.1 : GL (Fin n) E)⁻¹).val i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (eventually_mem_integers _).and (eventually_mem_integers _)
  filter_upwards [hint, GlobalTheory.T.eventually_integral_lift_coprime_derivative E _ hsep] with w hw hP
  obtain ⟨P₀, hP₀, hcop⟩ := hP
  intro g hg
  set y : GLw n w := Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ.1 : GL (Fin n) E) with hy
  by_cases hmem : y ∈ UL n w
  · have hloc : ((locPt w γ : UL n w) : GLw n w) = y := by
      simp only [locPt, toSub]
      rw [dif_pos hmem]
    have hyK : y ∈ GlobalTheory.LFun.KGL w n := by
      apply mem_KGL_of_entries
      · intro a b; exact (hw a b).1
      · intro a b
        rw [hy, ← map_inv]
        exact (hw a b).2
    have hK : locPt w γ ∈ KL n w := by
      rw [KL, Subgroup.mem_subgroupOf, hloc]; exact hyK
    obtain ⟨h1, h2⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
    have hcp : (locPt w γ).1.val.charpoly =
        P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
      rw [hloc, hP₀, hy]
      exact Matrix.charpoly_map _ _
    obtain ⟨t, ht, k, hk, he⟩ := GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w h1 h2 P₀ hcop (locPt w γ) hcp 1 g
      (by simpa using hK) hg
    refine ⟨t, ht, ?_⟩
    rw [he, mul_one, inv_mul_cancel_left]
    exact hk
  · have hloc : locPt w γ = 1 := by
      simp only [locPt, toSub]
      rw [dif_neg hmem]
    refine ⟨g, ?_, by rw [inv_mul_cancel]; exact one_mem _⟩
    rw [hloc]
    show g * 1 = 1 * (MonoidHom.id _) g
    simp

end GlobalTheory.BCT.GoodConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  first | (exact @GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (exact GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (intros; apply GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (exact GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (intros; apply GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGLStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w), ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = p * k := by
  first | exact @GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | exact GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | (intros; apply GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharacters
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

noncomputable section

namespace GlobalTheory.RepFinExtJoint

theorem characterAsRankOneRep_entry {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) (g : Γ) :
    ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = ((χ g : Kˣ) : K) := by
  simp [GlobalTheory.TripleGal.rk1, Matrix.scalar_apply]

theorem exists_finExt_chars (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] {ι : Type} (χ : ι → G E Ω →* (PadicAlgCl l)ˣ)
    (hχ : ∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) (S : Finset ι) (L₀ : FinExt l) :
    ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ s ∈ S, ∀ g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ L.1 := by
  classical
  induction S using Finset.induction_on generalizing L₀ with
  | empty => exact ⟨L₀, le_rfl, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert i S hi ih =>
    obtain ⟨L₁, h01, h1⟩ := ih L₀
    obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1
      (GlobalTheory.TripleGal.rk1 (χ i)) (Units.continuous_val.comp (hχ i)) L₁
    refine ⟨L₂, h01.trans h12, fun s hs g => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · have := h2 g 0 0
      rwa [characterAsRankOneRep_entry] at this
    · exact h12 (h1 s hs g)

theorem exists_finExt_root_emb (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ L : FinExt l, (∃ ζ : ↥L.1, IsPrimitiveRoot ζ l) ∧ ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ L.1 := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ l := HasEnoughRootsOfUnity.prim
  let b := Module.finBasis ℚ E
  haveI : Fintype (E →+* PadicAlgCl l) := Fintype.ofFinite _
  let T : Finset (PadicAlgCl l) :=
    insert ζ (Finset.univ.image fun p : (E →+* PadicAlgCl l) × Fin (Module.finrank ℚ E) => p.1 (b p.2))
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hT : ∀ x ∈ T, x ∈ K := fun x hx => IntermediateField.subset_adjoin _ _ hx
  refine ⟨⟨K, inferInstance⟩, ⟨⟨ζ, hT _ (Finset.mem_insert_self _ _)⟩, ?_⟩, fun τ x => ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa using hζ) K.val.injective
  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact SubfieldClass.qsmul_mem K _ (hT _ (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩)))

theorem finext_joint : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  intro E Ω _ _ _ _ _ l _ n a t r ρ χ hr hρ hχ
  obtain ⟨L₀, ⟨ζ, hζ⟩, hemb⟩ := exists_finExt_root_emb E l
  obtain ⟨L₁, h01, h1⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) n r
    (Units.continuous_val.comp hr) L₀
  obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a ρ
    (Units.continuous_val.comp hρ) L₁
  obtain ⟨L₃, h23, h3⟩ := exists_finExt_chars E Ω l χ hχ Finset.univ L₂
  refine ⟨L₃, ⟨⟨ζ, h23 (h12 (h01 ζ.2))⟩, ?_⟩, fun τ x => h23 (h12 (h01 (hemb τ x))),
    fun g i j => h23 (h12 (h1 g i j)), fun g i j => h23 (h2 g i j), fun s g => h3 s (Finset.mem_univ s) g⟩
  have h0 : IsPrimitiveRoot ((ζ : ↥L₀.1) : PadicAlgCl l) l :=
    hζ.map_of_injective (f := L₀.1.val) L₀.1.val.injective
  exact IsPrimitiveRoot.of_map_of_injective (f := L₃.1.val) h0 L₃.1.val.injective

end GlobalTheory.RepFinExtJoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactBoxOfUnitaryTranslateCompact
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BoxMove

theorem inBox_image_mul : ∀ (D : D7) (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.InBox K (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) → GlobalTheory.Unf.InBox K' x := by
  intro D V n Q hQ K hK
  have hmt : Continuous (Formalism.L2.Theta.mt V) := Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n) :=
    (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨(fun p : GA D V × Mx D V.rank n => (HMul.hMul (Formalism.L2.Theta.mt V p.1) p.2 : Mx D V.rank n)) '' (Q ×ˢ K), (hQ.prod hK).image hf, ?_⟩
  rintro y hy x ⟨k, hk, h0⟩
  refine ⟨(HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n), ⟨(y, k), ⟨hy, hk⟩, rfl⟩, ?_⟩
  have hyy : Formalism.L2.Theta.mt V y * Formalism.L2.Theta.mt V y⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hx : x - (HMul.hMul (Formalism.L2.Theta.mt V y) k : Mx D V.rank n) = (HMul.hMul (Formalism.L2.Theta.mt V y) ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) - k) : Mx D V.rank n) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hyy, Matrix.one_mul]
  rw [hx, Matrix.map_mul, h0, Matrix.mul_zero]

end GlobalTheory.BoxMove
end

