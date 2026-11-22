import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.DegGrowth

open MvPolynomial

theorem expand (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Ψ ((X 0 + C t * X 1) ^ D) = ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  intro hC k _ Y _ p D hX L A
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).2
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  have hiso0 : (comb ![L, A] ![1, 0]).Isometric L := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, Fin.sum_univ_two]
  have hlin0 : (lin fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ)) = (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp [lin, Fin.sum_univ_two]
  have h0 : Ψ (X 0 ^ D) = gdeg L D := by
    rw [← hlin0, hΨ.1, hiso0.gdeg_eq]
  have hn_eq (n : ℕ) : gdeg ((L.pow n).tens A) D = Ψ ((C (n : ℝ) * X 0 + C 1 * X 1) ^ D) := by
    rw [← (hiso n).gdeg_eq, ← hΨ.1, hlin]
  set f : ℝ → ℝ := fun t => Ψ ((X 0 + C t * X 1) ^ D) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Ψ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = gdeg L D := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hn_eq, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.DegGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.TwistInvol

theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x : w.adicCompletion E) :
    cj w (cj w x) = x := by
  unfold cj
  split_ifs with h
  · obtain ⟨hc, he⟩ := h.choose_spec
    have hd : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
    refine hd.induction_on (p := fun x => h.choose (h.choose x) = x) x
      (isClosed_eq (hc.comp hc) continuous_id) fun y => ?_
    rw [he, he, IsCMField.complexConj_apply_apply]
  · rfl

theorem thL_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    thL n w (thL n w g) = g := by
  intro E _ _ _ n w g
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g

end GlobalTheory.BCT.TwistInvol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAddStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormIntegral_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  first | exact @GlobalTheory.GoodTop.hasInt_add | exact GlobalTheory.GoodTop.hasInt_add | (intros; apply GlobalTheory.GoodTop.hasInt_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  first | exact @GlobalTheory.GoodTop.hasInt_of_chart | exact GlobalTheory.GoodTop.hasInt_of_chart | (intros; apply GlobalTheory.GoodTop.hasInt_of_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1Projective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjSpaceDegree

theorem topSelf_O1_str : ∀ (k : Type) [Field k] (N : ℕ),
    letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 :=
  fun k _ N => GlobalTheory.NefNumericsModel.selfIntersection_O1 k N

end GlobalTheory.ProjSpaceDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_fieldBaseChange_le : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (f' : X' ⟶ Sp K) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k K)) → topologicalKrullDim X' ≤ topologicalKrullDim X := by
  first | exact @GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | exact GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le | (intros; apply GlobalTheory.FieldExtDim.topologicalKrullDim_baseChange_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeOfIsClosedNeUnivIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_isClosed_ne_univ_integral : ∀ (X : Scheme.{0}) [IsIntegral X] (d : ℕ), topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → topologicalKrullDim Z ≤ (d : ℕ) := by
  first | exact @GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | exact GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | (intros; apply GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
section
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapOrb

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsModelMap (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) : Prop :=
  (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧ (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧
    ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

theorem isModel_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : IsModel w e B u x γ ↔ ∃ ψ, IsModelMap w e B u x γ ψ := Iff.rfl

def pullLat (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : Submodule K.O B.A where
  carrier := {y | ∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E}
  zero_mem' := by
    intro c i
    simp
  add_mem' := by
    intro a b ha hb c i
    rw [smul_add, map_add, Matrix.mulVec_add, Pi.add_apply]
    exact add_mem (ha c i) (hb c i)
  smul_mem' := by
    intro c' a ha c i
    rw [smul_smul]
    exact ha (c * c') i

def torusOf (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) : B.Aˣ :=
  if h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y then h.choose else 1

theorem torusOf_spec (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g : GLw n w) (a : B.Aˣ)
    (ha : ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y) : torusOf w B ψ g = a := by
  have h : ∃ a : B.Aˣ, ∀ y, ψ ((a : B.A) * y) = g.val *ᵥ ψ y := ⟨a, ha⟩
  unfold torusOf
  rw [dif_pos h]
  apply Units.ext
  have h1 := h.choose_spec 1
  have h2 := ha 1
  rw [mul_one] at h1 h2
  exact ψ.injective (h1.trans h2.symm)

end GlobalTheory.KapOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnMapOfInjective
section
namespace GlobalTheory.TraceOnInjectiveMap

theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dif_pos (hpres.2 h'), dif_pos h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dif_neg (mt hpres.1 h'), dif_neg h']

end GlobalTheory.TraceOnInjectiveMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormGramAsymmetryForcesBetaRelation
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem betaSym_expand {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (f : B.A →ₗ[K.E] K.E) (a : B.A) :
    f a = ∑ k, b.repr a k * f (b k) := by
  calc f a = f (∑ k, b.repr a k • b k) := by rw [b.sum_repr]
    _ = ∑ k, b.repr a k * f (b k) := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

theorem betaSym_trace_sigma {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (y : B.A) :
    Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) y
  rw [h, RingEquiv.apply_symm_apply]

theorem betaSym : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u β : B.A), (Algebra.traceForm K.E B.A).Nondegenerate → IsUnit (GlobalTheory.TwLat.gram e b β) → (cj w).mapMatrix (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * GlobalTheory.TwLat.mulMat e b u) → B.σ β = β * ((-1) ^ (m - 1) * u) ∧ IsUnit β := by
  intro E _ _ _ w K e he B m b u β hnd hG hsym

  let f : B.A → (B.A →ₗ[K.E] K.E) := fun z =>
    (Algebra.trace K.E B.A).comp ((LinearMap.mulRight K.E (B.σ z)).comp (LinearMap.mulLeft K.E β))
  have hf : ∀ y z, f z y = Algebra.trace K.E B.A (β * y * B.σ z) := fun y z => rfl
  have hsgn : ((-1 : B.A) ^ (m - 1)) = algebraMap K.E B.A ((-1) ^ (m - 1)) := by simp
  set x : B.A := B.σ β - β * ((-1) ^ (m - 1) * u) with hx
  have h1 : ∀ i j, Algebra.trace K.E B.A (x * b j * B.σ (b i)) = 0 := by
    intro i j
    have h := congrFun (congrFun hsym i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, gram, mulMat, Matrix.of_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm] at h
    have hA : Algebra.trace K.E B.A (B.σ β * b j * B.σ (b i)) =
        K.c (Algebra.trace K.E B.A (β * b i * B.σ (b j))) := by
      rw [← betaSym_trace_sigma B]; congr 1; rw [map_mul, map_mul, B.σ_σ]; ring
    have hB : Algebra.trace K.E B.A (β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i)) =
        (-1) ^ (m - 1) * ∑ k, b.repr (u * b j) k * Algebra.trace K.E B.A (β * b k * B.σ (b i)) := by
      have : β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) = ((-1 : K.E) ^ (m - 1)) • (β * (u * b j) * B.σ (b i)) := by
        rw [Algebra.smul_def, ← hsgn]; ring
      rw [this, map_smul, smul_eq_mul, ← hf, betaSym_expand b (f (b i)) (u * b j)]
      rfl
    have hsub : x * b j * B.σ (b i) = B.σ β * b j * B.σ (b i) - β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) := by
      rw [hx]; ring
    apply e.injective
    rw [hsub, map_sub, hA, hB, map_sub e, map_zero, he, h, map_mul e, map_sum e, map_pow, map_neg, map_one]
    simp only [map_mul e]
    rw [sub_eq_zero]; congr 1; refine Finset.sum_congr rfl fun k _ => ?_; ring
  have h2 : ∀ i a, Algebra.trace K.E B.A (x * B.σ (b i) * a) = 0 := by
    intro i a
    have h := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (x * B.σ (b i)))) a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h]
    apply Finset.sum_eq_zero
    intro j _
    rw [show x * B.σ (b i) * b j = x * b j * B.σ (b i) by ring, h1, mul_zero]
  have h3 : ∀ a, Algebra.trace K.E B.A (x * a) = 0 := by
    intro a
    have hs : ∀ i, Algebra.trace K.E B.A (B.σ (x * a) * b i) = 0 := by
      intro i
      have h := h2 i a
      rw [show x * B.σ (b i) * a = B.σ (B.σ (x * a) * b i) by rw [map_mul, B.σ_σ]; ring,
        betaSym_trace_sigma] at h
      exact (map_eq_zero_iff K.c K.c.injective).mp h
    have h4 := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (B.σ (x * a)))) 1
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, hs, mul_zero, Finset.sum_const_zero,
      betaSym_trace_sigma] at h4
    exact (map_eq_zero_iff K.c K.c.injective).mp h4
  have hx0 : x = 0 := hnd.1 x (fun n => by simpa [Algebra.traceForm_apply] using h3 n)
  refine ⟨by rw [hx] at hx0; exact sub_eq_zero.mp hx0, ?_⟩
  by_contra hβ
  have hinj : ¬ Function.Injective (LinearMap.mulLeft K.E β) := by
    intro hi
    have hs := (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft K.E β)).mp hi
    obtain ⟨a, ha⟩ := hs 1
    have ha' : β * a = 1 := ha
    exact hβ ⟨⟨β, a, ha', by rw [mul_comm]; exact ha'⟩, rfl⟩
  obtain ⟨a, ha0, hβa⟩ : ∃ a, a ≠ 0 ∧ β * a = 0 := by
    rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨a, h, ha⟩ := hinj
    exact ⟨a, ha, h⟩
  let v : Fin m → w.adicCompletion E := fun i => e (b.repr a i)
  have hv : Matrix.vecMul v (gram e b β) = 0 := by
    funext j
    have h := betaSym_expand b (f (b j)) a
    simp only [hf] at h
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm, v, Pi.zero_apply]
    simp_rw [← map_mul e]
    rw [← map_sum e, ← h, hβa]
    simp
  have hvz : v = 0 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hG
    calc v = Matrix.vecMul v (gram e b β * (gram e b β)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  apply ha0
  have hr : b.repr a = 0 := by
    ext i
    have h := congrFun hvz i
    simpa [v] using h
  simpa using hr

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dif_pos hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dif_pos (hinv i)]

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChange
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_changeFrame {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n} (h₀ : MContDiffAt 2 G₀ v) (u₀ : IsUnit (G₀ v).det)
    (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) (hA : MContDiffAt 2 A v) (hAu : IsUnit (A v).det)
    (hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) :
    corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  unfold corrC
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.T.polarisedTopChernCoeff_conj (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) (A v) hAu]
  congr 1
  funext i a b
  unfold intersection_update_fsHerm_neg_one
  split_ifs
  · exact curv_changeFrame h₁ u₁ hA hAu hA0 _ _
  · simp only [cutForm]
    rw [conn_changeFrame (h₁.of_le one_le_two) u₁ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      conn_changeFrame (h₀.of_le one_le_two) u₀ (hA.of_le one_le_two) hAu hA0.self_of_nhds,
      ← Matrix.mul_sub, add_sub_add_right_eq_sub, ← Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  · exact curv_changeFrame h₀ u₀ hA hAu hA0 _ _

end GlobalTheory.GoodTop
end

