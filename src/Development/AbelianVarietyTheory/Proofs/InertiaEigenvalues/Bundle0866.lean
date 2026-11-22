import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0042
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT4_of_roots_in_field : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  first | exact @GlobalTheory.TwInputs.admT4_of_full_compatibility | exact GlobalTheory.TwInputs.admT4_of_full_compatibility | (intros; apply GlobalTheory.TwInputs.admT4_of_full_compatibility <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
section
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem cell_lintegral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℝ≥0∞) (hB : Measurable B) (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    ∫⁻ g in 𝓕, B g ∂μ =
      ∑' l : abelian₂ E n S, ENNReal.ofReal (dinv n l.1) * ∫⁻ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ := by
  have hC : MeasurableSet (C0 E n S) := (GlobalTheory.T.isOpen_C0 E n S).measurableSet
  let cellS : abelian₂ E n S → Set (GA E n) := fun l => {g | (tl n ϖ l.1)⁻¹ * g ∈ C0 E n S}
  have hmeas : ∀ l, MeasurableSet (cellS l) := fun l =>
    ((GlobalTheory.T.isOpen_C0 E n S).preimage (continuous_const.mul continuous_id)).measurableSet
  have hpart : ∀ g, ∑' l : abelian₂ E n S, (cellS l).indicator B g = B g := by
    intro g
    obtain ⟨l0, hl0S, hl0⟩ := GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset E n S ϖ hϖ g
    have hz : ∀ l : abelian₂ E n S, l ≠ (⟨l0, hl0S⟩ : abelian₂ E n S) → (cellS l).indicator B g = 0 := fun l hl =>
      Set.indicator_of_notMem (show g ∉ cellS l from fun hg => hl (Subtype.ext (GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset E n S ϖ hϖ l.1 l0 g l.2 hl0S hg hl0))) B
    rw [tsum_eq_single _ hz]
    exact Set.indicator_of_mem (show g ∈ cellS ⟨l0, hl0S⟩ from hl0) _
  calc ∫⁻ g in 𝓕, B g ∂μ = ∫⁻ g in 𝓕, ∑' l, (cellS l).indicator B g ∂μ := by simp_rw [hpart]
    _ = ∑' l, ∫⁻ g in 𝓕, (cellS l).indicator B g ∂μ :=
        lintegral_tsum fun l => (hB.indicator (hmeas l)).aemeasurable
    _ = _ := tsum_congr fun l => ?_
  let t := tl n ϖ l.1
  let F : GA E n → ℝ≥0∞ := (C0 E n S).indicator fun h => B (t * h)
  have e : (cellS l).indicator B = fun g => F (t⁻¹ * g) := by
    funext g
    show (cellS l).indicator B g = (C0 E n S).indicator (fun h => B (t * h)) (t⁻¹ * g)
    by_cases hg : t⁻¹ * g ∈ C0 E n S
    · rw [Set.indicator_of_mem (show g ∈ cellS l from hg), Set.indicator_of_mem hg, mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem (show g ∉ cellS l from hg), Set.indicator_of_notMem hg]
  have hF : Measurable F := (hB.comp (measurable_const_mul t)).indicator hC
  have hFinv : ∀ u ∈ NA E n, ∀ g, F (u * g) = F g := by
    intro u hu g
    show (C0 E n S).indicator (fun h => B (t * h)) (u * g) = (C0 E n S).indicator (fun h => B (t * h)) g
    by_cases hg : g ∈ C0 E n S
    · rw [Set.indicator_of_mem (adelicUnitriangular_mul_mem_unipotentTimesIntegral hu hg), Set.indicator_of_mem hg]
      change B (t * (u * g)) = B (t * g)
      rw [show t * (u * g) = (t * u * t⁻¹) * (t * g) by group]
      exact hinv _ (tl_conj_mem ϖ l.1 hu) _
    · have : u * g ∉ C0 E n S := fun h => hg (by simpa using adelicUnitriangular_mul_mem_unipotentTimesIntegral (inv_mem hu) h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]
  rw [e, GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient E n μ ϖ hϖ l.1 𝓕 h𝓕 F hF hFinv]
  congr 1
  rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]

theorem cell_integral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℂ) (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    (∀ l : abelian₂ E n S, Integrable (fun g => B (tl n ϖ l.1 * g)) (μ.restrict (𝓕 ∩ C0 E n S))) ∧
      HasSum (fun l : abelian₂ E n S => (dinv n l.1 : ℂ) * ∫ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ)
        (∫ g in 𝓕, B g ∂μ) := by
  have hpos : ∀ l : abelian₂ E n S, 0 < dinv n l.1 := fun l =>
    Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
  exact GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable μ 𝓕 (𝓕 ∩ C0 E n S) (fun l : abelian₂ E n S => dinv n l.1) hpos (fun l g => tl n ϖ l.1 * g)
    (fun l => measurable_const_mul _) ((fun u : GA E n => fun g => u * g) '' (NA E n : Set (GA E n)))
    (fun f hf hfi => cell_lintegral μ S ϖ hϖ 𝓕 h𝓕 f hf fun u hu g => hfi _ ⟨u, hu, rfl⟩ g)
    B hB hBi (by rintro _ ⟨u, hu, rfl⟩ x; exact hinv u hu x)

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ClassRefineBridge

open GlobalTheory.ClassRefine
open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

theorem injective_of_isReps {J : Subgroup G} {I : Type} {y : I → G} (hy : Bridge.IsReps ι J y) :
    Function.Injective y := by
  intro i j hij
  have h1 : ∃ (γ : Γ) (k : J), y i = ι γ * y i * k := ⟨1, 1, by simp⟩
  have h2 : ∃ (γ : Γ) (k : J), y i = ι γ * y j * k := ⟨1, 1, by simp [hij]⟩
  exact (hy (y i)).unique h1 h2

theorem image_reps {J : Subgroup G} {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι J y) :
    ∀ g : G, ∃! t, t ∈ Finset.univ.image y ∧ ∃ (γ : ι.range) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ := by
  intro g
  obtain ⟨i, ⟨γ, k, e⟩, hu⟩ := hy g
  refine ⟨y i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ⟨ι γ, γ, rfl⟩, k, k.2, e⟩, ?_⟩
  rintro t ⟨ht, ⟨_, δ, rfl⟩, κ, hκ, e'⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
  rw [hu j ⟨δ, ⟨κ, hκ⟩, e'⟩]

theorem card_stab_eq (hι : Function.Injective ι) (J : Subgroup G) (t : G) :
    Nat.card (Bridge.stab ι J t) = Nat.card (stabQ ι.range J t) := by
  refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨⟨ι γ, γ, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [mem_stabQ]; exact (Bridge.mem_stab ι).1 γ.2
  · intro a b h
    apply Subtype.ext
    apply hι
    have := congrArg (fun x : stabQ ι.range J t => ((x : ι.range) : G)) h
    simpa using this
  · rintro ⟨⟨_, γ, rfl⟩, hq⟩
    refine ⟨⟨γ, (Bridge.mem_stab ι).2 (mem_stabQ.1 hq)⟩, rfl⟩

theorem sum_image_eq {I : Type} [Fintype I] {y : I → G} (hy : Function.Injective y) (f : G → ℂ) :
    ∑ i, f (y i) = ∑ t ∈ Finset.univ.image y, f t := by
  rw [Finset.sum_image (fun a _ b _ h => hy h)]

theorem sum_isReps_refine : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  intro G Γ _ _ ι hι J J₀ hJ F hF hFu I₀ _ y₀ hy₀ I _ y hy Φ hl hr
  have key := sum_classReps_refine (Q := ι.range) hJ (image_reps ι hy) (image_reps ι hy₀) Φ
    (by rintro ⟨_, γ, rfl⟩ g; exact hl γ g) hr hF hFu
  simp only [card_stab_eq ι hι]
  rw [sum_image_eq (injective_of_isReps ι hy₀) (fun t => ((Nat.card (stabQ ι.range J₀ t) : ℂ))⁻¹ * Φ t),
    sum_image_eq (injective_of_isReps ι hy) (fun t => ((Nat.card (stabQ ι.range J t) : ℂ))⁻¹ * ∑ u ∈ F, Φ (t * u))]
  exact key

end GlobalTheory.ClassRefineBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexCoefficientMapCoreFieldPropertiesStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoefficientMap_coreField_properties : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ (hw : VsV D i T.Q.c.F), hwOK T.Q.c (lamV D i) hw → ‖c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) hw)‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v)) = (R.cV i).ρ γ (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) ∧ Submodule.span ℂ (Set.range fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)) = ⊤ ∧ (∀ (m : ℕ) (b : Fin m → VsV D i T.Q.c.F), LinearIndependent T.Q.c.F b → LinearIndependent ℂ (fun j => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (b j)))) ∧ Function.Injective c0 := by
  first | exact @GlobalTheory.AdTh.CoefC.coefMap_complex_core | exact GlobalTheory.AdTh.CoefC.coefMap_complex_core | (intros; apply GlobalTheory.AdTh.CoefC.coefMap_complex_core <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.RSTheta

section Row

variable {R : Type} [CommRing R] {a : ℕ}

def rowMat (ℓ : Fin a) (y : Fin a → R) : Matrix (Fin a) (Fin a) R := (1 : Matrix (Fin a) (Fin a) R).updateRow ℓ y

theorem det_rowMat (ℓ : Fin a) (y : Fin a → R) : (rowMat ℓ y).det = y ℓ := by
  have h := det_updateRow_sum (1 : Matrix (Fin a) (Fin a) R) ℓ y
  have e : ∑ k, y k • (1 : Matrix (Fin a) (Fin a) R) k = y := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply]
  rw [e] at h
  simpa [rowMat] using h

theorem isUnit_rowMat_iff {ℓ : Fin a} {y : Fin a → R} : IsUnit (rowMat ℓ y) ↔ IsUnit (y ℓ) := by
  rw [isUnit_iff_isUnit_det, det_rowMat]

open Classical in

def rowGL (ℓ : Fin a) (y : Fin a → R) : GL (Fin a) R :=
  if h : IsUnit (y ℓ) then (isUnit_rowMat_iff.2 h).unit else 1

theorem val_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) : (rowGL ℓ y).val = rowMat ℓ y := by
  rw [rowGL, dif_pos h, IsUnit.unit_spec]

theorem single_vecMul_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) :
    Pi.single ℓ 1 ᵥ* (rowGL ℓ y).val = y := by
  rw [val_rowGL h, single_one_vecMul]
  exact updateRow_self

theorem rowGL_single (ℓ : Fin a) : rowGL ℓ (Pi.single ℓ (1 : R)) = 1 := by
  refine Units.ext ((val_rowGL (by simp)).trans ?_)
  have : (Pi.single ℓ 1 : Fin a → R) = (1 : Matrix (Fin a) (Fin a) R) ℓ := by
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [rowMat, this]
  exact updateRow_eq_self _ _

end Row

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
variable (E) in

def rowSet (ℓ : Fin a) : Set (Fin a → Cinf E) := {u | ∀ w, u ℓ w ≠ 0}

omit [NumberField E] [IsTotallyComplex E] in
theorem isUnit_of_mem_rowSet {ℓ : Fin a} {u : Fin a → Cinf E} (h : u ∈ rowSet E ℓ) : IsUnit (u ℓ) :=
  Pi.isUnit_iff.2 fun w => (h w).isUnit

omit [IsTotallyComplex E] in
theorem isOpen_rowSet (ℓ : Fin a) : IsOpen (rowSet E ℓ) := by
  rw [rowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const

omit [IsTotallyComplex E] in

theorem continuousOn_rowGL (ℓ : Fin a) : ContinuousOn (rowGL ℓ) (rowSet E ℓ) := by
  refine GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.continuousOn_iff.2 ?_
  have h : Continuous fun u : Fin a → Cinf E => rowMat ℓ u := continuous_const.matrix_updateRow ℓ continuous_id
  exact h.continuousOn.congr fun u hu => val_rowGL (isUnit_of_mem_rowSet hu)

def rsInf (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (g : GA E a) (u : Fin a → Cinf E) : ℂ :=
  φ (g * (infGL E a (rowGL ℓ u))⁻¹) * conj (φ' (g * (infGL E a (rowGL ℓ u))⁻¹)) * Φ u

def rsPsi (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  thetaFn (rsInf ℓ φ φ' Φ g) J η y

theorem rsPsi_ratGL_mul (ℓ : Fin a) {φ φ' : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (γ : GL (Fin a) E) (g : GA E a) (y : Fin a → Ad E) :
    rsPsi ℓ φ φ' Φ J η (ratGL E a γ * g) y = rsPsi ℓ φ φ' Φ J η g y := by
  simp only [rsPsi, thetaFn, rsInf, mul_assoc, h, h']

theorem continuousOn_inv_rowGL (ℓ : Fin a) :
    ContinuousOn (fun u => (infGL E a (rowGL ℓ u))⁻¹) (rowSet E ℓ) :=
  (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn (continuousOn_rowGL ℓ)).inv

theorem continuous_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ tsupport Φ
  · have h1 : ContinuousAt (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) p :=
      continuousAt_fst.mul (ContinuousAt.comp (f := Prod.snd)
        ((continuousOn_inv_rowGL ℓ).continuousAt ((isOpen_rowSet ℓ).mem_nhds (hs hp))) continuousAt_snd)
    exact ((h.continuousAt.comp h1).mul ((Complex.continuous_conj.comp h').continuousAt.comp h1)).mul
      (hΦ.comp continuous_snd).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuousAt_snd.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [rsInf, hq]

omit [IsTotallyComplex E] in
theorem isOpen_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsOpen (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (isOpen_idealFiniteAdeles J).preimage (continuous_apply i)

omit [IsTotallyComplex E] in
theorem isCompact_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsCompact (latt a J) :=
  isCompact_pi_infinite fun _ => isCompact_idealFiniteAdeles J

omit [IsTotallyComplex E] in
theorem isClosed_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsClosed (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles J)).preimage (continuous_apply i)

theorem continuous_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) : Continuous fun p : GA E a × (Fin a → Ad E) => rsPsi ℓ φ φ' Φ J η p.1 p.2 := by
  have h1 : Continuous fun p : GA E a × (Fin a → Ad E) => (p.1, fun i => pInf E (p.2 i)) :=
    continuous_fst.prodMk (continuous_pi fun i =>
      GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_snd))
  have h2 : Continuous fun p : GA E a × (Fin a → Ad E) => (fun i => pFin E (p.2 i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const)
  exact ((continuous_rsInf h h' hΦ hs).comp h1).mul (h3.comp h2)

theorem continuous_of_mem_smoothSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hS := GlobalTheory.ShortVecDecay.smoothSpan_le_Sm π (Submodule.subset_span hF)
    obtain ⟨f, φ, hf, hφ, rfl⟩ := hF
    refine ContAut.continuous_of_isOpen_stab E a ⟨_, hS⟩ (isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
    have e : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hk
    exact (GlobalTheory.JSW.smoothInf_rt_fin f φ.1 k g).symm.trans (by rw [e])
  | zero => exact continuous_const
  | add F G _ _ hF hG => exact hF.add hG
  | smul z F _ hF => exact hF.const_smul z

theorem continuous_of_mem_or {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous φ.1 :=
  h.elim (fun h => ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ h).1.level) continuous_of_mem_smoothSpan

end GlobalTheory.RSTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodPin

set_option maxHeartbeats 2000000 in

theorem goodFTAll_pinned : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : NAt hL D cf nch tp), OPin a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hDZ hL D cf nch tp a hp hloc
  have h0 : GoodFTAll a.nt.D := by
    refine GlobalTheory.T.labels_of_depth_zero hG hZ hL a.nt.D a.nt.A.wdT a.nt.A.row a.nt.rep
      (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) a.nt.row a.depth hp.lab
      (fun k => @GlobalTheory.DepthZeroCusp.depthZeroCuspidal (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) ?_ hloc
    intro I rc hrc k v
    refine GlobalTheory.T.tame_parameter_coupled hDZ hL a.nt.D a.nt.A.wdT I rc hrc (fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩) k v (a.nt.A.grp.kv k v) ?_
    rw [← hp.gen k]
    exact a.nt.A.grp.tg_tame k v
  have e : ∀ D', D' = withLoc a.nt.L → GoodFTAll D' := by
    rintro _ rfl
    exact h0
  exact e D a.nt.eq

end GlobalTheory.GoodPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockReadingTranslatedFormMemComplexForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.FockReadForms

theorem fockRead_mem_formsC : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  intro D X E Y i j b t hxi hQ y hlaw u hu z hz
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hBo : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have hact := (GlobalTheory.CoefActIo.act_ioP hC hG hBo (Twist.triv_good splitSet_empty) htup).2
  have hio : Formalism.IndefR.FWT.IoExt X.R.toRealDat :=
    GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hval : ∀ w, X.R.ioP j (PiTensorProduct.tprod ℂ u) w ∈ (Y.Z.ρ.B i j b).valSpace := by
    intro w
    have hcV : (X.R.cV j).Is := hC.models.cV j
    obtain ⟨u', w₀, hu', -, hw⟩ := Formalism.IndefR.FWT.IsChosenExtremalVector.io _ (Y.Z.vec j) hio
    have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (congrFun hu ρ).symm)
    rw [huu] at hw
    have hT := Scale.io_act hC.lev hC.thP hG hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
          (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u)))

  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  rw [Base.mem_formsC]
  refine ⟨fun h => hval _, fun γ h k => ?_⟩
  have hzc := Subgroup.mem_center_iff.1 hz
  have e1 : Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z =
      Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)) := by
    simp only [mul_assoc]
    rw [← hzc]
  have h2 : Bridge.ratF (Vc D j) γ * (h * z) * ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j)) =
      Bridge.ratF (Vc D j) γ * (h * z) := by
    rw [OneMemClass.coe_one]
    exact mul_one _
  have e2 : (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z)) =
      (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
    calc (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))
        = (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) *
            ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j))) := congrArg _ h2.symm
      _ = (((levEnv _ (X.R.βV j) (X.R.datVt j t)).χ 1 : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          hx γ (h * z) 1
      _ = (1 : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          congrArg (fun c : ℂ => c • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)))
            (by rw [MonoidHom.map_one, Units.val_one])
      _ = (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) := one_smul ℂ _
  calc X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z))
      = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)))) :=
        congrArg (fun g => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y g)) e1
    _ = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        congrArg (X.R.ioP j (PiTensorProduct.tprod ℂ u)) (hlaw _ k)
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        map_smul _ _ _
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • X.R.ioP j (PiTensorProduct.tprod ℂ u) v) e2
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (Y.Z.ρ.B i j b).act (γ : GA D (Vc D j)) (X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • v) (hact _ _ _).symm

end GlobalTheory.FockReadForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignaturStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_framed_point_good_reduction_definite_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  first | exact @GlobalTheory.GoodDefinite.good_of_definite | exact GlobalTheory.GoodDefinite.good_of_definite | (intros; apply GlobalTheory.GoodDefinite.good_of_definite <;> assumption)
end

