import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import GroundTheory.AutomorphicForms.ReductionMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Formalism.AdmissibleDesigns.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0053
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace GlobalTheory.AdeleScale

variable {E : Type} [Field E] [NumberField E]

theorem qV_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (qV E v : ℝ) ≠ 0 := by
  rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem finId_adl_snd (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  change ((1 : Af E) - 1 + ((GlobalTheory.CellDec.adl ϖ m : (Af E)ˣ) : Af E)) v = _
  rw [sub_self, zero_add]
  rfl

theorem finId_fst (a : (Af E)ˣ) : ((finId E a : AdeleRing (𝓞 E) E)).1 = 1 := by
  change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_finId_adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ v, v ∉ s → m v = 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (finId E (GlobalTheory.CellDec.adl ϖ m)) : ℝ) =
      ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ w : InfinitePlace E,
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).1 w‖ ^ w.mult = 1 := fun w => by
    rw [finId_fst]
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E),
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v‖ = ((qV E v : ℝ) ^ m v)⁻¹ := fun v => by
    have hu : Valued.v ((ϖ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ v
    rw [finId_adl_snd, Units.val_zpow_eq_zpow_val, norm_zpow, GroundTheory.Global.norm_uniformizer hu, _root_.inv_zpow]
    rfl
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  simp_rw [h2]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvs
  exact hv (by show ((qV E v : ℝ) ^ m v)⁻¹ = 1; rw [hs v hvs, zpow_zero, inv_one])

end GlobalTheory.AdeleScale

open GlobalTheory.AdeleScale in

theorem GlobalTheory.AdeleScale.map_mul_finId_adl : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  intro E _ _ ϖ hϖ m s hs _ _ μR _
  set a : (AdeleRing (𝓞 E) E)ˣ := finId E (GlobalTheory.CellDec.adl ϖ m) with ha
  have hm : Measurable fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x :=
    (continuous_const.mul continuous_id).measurable
  have hchar : distribHaarChar (AdeleRing (𝓞 E) E) a • μR.map (fun x => (a : AdeleRing (𝓞 E) E) * x) = μR := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hm hS]
    have h1 := distribHaarChar_mul μR a ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S)
    have e : a • ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S) = S := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Units.smul_def]
    rw [e] at h1
    rw [ENNReal.smul_def, smul_eq_mul]
    exact h1
  have hmod : (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ) = ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
    rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing]
    exact ideleModule_finId_adl ϖ hϖ m s hs
  have hone : ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) * (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _), hmod, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (zpow_ne_zero _ (qV_ne_zero v)), ENNReal.ofReal_one]
  conv_rhs => rw [← hchar]
  rw [ENNReal.smul_def (distribHaarChar (AdeleRing (𝓞 E) E) a), smul_smul, hone, one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_mem_unipB (v : HeightOneSpectrum (𝓞 E)) {u : GA E n} (hu : u ∈ NA E n) :
    compV E n v u ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [compV, h1 i j hij]
  · simp [compV, h2 i]

theorem compV_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (v : HeightOneSpectrum (𝓞 E)) :
    compV E n v (tl n ϖ l) = GlobalTheory.IwaCell.tD (ϖ v) (l v) := by
  rw [tl_eq_diagT]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [compV, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have hc : ∀ x : Af E, pFin E (GlobalTheory.CuspRep.corner (sFin E) x) = x := fun x => by
      show ((1 : InfiniteAdeleRing E × Af E) - ((0 : InfiniteAdeleRing E), (1 : Af E)) + ((0 : InfiniteAdeleRing E), x)).2 = x
      simp
    have hf : ∀ y : (Af E)ˣ, ((finId E y : Ad E)) = GlobalTheory.CuspRep.corner (sFin E) (y : Af E) := fun y => rfl
    rw [hf, hc]
    congr 1
    show ((ϖ v ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply, Units.val_zpow_eq_zpow_val]
  · simp

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ord_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ}
    (hx : IsUnifV E v (x : v.adicCompletion E)) : GlobalTheory.SmGL.ord (v.adicCompletion E) x = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
  rfl

theorem compV_mem_cell (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {g : GA E n} (h : (tl n ϖ l)⁻¹ * g ∈ C0 E n S)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) : compV E n v g ∈ GlobalTheory.IwaCell.cell (ϖ v) (l v) := by
  obtain ⟨u, hu, k, hk, e⟩ := h
  have hg : g = tl n ϖ l * u * (tl n ϖ l)⁻¹ * tl n ϖ l * k := by
    rw [inv_mul_eq_iff_eq_mul] at e
    rw [e]; group
  have hkv : compV E n v k ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.HeckeEigConj.KO_eq_KGL]
    have := (Subgroup.mem_iInf.1 hk) v
    exact Subgroup.mem_comap.1 ((Subgroup.mem_iInf.1 this) hv)
  refine ⟨compV E n v (tl n ϖ l * u * (tl n ϖ l)⁻¹), compV_mem_unipB v (tl_conj_mem ϖ l hu), compV E n v k, hkv, ?_⟩
  rw [hg, map_mul, map_mul, compV_tl]

end GlobalTheory.CellDec

theorem GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  intro E _ _ n S ϖ hϖ l l' g hl hl' h h'
  ext v : 1
  by_cases hv : v ∈ S
  · rw [hl v hv, hl' v hv]
  · exact GlobalTheory.IwaCell.eq_of_mem_cell (GlobalTheory.CellDec.ord_of_isUnifV (hϖ v))
      (GlobalTheory.CellDec.compV_mem_cell ϖ l h hv) (GlobalTheory.CellDec.compV_mem_cell ϖ l' h' hv)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrame
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

open scoped Matrix

namespace GlobalTheory.ArcGenBound

open Matrix

theorem affine_pos {T a b c : ℝ} (h : ∀ x s : ℝ, T < s → 0 < a + x * b + s * c) : b = 0 ∧ 0 ≤ c := by
  have h1 := h 0 (T + 1) (by linarith)
  constructor
  · by_contra hb
    have := h (-(a + (T + 1) * c) / b) (T + 1) (by linarith)
    rw [div_mul_cancel₀ _ hb] at this
    linarith
  · by_contra hc
    have hc' : 0 < -c := by linarith [not_le.1 hc]
    have hd : 0 < (a + (T + 1) * c) / (-c) := div_pos (by linarith) hc'
    have := h 0 (T + 1 + (a + (T + 1) * c) / (-c)) (by linarith)
    have e := div_mul_cancel₀ (a + (T + 1) * c) hc'.ne'
    nlinarith

theorem det_im_lower_bound {g : ℕ} (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (T : ℝ) (A B : Matrix (Fin g) (Fin g) ℂ)
    (haff : ∀ w, τ w = A + w • B) (hpos : ∀ w : ℂ, T < w.im → ((τ w).map Complex.im).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, T + 1 < w.im → C ≤ ((τ w).map Complex.im).det := by
  have hq : ∀ (w : ℂ) (v : Fin g → ℝ), v ⬝ᵥ ((τ w).map Complex.im) *ᵥ v = v ⬝ᵥ (A.map Complex.im) *ᵥ v +
      w.re * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + w.im * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := by
    intro w v
    have e : (τ w).map Complex.im = A.map Complex.im + w.re • B.map Complex.im + w.im • B.map Complex.re := by
      ext i j
      simp [haff, add_assoc]
    rw [e]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h0 : T < (⟨0, T + 1⟩ : ℂ).im := by simp
  refine ⟨((τ ⟨0, T + 1⟩).map Complex.im).det, (hpos _ h0).det_pos, fun w hw => ?_⟩
  have hw' : T < w.im := by linarith
  have hD : ((τ w).map Complex.im - (τ ⟨0, T + 1⟩).map Complex.im).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hpos w hw').isHermitian.sub (hpos _ h0).isHermitian) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hp : ∀ x s : ℝ, T < s → 0 < v ⬝ᵥ (A.map Complex.im) *ᵥ v +
        x * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + s * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := fun x s hs => by
      have := (hpos ⟨x, s⟩ hs).dotProduct_mulVec_pos hv
      rwa [star_trivial, hq] at this
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq, hq]
    obtain ⟨hb, hc⟩ := affine_pos hp
    have := mul_nonneg (sub_pos.2 hw).le hc
    rw [hb]
    dsimp only
    linarith
  have := GlobalTheory.ClassFin.gramLB_det_mono (hpos _ h0) hD
  rwa [add_sub_cancel] at this

end GlobalTheory.ArcGenBound

open GlobalTheory.ArcGenBound in

theorem GlobalTheory.ArcGenBound.gen_ratio_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z _ _ _
  have haff : ∀ w, Θ.τ w = Matrix.of (fun i k => (Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) i) +
      w • Matrix.of (fun i k => (Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) i) := by
    intro w
    ext i k
    have e := congrFun (Θ.per w k).2 i
    rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e
    simpa [Matrix.transpose_apply] using e.symm
  obtain ⟨C, hC, hdet⟩ := det_im_lower_bound Θ.τ Ha.T _ _ haff (fun w hw => (Θ.pos w hw).2)
  refine ⟨Ha.T + 1, Real.sqrt (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ Uw.g * C))⁻¹), ?_⟩
  intro w hw yw hA k x t hx hb
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨hLie, hGen⟩ := hA
  have V1 := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W Uw.g _ Uw.F Ha th Θ w yw hw' hLie.1 hGen
  have V2 := Uw.norm k x hx
  obtain ⟨G, -, -, hchg⟩ := (GlobalTheory.Frames.frBor_iff_frChg _ _ _).1 hb
  have hs := (GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 E H Dw l Xo c
    σ Uw.g _ Uw.F (Uw.ik k) Ha.i (Uw.Pm k x) (Ha.Pw w) (U.un k x) yw G (t none : CAt σ) 1 _ (Uw.period k x)
    (Ha.period w hw') (Uw.lie k x).1 hLie.1 hchg V2 V1).2
  rw [mul_one] at hs
  apply Real.le_sqrt_of_sq_le
  rw [← hs]
  have hd := hdet w hw
  have h2 : (0 : ℝ) < 2 ^ Uw.g := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos h2 hC)) (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd h2.le))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTwistingCharacterDeltaGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaGood

theorem coprime_fifteen_of_prime_mod_fifteen_eq_one {q : ℕ} (hq : q.Prime) (hm : q % 15 = 1) : Nat.Coprime 15 q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
  intro hd
  have := Nat.le_of_dvd (by norm_num) hd
  have h1 : q = 1 := by omega
  exact hq.one_lt.ne' h1

theorem twistOf_delta_good : ∀ (D : D7) (a : Recip D D.nd.Om), a.Good → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (f : D.ntw.O0 i →+* ℂ), Function.Injective f → ∀ b : Bool, (twistOf a f ch (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))).Good := by
  intro D a ha i ch hch f _ b
  classical
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hval : ∀ σ, ψ σ = 1 ↔ D.ntw.delta i σ = 1 := fun σ => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hopen : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by ext σ; simp only [MonoidHom.mem_ker]; exact hval σ
    rw [this]; exact D.ntw.delta_open i
  have hanti : AntiHom D.ntw.cc ψ := fun g g' h => by
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, D.ntw.delta_anti i g g' h]

  set p := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hp
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rw [hp]; split_ifs
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
  have hmem : ∀ v : Pl D.host.E, v ∈ D.ntw.pD i ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun v => by
    have := D.ntw.pD_eq i
    rw [Set.ext_iff] at this
    exact this v
  have h15 : ∀ P ∈ D.ntw.pD i, ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP h
    have hpP := (hmem P).1 hP
    have hcop : Nat.Coprime 15 p := coprime_fifteen_of_prime_mod_fifteen_eq_one hpp.1 hpp.2
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have : ((u * (15 : ℕ) + w * (p : ℕ) : ℤ) : 𝓞 D.host.E) = 1 := by rw [huw]; simp
    rw [← this]
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast h)) (Ideal.mul_mem_left _ _ (by exact_mod_cast hpP))
  have hconj : ∀ P ∈ D.ntw.pD i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.pD i := by
    intro P hP P' hc
    rw [hmem] at hP ⊢
    exact (hc _ _ (by simp)).1 hP
  set Q := half ch (D.ntw.pD i) with hQ
  have hsplit : SplitSet Q := by
    refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) fun P hP P' hP' hc => ?_
    have hne : P ≠ P' := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i P (mem_half.1 hP).1) hc
    exact (hch.pair P P' hc hne).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  let g : (D.ntw.O0 i)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf a f ψ = a.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  show (⟨Q, charOf a f ψ, resOf (charOf a f ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.split_set_inertia_power_trivial D D.nd D.ntw a ha Circle (g.comp ψ) ?_ ?_ Q hsplit ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · intro P hP
    have hPD := (mem_half.1 hP).1
    refine ⟨15, h15 P hPD, fun B hB σ hσ => ?_⟩
    have hc := D.ntw.delta_15 i P hPD B hB
    have h1 : D.ntw.delta i σ ^ 15 = 1 := by
      have := pow_card_eq_one' (G := ((Ine (F := D.host.E) B).map (D.ntw.delta i)))
        (x := ⟨D.ntw.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
      rw [hc] at this
      exact congrArg Subtype.val this
    have h2 : ψ σ ^ 15 = 1 := by
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]
    rw [MonoidHom.comp_apply, ← map_pow, h2, map_one]
  · intro v hv hnc B hB σ hσ
    have hvD : v ∉ D.ntw.pD i := by
      intro hvD
      by_cases hc : v ∈ ch
      · exact hv (mem_half.2 ⟨hvD, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'D := hconj v hvD v' hv'
        have hne := ne_of_split (GlobalTheory.T.anticyclotomicTwist_ramified_places_split D i v hvD) hv'
        have hv'c : v' ∈ ch := by
          by_contra h
          exact hc (((hch.pair v v' hv' hne).2 h))
        exact hnc v' (mem_half.2 ⟨hv'D, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : D.ntw.delta i σ = 1 := by
      by_contra h
      exact hvD ((D.ntw.delta_ram i v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, (hval σ).2 h1, map_one]

end GlobalTheory.DeltaGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockLiftIdentityMemUnipotentLevelCharacterOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLiftIdentity_mem_unipotentLevel_character_one : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r q : ℕ), 1 < q → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ → NG.LevelUni J χ s r ψ₀ ξ → ∀ p : GAf L n, TrivOutside {s.v} p → IsLiftAt s r q (1 : GL (Fin r) (ZMod q)) (s.loc n p) → ∃ h : p ∈ J, χ ⟨p, h⟩ = 1 := by
  first | exact @GlobalTheory.UniLevelLift.main | exact GlobalTheory.UniLevelLift.main | (intros; apply GlobalTheory.UniLevelLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAlStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralityFromMetric_of_designConditionAll : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  first | exact @GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions | exact GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions | (intros; apply GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem universalPart_caseA :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D →
      UnusedSlot80.UniversalComponentCaseA D HW F Cm :=
  fun D HW F Cm hAdm h9 hH h15 => Formalism.MainNotions.UnusedSlot80.universal_general_statement_holds D HW F Cm hAdm h9 hH h15

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExtensionPotentiallySemistable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem extStep_holds : ExtStep := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c hρ hblk hdR h₁ h₂
  obtain ⟨K₁, hK₁, Q₁, hQ₁⟩ := h₁
  obtain ⟨K₂, hK₂, Q₂, hQ₂⟩ := h₂
  haveI := K₁.2
  haveI := K₂.2
  let K' : FinExt l := ⟨K₁.1 ⊔ K₂.1, inferInstance⟩
  have h1' : K₁.1 ≤ K'.1 := le_sup_left
  have h2' : K₂.1 ≤ K'.1 := le_sup_right
  have hK : K.1 ≤ K'.1 := hK₁.trans h1'
  let ι : ↥(GK K') →* ↥(GK K) := Subgroup.inclusion (GK_le hK)
  have hQ₁' : ∀ g : ↥(GK K'), ((ρ₁.comp ι) g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁ := fun g => hQ₁ ⟨g, GK_le h1' g.2⟩
  have hQ₂' : ∀ g : ↥(GK K'), ((ρ₂.comp ι) g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂ := fun g => hQ₂ ⟨g, GK_le h2' g.2⟩
  have hdR₂ : AdmDR P ρ₂ := (GlobalTheory.T.deRham_blockTriangular_diagonal_blocks l P AI T a b K r ρ ρ₁ ρ₂ c hρ hblk hdR).2
  obtain ⟨hcr, hcc, hcoc⟩ := GlobalTheory.T.matrixHomRepresentationCocycle_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk
  obtain ⟨v, hv⟩ := GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients l P AI T (a × b) K' r (homRep (ρ₁.comp ι) (ρ₂.comp ι)) (homUnit Q₁ Q₂)
    (GlobalTheory.T.matrixHomRepresentation_restrict_rational_continuous l a b K K' hK r ρ ρ₁ ρ₂ c hρ hblk) (GlobalTheory.T.matrixHom_periodMatrix_semistable l P a b K' (ρ₁.comp ι) (ρ₂.comp ι) Q₁ Q₂ hQ₁' hQ₂')
    (extCoc (ρ₂.comp ι) (fun g => c (ι g))) hcr hcc hcoc
    (fun m => by
      obtain ⟨w, hw⟩ := GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham l P AI T a b K ρ ρ₁ ρ₂ c hblk hdR hdR₂ m
      exact ⟨w, fun g => hw (ι g)⟩)
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.extension_block_periodMatrix_semistable l P a b K' (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hblk (ι g))
    Q₁ Q₂ hQ₁' hQ₂' v hv
  exact ⟨K', hK, Q, fun g => hQ g⟩

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_map_correspondence : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D), ∃ rc : GlobalTheory.SerSys.Corr D, IsRc hL T I rc ∧ ∀ k v, IsClassMap D.naut.lpDim (rc k v) := by
  first | exact @GlobalTheory.TypeRec.exists_isRc_isClassMap | exact GlobalTheory.TypeRec.exists_isRc_isClassMap | (intros; apply GlobalTheory.TypeRec.exists_isRc_isClassMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponentsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_type_components : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧ ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  first | exact @GlobalTheory.TypeRec.exists_comp_irrSm_param | exact GlobalTheory.TypeRec.exists_comp_irrSm_param | (intros; apply GlobalTheory.TypeRec.exists_comp_irrSm_param <;> assumption)
end

