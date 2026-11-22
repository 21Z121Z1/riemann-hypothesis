import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBound
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_mul_of_ne_zero {s : ℝ} (hs : s < 0) {a : k} (ha : a ≠ 0) (y : k) :
    ENNReal.ofReal (if h : a * y = 0 then 0 else nabs k (Units.mk0 (a * y) h)) ^ s =
      ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s *
        ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s := by
  have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
    simpa using Model.nabs_pos _
  by_cases hy : y = 0
  · subst hy
    have : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hpa]
    simp [ENNReal.zero_rpow_of_neg hs, ENNReal.mul_top this]
  · have hay : a * y ≠ 0 := mul_ne_zero ha hy
    have hpy : ENNReal.ofReal (nabs k (Units.mk0 y hy)) ≠ 0 := by
      simpa using Model.nabs_pos _
    have e : Units.mk0 (a * y) hay = Units.mk0 a ha * Units.mk0 y hy := Units.ext rfl
    rw [dif_neg hay, dif_neg hy, e, Model.nabs_mul, ENNReal.ofReal_mul (Model.nabs_pos _).le,
      ENNReal.mul_rpow_of_ne_zero hpa hpy]

theorem absPow_le_one_of_notMem [MeasurableSpace k] [BorelSpace k] {s : ℝ} (hs : s < 0) {y : k} (hy : y ∉ 𝒪[k]) :
    ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s ≤ 1 := by
  have h0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  rw [dif_neg h0]
  refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ hs
  have h1 : valuation k y⁻¹ ≤ 1 := ((valuation k).val_le_one_or_val_inv_le_one y).resolve_left hy
  have h2 : nabs k (Units.mk0 y h0)⁻¹ ≤ 1 := Model.nabs_le_one _ (by simpa using h1)
  have h3 : nabs k (Units.mk0 y h0) * nabs k (Units.mk0 y h0)⁻¹ = 1 := by
    rw [← Model.nabs_mul, mul_inv_cancel, Model.nabs_one]
  have h4 := Model.nabs_pos (Units.mk0 y h0)
  rw [ENNReal.one_le_ofReal]
  nlinarith

end OneVar

theorem lintegral_absPow_affine_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ)
    (hs : s < 0) (a b : k) :
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  have hO : IsOpen (𝒪[k] : Set k) := Model.isOpen_int
  by_cases ha : a = 0
  · have hpos : μ (𝒪[k] : Set k) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    rw [dif_pos ha, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hs, ENNReal.top_mul]
    · exact le_top
    · exact fun h => hpos (add_eq_zero.1 h).2
  rw [dif_neg ha]
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  set C : ℝ≥0∞ := ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s with hC
  have hCt : C ≠ ⊤ := by
    have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
      simpa using Model.nabs_pos _
    simp [hC, ENNReal.rpow_eq_top_iff, hpa]
  have hpt : ∀ x, (𝒪[k] : Set k).indicator (fun y => P (a * y + b)) x ≤
      C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) := by
    intro x
    by_cases hx : x ∈ (𝒪[k] : Set k)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have e : a * x + b = a * (x + b / a) := by field_simp
      have e' : P (a * x + b) = C * P (x + b / a) := by
        rw [e]; exact absPow_mul_of_ne_zero hs ha _
      rw [e']
      gcongr
      by_cases hx' : x + b / a ∈ (𝒪[k] : Set k)
      · rw [Set.indicator_of_mem hx']; exact le_self_add
      · rw [Set.indicator_of_notMem hx', zero_add]; exact absPow_le_one_of_notMem hs hx'
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  calc _ ≤ ∫⁻ x, C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ hCt,
          lintegral_add_right _ (measurable_one.indicator hO.measurableSet),
          lintegral_add_right_eq_self (fun x => (𝒪[k] : Set k).indicator P x),
          lintegral_indicator_one hO.measurableSet]

end GlobalTheory.KSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
section
open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Af Ainf)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE)
open scoped GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens

noncomputable section

namespace GlobalTheory.TateConv

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.LiesOver nonZeroDivisors
open GroundTheory.Global.IdeleGroup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tens : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem continuous_tens : Continuous (tens F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (tens F E).toLinearMap

theorem continuous_tens_symm : Continuous (tens F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  exact IsModuleTopology.continuous_of_linearMap (tens F E).symm.toLinearMap

def idl : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (tens F E).toMulEquiv
  continuous_toFun := Continuous.units_map (tens F E).toMulEquiv.toMonoidHom (continuous_tens F E)
  continuous_invFun := Continuous.units_map (tens F E).symm.toMulEquiv.toMonoidHom (continuous_tens_symm F E)

theorem idl_val (l : (AE F E)ˣ) : ((idl F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = tens F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) :
    (absE F E l : ℝ) = (IdeleGroup.ideleModule E (idl F E l) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (idl F E l),
    IdeleGroup.ideleModule_apply]
  have hN : ((ideleNorm F E (idl F E l) : IdeleGroup F) : AF F) = Algebra.norm (AF F) (l : AE F E) := by
    rw [coe_ideleNorm, idl_val]
    exact Algebra.norm_eq_of_algEquiv (tens F E) _
  have hf : ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod, hf]
  simp only [IdeleGroup.infiniteModule, IdeleGroup.finiteModule, hN]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin, coe_nnnorm]
    rfl

theorem crd_eq (x : AE F E) (i : Fin (Module.finrank F E)) :
    GlobalTheory.XTermMaj.crd F E x i = coord (Module.finBasis F E) i (tens F E x) := by
  rw [← adeleBasis_repr]
  simp [GlobalTheory.XTermMaj.crd, adeleBasis, tens]

theorem eq_sum (y : AdeleRing (𝓞 E) E) :
    y = ∑ i, algebraMap E (AdeleRing (𝓞 E) E) (Module.finBasis F E i) *
      adeleMap F E (coord (Module.finBasis F E) i y) := by
  conv_lhs => rw [← adeleTensorEquiv_sum_coord (Module.finBasis F E) y]
  rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]

def gfin (c : Fin (Module.finrank F E) → Af F) : FiniteAdeleRing (𝓞 E) E :=
  ∑ i, algebraMap E (FiniteAdeleRing (𝓞 E) E) (Module.finBasis F E i) * finiteAdeleMap F E (c i)

theorem continuous_gfin : Continuous (gfin F E) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_finiteAdeleMap.comp (continuous_apply i))

theorem snd_eq (y : AdeleRing (𝓞 E) E) :
    y.2 = gfin F E (fun i => (coord (Module.finBasis F E) i y).2) := by
  conv_lhs => rw [eq_sum F E y]
  change sndAddHom (∑ i, _) = _
  rw [map_sum]
  rfl

def infPart {K : Type} [Field K] [NumberField K] (y : AdeleRing (𝓞 K) K) : InfiniteAdeleRing K := y.1

theorem fst_apply (y : AdeleRing (𝓞 E) E) (w : InfinitePlace E) :
    infPart y w = ∑ i, (algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w *
      algebraMap (w.comap (algebraMap F E)).Completion w.Completion
        ((coord (Module.finBasis F E) i y).1 (w.comap (algebraMap F E))) := by
  conv_lhs => rw [eq_sum F E y]
  change ((fstAddHom (L := E)) (∑ i, _)) w = _
  rw [map_sum]
  refine (map_sum (Pi.evalAddMonoidHom (fun v : InfinitePlace E => v.Completion) w) _ (Finset.univ : Finset (Fin (Module.finrank F E)))).trans ?_
  rfl

theorem norm_alg (w : InfinitePlace E) (x : (w.comap (algebraMap F E)).Completion) :
    ‖algebraMap (w.comap (algebraMap F E)).Completion w.Completion x‖ = ‖x‖ := by
  refine NumberField.InfinitePlace.Completion.induction_on _ x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (continuous_algebraMap _ _)) continuous_norm
  · intro a
    rw [NumberField.InfinitePlace.Completion.algebraMap_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe]
    exact (NumberField.InfinitePlace.LiesOver.isometry_algebraMap w _).norm_map_of_map_zero (map_zero _) a

def bc : ℝ := ∑ w : InfinitePlace E, ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖

theorem bc_nonneg : 0 ≤ bc F E := by unfold bc; positivity

theorem norm_fst_le (x : AE F E) (y : AdeleRing (𝓞 E) E) (hy : y = tens F E x) (w : InfinitePlace E) :
    ‖infPart y w‖ ≤ bc F E * ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖ := by
  set S := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖
  have hS : 0 ≤ S := by positivity
  have hx : ∀ i, ‖(coord (Module.finBasis F E) i (tens F E x)).1 (w.comap (algebraMap F E))‖ ≤ S := by
    intro i
    rw [← crd_eq]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  rw [fst_apply F E, hy]
  calc _ ≤ ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w *
        algebraMap (w.comap (algebraMap F E)).Completion w.Completion
          ((coord (Module.finBasis F E) i (tens F E x)).1 (w.comap (algebraMap F E)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖ * S := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_alg]
        exact mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)
    _ = (∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖) * S := (Finset.sum_mul _ _ _).symm
    _ ≤ bc F E * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact Finset.single_le_sum (f := fun w : InfinitePlace E =>
          ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖) (fun _ _ => by positivity) (Finset.mem_univ w)

theorem bound {s : ℝ} (hs : 1 < s) {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) :
    ∃ (N k : ℕ) (L : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : ℝ), 2 * s + 2 < k ∧ ∀ l : (AE F E)ˣ,
      GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s) ≤
        ENNReal.ofReal (C * (infiniteZetaBound s k (IdeleGroup.toInfinite E (idl F E l)) *
          finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)))) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * s + 2 < k := exists_nat_gt _
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hU.image (continuous_gfin F E))
  set r := Fintype.card (InfinitePlace E)
  have hB := bc_nonneg F E
  refine ⟨k * r, k, L, (1 + bc F E) ^ (k * r), hk, fun l => ?_⟩
  set S := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖ with hSdef
  have hS : 0 ≤ S := by positivity
  by_cases hU' : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hU', ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set y : AdeleRing (𝓞 E) E := tens F E (l : AE F E) with hy
    have hfin : y.2 ∈ idealFiniteAdeles L := by
      rw [snd_eq F E]
      apply hL
      refine ⟨_, hU', ?_⟩
      simp only [hy, crd_eq]
    have hfz : finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)) =
        finiteModule (ofFinite (IdeleGroup.toFinite E (idl F E l))) ^ s := by
      rw [finiteZetaBound, if_pos]
      exact hfin
    rw [hfz, absE_eq, ideleModule_rpow_eq]
    set fm := finiteModule (ofFinite (IdeleGroup.toFinite E (idl F E l))) ^ s
    have hfm : 0 ≤ fm := Real.rpow_nonneg (finiteModule_pos _).le _
    set a : InfiniteAdeleRing E := ((IdeleGroup.toInfinite E (idl F E l) : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E)
    have ha : ∀ w, 1 + ‖a w‖ ≤ (1 + bc F E) * (1 + S) := fun w => by
      have h1 := norm_fst_le F E (l : AE F E) y hy w
      have e : a w = infPart y w := rfl
      rw [e]
      nlinarith
    have key : (1 + S) ^ (-((k * r : ℕ) : ℝ)) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) ≤
        (1 + bc F E) ^ (k * r) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) / (1 + ‖a w‖) ^ k := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      have e1 : (1 + S) ^ (k * r) = ∏ _w : InfinitePlace E, (1 + S) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      have e2 : (1 + bc F E) ^ (k * r) = ∏ _w : InfinitePlace E, (1 + bc F E) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      rw [e1, e2, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => ?_)
      have h2 : (1 + ‖a w‖) ^ k ≤ (1 + bc F E) ^ k * (1 + S) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (ha w) k
      have hP : 0 ≤ ‖a w‖ ^ ((w.mult : ℝ) * s) := by positivity
      have h1S : 0 < (1 + S) ^ k := by positivity
      have h1a : 0 < (1 + ‖a w‖) ^ k := by positivity
      rw [mul_div_assoc', le_div_iff₀ h1a]
      calc ((1 + S) ^ k)⁻¹ * ‖a w‖ ^ ((w.mult : ℝ) * s) * (1 + ‖a w‖) ^ k
          ≤ ((1 + S) ^ k)⁻¹ * ‖a w‖ ^ ((w.mult : ℝ) * s) * ((1 + bc F E) ^ k * (1 + S) ^ k) := by gcongr
        _ = (1 + bc F E) ^ k * ‖a w‖ ^ ((w.mult : ℝ) * s) := by field_simp
    calc (1 + S) ^ (-((k * r : ℕ) : ℝ)) * ((∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s)) * fm)
        = ((1 + S) ^ (-((k * r : ℕ) : ℝ)) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s)) * fm := by ring
      _ ≤ ((1 + bc F E) ^ (k * r) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) / (1 + ‖a w‖) ^ k) * fm :=
          mul_le_mul_of_nonneg_right key hfm
      _ = _ := by rw [infiniteZetaBound]; ring
  · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_notMem hU', zero_mul]
    exact zero_le

theorem lintegral_bound_lt_top (ν : Measure (AE F E)ˣ) [ν.IsHaarMeasure] {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hk : 2 * s + 2 < k) (L : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : ℝ) :
    ∫⁻ l, ENNReal.ofReal (C * (infiniteZetaBound s k (IdeleGroup.toInfinite E (idl F E l)) *
      finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)))) ∂ν < ⊤ := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  set G : IdeleGroup E → ENNReal := fun x => ENNReal.ofReal (C * (infiniteZetaBound s k
    (IdeleGroup.toInfinite E x) * finiteZetaBound L s (IdeleGroup.toFinite E x))) with hG
  have hm : ∫⁻ l, G (idl F E l) ∂ν = ∫⁻ x, G x ∂(ν.map (idl F E)) :=
    (lintegral_map_equiv G (idl F E).toHomeomorph.toMeasurableEquiv (μ := ν)).symm
  rw [hm]
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : (ν.map (idl F E)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (idl F E)
  rw [Measure.isMulLeftInvariant_eq_smul (ν.map (idl F E)) (ideleMeasure E), lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (((integrable_zetaBound hs hk L).const_mul C).lintegral_lt_top)

end GlobalTheory.TateConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

theorem lintegral_prod_le_symm {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  exact lintegral_prod_le _

theorem lintegral_cons_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ u, ∫⁻ x, G (Fin.cons x u) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  rw [h.lintegral_map_equiv G _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_col_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m n : ℕ)
    (G : (Fin m → Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ M, ∫⁻ v, G (fun i => Fin.cons (v i) (M i)) ∂(Measure.pi fun _ : Fin m => μ)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin m => e)
      (Measure.pi fun _ : Fin m => μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) :=
    measurePreserving_pi _ _ (f := fun _ : Fin m => e) (fun _ => h)
  have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin n → α) (Fin m) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => μ)).symm
  rw [h1.lintegral_map_equiv G _, h2.lintegral_map_equiv _ _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  refine lintegral_congr fun M => lintegral_congr fun v => congrArg G ?_
  funext i
  change e (v i, M i) = _
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_volM_le_corner (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞) :
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  refine (lintegral_cons_le (Measure.pi fun _ : Fin (n + 1) => ν) n F).trans ?_
  refine (lintegral_col_le ν n n _).trans ?_
  refine lintegral_mono fun M => lintegral_mono fun v => ?_
  exact lintegral_cons_le ν n
    (fun r => F (Matrix.of (Fin.cons r (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))))

end GlobalTheory.KSplit.CornerFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwistStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localEpsilonFactor_tame_finiteOrder_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  first | exact @GlobalTheory.TameTwistEps.locEps_tame_twist | exact GlobalTheory.TameTwistEps.locEps_tame_twist | (intros; apply GlobalTheory.TameTwistEps.locEps_tame_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFinIrr
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  first | (exact @GlobalTheory.FinClsLoc.localTransfer) | (exact GlobalTheory.FinClsLoc.localTransfer) | (intros; apply GlobalTheory.FinClsLoc.localTransfer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRootsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mt n → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → IsDS ε lam σ → ∀ v ∈ lowKSub ε lam σ, SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v → ∀ a c : Fin n, ε a = true → ε c = false → dRepC (Formalism.REAL.Jm ε) σ (Matrix.single c a 1) v = 0 := by
  first | exact @GlobalTheory.HolDict.Lowering.lowK_killed | exact GlobalTheory.HolDict.Lowering.lowK_killed | (intros; apply GlobalTheory.HolDict.Lowering.lowK_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem Dbl.p_comp_eq_of_isHom : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  intro F _ X Y φ f hf W hW
  haveI : IsDominant (W.Z.fromSpecStalk (genericPoint W.Z)) := ⟨by
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W.Z).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  haveI : IsSeparated X.str := (ratOf X).sep
  have hs : f ≫ X.str = Y.str := hf.inducedModelMorphism_comp_structureMap
  refine ext_of_isDominant_of_isSeparated X.str ?_ (W.Z.fromSpecStalk (genericPoint W.Z)) ?_
  · change (W.p₁ ≫ f) ≫ X.str = (W.p₂ ≫ f) ≫ X.str
    rw [Category.assoc, Category.assoc, hs, W.str_eq]
  · have e₁ := specMap_functionFieldMap W.p₁
    have e₂ := specMap_functionFieldMap W.p₂
    have hφ : (functionFieldMap W.p₁).comp φ.toRingHom = (functionFieldMap W.p₂).comp φ.toRingHom :=
      RingHom.ext hW
    have key : ∀ (α : Y.Fn →+* W.Z.functionField),
        Spec.map (CommRingCat.ofHom α) ≫ genericFieldPoint Y.X ≫ f =
          Spec.map (CommRingCat.ofHom (α.comp φ.toRingHom)) ≫ (ratOf X).pt := by
      intro α
      have hf' : genericFieldPoint Y.X ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hf
      rw [hf', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    change genericFieldPoint W.Z ≫ W.p₁ ≫ f = genericFieldPoint W.Z ≫ W.p₂ ≫ f
    rw [← Category.assoc, ← e₁, Category.assoc, ← Category.assoc (genericFieldPoint W.Z), ← e₂, Category.assoc,
      key, key, hφ]

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernelStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)), (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) → y ∈ tensAll H := by
  first | exact @GlobalTheory.HoweR.mem_tensAll_of_killed | exact GlobalTheory.HoweR.mem_tensAll_of_killed | (intros; apply GlobalTheory.HoweR.mem_tensAll_of_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvariStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyPeriodLatticePropertiesHoldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_periodLattice_properties_hold : GlobalTheory.ColNorms.PeriodLattices := by
  first | exact @GlobalTheory.ColNorms.periodLattices | exact GlobalTheory.ColNorms.periodLattices | (intros; apply GlobalTheory.ColNorms.periodLattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilocalConjugateSameCharpoly
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilocal_conjugate_same_charpoly : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  first | (exact @GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (exact GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable) | (intros; apply GlobalTheory.SemilocalConj.conj_of_charpoly_eq_of_separable <;> assumption)
end

