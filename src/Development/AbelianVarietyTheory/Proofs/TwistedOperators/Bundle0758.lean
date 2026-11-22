import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0531
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0753
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunctionalEquationLocalLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0582
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobi
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem GlobalTheory.FrameFB.frame_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b = ι a → a = Fin.last σ ∧ b = Fin.last σ) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ*
    ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcFB W F σ h h').A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨k, _, _, _, _, p, β, j, ϖ, hpv, hid, hlat, hmax, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, hj, hcol, hperp⟩ :=
    GlobalTheory.StairFrameFJ.exists_frame D hq T L μ0 hL sc G W M hM F hF σ h' v hv
  have hϖ : (ϖ : k) ≠ 0 := by
    intro h0
    have h0' : ϖ = 0 := Subtype.ext h0
    have : IsLocalRing.maximalIdeal 𝒪[k] = ⊥ := by rw [hmax, h0', Ideal.span_singleton_eq_bot.2 rfl]
    exact IsDiscreteValuationRing.not_a_field _ this
  obtain ⟨hs, ht⟩ := GlobalTheory.FrameScale.clauses D hq T L μ0 hL sc G W M hM F hF σ h' k p β j (ϖ : k) (G.pl.depth sc v) hϖ hj hcol hperp
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β,
    fun q => j ⟨q.1, by omega⟩, fun q => j ⟨2 * σ - q.1, by omega⟩, _, _, hpv, hid, hlat, ?_, ?_, ?_, hs, ht, ?_⟩
  · intro a b hab
    have := hj hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    exact Fin.ext (by omega)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    constructor <;> exact Fin.ext (by simp; omega)
  · intro a ha
    have hu2 : (p.pr (incA D (star (-D.host.xi0)))) ≠ 0 := right_ne_zero_of_mul_eq_one hu₂
    refine ⟨fun q i => ?_, fun q i => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.split_frame_lattice_functional D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      exact ⟨z, hz, hz'⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.ConjClause.functional_equation_local_lattice D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      refine ⟨z * (if q.1 = σ then -1 else 1), Ideal.mul_mem_right _ _ hz, ?_⟩
      clear hperp hcol hs ht hlat
      have hϖn : (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) ≠ 0 := pow_ne_zero _ hϖ
      have hx : (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hu2
      rw [← hz']
      generalize (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) = X at hx ⊢
      generalize (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) = Y at hϖn ⊢
      by_cases hqσ : q.1 = σ
      · simp only [hqσ, if_true]
        push_cast
        field_simp
      · simp only [hqσ, if_false]
        push_cast
        field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseIdealsCompletionEqOfModulusUnitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staircase_ideals_completion_eq_of_modulus_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  first | exact @GlobalTheory.StairIdealAt.completion_eq_of_modul_unit | exact GlobalTheory.StairIdealAt.completion_eq_of_modul_unit | (intros; apply GlobalTheory.StairIdealAt.completion_eq_of_modul_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  first | exact @GlobalTheory.StairLine.colMul_dJ_mem_iff | exact GlobalTheory.StairLine.colMul_dJ_mem_iff | (intros; apply GlobalTheory.StairLine.colMul_dJ_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_frames_successive_levels : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | exact GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | (intros; apply GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SubsetVecs

open GlobalTheory.FinPl.PutIn

variable {D : D7} {S T : HSp D} {ι : Type} [DecidableEq ι]

def prodD (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (s : Finset ι) (y : WO S T) : ℂ :=
  if IsHalf (∑ w ∈ s, a w) y then ∏ w ∈ s, Ψ w (a w • y) else 0

theorem sum_mul_zero {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) {s : Finset ι} {w : ι} (hw : w ∉ s) :
    (∑ v ∈ s, a v) * a w = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun v hv => ho v w fun h => hw (h ▸ hv)

theorem prodD_empty (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (Λ : AddSubgroup (WO S T)) :
    prodD a Ψ ∅ = halfInd 0 Λ := by
  funext y
  unfold prodD halfInd
  rw [Finset.sum_empty, Finset.prod_empty]
  by_cases h : IsHalf (0 : AE D) y
  · rw [if_pos h, if_pos ⟨(GlobalTheory.VecProd.isHalf_zero_iff y).1 h ▸ Λ.zero_mem, h⟩]
  · rw [if_neg h, if_neg fun h' => h h'.2]

theorem prodD_insert {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (Ψ : ι → WO S T → ℂ) {s : Finset ι} {w : ι}
    (hw : w ∉ s) : prodD a Ψ (insert w s) = tens (a w) (prodD a Ψ s) (Ψ w) := by
  funext y
  have h0 := sum_mul_zero ho hw
  have hiff : IsHalf (a w + ∑ v ∈ s, a v) y ↔ IsHalf (∑ v ∈ s, a v) (y - a w • y) :=
    GlobalTheory.VecProd.isHalf_add_iff h0 y
  have hp : ∏ v ∈ s, Ψ v (a v • (y - a w • y)) = ∏ v ∈ s, Ψ v (a v • y) :=
    Finset.prod_congr rfl fun v hv => by
      rw [smul_sub, smul_smul, ho v w fun h => hw (h ▸ hv), zero_smul, sub_zero]
  rw [tens_apply]
  unfold prodD
  rw [Finset.sum_insert hw, Finset.prod_insert hw, hp]
  by_cases h : IsHalf (a w + ∑ v ∈ s, a v) y
  · rw [if_pos h, if_pos (hiff.1 h), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h'), zero_mul]

theorem prodD_congr (a : ι → AE D) {Ψ Ψ' : ι → WO S T → ℂ} {s : Finset ι} (h : ∀ w ∈ s, Ψ w = Ψ' w) :
    prodD a Ψ s = prodD a Ψ' s := by
  funext y
  unfold prodD
  rw [Finset.prod_congr rfl fun w hw => congrFun (h w hw) _]

theorem prodD_sb {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) Λ (Ψ w)) (s : Finset ι) : IsSBHalf (∑ w ∈ s, a w) Λ (prodD a Ψ s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prodD_empty a Ψ Λ, Finset.sum_empty]
    exact GlobalTheory.isSBHalf_halfInd _ _
  | insert w s hw ih =>
    rw [prodD_insert ho Ψ hw, Finset.sum_insert hw, add_comm]
    exact Factor.isSBHalf_tens (sum_mul_zero ho hw) (hi w) (hΛ w) ih (hΨ w)

theorem prodD_ind {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) (s : Finset ι) :
    prodD a (fun w => halfInd (a w) Λ) s = halfInd (∑ w ∈ s, a w) Λ := by
  induction s using Finset.induction_on with
  | empty => rw [prodD_empty a _ Λ, Finset.sum_empty]
  | insert w s hw ih =>
    rw [prodD_insert ho _ hw, Finset.sum_insert hw, add_comm, ih]
    have h := HalfOff.tens_vac (sum_mul_zero ho hw) (hi w) Λ (hΛ w)
    rwa [one_smul, one_smul] at h

theorem exists_chain [Fintype ι] {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0)
    (hi : ∀ w, a w * a w = a w) (hinf : ∀ w, infPart D (a w) = 0) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (Ψ w)) {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ w, a w) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (prodD a Ψ Finset.univ) f) :
    ∃ V : Finset ι → WO S T → ℂ, V ∅ = f₀ ∧ V Finset.univ = f ∧ (∀ s, IsThetaFunO ψ S T (V s)) ∧
      ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1 (V s) (Ψ w)
        (V (insert w s)) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hΛ : ∀ w, ∀ u ∈ (latO S T ΛS ΛT fun _ => True), a w • u ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun w u hu => GlobalTheory.CosetRow.smul_mem_latO_idem _ _ (hi w) hu
  let mix : Finset ι → ι → WO S T → ℂ := fun s w =>
    if w ∈ s then Ψ w else halfInd (a w) (latO S T ΛS ΛT fun _ => True)
  have hmix : ∀ s w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (mix s w) := fun s w => by
    by_cases h : w ∈ s
    · simp only [mix, if_pos h]; exact hΨ w
    · simp only [mix, if_neg h]; exact GlobalTheory.isSBHalf_halfInd _ _
  have hV0 : Tm (prodD a (mix ∅) Finset.univ) = f₀ := by
    rw [prodD_congr a (Ψ' := fun w => halfInd (a w) (latO S T ΛS ΛT fun _ => True))
      (fun w _ => if_neg (Finset.notMem_empty w)), prodD_ind ho hi hΛ]
    have h := hTm.vac
    rwa [one_smul] at h
  have hstep : ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1
      (Tm (prodD a (mix s) Finset.univ)) (Ψ w) (Tm (prodD a (mix (insert w s)) Finset.univ)) := by
    intro s w hw
    have hne : w ∉ Finset.univ.erase w := Finset.notMem_erase w _
    have hu : (Finset.univ : Finset ι) = insert w (Finset.univ.erase w) :=
      (Finset.insert_erase (Finset.mem_univ w)).symm
    have e1 : prodD a (mix s) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w))
        (halfInd (a w) (latO S T ΛS ΛT fun _ => True)) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne]
      simp only [mix, if_neg hw]
    have e2 : prodD a (mix (insert w s)) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w)) (Ψ w) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne, prodD_congr a (Ψ := mix (insert w s)) (Ψ' := mix s) fun v hv => by
        have hvw : v ≠ w := Finset.ne_of_mem_erase hv
        simp only [mix, Finset.mem_insert, hvw, false_or]]
      simp only [mix, if_pos (Finset.mem_insert_self w s)]
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) ((∑ v ∈ Finset.univ.erase w, a v) + a w)
        (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
      rwa [Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    have hM := Factor.isPlaceModel_tensR D ψ S T _ (a w) _ _ _ f₀ Tm (sum_mul_zero ho hne) (hi w) (hΛ w)
      (fun _ _ => Iff.rfl) (prodD_sb ho hi hΛ (hmix s) (Finset.univ.erase w)) hTm'
    rw [e1, e2]
    exact ⟨⟨_, hM⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT (hi w) (hinf w) hM hT' (hΨ w)⟩
  refine ⟨fun s => Tm (prodD a (mix s) Finset.univ), hV0, ?_, fun s => ?_, hstep⟩
  · rw [hall Tm hTm]
    exact congrArg Tm (prodD_congr a fun w hw => if_pos hw)
  · induction s using Finset.induction_on with
    | empty => beta_reduce; rw [hV0]; exact h₀
    | insert w s hw ih => exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hstep s w hw) ih

theorem idemAt_of_single {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) : Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [Finset.sum_singleton]
  exact hes w (Finset.mem_singleton_self w)

theorem sum_eq {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {a : P → AE D}
    (ha : ∀ w, IsIdemSum (a w) {w.1}) : ∑ w, a w = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P es]
  exact Finset.sum_congr rfl fun w _ => by
    rw [GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (idemAt_of_single (ha w)), GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w.1 w.2)]

theorem orth {a b : AE D} {v w : Pl D.host.E} (ha : IsIdemSum a {v}) (hb : IsIdemSum b {w}) (h : v ≠ w) : a * b = 0 := by
  have h1 := cpt_of_isIdemAt (idemAt_of_single ha)
  have h2 := cpt_of_isIdemAt (idemAt_of_single hb)
  refine ae_ext ?_ fun Q => ?_
  · rw [map_mul, GlobalTheory.PlaceVec.idemSum_infPart ha, zero_mul, map_zero]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hQ : Q = v
    · rw [h2.2 Q (hQ ▸ h), mul_zero]
    · rw [h1.2 Q hQ, zero_mul]

theorem map_cpt_smul {a : AE D} {w : Pl D.host.E} (ha : IsIdemSum a {w}) {m n : ℕ} (y : Mx D m n) :
    ((a • y).map fun x => cpt w (toEAf D x)) = y.map fun x => cpt w (toEAf D x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, map_mul, (cpt_of_isIdemAt (idemAt_of_single ha)).1, one_mul]

theorem subset_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ fd hfd eL heL
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have ho : ∀ v w, v ≠ w → eL v * eL w = 0 := fun v w h => orth (heL v) (heL w) fun h' => h (Subtype.ext h')
  have hi : ∀ w, eL w * eL w = eL w := fun w => GlobalTheory.PlaceVec.idemSum_mul_self (heL w)
  have hinf : ∀ w, infPart D (eL w) = 0 := fun w => GlobalTheory.PlaceVec.idemSum_infPart (heL w)
  have hsum := sum_eq he heL
  have key : ∀ j : Fin D.R.m, ∃ V : Finset (locPl ch.G t) → Sch ch.G (.down t D.R.m j), V ∅ = ch.rm.vT D.R.m j ∧
      V Finset.univ = fd j ∧ (∀ S, IsThetaFunO ch.W.ψ _ _ (V S)) ∧
      ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S)) := by
    intro j
    have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    let Ψ : locPl ch.G t → WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ := fun w y =>
      if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0
    have hΨ : ∀ w, IsSBHalf (eL w) (latO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
        (ch.G.latS (.mu t D.R.m j) : Set _) (ch.G.latT (.mu t D.R.m j) : Set _) fun _ => True) (Ψ w) := by
      intro w
      have hin : ∀ v : ({w.1} : Finset (Pl D.host.E)), v.1 ∈ locPl ch.G t := fun v => by
        rw [Finset.mem_singleton.1 v.2]; exact w.2
      have hSB := GlobalTheory.VecsLast.isSBHalf_frames hS hT hβS hβT (heL w) (fun v hv => hAA v (hin ⟨v, hv⟩))
        (fun v => GlobalTheory.VecsLast.coordHom ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
        (fun v z => GlobalTheory.VecsLast.coordHom_int_iff ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)
        (fun v => depthAt ch.G v.1) (fun v => φ ⟨v.1, hin v⟩ (.theta D.R.m j))
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).1)
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).2)
      haveI : Subsingleton ({w.1} : Finset (Pl D.host.E)) :=
        ⟨fun a b => Subtype.ext ((Finset.mem_singleton.1 a.2).trans (Finset.mem_singleton.1 b.2).symm)⟩
      convert hSB using 1
      funext y
      rw [Fintype.prod_subsingleton _ ⟨w.1, Finset.mem_singleton_self _⟩]
      rfl
    have hprod : prodD eL Ψ Finset.univ = fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0 := by
      funext y
      unfold prodD
      rw [hsum]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun w _ => ?_) rfl
      refine (if_pos (Factor.half_of_idem (hi w) y)).trans ?_
      exact congrArg (fun z => φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)) (map_cpt_smul (heL w) y)
    obtain ⟨V, h1, h2, h3, h4⟩ := exists_chain ch.W.ψ_std ch.W.θ_is hS hT ho hi hinf hΨ
      (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta (f := fd j) (by rw [hsum, hprod]; exact (hfd j).2)
    exact ⟨V, h1, h2, h3, fun S w hw => ⟨hΨ w, h4 S w hw⟩⟩
  choose V h1 h2 h3 h4 using key
  exact ⟨fun S j => V j S, funext h1, funext h2, fun S j => h3 j S, fun S w hw j => h4 j S w hw⟩

end GlobalTheory.SubsetVecs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MixCondT

variable {D : D7}

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixT_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (c • f) y = c • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  simp only [GlobalTheory.MixModel.Check.mixT_eq, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext a
  ring

theorem isHalf_of_wittHyperbolic_inclusion {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} {e : AE D} {w : WO S T₀}
    (h : IsHalf e (d.inc0 S w)) : IsHalf e w := by
  have hw : w = d.p0 ⬝ d.inc0 S w := by rw [HypDec.wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul]
  intro i j
  rw [hw]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem mul_eq_zero_real_fin {m k n : ℕ} {r : Mx D m k} {ξ : Mx D k n} (hr : r.map (finPart D) = 0)
    (hξ : MxAt (fun _ => True) ξ) : r ⬝ ξ = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have h1 : finPart D (r i l) = 0 := by
    have := congrFun (congrFun hr i) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  have h2 : infPart D (ξ l j) = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 (hξ l j)).1
  rw [mul_comm]
  exact GlobalTheory.RatHalfDense.mul_eq_zero_of_parts h2 h1

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vT : VolM D σ V₀.rank) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ), p.Is dV dW x ψ → ∀ (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ), VacG ψ V₀ W₀ p.Γ₀ g → IsThetaFunO ψ V₀ W g' → (∀ y', dW.mixT V₀ ψ vT.μ vT.𝓕 g' y' = β₂ y' • g) → (∀ η ∈ p.B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β₂ (z + b) = β₂ z) → (∀ z, β₂ z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ p.B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η) → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') ∧ (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') ∧ IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vT p x y hp β₂ g g' hgv hg' hmix hinv hsupp
  have L := GlobalTheory.HeisTarget.main D ψ hψ V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol g' hg'
  have inj : ∀ f f' : WO V₀ W → ℂ, IsThetaFunO ψ V₀ W f → IsThetaFunO ψ V₀ W f' →
      (∀ y', dW.mixT V₀ ψ vT.μ vT.𝓕 f y' = dW.mixT V₀ ψ vT.μ vT.𝓕 f' y') → f = f' :=
    fun f f' hf hf' h => (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V₀ W f f' hf hf').2 W₀ σ dW vT h
  have th : ∀ u, IsThetaFunO ψ V₀ W (heisO ψ V₀ W u g') := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ hξ
    have hξf : MxAt (fun _ => True) ξ := hp.b₁.fin ξ hξ
    have key : ∀ z, symplO V₀ W (dW.incAdj V₀ z) (dW.incX V₀ ξ) =
        -Algebra.trace (AF D.host.F) (AE D) (z ⬝ ξ).trace := fun z => by
      rw [GlobalTheory.OrientedHeis.symplO_skew, HypDec.symplO_incX_incAdj]
    refine inj _ _ (th _) (GlobalTheory.OrientedHeis.theta_smul _ hg') fun y' => ?_
    rw [L.1 ξ y', mixT_smul, hmix y']
    by_cases hb : β₂ y' = 0
    · simp only [hb, zero_smul, smul_zero]
    obtain ⟨r, hr, η, hη, he⟩ := hsupp y' hb
    have hη1 : ψ (symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ)) = 1 := by
      rw [GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv,
        (hp.dualB' η (hp.b₂.fin η hη)).1 hη ξ hξ, inv_one]
    have hsplit : y' = y + r + (y' - (y + r)) := by abel
    have e1 : symplO V₀ W (dW.incAdj V₀ y') (dW.incX V₀ ξ) =
        symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ) + symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ) := by
      rw [← he, key, key, key]
      conv_lhs => rw [hsplit]
      rw [Matrix.add_mul, Matrix.add_mul, mul_eq_zero_real_fin hr hξf, add_zero, Matrix.trace_add, map_add, neg_add]
    rw [e1, AddChar.map_add_eq_mul, hη1, mul_one]
  · intro η hη
    obtain ⟨b, hb⟩ := incAdj_surj dW V₀ η
    rw [← hb]
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [GlobalTheory.MixModel.Check.mixT_heis_incAdj, hmix, hmix, hinv η hη b hb y']
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    rw [← map_nsmul]
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.1 w hw]
  · intro e he u hu hh
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.2 e he w hw (isHalf_of_wittHyperbolic_inclusion dW hh)]

end GlobalTheory.MixCondT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi : ∀ D : D7, VanBF D := by
  first | exact @GlobalTheory.Asc.vanBF | exact GlobalTheory.Asc.vanBF | (intros; apply GlobalTheory.Asc.vanBF <;> assumption)
end

