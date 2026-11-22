import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem standingHypotheses_of_glob0_nodes_Tr_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD →
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' →
      Glob0 D x eps CD Cg → Nodes D x eps →
      (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) →
      StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  intro eps CD he he52 hCD C' Cl Cg hCl hClD
  obtain ⟨x1, h1⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD C'
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD Cl
  obtain ⟨x3, h3⟩ := GlobalTheory.T.globalRankNumberBounds_rootDiscriminant_clauses eps CD he he52 hCD Cl hCl
  obtain ⟨x4, h4⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he52 hCD Cl hCl
  obtain ⟨x5, h5⟩ := GlobalTheory.T.globalRankNumberBounds_gaps_exceed eps CD he he52 hCD Cl hCl
  refine ⟨max x1 (max x2 (max x3 (max x4 x5))), fun x hx D large₂ cT CT hL h8 G N hT => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hx4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have R := G.nums
  obtain ⟨a1, -, -, -, -, -, -, -⟩ := h1 x hx1 _ _ _ _ _ R
  obtain ⟨-, a2, a3, a4, a5, -, -, -⟩ := h2 x hx2 _ _ _ _ _ R
  obtain ⟨c1, c2, c3⟩ := h3 x hx3 _ _ _ _ _ R
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := h4 x hx4 _ _ _ _ _ R
  have e := h5 x hx5 _ _ _ _ _ R (D.R.r : ℝ) k_le_r r_le_two_k
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hb : large₂.sc.b = bx x eps := by
    show Real.exp large₂.sc.L = Real.exp (x ^ eps)
    rw [hL]
  have hrd := G.rd_lo
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hbj : ∀ τ j, 1 ≤ j → j ≤ D.R.m → Real.sqrt (bx x eps) ≤ bOne D τ j ∧ bOne D τ j ≤ bx x eps ^ 2 := by
    intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ j (by omega)]
    exact N.b_win τ ⟨j, by omega⟩
  have hrS : (D.R.rS : ℝ) = (D.R.m : ℝ) / 2 - 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have h' : D.R.rS + 1 = a := by unfold Ranks.rS; omega
    have e1 : (D.R.rS : ℝ) + 1 = a := by exact_mod_cast h'
    have e2 : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    linarith
  rw [hb] at hT
  unfold StandingHypotheses
  dsimp only
  rw [hb, hL]
  refine ⟨h8, a1, by exact_mod_cast R.mf, by exact_mod_cast R.fk, by rw [hrS]; exact a2, a3, a4, ?_, ?_, c2, c3,
    (G.g_win 0).1, (G.g_win 0).2, (G.g_win 1).1, (G.g_win 1).2, ?_, ?_, ?_, ?_, d7 hClD, ?_, ?_, hT, a5, hCl⟩
  · intro τ j h1 h2
    exact le_trans d2 (hbj τ j h1 h2).1
  · rw [hv, Real.log_div (by linarith) (by norm_num)]
    exact c1
  · intro τ j h1 h2
    rw [Real.rpow_two]
    exact ⟨le_trans d3 (hbj τ j h1 h2).1, (hbj τ j h1 h2).2⟩
  · intro τ
    have a := N.bm τ
    have e' : D.R.m = D.R.m - 1 + 1 := by omega
    have b := bOne_succ τ (D.R.m - 1) (by omega)
    rw [← e'] at b
    have b0 : bOne D τ 1 = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := bOne_succ τ 0 (by omega)
    rw [b, b0]
    exact a
  · intro u τ
    have e1 : uOne D u τ 1 = uFirst D τ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 k_pos, D.hcW_first u τ k_pos]
      rfl
    rw [e1]
    by_cases ht : Top D τ
    · exact le_trans (N.top τ ht).2.1 d6
    · have o := (G.off τ ht).2.1
      have v0 := (G.cloud τ ⟨0, by omega⟩).2
      have v0' : vFirst D τ ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) := v0
      linarith
  · rw [hv]; linarith
  · intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ (j + 1) (by omega), bOne_succ τ j (by omega)]
    have g := G.gap τ j (by omega)
    push_cast at g
    linarith [e.2.2.2]
  · intro τ i h
    by_cases c1 : i.1 + 1 < D.R.k - 1
    · rw [lamS_lo τ i (by omega), lamS_lo τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 (by omega),
        vOne_succ τ (i.1 + 1) c1]
      have g := D.s.cloud_gap D.u₀ τ i.1 c1
      simp only [D.hcW_v] at g
      have g' := congrArg (fun q : ℚ => (q : ℝ)) g
      push_cast at g'
      linarith [e.1]
    · by_cases c2 : i.1 < D.R.k - 1
      · rw [lamS_lo τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 c2]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = 0 + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ 0 (by omega)]
        have v0 := (G.cloud τ ⟨i.1, c2⟩).1
        have b0 := (N.b_win τ ⟨0, by omega⟩).1
        linarith [e.2.1]
      · have hi := i.isLt
        rw [lamS_hi τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = (i.1 - (D.R.k - 1) + 1) + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ (i.1 - (D.R.k - 1)) (by omega), bOne_succ τ (i.1 - (D.R.k - 1) + 1) (by omega)]
        have g := G.gap τ (i.1 - (D.R.k - 1)) (by omega)
        push_cast at g
        linarith [e.2.2.1]

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.EichlerUnip

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

noncomputable def eich (σ w : S.V) (t : E) : S.V →ₗ[E] S.V :=
  LinearMap.id - (S.hT σ).smulRight w + (S.hT w).smulRight σ - t • (S.hT w).smulRight w

theorem eich_apply (σ w : S.V) (t : E) (x : S.V) :
    eich S σ w t x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  simp only [eich, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, mul_smul]

theorem herm (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← LinearMap.isSymm_def.mp S.herm x y, starRingEnd_apply]

theorem eich_inv (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x : S.V) : eich S (-σ) w (star t) (eich S σ w t x) = x := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add, map_neg, map_smul,
    LinearMap.neg_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero]
  rw [← ht]
  module

theorem eich_isom (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) (x y : S.V) :
    S.hT (eich S σ w t x) (eich S σ w t y) = S.hT x y := by
  have hσw : S.hT σ w = 0 := by rw [herm, hwσ, star_zero]
  rw [eich_apply, eich_apply]
  simp only [map_sub, map_add, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sub_apply,
    LinearMap.add_apply, smul_eq_mul, hw, hwσ, hσw, mul_zero, sub_zero, add_zero, starRingEnd_apply,
    star_mul']
  rw [herm S w x, herm S σ x, ← ht]
  ring

noncomputable def eichE (σ w : S.V) (t : E) (hw : S.hT w w = 0) (hwσ : S.hT w σ = 0)
    (ht : t + star t = S.hT σ σ) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (eich S σ w t) (eich S (-σ) w (star t))
    (LinearMap.ext fun x => by
      have := eich_inv S (-σ) w (star t) hw (by simp [hwσ]) (by simp [← ht, add_comm]) x
      simpa using this)
    (LinearMap.ext fun x => eich_inv S σ w t hw hwσ ht x)

theorem integral_of_unimodular {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, (o : E) = S.hT x y := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hΛ
  have h1 : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hΛ]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one] at h1
  obtain ⟨o, ho⟩ := h1 x hx
  exact ⟨o, ho⟩

theorem smul_mem_of {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : ∃ o : 𝓞 E, (o : E) = c) {x : S.V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  have h := Λ.smul_mem o hx
  rw [← algebraMap_smul E o x] at h
  exact h

theorem eich_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {σ w : S.V} {t : E}
    (hσ : σ ∈ Λ) (hw : w ∈ Λ) (ht : ∃ o : 𝓞 E, (o : E) = t) {x : S.V} (hx : x ∈ Λ) :
    eich S σ w t x ∈ Λ := by
  rw [eich_apply]
  obtain ⟨a, ha⟩ := integral_of_unimodular S hΛ hσ hx
  obtain ⟨b, hb⟩ := integral_of_unimodular S hΛ hw hx
  obtain ⟨o, ho⟩ := ht
  have hob : ∃ c : 𝓞 E, (c : E) = t * S.hT w x := ⟨o * b, by rw [← ho, ← hb]; rfl⟩
  exact Λ.sub_mem (Λ.add_mem (Λ.sub_mem hx (smul_mem_of S ⟨a, ha⟩ hw)) (smul_mem_of S ⟨b, hb⟩ hσ))
    (smul_mem_of S hob hw)

theorem star_int {t : E} (ht : ∃ o : 𝓞 E, (o : E) = t) : ∃ o : 𝓞 E, (o : E) = star t := by
  obtain ⟨o, rfl⟩ := ht
  exact ⟨⟨star (o : E), (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem iso_X {r : ℕ} {T : E} (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) :
    S.hT x y = 0 := by
  have key : ∀ a, ∀ v ∈ Submodule.span E (Set.range F.fl.e), S.hT (F.fl.e a) v = 0 := by
    intro a v hv
    induction hv using Submodule.span_induction with
    | mem u hu => obtain ⟨b, rfl⟩ := hu; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  have key2 : ∀ u ∈ Submodule.span E (Set.range F.fl.e), S.hT u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨a, rfl⟩ := hu; exact key a y hy
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key2 x hx

theorem mem_orth {U : Submodule E S.V} {y : S.V} : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem exists_eichler (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) {r : ℕ} {T : E} (F : LFlag S r T)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (σ : S.V) (hσ : σ ∈ Lrep Λ F)
    (w : S.V) (hw : w ∈ XLam Λ F) :
    ∃ n ∈ NLam Λ F, ∃ t : E, (∀ x ∈ Xsp F, n x = x) ∧
      ∀ x, n x = x - S.hT σ x • w + S.hT w x • σ - (t * S.hT w x) • w := by
  obtain ⟨hσΛ, hσX⟩ := Submodule.mem_inf.mp hσ
  obtain ⟨hwΛ, hwX⟩ := Submodule.mem_inf.mp hw
  have hσX' : σ ∈ orth S (Xsp F) := hσX
  have hwX' : w ∈ Xsp F := hwX
  have hww : S.hT w w = 0 := iso_X S F hwX' hwX'
  have hwσ : S.hT w σ = 0 := (mem_orth S).mp hσX' w hwX'
  have hσσ : star (S.hT σ σ) = S.hT σ σ := (herm S σ σ).symm
  obtain ⟨oσ, hoσ⟩ := integral_of_unimodular S hΛ hσΛ hσΛ
  have ht : (θ : E) * S.hT σ σ + star ((θ : E) * S.hT σ σ) = S.hT σ σ := by
    rw [star_mul', hσσ]
    linear_combination (S.hT σ σ) * hθ
  have htI : ∃ o : 𝓞 E, (o : E) = (θ : E) * S.hT σ σ := ⟨θ * oσ, by rw [← hoσ]; rfl⟩
  have hfix : ∀ x ∈ Xsp F, eich S σ w ((θ : E) * S.hT σ σ) x = x := by
    intro x hx
    have h1 : S.hT σ x = 0 := by rw [herm, (mem_orth S).mp hσX' x hx, star_zero]
    have h2 : S.hT w x = 0 := iso_X S F hwX' hx
    rw [eich_apply, h1, h2]
    simp
  refine ⟨eichE S σ w _ hww hwσ ht, ?_, _, hfix, fun x => eich_apply S σ w _ x⟩
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · change ∀ x y, S.hT (eich S σ w _ x) (eich S σ w _ y) = S.hT x y
    exact fun x y => eich_isom S σ w _ hww hwσ ht x y
  · apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact eich_mem S hΛ hσΛ hwΛ htI hy
    · intro y hy
      refine ⟨(eichE S σ w _ hww hwσ ht).symm y, ?_, by simp⟩
      exact eich_mem S hΛ (Λ.neg_mem hσΛ) hwΛ (star_int htI) hy
  · intro j x hx
    have hxX : x ∈ Xsp F := Submodule.span_mono (Set.image_subset_range _ _) hx
    change eich S σ w _ x - x ∈ _
    rw [hfix x hxX, sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have h2 : S.hT w x = 0 := (mem_orth S).mp hx w hwX'
    have : eich S σ w ((θ : E) * S.hT σ σ) x - x = -(S.hT σ x • w) := by
      rw [eich_apply, h2]
      module
    change eich S σ w _ x - x ∈ _
    rw [this]
    exact (Xsp F).neg_mem ((Xsp F).smul_mem _ hwX')

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eichler_mem_unipotent : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → ∀ σ ∈ Lrep Λ F, ∀ w ∈ XLam Λ F, ∃ n ∈ NLam Λ F, ∃ t : D.host.E, (∀ x ∈ Xsp F, n x = x) ∧ ∀ x, n x = x - (hS D).hT σ x • w + (hS D).hT w x • σ - (t * (hS D).hT w x) • w := by
  intro D T F Λ hΛ σ hσ w hw
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.TraceOne.exists_trace_one D 2 Nat.prime_two
  refine exists_eichler (hS D) θ ?_ F Λ hΛ σ hσ w hw
  have h := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hθ
  simp only [map_add, map_one, GlobalTheory.InertSign.sgO_coe] at h
  rw [GlobalTheory.NormSum.AdLattice.star_eq_conj D]
  exact h

end GlobalTheory.EichlerUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PolarSqCompare
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_qf_le_sum_sq {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
  have h1 : 0 ≤ ∑ i : Fin P, ‖z (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h2 : 0 ≤ ∑ j : Fin Q, ‖z (Sum.inr j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  rw [Fintype.sum_sum_type]
  simp only [qf, Complex.normSq_eq_norm_sq]
  rw [abs_le]
  constructor <;> linarith

theorem sq_compare_left {T S N r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 3 * r < 1 - s) (h1 : N ≤ T + S)
    (h : T ^ 2 + 2 * S < s * r ^ 2) : N ^ 2 + 2 * S < r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hs : s < 1 := by linarith
  have hsr : s * r ^ 2 < r ^ 2 := by nlinarith
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hT2 : T ^ 2 < r ^ 2 := by nlinarith
  have hTr : T < r := by nlinarith
  have hN2 : N * N ≤ (T + S) * (T + S) := mul_self_le_mul_self hN h1
  have a1 : T * S ≤ r * S := mul_le_mul_of_nonneg_right hTr.le hS
  have a2 : r * (2 * S) ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hS2.le hr0.le
  have a3 : (2 * S) * (2 * S) ≤ r ^ 2 * r ^ 2 := mul_self_le_mul_self (by linarith) hS2.le
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 3 * r * r ^ 2 < (1 - s) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem sq_compare_right {T S N E r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 11 * r < s - 1) (h1 : E ≤ N + S) (h2 : T ≤ 2 * E)
    (h3 : T ≤ 2 → T - T ^ 3 / 16 ≤ E)
    (h : N ^ 2 + 2 * S < r ^ 2) : T ^ 2 + 2 * S < s * r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hNr : N < r := by nlinarith
  have hrr : r ^ 2 < r / 2 := by nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  have hT3r : T ≤ 3 * r := by linarith
  have hTE : T - T ^ 3 / 16 ≤ E := h3 (by linarith)
  have hc1 : T * T ≤ 3 * r * (3 * r) := mul_self_le_mul_self hT hT3r
  have hc2 : T * T * T ≤ 3 * r * (3 * r) * (3 * r) := mul_le_mul hc1 hT3r hT (by positivity)
  have hr3 : r ^ 2 * r ≤ r ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hr1.le (sq_nonneg r)
  have hb0 : 0 ≤ S + T ^ 3 / 16 := by positivity
  have hb2 : S + T ^ 3 / 16 ≤ 2 * r ^ 2 := by nlinarith
  have hTNb : T ≤ N + (S + T ^ 3 / 16) := by linarith
  have hT2 : T * T ≤ (N + (S + T ^ 3 / 16)) * (N + (S + T ^ 3 / 16)) :=
    mul_self_le_mul_self hT hTNb
  have a1 : N * (S + T ^ 3 / 16) ≤ r * (S + T ^ 3 / 16) :=
    mul_le_mul_of_nonneg_right hNr.le hb0
  have a2 : r * (S + T ^ 3 / 16) ≤ r * (2 * r ^ 2) := mul_le_mul_of_nonneg_left hb2 hr0.le
  have a3 : (S + T ^ 3 / 16) * (S + T ^ 3 / 16) ≤ (2 * r ^ 2) * (2 * r ^ 2) :=
    mul_self_le_mul_self hb0 hb2
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 11 * r * r ^ 2 < (s - 1) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem polar_sq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  intro P Q P' Q' e t ht
  have ht0 : 0 < t := by linarith
  have hA : 0 < 1 - t⁻¹ ^ 2 := by
    have h1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have h2 : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  have hB : 0 < t ^ 2 - 1 := by nlinarith
  have hc : 0 < min (1 / 2 : ℝ) (min ((1 - t⁻¹ ^ 2) / 3) ((t ^ 2 - 1) / 11)) :=
    lt_min (by norm_num) (lt_min (div_pos hA (by norm_num)) (div_pos hB (by norm_num)))
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hc)] with r hr
  obtain ⟨hr0, hrc⟩ := hr
  simp only [Set.mem_Ioi, Set.mem_Iio] at hr0 hrc
  have hr1 : r < 1 / 2 := lt_of_lt_of_le hrc (min_le_left _ _)
  have hr2 : 3 * r < 1 - t⁻¹ ^ 2 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr3 : 11 * r < t ^ 2 - 1 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  rintro ⟨θ, z⟩ hu
  simp only [Set.mem_Ioo] at hu
  have hθ : |θ| ≤ Real.pi := abs_le.mpr ⟨hu.1.le, hu.2.le⟩

  have hq : |sg (e none) * qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> rw [h] <;> simpa using abs_qf_le_sum_sq z
  have hρ1 := (abs_sqrt_sub_one_le (sg (e none) * qf z)).trans hq
  have hw1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hpt : ptSq e (polarPt e (θ, z)) =
      ‖(Real.sqrt (1 - sg (e none) * qf z) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 +
        2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [ptSq, polarPt_none, polarPt_some]
  have htan : tanSq (θ, z) = |θ| ^ 2 + 2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [tanSq, sq_abs]
  obtain ⟨hb1, hb2, hb3⟩ := exp_bounds θ hθ
  rw [hpt, htan]
  generalize Real.sqrt (1 - sg (e none) * qf z) = ρ at hρ1 ⊢
  generalize Complex.exp ((θ : ℂ) * Complex.I) = w at hw1 hb1 hb2 hb3 ⊢
  generalize ∑ i, ‖z i‖ ^ 2 = S at hρ1 ⊢
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hρ1
  have hdiff : ‖(ρ : ℂ) * w - w‖ = |ρ - 1| := by
    have : (ρ : ℂ) * w - w = ((ρ - 1 : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hNE : ‖(ρ : ℂ) * w - 1‖ ≤ |θ| + S := by
    have := norm_sub_le_norm_sub_add_norm_sub ((ρ : ℂ) * w) w 1
    rw [hdiff] at this
    linarith
  have hEN : ‖w - 1‖ ≤ ‖(ρ : ℂ) * w - 1‖ + S := by
    have := norm_sub_le_norm_sub_add_norm_sub w ((ρ : ℂ) * w) 1
    rw [norm_sub_rev w ((ρ : ℂ) * w), hdiff] at this
    linarith
  constructor
  · intro h
    rw [mul_pow] at h
    exact sq_compare_left (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr2 hNE h
  · intro h
    rw [mul_pow]
    exact sq_compare_right (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr3 hEN hb2 hb3 h

end GlobalTheory.PolarCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_measure_real_diagonal : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) → ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) → μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  first | exact @GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | exact GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | (intros; apply GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGeneratorStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_different_eq_localGenerator : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  first | exact @GlobalTheory.LocDiffGen.span_different_eq | exact GlobalTheory.LocDiffGen.span_different_eq | (intros; apply GlobalTheory.LocDiffGen.span_different_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  first | exact @GlobalTheory.St.G.split_components | exact GlobalTheory.St.G.split_components | (intros; apply GlobalTheory.St.G.split_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIsotropicFlagMovesStepIntoPrev
section
open Formalism.MainNotions.S

namespace GlobalTheory

theorem unipRadical_moves_step_into_prev :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
      [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V]
      [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
      (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ j : ℕ, j ≤ r → ∀ v ∈ Fr.Fj j,
        n v - v ∈ Fr.Fj (j - 1) ∧ n.symm v - v ∈ Fr.Fj (j - 1) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn j hj v hv
  have hs := Formalism.MainNotions.BridgeLemma.mem_NSet_of_mem_N Fr hn
  exact ⟨hs.2.1 j hj v hv, Formalism.MainNotions.BridgeLemma.NSet_inv_Fj Fr hs j hj v hv⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBoundStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 12 * n * rkR ε < c → ‖w‖ = 1 → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → ∀ x y : UJ ε, ∫ m, ⟪w, σ (umat (x * m * y)) w⟫_ℂ ∂ν = 0 := by
  first | exact @GlobalTheory.ConstTermZero.constant_term_zero | exact GlobalTheory.ConstTermZero.constant_term_zero | (intros; apply GlobalTheory.ConstTermZero.constant_term_zero <;> assumption)
end

