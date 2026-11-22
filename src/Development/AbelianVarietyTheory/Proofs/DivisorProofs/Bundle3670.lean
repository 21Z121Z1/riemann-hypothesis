import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3666
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassSumFunctionsThetaMembers
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKernelsPIsogeniesHarrisTaylorCharP
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_nef_volume_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.NefUpper.main | exact GlobalTheory.NefUpper.main | (intros; apply GlobalTheory.NefUpper.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalized
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.root_unit {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1 := by
  have hQ : ζ ∈ Qbar := by
    have : IsIntegral ℚ ζ := IsIntegral.of_pow hn (h ▸ isIntegral_one)
    exact mem_algebraicClosure_iff.2 this.isAlgebraic
  refine ⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩
  have h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h3 : lamC lam ζ = lam ⟨ζ, hQ⟩ := by simp [lamC, hQ]
  have h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
  rw [h3]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.BotFormula.bottom_formula : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := GlobalTheory.T.exists_bottom_triple_period_const hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := GlobalTheory.T.exists_bottom_triple_period_const_dual hPr hK hM hI hB
  obtain ⟨cC, hC⟩ := GlobalTheory.T.exists_constant_triple_coefficient hPr.minguezThetaGL hPr hK hM hI hB
  obtain ⟨cD, hD⟩ := GlobalTheory.T.bottom_triangle_root_of_unity_twist hPr
  refine ⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨CA, xA, hA⟩ := hA ε CF hCF.1.1.1
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF hCF.1.1.2
  obtain ⟨CC, xC, hC⟩ := hC ε CF hCF.1.2
  obtain ⟨CD, xD, hD⟩ := hD ε CF hCF.2
  refine ⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  simp only [max_le_iff] at hC0 hx
  have hA := hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G
  have hB' := hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G
  have hC := hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G
  have hD := hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G
  intro W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀
  obtain ⟨X, ζ, hX, hβ, hζ, hc⟩ := hD W hψ i j A A' WW X₀ c0 hX₀ hc₀
  obtain ⟨Ω, hΩ, HA⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', hΩ', HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, hκ₀, HC⟩ := hC W hψ i j A A' WW X _ hX hc
  refine ⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩
  obtain ⟨uA, huA, huAQ, huAu, HA⟩ := HA s Q P P' hP
  obtain ⟨uB, huB, huBQ, huBu, HB⟩ := HB s Q P P' hP
  obtain ⟨n, hn, hζn⟩ := hζ s
  obtain ⟨hz0, hzQ, hzu⟩ := GlobalTheory.BotFormula.root_unit hn hζn
  have ea : P.a = A.rank := hP.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hP.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have ed' : P'.d = WW.rank := hP.rank.2.2.2.trans ed
  obtain ⟨M, M', hMM, HC⟩ := HC s Q δ t0 P P' hP ea ea' ed ed'
  refine ⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩
  · rw [GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul,
      huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  have key : ∀ T, starRingEnd ℂ (P.coord h T) =
      Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T' := by
    intro T
    rw [HA ea ed h g hg T, HC g T]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T']
    ring
  refine ⟨key, fun T' => ?_⟩
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) =
      ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'') := by
    intro T'' T; push_cast; ring
  simp_rw [e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]
  simp [mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NonVanBottom

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  omega

theorem exists_ne_zero_of_integral {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ}
    (h : (∫ y in S, ‖f y‖ ^ 2 ∂ν) ≠ 0) : ∃ y, f y ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (by simp [hc])

theorem exists_ne_zero_of_norm_formula {Y : Type} [MeasurableSpace Y] {ν : Measure Y} {S : Set Y} {f : Y → ℂ} {c : ℂ}
    {Λ : ℂ → ℂ} {a b : ℤ} (hc : c ≠ 0) (hΛ : ∀ s : ℤ, a ≤ s → s ≤ b → Λ s ≠ 0)
    (h : ((∫ y in S, ‖f y‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc a b, Λ s) : ∃ y, f y ≠ 0 := by
  refine exists_ne_zero_of_integral (ν := ν) (S := S) fun h0 => ?_
  have hp : ∏ s ∈ Icc a b, Λ s ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => hΛ s (mem_Icc.1 hs).1 (mem_Icc.1 hs).2
  rw [h0, Complex.ofReal_zero] at h
  exact mul_ne_zero hc hp h.symm

theorem nonvan : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
      IsBottomTri W i j X → ∀ t : T, (∃ P h, X.I W.ψ W.θ t P h ≠ 0) ∧ ∃ P' h, X.I' W.ψ W.θ t P' h ≠ 0 := by
  intro hP hK hM hL
  obtain ⟨a1, h1⟩ := GlobalTheory.T.petersson_norm_hecke_product hP
  obtain ⟨a2, h2⟩ := GlobalTheory.T.bottom_triangle_polynomial_factor hP.howeDualityReal hP hK hM hL
  obtain ⟨a3, h3⟩ := hL
  refine ⟨max (max a1 a2) a3, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCF)
  obtain ⟨C3, x3, k3⟩ := h3 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max (max C1 C2) C3, max (max x1 x2) x3, fun C hC D large₂ he hx hr T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩
  have n1 := k1 C (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX t
  have n2 := k2 C (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx) hr T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Λ, hΛ, hne⟩ := ((k3 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G) i j).1 t
  have hh : ((h0 D i j : ℕ) : ℤ) ≤ (halfRank D i j : ℤ) := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨P, ν, 𝓕, c, hc, -, -, hf⟩ := n1
  obtain ⟨Pi, p, p', J, -, ⟨P', hP'⟩, hJ, hI, hI'⟩ := n2
  obtain ⟨y, hy⟩ := exists_ne_zero_of_norm_formula hc (fun s hs hs' => hne s hs (hs'.trans hh)) (hf Λ hΛ)
  refine ⟨⟨P, y, hy⟩, P', ?_⟩
  obtain ⟨lam, hlam⟩ := hI t
  have hinj : Function.Injective (J t) := by
    refine (hJ t).resolve_left fun h0 => hy ?_
    rw [hlam P, h0]
    simp
  by_contra hc'
  push_neg at hc'
  apply hP'
  apply hinj
  rw [← hI' t P', map_zero]
  exact funext hc'

end GlobalTheory.NonVanBottom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Core

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

set_option maxHeartbeats 4000000 in

theorem core (hA : IsAbelianScheme A₀) {O : Type} [CommRing O] (act : O → (A₀ ⟶ A₀)) [∀ c, IsMonHom (act c)]
    (ρ' : O →+* Module.End k (HdR A₀)) (hρ' : ∀ c h, ρ' c h = push (dp0 k) (𝟙 _) (act c) h)
    (ω : O) (r : k) {a : ℕ} (χ : Fin a → O → k) (hχ : ∀ i i', i ≠ i' → ∃ c, χ i c ≠ χ i' c)
    {d : ℕ} (hd : 0 < d) (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (E' : Fin d → Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ j e, e ∈ E' j ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f j (fstC A₀ e) ∈ Fil A₀))
    (hlift : ∀ j, ∀ x ∈ Fil A₀, ∃ e ∈ E' j, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f j x)
    (hstab : ∀ j c, ∀ e ∈ E' j,
      push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) e ∈ E' j)
    (hlie : ∀ j e, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E' j →
      ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀,
        (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) (w i) -
          algebraMap k (TrivSqZeroExt k k) (χ i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (he : push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
        (act ω) e - algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f) :
    ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀,
      (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
          (act c) (w i) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (χ i c) • w i ∈ GlobalTheory.HTGlue.glueFil A₀ f) ∧
        e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f := by
  rw [push_sub_mem_glueFil_iff] at he
  obtain ⟨he1, he2⟩ := he

  choose ee hee1 hee2 using fun j : Fin d ↦ exists_of_coords (V := k) hA (fstC A₀ e)
    (LinearMap.proj j ∘ₗ sndC A₀ e)
  have hEj : ∀ j, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) (ee j) -
      algebraMap k (TrivSqZeroExt k k) r • ee j ∈ E' j := fun j ↦ by
    rw [push_sub_mem_iff (f j) (E' j) (hE j), hee1, hee2]
    exact ⟨he1, he2 j⟩
  choose W hW1 hW2 using fun j ↦ hlie j (ee j) (hEj j)
  have hα := fun j i c ↦ (push_sub_mem_iff (f j) (E' j) (hE j) _ _ _).1 (hW1 j i c)
  have hs : ∀ j, fstC A₀ e - ∑ i, fstC A₀ (W j i) ∈ Fil A₀ ∧
      ((LinearMap.proj j ∘ₗ sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (W j i) : HdR A₀)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (W j i)) ∈ Fil A₀ := fun j ↦ by
    have := (sub_sum_mem_iff (f j) (E' j) (hE j) _ _).1 (hW2 j)
    rwa [hee1, hee2] at this

  have hfstab : ∀ j c, ∀ x ∈ Fil A₀,
      push (dp0 k) (𝟙 _) (act c) (f j x) - f j (push (dp0 k) (𝟙 _) (act c) x) ∈ Fil A₀ := by
    intro j c x hx
    obtain ⟨e1, he1E, h1, h2⟩ := hlift j x hx
    have := ((push_mem_iff (f j) (E' j) (hE j) (act c) e1).1 (hstab j c e1 he1E)).2
    rwa [h1, h2] at this

  let j₀ : Fin d := ⟨0, hd⟩
  have hFst : ∀ c, ∀ x ∈ Fil A₀, ρ' c x ∈ Fil A₀ := fun c x hx ↦ by rw [hρ']; exact push_mem_Fil _ hx
  have hglue : ∀ j i, fstC A₀ (W j i) - fstC A₀ (W j₀ i) ∈ Fil A₀ := fun j ↦
    GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod k (HdR A₀) O ρ' (Fil A₀) hFst a χ hχ (fun i ↦ fstC A₀ (W j i) - fstC A₀ (W j₀ i))
      (fun i c ↦ by
        rw [hρ', map_sub, smul_sub, sub_sub_sub_comm]; exact sub_mem (hα j i c).1 (hα j₀ i c).1)
      (by
        rw [Finset.sum_sub_distrib]
        have := sub_mem (hs j₀).1 (hs j).1
        convert this using 1
        abel)

  choose w hw1 hw2 using fun i ↦ exists_of_coords (V := Fin d → k) hA (fstC A₀ (W j₀ i))
    (LinearMap.pi fun j ↦ (sndC A₀ (W j i) : HdR A₀) + f j (fstC A₀ (W j₀ i) - fstC A₀ (W j i)))
  refine ⟨w, fun i c ↦ ?_, ?_⟩
  · rw [push_sub_mem_glueFil_iff, hw1, hw2]
    refine ⟨(hα j₀ i c).1, fun j ↦ ?_⟩
    rw [LinearMap.proj_pi]
    have hδ : fstC A₀ (W j₀ i) - fstC A₀ (W j i) ∈ Fil A₀ := by
      have := neg_mem (hglue j i); rwa [neg_sub] at this
    have := add_mem (hα j i c).2 (hfstab j c _ hδ)
    convert this using 1
    simp only [map_add, map_sub, map_smul, smul_add, smul_sub]
    abel
  · rw [sub_sum_mem_glueFil_iff]
    simp only [hw1, hw2, LinearMap.proj_pi]
    refine ⟨(hs j₀).1, fun j ↦ ?_⟩
    convert (hs j).2 using 1
    simp only [Finset.sum_add_distrib, map_sub, map_sum, Finset.sum_sub_distrib]
    abel

end Core

set_option maxHeartbeats 1000000 in

theorem lie_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ), 0 < d → ∀ (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) b.ρ • e ∈ E' j → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) (b.t i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) b.ρ • e ∈ GlobalTheory.HTGlue.glueFil o₀.A f → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) (b.t i c) • w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f) ∧ e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d hd f E' hcompl hred hlift hstab hlie e he
  haveI hact : ∀ c : 𝓞 D.F, IsMonHom (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) := fun c ↦ o₀.act.hom _
  have L1j := fun j ↦ GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates k o₀.A o₀.ab (f j) (E' j) (hcompl j) (hred j) (hlift j)
  have hχ : ∀ i i', i ≠ i' → ∃ c : 𝓞 D.F, tk (b.t i c) ≠ tk (b.t i' c) := by
    intro i i' hii'
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (Set.range fun x ↦ b.t i x - b.t i' x) ≤ RingHom.ker tk := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hcon x, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker tk := hle (b.comax i i' hii' ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hlift' : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, fstC o₀.A e = x ∧ (sndC o₀.A e : HdR o₀.A) = f j x := by
    intro j x hx
    obtain ⟨e1, he1, h⟩ := hlift j x hx
    refine ⟨e1, he1, ?_, ?_⟩ <;> ext c
    · rw [fstC_apply, h c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · rw [sndC_apply, h c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact core o₀.ab (fun c : 𝓞 D.F ↦ o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O)) (fun _ _ ↦ rfl) D.ω (tk b.ρ)
    (fun i c ↦ tk (b.t i c)) hχ hd f E' L1j hlift' (fun j c e he ↦ hstab j _ e he) hlie e he

end GlobalTheory.HTGlueLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassSumFunctionsThetaMembersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_sum_functions_theta_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  first | exact @GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | exact GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | (intros; apply GlobalTheory.GSep.ClassSumFun.exists_classSum_fun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTTors

open GlobalTheory.IwLevel GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

def actF (o : Obj b N s) : Out.RingAct o.A (𝓞 D.F) :=
  ⟨fun c => o.act.act (algebraMap (𝓞 D.F) D.O c), fun _ => o.act.hom _,
   by rw [map_one]; exact o.act.one,
   fun _ _ => by rw [map_mul]; exact o.act.mul _ _,
   fun _ _ => by rw [map_add]; exact o.act.add _ _⟩

theorem killedBy_map (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    KilledBy (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy (actF o) w x := by
  rw [Ideal.map, killedBy_span]
  exact Set.forall_mem_image

theorem inSub_ker {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {T : Over S} (x : T ⟶ A) :
    InSub (pullback.fst f η[B]) x ↔ x ≫ f = 1 := by
  refine ⟨?_, fun h => ⟨KerGrp.lift f x h, KerGrp.lift_fst _ _ _⟩⟩
  rintro ⟨y, rfl⟩
  rw [Category.assoc, KerGrp.fst_comp, MonObj.comp_one]

theorem comp_lift_eq_one {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) (a c : A ⟶ A) :
    x ≫ lift a c = 1 ↔ x ≫ a = 1 ∧ x ≫ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (· ≫ fst A A) h
    have h2 := congrArg (· ≫ snd A A) h
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.one_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, MonObj.one_comp]
    · rw [Category.assoc, lift_snd, h2, MonObj.one_comp]

theorem killedBy_pair {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A (𝓞 D.F)) (g e : 𝓞 D.F)
    {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span {g, e}) x ↔ x ≫ lift (ρ.act g) (ρ.act e) = 1 := by
  rw [killedBy_span, comp_lift_eq_one]
  simp

theorem htTorsion : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o w hw
  obtain ⟨g, e, 𝔟, hg0, he, hf, hmul, hp⟩ := GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField D.F p (Fact.out) w hw
  have hI2 := fun c hc => GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor p D R b N S s o c hc
  let ρ := actF o
  have hρ : ∀ c, IsMonHom (ρ.act c) := ρ.hom

  have hgw : g ∈ w * 𝔟 := by rw [hmul]; exact Ideal.mem_span_singleton_self g
  have hgw1 : g ∈ w := Ideal.mul_le_left (I := w) (J := 𝔟) hgw
  have hgw2 : g ∈ 𝔟 := Ideal.mul_le_right (I := w) (J := 𝔟) hgw
  have hw' : w = Ideal.span {g, e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = a * (1 - e) + a * e := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : a * (1 - e) ∈ w * 𝔟 := Ideal.mul_mem_mul ha hf
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw1, Set.singleton_subset_iff.2 he⟩)
  have h𝔟' : 𝔟 = Ideal.span {g, 1 - e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = e * a + a * (1 - e) := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : e * a ∈ w * 𝔟 := Ideal.mul_mem_mul he ha
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw2, Set.singleton_subset_iff.2 hf⟩)
  have hcop : w ⊔ 𝔟 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 D.F) = e + (1 - e) := by ring
    rw [h1]
    exact Submodule.add_mem_sup he hf
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmul
    exact hg0 hmul

  let f₁ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act e)
  let f₂ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act (1 - e))
  letI := KerGrp.grp f₁
  have h₁ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₁ η[o.A ⊗ o.A]) x ↔ KilledBy ρ w x := by
    intro T x; rw [inSub_ker, hw', killedBy_pair]
  have h₂ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₂ η[o.A ⊗ o.A]) x ↔ KilledBy ρ 𝔟 x := by
    intro T x; rw [inSub_ker, h𝔟', killedBy_pair]
  have h₃ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst (ρ.act g) η[o.A]) x ↔ KilledBy ρ (w * 𝔟) x := by
    intro T x; rw [inSub_ker, hmul, killedBy_span]; simp
  have d₃ : IsIsogDeg (toUnit (ker (ρ.act g)))
      (Ideal.absNorm w ^ (D.m * D.n) * Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
    rw [← mul_pow, ← map_mul, hmul, Ideal.absNorm_span_singleton]
    exact (hI2 g hg0).ker
  have d₂ : IsIsogDeg (toUnit (ker f₂)) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) :=
    GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor p D R b N S s o hI2 𝔟 hp _ (pullback.fst f₂ η[o.A ⊗ o.A]) inferInstance
      (fun T x => by rw [h₂, killedBy_map])
  have hpos : 0 < Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have d₁ := GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product S o.A (𝓞 D.F) ρ w 𝔟 hcop _ _ _ (pullback.fst f₁ η[o.A ⊗ o.A])
    (pullback.fst f₂ η[o.A ⊗ o.A]) (pullback.fst (ρ.act g) η[o.A]) inferInstance inferInstance inferInstance
    h₁ h₂ h₃ _ _ hpos d₃ d₂
  refine ⟨ker f₁, KerGrp.grp f₁, pullback.fst f₁ η[o.A ⊗ o.A], KerGrp.isMonHom_fst f₁, inferInstance,
    by rw [← pow_mul]; exact d₁, fun T x => by rw [h₁, killedBy_map]⟩

end GlobalTheory.HTTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerChartOfHeatOperatorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_chart_of_heat_operators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (O : Type) [CommRing O] [StarRing O] [Module O P.D.toPre.X] (oa : P.D.toPre.OAct O) (Y : Ray oa) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  first | exact @GlobalTheory.ChartKSBracket.exists_isKS_of_heat | exact GlobalTheory.ChartKSBracket.exists_isKS_of_heat | (intros; apply GlobalTheory.ChartKSBracket.exists_isKS_of_heat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKernelsPIsogeniesHarrisTaylorCharPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kernels_pIsogenies_harrisTaylor_charP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (s : Sp k ⟶ Sp R) (o : Obj b N s), Set.Finite {P : ∀ T : Over (Sp k), (T ⟶ o.A) → Prop | ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ P = fun T x => x ≫ ψ = 1} := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerFin.finite_kernels) | (exact GlobalTheory.UPel.HT.ES.KerFin.finite_kernels) | (intros; apply GlobalTheory.UPel.HT.ES.KerFin.finite_kernels  <;> assumption)
end

