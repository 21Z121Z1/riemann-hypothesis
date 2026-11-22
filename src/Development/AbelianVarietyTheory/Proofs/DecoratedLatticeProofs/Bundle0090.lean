import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory.CritLevelSize

open Formalism.FourierDecayAlt Finset GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem num_bound_pow (k m r e : ℕ) (B P ae c ka : ℝ) (hm : m = 2 * r + 2) (he : 2 * e + 40 ≤ m) (hk : 5 ≤ k)
    (hB : (k : ℝ) ^ 40 ≤ B) (hP : B ^ m ≤ P) (ha0 : 0 < ae) (ha : ae ≤ B ^ e) (hc : 1 / 8 ≤ c) (hka0 : 0 < ka)
    (hka : ka ≤ 4) : (k : ℝ) ^ (3 * r) ≤ c * (ka ^ (m - 1))⁻¹ * P / ae := by
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h1 : ka ^ (m - 1) ≤ (k : ℝ) ^ (m - 1) := pow_le_pow_left₀ hka0.le (by linarith) _
  have h2 : (8 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h3 : (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 ≤ B ^ (m - e) := by
    rw [← pow_add, ← pow_add]
    calc (k : ℝ) ^ (3 * r + (m - 1) + 2) ≤ (k : ℝ) ^ (40 * (m - e)) := pow_le_pow_right₀ (by linarith) (by omega)
      _ = ((k : ℝ) ^ 40) ^ (m - e) := pow_mul _ _ _
      _ ≤ B ^ (m - e) := pow_le_pow_left₀ (by positivity) hB _
  have h4 : B ^ (m - e) * B ^ e = B ^ m := by rw [← pow_add]; congr 1; omega
  have h5 : (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae ≤ P :=
    calc (k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae
        ≤ (k : ℝ) ^ (3 * r) * (k : ℝ) ^ (m - 1) * (k : ℝ) ^ 2 * B ^ e := by gcongr
      _ ≤ B ^ (m - e) * B ^ e := by gcongr
      _ ≤ P := h4 ▸ hP
  rw [le_div_iff₀ ha0]
  calc (k : ℝ) ^ (3 * r) * ae = 1 / 8 * (ka ^ (m - 1))⁻¹ * ((k : ℝ) ^ (3 * r) * ka ^ (m - 1) * 8 * ae) := by
        field_simp
    _ ≤ c * (ka ^ (m - 1))⁻¹ * P := by
        gcongr

theorem le_pow_ceil (b B u cb Cu : ℝ) (hcb : 0 < cb) (hb : 1 ≤ b) (hB : b ^ cb ≤ B) (hu : u ≤ b ^ Cu) :
    u ≤ B ^ ⌈max Cu 0 / cb⌉₊ := by
  have hB1 : 1 ≤ B := le_trans (Real.one_le_rpow hb hcb.le) hB
  have hM : 0 ≤ max Cu 0 / cb := div_nonneg (le_max_right _ _) hcb.le
  calc u ≤ b ^ Cu := hu
    _ ≤ b ^ max Cu 0 := Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)
    _ = (b ^ cb) ^ (max Cu 0 / cb) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    _ ≤ B ^ (max Cu 0 / cb) := Real.rpow_le_rpow (by positivity) hB hM
    _ ≤ B ^ ((⌈max Cu 0 / cb⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil _)
    _ = B ^ ⌈max Cu 0 / cb⌉₊ := Real.rpow_natCast _ _

set_option maxHeartbeats 1600000 in

theorem tcrit_low_of_sizes (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hcb : 0 < cb)
    (hCl : 2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40 ≤ Cl)
    (hVV : ∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) :
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  rintro ⟨hH, hD, -⟩ u τ
  obtain ⟨-, -, -, -, -, -, hmL, hbD, -, -, -, hg0, -, hg1, -, hbj, -, hu, hv, hDel, hgap, -, -, hClm, -⟩ := hH
  obtain ⟨hvw, -, ha, ha', hl, htop, -⟩ := hD
  set e : ℕ := ⌈max Cu 0 / cb⌉₊ + 4 with he
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hCl40 : (40 : ℝ) ≤ Cl := by linarith
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm := GlobalTheory.CritLevel.m_eq D.R
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hmR : (40 : ℝ) ≤ D.R.m := hCl40.trans hClm
  have hme : 2 * e + 40 ≤ D.R.m := by
    have : ((2 * e + 40 : ℕ) : ℝ) ≤ D.R.m := by push_cast; linarith
    exact_mod_cast this
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlog : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hD1 : (1 : ℝ) ≤ D.s.Del :=
    le_trans (Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hf) hL)
      (by linarith)) hDel
  set B := bOne D τ 1 with hBdef
  have hB : (D.R.k : ℝ) ^ 40 ≤ B := by
    refine le_trans ?_ ((le_max_left _ _).trans (hbj τ 1 le_rfl (by omega)).1)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hCl40)
  have hBcb : large₂.sc.b ^ cb ≤ B := (le_max_right _ _).trans (hbj τ 1 le_rfl (by omega)).1
  have hk2 : 3 * (D.R.k : ℝ) ≤ B := by
    refine le_trans ?_ hB
    calc 3 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hB1 : 1 ≤ B := by linarith
  have hkD : 0 < (D.R.k : ℝ) * D.s.Del := by positivity
  have hBD : 40 * (D.R.m * D.R.k * D.s.Del) ≤ B :=
    le_trans (mul_le_mul_of_nonneg_right hCl40 (by positivity)) (hbD τ 1 le_rfl (by omega))
  have hBD' : 8 * ((D.R.k : ℝ) * D.s.Del) ≤ B := by nlinarith
  have hg : ∀ j, 1 ≤ j → j < D.R.m → bOne D τ j + 1 ≤ bOne D τ (j + 1) := fun j h1 h2 => by
    have h3 := hgap τ j h1 h2
    have h4 : (1 : ℝ) ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hn)) (one_le_pow₀ hf)) hL
    linarith
  have hmono : ∀ j, 1 ≤ j → j ≤ D.R.m → B ≤ bOne D τ j := by
    intro j h1
    induction j, h1 using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j h1 ih => intro h2; linarith [ih (by omega), hg j h1 h2]
  set c := GlobalTheory.CritLevel.cfg D u τ with hc
  have hv1 : c.v 1 = vOne D τ 1 := GlobalTheory.CritLevel.cfg_v D u τ le_rfl (by omega)
  have htp : c.top = true ↔ IsTop D τ := by simp [hc, GlobalTheory.CritLevel.cfg]
  have hOk : c.Ok := by
    refine ⟨show 4 ≤ D.R.k by omega, hm2, hD1, (hvw τ _ (by omega) le_rfl).1, ?_, hB1, hg, ?_, fun h => ?_⟩
    · rw [hv1]; exact (hvw τ 1 le_rfl (by omega)).2
    · rw [hv1]; exact ha u τ
    · have := htop τ (htp.1 h)
      exact ⟨this.2, show bTop D τ ≤ B - 3 by linarith [this.1]⟩
  have hSm : c.Small large₂.sc.b := by
    refine ⟨hb, ?_, fun j h1 h2 => ?_, ?_⟩
    · show 4 * (D.R.m : ℝ) * D.R.k * D.s.Del / B ≤ 1 / 10
      rw [div_le_iff₀ (by linarith)]
      linarith
    · have := (hbj τ j h1 h2).2
      rwa [Real.rpow_two] at this
    · show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / D.R.k ≤ 1 / 10
      rw [hlog, div_le_iff₀ (by linarith)]
      have h1 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by gcongr; nlinarith
      have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by gcongr
      have h3 : 0 ≤ (D.R.m : ℝ) * large₂.sc.L := by positivity
      linarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 2 * Real.pi ≤ gg D := by
    have h1 : (5 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
    unfold gg
    nlinarith
  have hV : 0 < VV D τ := mul_pos (D.dsig_pos τ) (prod_pos fun i _ => by positivity)
  have hlow := Final.sz_tcritLower c D.R.rS large₂.sc.b (GlobalTheory.CritLevel.letters D u) D.host.ka D.host.rdE (gg D) (VV D τ) hOk hm hSm
    (GlobalTheory.CritLevel.isWord_letters D u) (by linarith) (by rw [hrd]; unfold Host.ka; field_simp) hgg (by
      show (1 - 1 / 2) * Sz.Vand (D.R.k + D.R.m - 1) c.lam ≤ _
      rw [← GlobalTheory.CritLevel.cfg_lam D u τ, ← hVV]
      linarith)
  change _ * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * _ / _ ≤
    Sz.Tcrit D.R.k D.R.m _ _ _ _ (Sz.Vand D.R.k _) at hlow
  rw [← GlobalTheory.CritLevel.cfg_u D u τ (hl u τ), ← GlobalTheory.CritLevel.tcrit_eq D (by linarith)] at hlow
  have hg0' : 0 < gg D := by linarith
  have hvone := (hvw τ 1 le_rfl (by omega)).1
  have hBe : B ≤ B ^ e := le_self_pow₀ hB1 (by omega)
  have hae : 0 < c.aeff ∧ c.aeff ≤ B ^ e ∧ 0 ≤ c.vthp ∧ c.vthp ≤ 1 := by
    unfold Sz.Cfg.aeff Sz.Cfg.vthp
    by_cases ht : IsTop D τ
    · rw [if_pos (htp.2 ht), if_pos (htp.2 ht)]
      obtain ⟨t1, t2⟩ := htop τ ht
      have ha0 : 0 < uOne D u τ 1 := by linarith [ha u τ]
      have hbp : 0 < bTop D τ := by linarith
      have hu1 : uOne D u τ 1 ≤ B ^ ⌈max Cu 0 / cb⌉₊ := le_pow_ceil _ _ _ _ _ hcb hb hBcb (hu u τ)
      have hpe : B ^ ⌈max Cu 0 / cb⌉₊ * B ≤ B ^ e := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hB1 (by omega)
      refine ⟨div_pos (mul_pos ha0 hbp) hkD, ?_, ?_, ?_⟩
      · show uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) ≤ B ^ e
        refine (div_le_self (by positivity) (by nlinarith)).trans ?_
        calc uOne D u τ 1 * bTop D τ ≤ B ^ ⌈max Cu 0 / cb⌉₊ * B := by gcongr; linarith
          _ ≤ B ^ e := hpe
      · show 0 ≤ 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ
        positivity
      · show 4 * (D.R.k : ℝ) * D.s.Del / bTop D τ ≤ 1
        rw [div_le_one hbp]
        linarith
    · rw [if_neg (fun h => ht (htp.1 h)), if_neg (fun h => ht (htp.1 h)), hv1]
      have h1 := ha u τ
      have h2 := ha' u τ ht
      refine ⟨?_, ?_, le_rfl, zero_le_one⟩
      · show 0 < uOne D u τ 1 - vOne D τ 1
        linarith
      · show uOne D u τ 1 - vOne D τ 1 ≤ B ^ e
        linarith
  have hc1 : 1 / 8 ≤ Sz.cOne c large₂.sc.b := by
    unfold Sz.cOne
    have h1 := Real.add_one_le_exp (-(2 * c.m * Real.log large₂.sc.b / c.k))
    have h2 := hSm.hmu
    rw [le_div_iff₀ (by linarith [hae.2.2.1])]
    linarith [hae.2.2.2]
  have hP : B ^ D.R.m ≤ c.prodb := by
    have := prod_le_prod (s := Icc 1 D.R.m) (f := fun _ => B) (g := bOne D τ) (fun _ _ => by linarith)
      fun j hj => hmono j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel] at this
    exact this
  have hka0 : 0 < D.host.ka := div_pos hpi (by linarith)
  have hka : D.host.ka ≤ 4 := (div_le_self hpi.le hv).trans hpi4
  have hnum := num_bound_pow D.R.k D.R.m D.R.rS e B c.prodb c.aeff _ _ hm hme (by omega) hB hP
    hae.1 hae.2.1 hc1 hka0 hka
  rw [Real.rpow_neg hg0'.le, Real.rpow_natCast, le_inv_mul_iff₀ (by positivity)]
  refine le_trans ?_ hlow
  calc gg D ^ D.R.m * (D.R.k : ℝ) ^ (3 * D.R.rS)
      ≤ gg D ^ D.R.m * (Sz.cOne c large₂.sc.b * (D.host.ka ^ (D.R.m - 1))⁻¹ * c.prodb / c.aeff) := by gcongr
    _ = _ := by ring

end GlobalTheory.CritLevelSize

theorem GlobalTheory.CritLevelSize.tcritLow_sizes : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro cb Cu hcb
  exact ⟨2 * ((⌈max Cu 0 / cb⌉₊ + 4 : ℕ) : ℝ) + 40, fun D large₂ C' Cl Cg cT CT C0 hCl hVV =>
    GlobalTheory.CritLevelSize.tcrit_low_of_sizes D large₂ C' Cl Cg cb Cu cT CT C0 hcb hCl hVV⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClassesStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.BasesFin.bases_finite_classes | exact GlobalTheory.BasesFin.bases_finite_classes | (intros; apply GlobalTheory.BasesFin.bases_finite_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZonalCoeff

open Formalism.UG

theorem apply_heckeVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) (ρ : Representation ℂ G V) (x : V)
    (l : V →ₗ[ℂ] ℂ) : l (GlobalTheory.LFun.heckeVec ρ K h x) = ∑ᶠ c : G ⧸ K, h c.out * l (ρ c.out x) :=
  (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => by simp)

theorem eq_zero_of_doset_sum {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) {w : G → ℂ}
    (hw : IsBiInv K w) (g : G) (e : ∑ᶠ c : G ⧸ K, dosetInd ℂ K g c.out * w c.out = 0) : w g = 0 := by
  classical
  have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ g).2
  have hmem : ∀ c ∈ hfin.toFinset, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c hc => by
    by_contra hn
    exact (hfin.mem_toFinset.1 hc) (Set.indicator_of_notMem hn _)
  have h1 : ∀ c ∈ hfin.toFinset, dosetInd ℂ K g c.out * w c.out = w g := fun c hc => by
    obtain ⟨a, ha, b, hb, e'⟩ := DoubleCoset.mem_doubleCoset.1 (hmem c hc)
    rw [dosetInd, Set.indicator_of_mem (hmem c hc), Pi.one_apply, one_mul, e']
    exact hw ⟨a, ha⟩ ⟨b, hb⟩ g
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun c hc =>
      hfin.mem_toFinset.2 (left_ne_zero_of_mul hc),
    Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul] at e
  refine (mul_eq_zero.1 e).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), ?_⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine hfin.mem_toFinset.2 ?_
  change dosetInd ℂ K g _ ≠ 0
  rw [dosetInd, Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩)]
  exact one_ne_zero

theorem coeff_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hx l hl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hbi : IsBiInv (KU σ n) fun g => l (ρ g x) := fun a b g => by
    beta_reduce
    rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2, hl _ a.2]
  refine ⟨fun h0 g => eq_zero_of_doset_sum hK hbi g ?_, fun h0 => ⟨fun a b g => ?_, ?_, fun h hh => ?_⟩⟩
  · have hm := Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g
    rw [← apply_heckeVec hK hm, hx.2.2 _ hm, map_smul, h0, smul_zero]
  · exact congrArg (· / l x) (hbi a b g)
  · simpa using div_self h0
  · have e := apply_heckeVec hK hh ρ x ((l x)⁻¹ • l)
    rw [hx.2.2 h hh, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h0, mul_one] at e
    rw [e]
    exact finsum_congr fun c => by simp [div_eq_inv_mul]

end GlobalTheory.ZonalCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvInertEqStdL
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvSplit
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpliStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrixStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_conjugate_transpose_matrix : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  first | exact @GlobalTheory.GramFrame.gram_frame_int | exact GlobalTheory.GramFrame.gram_frame_int | (intros; apply GlobalTheory.GramFrame.gram_frame_int <;> assumption)
end

