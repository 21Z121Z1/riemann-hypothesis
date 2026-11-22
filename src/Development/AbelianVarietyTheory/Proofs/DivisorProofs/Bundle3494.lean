import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelian
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeights
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameBerg

theorem one_le_gap_of_strictAnti {N : ℕ} {v : Fin N → ℤ} (hv : StrictAnti v) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ gap v k := by
  rw [gap, dif_pos hk]
  have := hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
  omega

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem antitone_of_gap_nonneg {N : ℕ} {v : Fin N → ℤ} (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  have key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have e : b = a := Fin.ext (by simpa using hab)
      rw [e]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < N := by omega
      have h1 := ih a ⟨(a : ℕ) + d, hc⟩ rfl
      have h2 := h ((a : ℕ) + d) (by omega)
      rw [gap, dif_pos (by omega)] at h2
      have e : b = ⟨(a : ℕ) + d + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]
      linarith
  intro a b hab
  exact key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

end GlobalTheory.FrameBerg

namespace GlobalTheory.FrameBerg

set_option maxHeartbeats 2000000 in

theorem frames_short_berg : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  intro hP2 _hDG hS hFD
  obtain ⟨C1, hC1, H1⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP2
  obtain ⟨C2, hC2, H2⟩ := GlobalTheory.T.antitone_weight_log_bound hP2
  have H0 := GlobalTheory.T.good_weight_antitone_gap hP2
  refine (((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and (wtBig_run.and hFD)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨_, _, a, ha⟩, ⟨_, _, b, hb⟩⟩, ⟨⟨_, _, c, hc⟩, ⟨_, _, d, hd⟩⟩⟩ := hh
  obtain ⟨e, he⟩ := GlobalTheory.family_sizes_eventually_large _ Fm (2 * C1 + C2 + 1)
  refine ⟨0, le_rfl, max (max a b) (max (max c d) e), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hA := ha x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi
  have hB := hb x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY
  have hW := hc x hx ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi
  have hF := hd x hx ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hle))) ι p hp i hi Y hY
  have hLM := (he x ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι).2.2.1
  clear ha hb hc hd he
  obtain ⟨h1p, h1q, hfin, -, hanti, -⟩ := hA
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, h8f, h100r, hflat, hkap, hZ12, -, -, -, hsum, -⟩ := hB
  obtain ⟨hr, hdim, -⟩ := GlobalTheory.RecGaps.gaps p (Fm.params x hx ι) i hi

  intro Zc
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i (Fm.parT x hx ι).PP⟩ with hPdef
  have hq : (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q := by omega
  have hg1 : ∀ τ, 1 ≤ gap (P.u₁ τ) ((dat p i).p - 1) := fun τ => one_le_gap_of_strictAnti (hanti τ).1 hq
  have ha1 : ∀ τ, Antitone (P.u₁ τ) := fun τ => (hanti τ).1.antitone
  have hgap2 : ∀ τ k, k + 1 < (dat p i).p + (dat p i).q → 1 ≤ gap (P.u₂ τ) k := by
    intro τ k hk
    have e : P.u₂ τ = P.u₁ τ + P.rem τ := rfl
    rw [e, gap_add]
    have := one_le_gap_of_strictAnti (hanti τ).1 hk
    have := (P.gap_rem τ k).1
    omega
  have ha2 : ∀ τ, Antitone (P.u₂ τ) := fun τ =>
    antitone_of_gap_nonneg fun k hk => (zero_lt_one.le).trans (hgap2 τ k hk)
  have hG := H0 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
  refine ⟨nonempty_cuspFrame ((hG P.u₂ ha2 fun τ => hgap2 τ _ hq).2 Zc), ?_⟩

  have hgapBig : ∀ τ, ((8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 : ℕ) : ℤ) ≤ gap (P.u₁ τ) ((dat p i).p - 1) := by
    intro τ
    refine le_trans ?_ (hW.gaps τ ((dat p i).p - 1) hq)
    have h9 : 9 * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.r.choose 2 := by
      rw [Nat.choose_two_right]
      apply (Nat.le_div_iff_mul_le two_pos).2
      have : 100 ≤ (Fm.D x ι).R.r := h100r
      have : 99 ≤ (Fm.D x ι).R.r - 1 := by omega
      nlinarith
    rw [hdim, hr]
    generalize (Fm.D x ι).R.r.choose 2 = c at h9 ⊢
    generalize ((Fm.D x ι).R.f * c + 1).choose 2 = B
    have h1 : 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ≤ (Fm.D x ι).R.f * c := by
      rw [mul_assoc, mul_comm 9, mul_assoc, mul_comm (Fm.D x ι).R.r]; exact Nat.mul_le_mul_left _ h9
    have h2 : B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3 ≤
        ((Fm.D x ι).R.f * c + 3) * (B + 4 * (Fm.D x ι).R.r + (Fm.D x ι).R.f * c + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 8 ≤ (Fm.D x ι).R.f := h8f
    have h4 : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 10 ≤ 9 * (Fm.D x ι).R.f * (Fm.D x ι).R.r := by
      have : 10 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    exact_mod_cast (h4.trans (h1.trans (by omega))).trans h2

  have hL1' : (1 : ℝ) ≤ (Fm.L x ι).sc.L := hL1
  have hZdef : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L = zBase (Fm.L x ι) := rfl
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast h8f
  have hr100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast h100r
  have hfrpos : (0 : ℝ) < ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by positivity
  have hE2 : (2 : ℝ) ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hfrE : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r ≤ Real.exp (Fm.L x ι).sc.L := by
    have := Real.exp_le_exp.2 hfr
    rwa [Real.exp_log (by exact_mod_cast hfrpos)] at this
  have hLE : (Fm.L x ι).sc.L ≤ Real.exp (Fm.L x ι).sc.L := by linarith [Real.add_one_le_exp (Fm.L x ι).sc.L]
  have hZE : zBase (Fm.L x ι) ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rw [← hZdef, sq]; exact mul_le_mul hfrE hLE (by linarith) (Real.exp_pos _).le
  have hZL : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    rw [← hZdef]
    have : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := hL1'.trans hZL
  have hkap0 : 0 ≤ kap p i := by unfold CovTop.kap sizeK; positivity
  have hkapE : kap p i ≤ Real.exp (Fm.L x ι).sc.L ^ 2 := by
    rcases hkap0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have := Real.exp_le_exp.2 hkap
      rw [Real.exp_log h0] at this
      rw [← Real.exp_nat_mul]; push_cast; linarith
  have hK1 : (1 : ℝ) ≤ kap p i / lenT p i (Fm.parT x hx ι).PP + 1 := by
    have : 0 ≤ kap p i / lenT p i (Fm.parT x hx ι).PP := div_nonneg hkap0 (Nat.cast_nonneg _)
    linarith
  have hKle : kap p i / lenT p i (Fm.parT x hx ι).PP ≤ kap p i := by
    rcases Nat.eq_zero_or_pos (lenT p i (Fm.parT x hx ι).PP) with h0 | h0
    · rw [h0]; simp [hkap0]
    · exact div_le_self hkap0 (by exact_mod_cast h0)
  have hS := hsum P.u₁ (by simp)
  have hS0 : 0 ≤ ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by positivity
  have hSE : ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤ Real.exp (7 * (Fm.L x ι).sc.L) := by
    have e7 : Real.exp (7 * (Fm.L x ι).sc.L) = Real.exp (Fm.L x ι).sc.L ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e7]
    refine hS.trans ?_
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ Real.exp (Fm.L x ι).sc.L ^ 4 := by
      calc zBase (Fm.L x ι) ^ 2 ≤ (Real.exp (Fm.L x ι).sc.L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hZE 2
        _ = _ := by ring
    have hK3 : kap p i / lenT p i (Fm.parT x hx ι).PP + 1 ≤ Real.exp (Fm.L x ι).sc.L ^ 3 := by
      nlinarith
    calc zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1)
        ≤ Real.exp (Fm.L x ι).sc.L ^ 4 * Real.exp (Fm.L x ι).sc.L ^ 3 :=
          mul_le_mul hZ2 hK3 (by linarith) (by positivity)
      _ = _ := by ring
  have hlogS : Real.log (∑ τ, ∑ k, |(P.u₁ τ k : ℝ)|) ≤ 7 * (Fm.L x ι).sc.L := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h0).2 hSE

  have ho : 391 * zBase (Fm.L x ι) ^ 2 ≤ 391 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 2 := by
    rw [hZdef]
  have hc₁ : |-GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by rw [abs_neg]; exact hflat
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := H1 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho _ hF hc₁ P.u₁ ha1 hgapBig (by linarith) Zc
  obtain ⟨f, hfn, -, hfN⟩ := exists_latFrame_of_isShortGen _ _ _ _ n w abelian₂
    (nonempty_cuspFrame ((hG P.u₁ ha1 hg1).2 Zc)) hsg
  have hb := (H2 (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) h1p h1q hfin hInR Y _ _ hY.1
    (Fm.L x ι).sc.L hL1 hM hfs hfr ho P.u₁ ha1 (by linarith) Zc).1
  rw [hZdef] at hLam hn hb

  have hMZ : 2 * C1 + C2 + 1 ≤ zBase (Fm.L x ι) := hLM.trans hZL
  have hZ35 : zBase (Fm.L x ι) ^ 3 ≤ zBase (Fm.L x ι) ^ 5 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ612 : zBase (Fm.L x ι) ^ 6 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ5 : 0 ≤ zBase (Fm.L x ι) ^ 5 := by positivity
  have hkey : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) ^ 12 := by
    have : (2 * C1 + C2) * zBase (Fm.L x ι) ^ 5 ≤ zBase (Fm.L x ι) * zBase (Fm.L x ι) ^ 5 :=
      mul_le_mul_of_nonneg_right (by linarith) hZ5
    nlinarith
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ12
  have hC1Z : C1 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  have hC2Z : C2 * zBase (Fm.L x ι) ^ 3 ≤ (Fm.parT x hx ι).PP := by nlinarith
  refine ⟨f, max abelian₂ 1, Real.exp (C2 * zBase (Fm.L x ι) ^ 3), le_max_right _ _,
    Real.one_le_exp (by positivity), ?_, ?_, ?_, fun q σ => (hfN q σ).trans (le_max_left _ _), hb⟩
  · rw [hfn]; exact hn.trans hC1Z
  · rw [Real.log_exp]; exact hC2Z
  · rcases le_total abelian₂ 1 with hl | hl
    · rw [max_eq_right hl, Real.log_one]; positivity
    · rw [max_eq_left hl]
      refine hLam.trans ?_
      have h3 : zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| ≤
          zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ zBase (Fm.L x ι) ^ 3)
        nlinarith
      have h4 : C1 * (zBase (Fm.L x ι) ^ 3 * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| + zBase (Fm.L x ι) ^ 5) ≤
          (2 * C1 * zBase (Fm.L x ι) ^ 5) * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
        have h6 := mul_le_mul_of_nonneg_left h3 hC1
        have h5 : C1 * zBase (Fm.L x ι) ^ 5 ≤ C1 * zBase (Fm.L x ι) ^ 5 * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) :=
          le_mul_of_one_le_right (by positivity) hK1
        linarith [h6, h5]
      refine h4.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
      nlinarith

end GlobalTheory.FrameBerg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLe
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem omega_finite_of_theory (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : Module.Finite k G.omega := by
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  obtain ⟨-, hs, -, hsm, -⟩ := hθ G
  haveI := T.base.finite G trivial
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) (T.M G)).FG)
  refine ⟨⟨S.image (θ G), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨m, rfl⟩ := hs y
  have hm : m ∈ Submodule.span (WittVector p k) (S : Set (T.M G)) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ : ∃ b, WittVector.frobenius b = a :=
      ⟨(WittVector.frobeniusEquiv p k).symm a, (WittVector.frobeniusEquiv p k).apply_symm_apply a⟩
    rw [hsm]
    exact Submodule.smul_mem _ _ hx

theorem range_omegaMap_le_of_range_map_le (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] {G Q H : PDivGroup p k} (q : G ⟶ Q) (f : G ⟶ H)
    (h : LinearMap.range (T.map f) ≤ LinearMap.range (T.map q)) :
    LinearMap.range (omegaMap G H f) ≤ LinearMap.range (omegaMap G Q q) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, rfl⟩ := (hθ H).2.1 v
  obtain ⟨m', hm'⟩ := h ⟨m, rfl⟩
  refine ⟨θ Q m', ?_⟩
  rw [← (hθ G).2.2.2.2 Q q m', ← (hθ G).2.2.2.2 H f m, hm']

theorem exists_comp_eq_of_colength (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) : ∀ (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H),
    G.IsConn → IsIsog q →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n →
    LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G Q H q f hG hq hn hfq
  have hω := range_omegaMap_le_of_range_map_le p T k q f hfq
  by_cases hsurj : Function.Surjective (omegaMap G Q q)
  · have hs := GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected p k G Q q hG hsurj
    obtain ⟨m, q', h1, h2⟩ := hq
    refine GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q H m q q' f h1 h2 ?_
    rw [kerIdeal_of_surjective (hs m)]
    exact (kerIdeal_le_ker_iff _ _).2 fun c => by simp
  obtain ⟨C, i1, i2, i3, i4, π, hπs, hker, hnil, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G Q q
  obtain ⟨Q₁, q₁, q₁', e1, e2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k G C π hπs
  have hqπ : kerIdeal (q.app 1) ≤ RingHom.ker π := hker ▸ le_sup_left
  have hcq := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q q C π hπs
  have hcq₁ := GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G Q₁ q₁ C π hπs
  have hcotf : cotMap (π.comp (f.app 1)) = 0 :=
    hcq.2.2 H f fun w hw => hcq.1 hqπ w (hω hw)
  have htriv := GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero p k C (H.A 1) (π.comp (f.app 1)) hnil hcotf
  have hfπ : kerIdeal (f.app 1) ≤ RingHom.ker π :=
    (kerIdeal_le_ker_iff (f.app 1) (π : G.A 1 →ₐ[k] C)).2 htriv
  have e1' : q₁ ≫ q₁' = (p : ℤ_[p]) ^ 1 • 𝟙 G := by rw [pow_one]; exact e1
  have e2' : q₁' ≫ q₁ = (p : ℤ_[p]) ^ 1 • 𝟙 Q₁ := by rw [pow_one]; exact e2
  obtain ⟨f', hf'⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ H 1 q₁ q₁' f e1' e2' (hk1 ▸ hfπ)
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k G Q₁ Q 1 q₁ q₁' q e1' e2' (hk1 ▸ hqπ)
  have hq₁ : IsIsog q₁ := ⟨1, q₁', e1', e2'⟩
  have hr' : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q₁ Q q₁ r hq₁ (hr ▸ hq)
  have hG₁ : Q₁.IsConn := GlobalTheory.T.pDivGroup_isConn_of_isogeny p k G Q₁ q₁ hq₁ hG
  have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ Q trivial trivial trivial
  have hfun' := GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G Q₁ H trivial trivial trivial
  have hmq : T.map q = T.map q₁ ∘ₗ T.map r := by rw [← hr]; exact hfun.2.1 q₁ r
  have hmf : T.map f = T.map q₁ ∘ₗ T.map f' := by rw [← hf']; exact hfun'.2.1 q₁ f'
  have hinj := (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q₁ q₁ hq₁).1
  have hfr : LinearMap.range (T.map f') ≤ LinearMap.range (T.map r) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hfq ⟨y, rfl⟩
    refine ⟨z, hinj ?_⟩
    rw [← LinearMap.comp_apply, ← hmq, hz, hmf, LinearMap.comp_apply]

  haveI := omega_finite_of_theory p T k G
  have hCq : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) = Module.finrank k (Cot k C) :=
    hcq.2.1 (hker ▸ sup_le_sup_left hfrob _) hqπ
  have hCq₁ : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q₁ q₁)) =
      Module.finrank k (Cot k C) := hcq₁.2.1 (hk1 ▸ le_sup_left) hk1.le
  have hpos : 0 < Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) := by
    haveI : Nontrivial (G.omega ⧸ LinearMap.range (omegaMap G Q q)) :=
      Submodule.Quotient.nontrivial_iff.2 fun h => hsurj (LinearMap.range_eq_top.1 h)
    exact Module.finrank_pos
  have h1 : (1 : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q₁)) := by
    refine le_trans ?_ (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G Q₁ q₁).1
    rw [hCq₁, ← hCq]
    exact_mod_cast hpos
  have hadd := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M Q₁) (T.M Q)).1 (T.map q₁) (T.map r) hinj
  rw [← hmq, hn] at hadd
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M G ⧸ LinearMap.range (T.map q₁)) ≠ ⊤ from fun h => by simp [h] at hadd)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M Q₁ ⧸ LinearMap.range (T.map r)) ≠ ⊤ from fun h => by simp [h] at hadd)
  rw [← ha, ← hb] at hadd
  rw [← ha] at h1
  have hab : n = a + b := by exact_mod_cast hadd
  have ha1 : 1 ≤ a := by exact_mod_cast h1
  obtain ⟨g, hg⟩ := ih b (by omega) Q₁ Q H r f' hG₁ hr' hb.symm hfr
  exact ⟨g, by rw [← hr, Category.assoc, hg, hf']⟩

theorem exists_comp_eq_of_range_map_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn →
    IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ T k _ _ _ G Q H q f hG hq hfq
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q hq).2.1
  exact exists_comp_eq_of_colength p T k n G Q H q f hG hq hn.symm hfq

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π := by
  first | (exact @GlobalTheory.ActFin.exists_actRep_finite) | (exact GlobalTheory.ActFin.exists_actRep_finite) | (intros; apply GlobalTheory.ActFin.exists_actRep_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem bdParam_ne_zero (k : Type) [Field k] (m e : ℕ) (i : Fin m) : bdParam k m e i ≠ 0 := fun h => by
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin e) 1)) h
  simp [bdParam, MvPowerSeries.coeff_X] at this

theorem exists_fractionRing_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ∃ fK : FractionRing A →+* FractionRing B, spMap fK ≫ jK A = jK B ≫ spMap ψ := by
  have hg : Function.Injective ((algebraMap B (FractionRing B)).comp ψ) :=
    (IsFractionRing.injective B (FractionRing B)).comp hψ
  let fK : FractionRing A →+* FractionRing B :=
    IsFractionRing.lift (K := FractionRing A) (L := FractionRing B) (g := (algebraMap B (FractionRing B)).comp ψ) hg
  have e0 : fK.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := FractionRing A) (L := FractionRing B) hg x
  refine ⟨fK, ?_⟩
  have e1 : CommRingCat.ofHom (algebraMap A (FractionRing A)) ≫ CommRingCat.ofHom fK =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B (FractionRing B)) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e0]
  have e2 := congrArg Spec.map e1
  rw [Spec.map_comp, Spec.map_comp] at e2
  exact e2

theorem exists_lift_normBl {X Z S : Scheme.{0}} (i : X ⟶ Z) (π : S ⟶ Z) (j : X ⟶ S) (J : Z.IdealSheafData)
    (hN : GlobalTheory.Poinc.IsNormBl π J) (hji : j ≫ π = i) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ X) (hy : jK R ≫ a = y ≫ i) (f : R) (hf : f ≠ 0)
    (hJ : idlAlong J a = Ideal.span {f}) : ∃ ξ : Sp R ⟶ S, jK R ≫ ξ = y ≫ j := by
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine GlobalTheory.NormBlLift.effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, -⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  obtain ⟨c, ⟨hc1, -⟩, -⟩ := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  exact ⟨c, hc1⟩

theorem taut_exists_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∃ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep k _ m e C hT
  obtain ⟨hm, hs, -⟩ := hT
  have hcF : CharZero (ChartRing k m e) := (C.b.charZero_iff C.b.injective).1 inferInstance
  haveI : CharZero k := (MvPowerSeries.C (σ := Fin m ⊕ Fin e) (R := k)).charZero
  have hAdm := GlobalTheory.MumfordChart.admissibleBase_chartRing k m e
  have hBase : GlobalTheory.Mum.Base (ChartRing k m e) := ⟨hAdm, hcF⟩
  haveI : IsIntegrallyClosed (ChartRing k m e) := hAdm.2.2.1
  obtain ⟨⟨-, -, hi, -, -, -, -⟩, -, hext, ⟨-, -, hval⟩, ⟨hbl, -, -, -, hji, -, -, -⟩, -⟩ := hU
  obtain ⟨ξZ, hξZ, -⟩ := hext _ hBase C.t ⟨C.P⟩ C.y C.gen (spMap C.b) C.y_over.symm
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) C.P.D.toPre.X
  have hPF := hpf C.P.D.toPre.X C.rank
  have hnat : ∀ i, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • C.δ i) = n := fun i =>
    hPF.exists_nat (Submodule.smul_mem _ _ (C.cone.mem i)) (fun y => by
      simpa using mul_nonneg (by positivity : (0 : ℤ) ≤ l.M') (C.cone.nonneg i y))
  choose b hb using hnat
  let a : Fin m → ℕ := fun i => d * b (Fin.cast hm.symm i)
  have hprod : ∏ i, bdParam k m e i ^ a i = ∏ i : Fin C.m, C.s i ^ (d * b i) :=
    (Fintype.prod_equiv (finCongr hm) _ _ (fun j => by simp [a, hs j])).symm
  have hI : idlAlong J ξZ = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
    refine GlobalTheory.MonoVal.eq_span_monomial_of_forall_cdvr k m e _ a fun W _ _ _ hW ψ hψi hψl => ?_
    haveI := hW.1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hne : ∀ i, ψ (C.s i) ≠ 0 := fun i h0 => by
      have : C.s i = 0 := hψi (h0.trans (map_zero ψ).symm)
      rw [hs i] at this
      exact bdParam_ne_zero k m e _ this
    choose w hw using fun i => IsDiscreteValuationRing.associated_pow_irreducible (hne i) hϖ
    obtain ⟨fK, hκ⟩ := exists_fractionRing_map ψ hψi
    obtain ⟨t, tK, P, h1, h2, be, hbe, hmono, hφ⟩ :=
      GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form Xo c φ _ hBase C W hW ψ hψi hψl ϖ hϖ w hw (spMap fK) hκ
    obtain ⟨n, hn, hIn⟩ := hval W hW ϖ hϖ (spMap ψ ≫ ξZ) (spMap fK ≫ C.y)
      (by rw [Category.assoc, ← hξZ, ← Category.assoc, hκ, Category.assoc]) t tK h1 h2 P be hbe hmono
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hIn, hprod, map_prod]
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    have hnw : n = ∑ i, w i * (d * b i) := by
      have : (n : ℝ) = ∑ i, (w i : ℝ) * (d * b i) := by
        rw [hn, hφ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
      exact_mod_cast this
    have : Associated (∏ i, ψ (C.s i ^ (d * b i))) (∏ i : Fin C.m, (ϖ ^ w i) ^ (d * b i)) :=
      Associated.prod _ _ _ fun i _ => by rw [map_pow]; exact (hw i).pow_pow
    rw [hnw]
    refine (this.trans ?_).symm
    rw [← Finset.prod_pow_eq_pow_sum]
    simp only [← pow_mul]
    exact Associated.refl _
  have hf0 : ∏ i, bdParam k m e i ^ a i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (bdParam_ne_zero k m e _)
  obtain ⟨ξ, hξ⟩ := exists_lift_normBl i π j J hbl hji _ ξZ C.y hξZ _ hf0 hI
  exact ⟨ξ, hξ.symm⟩

end GlobalTheory.UChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmLieAddPSmulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLogarithm_lie_add_p_smul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie), QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  first | exact @GlobalTheory.QLog.exists_isLie_add_smul | exact GlobalTheory.QLog.exists_isLie_add_smul | (intros; apply GlobalTheory.QLog.exists_isLie_add_smul <;> assumption)
end

