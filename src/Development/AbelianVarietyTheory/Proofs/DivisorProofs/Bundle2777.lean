import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.HodgeGapBounds

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}

theorem bar_lt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega

theorem one_le_gap_uMinus (P : WtPar Dw) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (hs : StrictAnti (P.u₁ τ)) : 1 ≤ gap (P.uMinus τ) (Dw.p - 1) := by
  have hk := bar_lt hp hq
  have h1 := P.gap_u₁ τ hk
  have hT : 0 < P.T₁ := by unfold WtPar.T₁; positivity
  have hg : 1 ≤ gap (P.u₁ τ) (Dw.p - 1) := by
    rw [gap, dif_pos hk]
    have := hs (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p - 1 + 1, hk⟩ from by
      rw [Fin.mk_lt_mk]; omega)
    omega
  rw [h1, Int.le_ediv_iff_mul_le hT, one_mul] at hg
  have hkap : gap (FlagTan.kap Dw τ) (Dw.p - 1) = 2 * ((Dw.p : ℤ) + Dw.q) - 2 := by
    simp only [gap, dif_pos hk, FlagTan.kap, Fin.val_mk]
    have := Nat.cast_sub (R := ℤ) hp
    split_ifs <;> push_cast at * <;> omega
  have hsub : gap ((P.uMinus - FlagTan.kap Dw) τ) (Dw.p - 1) =
      gap (P.uMinus τ) (Dw.p - 1) - gap (FlagTan.kap Dw τ) (Dw.p - 1) := by
    simp only [gap, dif_pos hk, Pi.sub_apply]; ring
  have hT1 : 1 ≤ P.T₁ := hT
  omega

theorem laOf_add_smul (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 s : ℤ) :
    laOf Dw a n + s • hodgeWt Dw =
      uMinus Dw a n kc c0 + (s + c0) • hodgeWt Dw + FlatLine.parWt Dw (anchor Dw a n kc) := by
  rw [← uWt_add_anchor Dw a n kc]
  simp only [uMinus, add_smul]
  abel

theorem gap_add_smul_hodge (v : AllWt.Weight Dw) (x : ℤ) (w : Psi H → ℤ) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    gap ((v + x • hodgeWt Dw + FlatLine.parWt Dw w) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + x := by
  have hk := bar_lt hp hq
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, FlatLine.parWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

theorem antitone_add_par (v : AllWt.Weight Dw) (w : Psi H → ℤ) (τ : Psi H) (h : Antitone (v τ)) :
    Antitone ((v + FlatLine.parWt Dw w) τ) :=
  fun _ _ hab => add_le_add (h hab) le_rfl

end Weights

end GlobalTheory.CovTop.HodgeGapBounds

namespace GlobalTheory.CovTop.HodgeGapBounds

theorem evidence : Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → LawsJ p.T ∧ 1 ≤ (dat p i).p ∧
    1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ Even (p.κ i).n ∧
    (∀ τ, Antitone (uM p i τ)) ∧ (∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1)) ∧
    ∀ s : ℤ, (s = -(cZero (Fm.D x ι) ((i : ℕ) + 1)) ∨ s = 0 ∨ s = cZero (Fm.D x ι) ((i : ℕ) + 1)) →
      (∀ τ, Antitone ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ)) ∧
      ∀ τ, 1 ≤ gap ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ) ((dat p i).p - 1) := by
  have hA := GlobalTheory.T.weight_parameter_strict_antitone GlobalTheory.T.size_bound_statement
  have hB := GlobalTheory.CovTop.WtShape.wtN
  unfold WtN at hB
  unfold Lifts at hA hB ⊢
  refine (hA.and hB).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi
  have b := h2 x hx ((le_max_right _ _).trans hle) ι p hp i
  obtain ⟨hp1, hq1, hdeg, -, hSA, -, hanti⟩ := a
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hgap : ∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1) := fun τ =>
    one_le_gap_uMinus _ τ hp1 hq1 (hSA τ).1
  have hant0 : ∀ τ, Antitone (uM p i τ) := fun τ => by simpa using (hanti 0 (by norm_num) τ).1
  refine ⟨p.fw.laws, hp1, hq1, hdeg, ⟨by omega, i.2⟩, b.dom.2, hant0, hgap, fun s hs => ?_⟩
  obtain ⟨t, ht3, hts⟩ : ∃ t : ℕ, t ≤ 3 ∧ s + cZero (Fm.D x ι) ((i : ℕ) + 1) = (t : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    rcases hs with hs | hs | hs
    · exact ⟨0, by norm_num, by rw [hs]; ring⟩
    · exact ⟨1, by norm_num, by rw [hs]; ring⟩
    · exact ⟨2, by norm_num, by rw [hs]; ring⟩
  rw [laOf_add_smul (kc := (Fm.D x ι).R.k - 1) (c0 := cZero (Fm.D x ι) ((i : ℕ) + 1))]
  refine ⟨fun τ => antitone_add_par _ _ τ ?_, fun τ => ?_⟩
  · rw [hts]; exact (hanti t ht3 τ).1
  · rw [gap_add_smul_hodge _ _ _ τ hp1 hq1]
    have := hgap τ
    have h2 : 0 ≤ s + cZero (Fm.D x ι) ((i : ℕ) + 1) := by rw [hts]; positivity
    exact le_add_of_le_of_nonneg this h2

end GlobalTheory.CovTop.HodgeGapBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBounds
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

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.ZedSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem bar_gap (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (hi : (i : ℕ) + 1 < D.R.m) (τ : Psi p.T.Q.H)
    (a b : Fin ((dat p i).p + (dat p i).q)) (hab : (b : ℕ) = a + 1) (hb : (b : ℕ) = (dat p i).p) :
    LevelStarExponents.h0 L ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e1 := WtShape.dat_p p i
  have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) = WtShape.sgR D t a - WtShape.sgR D t (a + 1) - 1 +
      if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
    rw [Int.cast_sub, WtShape.uW_real p i τ t ht, WtShape.uW_real p i τ t ht, hab, ← WtShape.entR_step]; ring
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have h1 := WtShape.sgR_step_low D L P t a (by omega) (by omega)
  rw [if_pos (by omega)] at hd
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast WtShape.six_le_r D.R
  linarith

abbrev wp (p : PtAt ex Csz) (i : Fin D.R.m) (PP : ℝ) : WtPar (dat p i) :=
  ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩

theorem zed_at (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (T : ParamsT D L P) (A M C1 : ℝ)
    (hS : SizeAt p i T.PP C1) (hq : ∀ u1, Quo p i T.PP u1 → u1 = (wp p i T.PP).u₁)
    (hsa : ∀ τ, StrictAnti ((wp p i T.PP).u₁ τ)) (hH : HostNum D L T.PP A M) (hW : WtNum p i T.PP)
    (hi : (i : ℕ) + 1 < D.R.m) :
    zed p i T.PP (wp p i T.PP).u₁ * (T.PP * kap p i) ≤ L.sc.b / 2 := by
  obtain ⟨hb1, -, -, -, -, hbk, hquo⟩ := hS
  obtain ⟨u0, hu0⟩ := (hquo hi).1
  have hQ : Quo p i T.PP (wp p i T.PP).u₁ := hq u0 hu0 ▸ hu0
  obtain ⟨h0', S, eta, -, -, -, -, -, hHyp⟩ := hW.hyp hi
  have hDv : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).IsDiv := (quo_iff p i T.PP h0' S eta _).1 hQ
  have hY : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).Hyp := hHyp _
  have hDp : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := hW.dim.trans T.Dp_eq.symm
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hDp]; exact Nat.ceil_le.2 (WtShape.len_le D L P T)
  obtain ⟨s1, s2, -⟩ := WtShape.spacing_ge T ((i : ℕ) + 1) _ hlen
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hb0 : 0 < L.sc.b := by linarith
  have hsb : 0 < Real.sqrt L.sc.b := Real.sqrt_pos.2 hb0
  have hw : ∀ τ, Real.sqrt L.sc.b / 2 ≤ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) := fun τ => by
    have := hW.low τ; have := hH.low; linarith
  have hrho := GlobalTheory.T.weightDegreeDefect_le_of_divided_weight _ _ (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁) (LevelStarExponents.h0 L) hY hDv hsa
    (fun τ => lt_of_lt_of_le (by positivity) (hw τ))
    (by
      show 4 * (((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + (lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1) ≤ LevelStarExponents.h0 L
      rw [eN, hDp]; simpa [cZero] using s1)
    (by
      show 24 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) ≤ LevelStarExponents.h0 L
      rw [eN]; exact s2)
    (fun τ a b hab hb => bar_gap p i P hi τ a b hab hb)
  have hrB : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ = GlobalTheory.CompHt.rhoOf (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u'
      (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u1 := by
    unfold GlobalTheory.CompHt.rhoB; congr 1; funext τ j; rw [GlobalTheory.CompHt.uPrime_apply]; rfl
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hrho' : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ ≤ 3 * (D.R.r : ℝ) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) * (2 / Real.sqrt L.sc.b))) := by
    rw [hrB]
    refine hrho.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) *
      (2 / Real.sqrt L.sc.b)) fun τ _ => ?_) (by rw [eN]; positivity)).trans_eq ?_)
    · show (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (2 * ((lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1)) / LevelStarExponents.h0 L +
          2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) /
          (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ _
      rw [eN, hDp]
      have hwp : 0 < (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) :=
        lt_of_lt_of_le (by positivity) (hw τ)
      have h2 : 1 / (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 2 / Real.sqrt L.sc.b := by
        rw [div_le_div_iff₀ hwp hsb]; linarith [hw τ]
      have h3 : 0 ≤ 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      rw [mul_one_div] at h4
      linarith
    · rw [Finset.card_univ, nsmul_eq_mul, hcard, eN]
  have hk : kap p i ≤ 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
    show ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ _
    calc ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|
        ≤ ∑ τ : Psi p.T.Q.H, ∑ k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b := by
          gcongr with τ _ k _; exact hW.up τ k
      _ = 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hcard, eN]; ring
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have h8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
    linarith
  have hD1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast WtShape.one_le_Dp T
  have hTl : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ (lenT p i T.PP : ℝ) := by
    unfold lenT; rw [hDp]; exact Nat.le_ceil _
  have hTO : (lenT p i T.PP : ℝ) ≤ T.TO := by exact_mod_cast hlen
  have hT4 : 4 * (T.Dp : ℝ) + 4 ≤ lenT p i T.PP := by
    have := hY.h1
    have h : 4 * T.Dp + 4 ≤ lenT p i T.PP := by rw [← hDp]; exact this
    exact_mod_cast h
  have hH0 : (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP ≤ LevelStarExponents.h0 L := by
    refine le_trans ?_ T.heightBound_ge_order_product
    have hP : 0 ≤ T.PP := by linarith [WtShape.forty_le_PP T]
    have : 0 ≤ (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP := by positivity
    nlinarith [T.ChT_ge]
  have hn0 : 2500 * (D.R.r : ℝ) * ((T.Dp : ℝ) + 1) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have h' : 2500 * D.R.r * (T.Dp + 1) ≤ T.TO := le_trans (by
      rw [show 2500 * D.R.r * (T.Dp + 1) = 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) by ring]; exact Nat.le_add_left _ _) h
    exact_mod_cast h'
  have hnW : (D.R.f : ℝ) * D.R.r * ((D.R.r : ℝ) + 1) ≤ T.nWn := by exact_mod_cast T.nW_lo.1
  have hP3 : T.PP ^ 3 * (T.TO : ℝ) ^ 2 ≤ Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; exact T.precision_cube_order_sq_le_sqrt
  have hsp : (T.TO : ℝ) * T.nWn ≤ D.R.r + D.R.t := by
    have h := T.split
    have h' : T.TO * T.nWn ≤ D.R.r + D.R.t := by omega
    exact_mod_cast h'
  have hNb : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ D.R.N D.R.m := by
    have h' : D.R.m * (D.R.t + 1) ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast h'
  have key := GlobalTheory.T.seven_mul_height_bound_le_half_of_parameters (T.Dp : ℝ) (lenT p i T.PP : ℝ) (GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁) T.PP (kap p i) L.sc.b
    D.R.f D.R.r D.R.m D.R.k (LevelStarExponents.h0 L) T.TO (D.R.N D.R.m) T.nWn D.R.t hD1 hb0 hf1 hm2 hmk (WtShape.r_cast D.R)
    (Nat.cast_nonneg _) (sizeK_nonneg _ _ _) hk hTl hTO hT4 hrho' hH0 hn0 hnW T.PP_nW hP3 hsp hNb
  unfold zed
  rw [hDp]
  exact key

theorem zed_size : Size → Covers fun Fm x _ ι p i Y PP _ => zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 := by
  intro hS
  have hI := GlobalTheory.T.weight_parameter_strict_antitone hS
  have hHN := GlobalTheory.CovTop.Sizes.hostN 1
  have hWN := GlobalTheory.CovTop.WtShape.wtN
  unfold Covers Lifts
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS hI) (Formalism.MainNotions.Closed.and hHN hWN)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩, ⟨C4, -, a4, h4⟩⟩ := hh
  refine ⟨0, le_rfl, max (max a1 a2) (max a3 a4), fun x hx hle ι p hp i hi Y _ => ?_⟩
  have e1 := h1 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle) ι p hp i
  have e2 := h2 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle) ι p hp i hi
  have e3 := h3 x hx (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle) ι p hp i
  have e4 := h4 x hx (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle) ι p hp i
  have key := zed_at p i (Fm.params x hx ι) (Fm.parT x hx ι) C3 1 C1 e1 e2.2.2.2.1 (fun τ => (e2.2.2.2.2.1 τ).1) e3 e4 hi
  have hb1 := e1.1
  have hbk := e1.2.2.2.2.2.1
  refine ⟨by linarith, ?_⟩
  by_contra hc
  push_neg at hc
  have : 1 / 2 * ((Fm.parT x hx ι).PP * kap p i) < _ * ((Fm.parT x hx ι).PP * kap p i) :=
    mul_lt_mul_of_pos_right hc (by linarith)
  linarith

end GlobalTheory.CovTop.ZedSz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingE8PowerDependsOnForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.PairVal

open GlobalTheory.PairingOfLam GlobalTheory.DescentPairing GlobalTheory.AdjointOfPairing

variable {S : Scheme.{0}}

theorem weilIs_of_lbIso {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {N : RigLB A}
    (cN : CubicalStr A N) (f g f' g' : B ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom f'] [IsMonHom g']
    (H : LBIso (cubeLB A ![fst B B ≫ f, snd B B ≫ g] N.L) (cubeLB A ![fst B B ≫ f', snd B B ≫ g'] N.L))
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y z : T ⟶ B) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (e : Γ(T.left, ⊤)ˣ) (he : WeilIs A N.L n (y ≫ f') (z ≫ g') e) : WeilIs A N.L n (y ≫ f) (z ≫ g) e := by
  have hyf : (y ≫ f) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hyc : (y ≫ f') ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hzg : (z ≫ g) ^ n = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  obtain ⟨e', hr⟩ := WeilCube.exists_isRatio cN n _ _ hyf hzg
  have he' := (WeilCube.weilIs_iff cN hG hA hyf hzg hr e').2 rfl
  refine (WeilCube.weilIs_iff cN hG hA hyf hzg hr e).2 (unit_ext fun p _ => ?_)
  obtain ⟨t, ht, v⟩ := exists_gen_lam hG hA cN p₀ hT f' g' n y hyc
  obtain ⟨t', ht', v'⟩ := exists_gen_lam hG hA cN p₀ hT f g n y hyf
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := val_ratio N.isLB N.isLB H _ t ht t' ht' (fst T B).left (WeilCube.surj_fst hG hB T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ
  rw [v z e hz he p J hJ, v' z e' hz he' p J hJ] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem exists_hom {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    (s : Fin 8 → ℤ) : ∃ f : B ⟶ A, IsMonHom f ∧ ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := by
  obtain ⟨f, hf, -⟩ := hP.2 B (fun a => 𝟙 B ^ s a)
  have h : ∀ (T : Over S) (x : T ⟶ B) (a : Fin 8), (x ≫ f) ≫ pr a = x ^ s a := fun T x a => by
    rw [Category.assoc, hf a]
    exact (map_zpow (PrimPic.preH (G := B) x) _ _).trans (congrArg (· ^ s a) (Category.comp_id x))
  refine ⟨f, isMonHom_of_mul f fun T x y => ?_, h⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  haveI := hP.1 a
  rw [MonObj.mul_comp, h, h, h, mul_zpow]

theorem bil_zpow {B : Over S} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M) {T : Over S}
    (m : Matrix (Fin 8) (Fin 8) ℤ) (s t : Fin 8 → ℤ) (x y : T ⟶ B) :
    PrimPic.bil (GlobalTheory.CechPic.cls M.L M.isLB) m (fun a => x ^ s a) (fun b => y ^ t b) =
      dotProduct s (m.mulVec t) • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) x y := by
  have hl : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) (u ^ k) v =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v =>
    map_zsmul (PrimPic.lamHom M cub v) k (Additive.ofMul u)
  have hr : ∀ (k : ℤ) (u v : T ⟶ B), PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u (v ^ k) =
      k • PrimPic.lam (GlobalTheory.CechPic.cls M.L M.isLB) u v := fun k u v => by
    rw [PrimPic.lam_comm, hl, PrimPic.lam_comm]
  simp only [PrimPic.bil, hl, hr, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem weilIs_of_form_eq : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L → ∀ (N : ℕ), 0 < N → ∀ (s t s' t' : Fin 8 → ℤ),
  dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
  ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
  ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
    (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
    ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c := by
  intro W _ gQ K _ _ P' B _ _ M pr hF hP hE N _ s t s' t' hst p q hp hq x y x' y' hx hy hx' hy' c hc
  letI := P'.isAb.comm
  obtain ⟨cub⟩ := hF.2.2.1
  obtain ⟨r, hr, ⟨cL⟩⟩ := GlobalTheory.PolAV_exists_cubical GlobalTheory.abelianSchemeLaws_all.1.cube P'
  obtain ⟨f, hfm, hf⟩ := exists_hom hP s
  obtain ⟨g, hgm, hg⟩ := exists_hom hP t
  obtain ⟨f', hfm', hf'⟩ := exists_hom hP s'
  obtain ⟨g', hgm', hg'⟩ := exists_hom hP t'
  have ex : x = p ≫ f := (hP.2 _ fun u => p ^ s u).unique hx (hf _ p)
  have ey : y = q ≫ g := (hP.2 _ fun u => q ^ t u).unique hy (hg _ q)
  have ex' : x' = p ≫ f' := (hP.2 _ fun u => p ^ s' u).unique hx' (hf' _ p)
  have ey' : y' = q ≫ g' := (hP.2 _ fun u => q ^ t' u).unique hy' (hg' _ q)
  subst ex ey ex' ey'
  have hc₁ : (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have hc₂ : (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L).IsLB := LB.isLB_linComb P'.isLB _ _
  have H : LBIso (cubeLB P'.A ![fst B B ≫ f', snd B B ≫ g'] P'.L) (cubeLB P'.A ![fst B B ≫ f, snd B B ≫ g] P'.L) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hc₁ hc₂).1 ?_
    rw [PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE, PrimPic.cube_class_e8Bundle_eighth_power W pr hP.1 P'.L P'.isLB M cub hE,
      funext (hf _ (fst B B)), funext (hg _ (snd B B)), funext (hf' _ (fst B B)), funext (hg' _ (snd B B)),
      bil_zpow M cub, bil_zpow M cub, hst]
  have : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact weilIs_of_lbIso GlobalTheory.abelianSchemeLaws_all.1.globalFns P'.isAb hF.1 cL f' g' f g H
    (T := Out.baseOver (Sp K)) (default : PrimeSpectrum K) (fun _ => Subsingleton.elim _ _) N p q hp hq c hc

end GlobalTheory.Poinc.Sep.E8Fibration.PairVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilDomain

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (a : A) :
    (spMap g).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (g a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

theorem weilIs_of_fractionField : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  intro R _ _ P W L _ _ _ _ _ f e he n x y hx hy w H
  have hL := (GlobalTheory.firstFiveLaws).1
  obtain ⟨c, hc, -⟩ := (hL.weil _ P n (Over.mk (spMap f))).1 x y hx hy
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB e hc
  have hu := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H' H
  have hinj : Function.Injective e.left.appTop.hom := by
    rw [he]
    intro a b hab
    have ia := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) a
    have ib := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) b
    rw [← ia, ← ib, appTop_spMap_inv, appTop_spMap_inv] at hab
    have h1 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1 hab
    have h2 := IsFractionRing.injective W L h1
    rw [← ia, ← ib, h2]
  have hc' : c = unitOn w := by
    apply Units.ext
    apply hinj
    have := congrArg Units.val hu
    refine this.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (algebraMap W L w) = _
    rw [he]
    exact (appTop_spMap_inv (algebraMap W L) (w : W)).symm
  exact hc' ▸ hc

end GlobalTheory.WeilDomain
end

