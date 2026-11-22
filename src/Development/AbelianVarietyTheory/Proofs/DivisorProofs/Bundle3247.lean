import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundOfAnchor
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw

namespace GlobalTheory.FlatSplit

section Congr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

theorem lieFacZ_congr (x : ℝ) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : lieFacZ Dw x G = lieFacZ Dw x G' := by
  unfold lieFacZ
  congr 4
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun h (some ⟨τ, i⟩))

theorem lat_congr {C C' : Submodule c.F (Rul Xo c)} (hC : C = C') {N N' : (c.F →+* ℂ) → Rul Xo c → ℝ} (hN : N = N') :
    ((HasGram (fun σ (f : C) => N σ f) ∧ (supLat C).FG ∧ Submodule.span c.F (supLat C : Set C) = ⊤) ↔
      (HasGram (fun σ (f : C') => N' σ f) ∧ (supLat C').FG ∧ Submodule.span c.F (supLat C' : Set C') = ⊤)) ∧
    Formalism.HN.rkK (supLat C) = Formalism.HN.rkK (supLat C') ∧
    slope_sq (fun σ (f : C) => N σ f) (supLat C) = slope_sq (fun σ (f : C') => N' σ f) (supLat C') := by
  subst hC hN
  exact ⟨Iff.rfl, rfl, rfl⟩

theorem congr_exZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') :
    (GoodW U x V dict G ↔ GoodW U x V dict G') ∧ rankW U G = rankW U G' ∧
      slopeW_sq U x V dict G = slopeW_sq U x V dict G' := by
  have hC : cuspW Xo c U G = cuspW Xo c U G' := by
    ext f
    rw [mem_cuspW, mem_cuspW, h]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]
  have hP : petW U x V dict G = petW U x V dict G' := by
    funext σ f
    unfold petW petAt
    rw [lieFacZ_congr x h, modelWt_congr (U (goodOf c σ)) (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h]
  exact lat_congr hC hP

end Congr

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)

theorem exZ_shift_neg (m kc : ℕ) (c0 : ℤ) :
    exZ Dw (shiftG Dw a (2 * m) (-c0)) =
      exZ Dw (wtOf Dw (uMinus Dw a (2 * m) kc c0 + parWt Dw (anchor Dw a (2 * m) kc)) ((0 : ℤ) + (m : ℤ))) := by
  rw [Model.exZ_shiftG, zero_add, exOf]
  congr 2
  simp only [uMinus, uWt, neg_smul]
  abel

end Weights

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem twice_twist_ge {ι : Type} [Fintype ι] (w c1v : ι → ℝ) (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L) (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E) (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b) (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ Finset.univ, (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_le {PP A M : ℝ} (hH : HostNum D L PP A M) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have h1 := hH.disc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
  rw [rootDiscr_def]
  push_cast
  rw [Real.log_rpow hd, hH.deg]
  push_cast
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem flatAt_of (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hP : Hypotheses2)
    (hDG : DeepGoodAt p i Y)
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧
      FlatExists Y.U (xiR D) ∧
      (∀ τ, |c1 Y.U (xiR D) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord D L p.Del p.h0).logOm| ≤
        3 * (dat p i).q * L.sc.L) ∧
      logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * L.sc.L)
    {CA PP PP' A : ℝ} (hA : AnchorAt p i CA) (hW : WtNum p i PP) (hH : HostNum D L PP' A 0) :
    FlatAt p i Y (11 * CA + 83) := by
  obtain ⟨hcx, hgood, hflat, hc1, hlog⟩ := hc
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have hUn := GlobalTheory.T.unramified_points_deep_level hP D p.T ((i : ℕ) + 1) Y _ _ p.fw.laws hj hY.1
  have hrank : 1 ≤ (dat p i).p + (dat p i).q := Inhab.rank_pos p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) hj
  have hev : Even (p.κ i).n := hW.dom.2
  have hFL := ((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D p.T.Q.H (dat p i) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (fun _ => D.sp.W ((i : ℕ) + 1))
    Y.dict hcx hY.1.geo hrank hgood hflat hUn (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1))
    ((p.κ i).n / 2)).2 (uM p i) 0).2 hDG.2.2.2.1
  obtain ⟨-, hrk, hdeg⟩ := hFL
  have hex : exZ (dat p i) (Gs p i (-(cZero D ((i : ℕ) + 1)))) = exZ (dat p i)
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := by
    have := exZ_shift_neg (dat p i) (wtA (p.κ i)) ((p.κ i).n / 2) (D.R.k - 1) (cZero D ((i : ℕ) + 1))
    rwa [Nat.two_mul_div_two_of_even hev] at this
  have hcg := congr_exZ Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict hY.1.unf hex
  have hR0 := hDG.2.2.2.2.1
  unfold FlatAt
  have e1 : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) = slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := hcg.2.2
  have e2 : Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1)))) = rankW Y.U (wtOf (dat p i) (uM p i) 0) := hcg.2.1.trans hrk
  have hR : (0 : ℝ) < (rankW Y.U (wtOf (dat p i) (uM p i) 0) : ℝ) := by rw [← e2]; exact_mod_cast hR0
  rw [degW_eq, degW_eq, hrk] at hdeg
  rw [e1]
  have hb1 : 1 ≤ L.sc.b := by have := hH.room; rwa [Real.rpow_zero] at this
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL := hH.big.2.1
  have hll := hH.big.2.2.2
  have k1 : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
  have k2 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L := by nlinarith
  have k3 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by nlinarith
  have k4 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.b * Real.log (Real.log L.sc.x) := by nlinarith
  have hbE : L.sc.b ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k3 (by linarith : (0 : ℝ) ≤ L.sc.b)]
  have hLE : L.sc.L ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k4 (by linarith : (0 : ℝ) ≤ L.sc.L)]
  have hfr : (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) = (D.R.f : ℝ) * D.R.r := by
    rw [hH.deg, hW.sig.2.2, Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring
  have hm : 2 * ((((p.κ i).n / 2 : ℕ) : ℝ)) ≤ (D.R.nV : ℝ) := by
    have := Nat.mul_div_le (p.κ i).n 2
    rw [hW.cols] at this
    rw [hW.cols]; exact_mod_cast (by omega : 2 * (D.R.nV / 2) ≤ D.R.nV)
  have num := twice_twist_ge (fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)) (c1 Y.U (xiR D))
    (((dat p i).p : ℝ) - (dat p i).q) ((dat p i).q : ℝ) (ofRecord D L p.Del p.h0).logOm L.sc.L L.sc.b (unitE p) (mainT p i) CA
    (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E) ((((p.κ i).n / 2 : ℕ) : ℝ))
    (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) (D.R.nV : ℝ)
    (logSum (badPrimes p.T.Q.H Y.d.l₂)) hc1 hA.1 hA.2.1 (Nat.cast_nonneg _) (lrd_le hH) hL hm (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by rw [hfr]; exact hA.2.2) hbE hLE hlog
  rw [← mul_add] at hdeg
  have key := le_of_mul_le_mul_left hdeg hR
  show slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict (wtOf (dat p i) (uM p i) 0) - mainT p i -
    (11 * CA + 83) * unitE p ≤ _
  linarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem flat : Hypotheses2 → DeepGood → FlatDeg → Anchor → Flat := by
  intro hP hDG hFD hA
  refine Closed.imp (Closed.and (Closed.and (Closed.and (Closed.and hDG (GlobalTheory.T.flat_line_c1_log_bound hFD)) hA) GlobalTheory.T.weight_bound_holds)
    (GlobalTheory.CovTop.Sizes.hostN 0)) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨CA, hCA, h3⟩⟩, ⟨C4, -, h4⟩⟩, ⟨C5, -, h5⟩⟩
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := (((h1.and h2).and h3).and h4).and h5
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hx x hx' hle ι p hp
  exact flatAt_of p i Y hY hP (a1 i hi Y hY) (a2 i hi Y hY) (a3 i) (a4 i) (a5 i)

end GlobalTheory.FlatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwistRank

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem rkK_eq_of_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) : Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  have hmap : (Submodule.span K (L : Set V)).map (φ : V →ₗ[K] W) = Submodule.span K (L' : Set W) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro f hf
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    · rw [Submodule.span_le]
      intro g hg
      refine ⟨a⁻¹ • (a • φ.symm g), Submodule.smul_mem _ _ (Submodule.subset_span (R := K) (hout g hg)), ?_⟩
      show φ (a⁻¹ • (a • φ.symm g)) = g
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul, φ.apply_symm_apply]
  unfold Formalism.HN.rkK
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem rankOn_twist {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) :
    rankOn U Z (G + G₀) = rankOn U Z G := by
  obtain ⟨φ, -, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := Good.exists_twist_scalar s
  exact rkK_eq_of_equiv φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _))

theorem cuspW_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') :
    cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem rankOn_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : rankOn U Z G = rankOn U Z G' := by
  have e : cuspOn U Z G = cuspOn U Z G' := by rw [cuspOn, cuspOn, cuspW_congr hU h]
  unfold rankOn latOn
  rw [e]

theorem psi_nonempty : Nonempty (Psi H) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : φ (H.rt : E) = H.rt0
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨conjEmb φ, conj_mem h⟩⟩

theorem exists_twSec_par (hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {a : ℝ} (hF : FlatExistsAt U x a) (Z : Comp Xo c) (w : Psi H → ℤ) :
    Nonempty (TwSec U x Z (wtOf Dw (parWt Dw w) 0)) := by
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF Z τ).1.some
  obtain ⟨τ₀⟩ := psi_nonempty (H := H)
  have hp : HasPts U Z := (sF τ₀).hasPts
  let s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ) :=
    (FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _)
  refine ⟨TwSec.ofConst s (GlobalTheory.FlatTwisting.finite_sum_flDefect w) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq s)
    fun G hG f hf => ?_⟩
  have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl)
    (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
  rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem wtOf_zero_nat (k : ℕ) : wtOf Dw 0 (k : ℤ) = k • wtOf Dw 0 1 := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul]; exact wtOf_zero
  | succ k ih =>
    rw [succ_nsmul, ← ih, ← wtOf_add]
    simp

end Gen

end GlobalTheory.TwistRank

namespace GlobalTheory.TwistRank

theorem flat_twist_ranks : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → (∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ), Dom a n → Even n → Y.GoodAt (shiftG (T.Q.Dw j) a n s) → (Y.rk (shiftG (T.Q.Dw j) a n s) : ℝ) = ∑ᶠ Z, Y.rkC (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) Z := by
  intro hP D T hL j hp hq hE hj Y e o hY c₁ hF
  have hU := hY.unf
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
    obtain ⟨σ, hσ⟩ : ∃ σ, GoodEmb Y.d.c₂ σ := ⟨Y.d.c₂.F.val.toRingHom, rfl⟩
    obtain ⟨-, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F hpq hY.geo
  have part1 : ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z,
      Y.rkC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z = Y.rkC la Z := by
    intro la w Z
    obtain ⟨t⟩ := exists_twSec_par hK hU hpq hF Z w
    show ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) 0) : ℕ) : ℝ) =
      ((AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℕ) : ℝ)
    rw [GlobalTheory.FlatLine.wtOf_add', rankOn_twist t _ (AllWt.even_wtOf _ _)]
  refine ⟨part1, ?_⟩
  intro a n kc s _hdom hn hgood
  have hR := GlobalTheory.T.supLattice_rank_eq_sum_component_ranks D T.Q.H (T.Q.Dw j) _ Y.d.Xo₂ Y.d.c₂ _ Y.U (xiR D) (fun _ => D.sp.W j) Y.dict
    (shiftG (T.Q.Dw j) a n s) hU hgood
  haveI : Finite (Comp Y.d.Xo₂ Y.d.c₂) := GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.finite_comp
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  show ((AllWt.rankW Y.U (shiftG (T.Q.Dw j) a n s) : ℕ) : ℝ) = _
  rw [hR]
  simp only [finsum_eq_sum_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  obtain ⟨m, hm⟩ := hn
  have hn2 : n / 2 = m := by omega
  set L := laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j) with hLdef

  have h1 : AllWt.rankOn Y.U Z (shiftG (T.Q.Dw j) a n s) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) := by
    refine rankOn_congr hU Z ?_
    rw [hLdef, ← add_zero (m : ℤ), AllWt.wtOf_add, shiftG, GlobalTheory.FlatTw.exZ_add_eq, GlobalTheory.FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)
    rw [AllWt.exOf] at this
    rw [laOf, hn2] at *
    rw [this, wtZ]
    congr 2
    omega

  have h2 : AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L (m : ℤ)) = AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) L 0) := by
    have he : wtOf (T.Q.Dw j) L (m : ℤ) = wtOf (T.Q.Dw j) L 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) := by
      rw [← AllWt.wtOf_add, add_zero, zero_add]
    obtain ⟨t1⟩ := GlobalTheory.T.nonempty_twisted_section_component hP D T hL j hp hq hE hj Y e o hY c₁ hF Z
    obtain ⟨t, -⟩ := GlobalTheory.FlatTw.TwSec.exists_pow t1 m
    rw [he]
    exact rankOn_twist (t.copy (wtOf_zero_nat (Dw := T.Q.Dw j) m).symm) _ (AllWt.even_wtOf _ _)

  have h3 : L = (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a n kc) := by
    rw [hLdef, ← uWt_add_anchor (T.Q.Dw j) a n kc]; abel
  have h4 := part1 (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) (anchor (T.Q.Dw j) a n kc) Z
  rw [← h3] at h4
  rw [h1, h2]
  exact h4

end GlobalTheory.TwistRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFlagBundleSmoothRelativeDimStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_flag_bundle_smooth_relative_dim : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  first | exact @GlobalTheory.FlagFreeSmooth.main | exact GlobalTheory.FlagFreeSmooth.main | (intros; apply GlobalTheory.FlagFreeSmooth.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTateGaloisActionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_tate_galois_action : ∀ (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K), tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧ vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  first | exact @GlobalTheory.AV.AbVar.frob_tate | exact GlobalTheory.AV.AbVar.frob_tate | (intros; apply GlobalTheory.AV.AbVar.frob_tate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLogSumWeightUniformlyBounded
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem abs_log_sum_pow_le {D : ℕ} (v : Fin (D + 1) → ℝ) (hv : ∀ l, 0 ≤ v l) {m M : ℝ} (hm : 0 < m) (hM : 1 ≤ M)
    (hvM : ∀ l, v l ≤ M) (hvm : ∃ l, m ≤ v l) {e n : ℕ} (he : 0 < e) (hn : 1 ≤ n) :
    |((e : ℝ) * n)⁻¹ * Real.log (∑ l, v l ^ (2 * n))| ≤ Real.log (D + 1) + 2 * Real.log M + 2 * |Real.log m| := by
  obtain ⟨l₀, hl₀⟩ := hvm
  have hD : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hM' : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlo : m ^ (2 * n) ≤ ∑ l, v l ^ (2 * n) :=
    (pow_le_pow_left₀ hm.le hl₀ _).trans
      (Finset.single_le_sum (f := fun l => v l ^ (2 * n)) (fun l _ => pow_nonneg (hv l) _) (Finset.mem_univ l₀))
  have hhi : ∑ l, v l ^ (2 * n) ≤ (D + 1 : ℝ) * M ^ (2 * n) := by
    refine (Finset.sum_le_sum (g := fun _ => M ^ (2 * n)) fun l _ => pow_le_pow_left₀ (hv l) (hvM l) _).trans ?_
    simp
  have hp : 0 < m ^ (2 * n) := pow_pos hm _
  have h1 := Real.log_le_log hp hlo
  have h2 := Real.log_le_log (hp.trans_le hlo) hhi
  rw [Real.log_pow] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
  push_cast at h1 h2
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hen : (n : ℝ) ≤ e * n := le_mul_of_one_le_left (by linarith) he'
  have ha := abs_nonneg (Real.log m)
  have hb := neg_abs_le (Real.log m)
  rw [abs_mul, abs_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hen (by positivity))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hn') hD, mul_nonneg (sub_nonneg.2 hn') hM',
    mul_nonneg (sub_nonneg.2 hn') ha, mul_nonneg (zero_le_one.trans hn') (sub_nonneg.2 hb)]

theorem can_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  intro k _ X _ p D hX P e x hx
  have hnn : ∀ (σ : k →+* ℂ) (y : CxPts p σ) l, 0 ≤ P.nu e 0 σ y (x l) := fun σ y l => by
    rw [← norm_val]; exact norm_nonneg _
  have hc := fun l => (GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P e 0).2 (x l) (hx.mem l)
  choose C hC using fun l => (hc l).2
  have hlow : ∀ σ : k →+* ℂ, ∃ κ : ℝ, 0 < κ ∧ ∀ y : CxPts p σ, κ ≤ ∑ l, P.nu e 0 σ y (x l) := fun σ => by
    haveI := hX.compactSpace σ
    have hcont : Continuous fun y : CxPts p σ => ∑ l, P.nu e 0 σ y (x l) :=
      continuous_finsetSum _ fun l _ => (hc l).1 σ
    have hpos : ∀ y : CxPts p σ, 0 < ∑ l, P.nu e 0 σ y (x l) := fun y => by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      exact Finset.sum_pos' (fun l _ => hnn σ y l) ⟨l, Finset.mem_univ _,
        ((GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2⟩
    rcases isEmpty_or_nonempty (CxPts p σ) with h | h
    · exact ⟨1, one_pos, fun y => h.elim y⟩
    · obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
      exact ⟨_, hpos y₀, fun y => hy₀ (Set.mem_univ y)⟩
  choose κ hκ hκ' using hlow
  haveI := hX.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  have hs : 0 ≤ ∑ σ, (κ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hκ σ)).le
  have hκ₀ : ∀ σ, (1 + ∑ σ, (κ σ)⁻¹)⁻¹ ≤ κ σ := fun σ => by
    refine inv_le_of_inv_le₀ (hκ σ) ?_
    have := Finset.single_le_sum (f := fun σ => (κ σ)⁻¹) (fun σ _ => (inv_pos.2 (hκ σ)).le) (Finset.mem_univ σ)
    linarith
  have hs' : 0 ≤ ∑ l, |C l| := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hM : 1 ≤ 1 + ∑ l, |C l| := by linarith
  refine ⟨Real.log (D + 1) + 2 * Real.log (1 + ∑ l, |C l|) + 2 * |Real.log ((1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1))|, ?_,
    fun n hn σ y => abs_log_sum_pow_le _ (hnn σ y) (by positivity) hM (fun l => ?_) ?_ hx.pos hn⟩
  · have h1 : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    have h2 := Real.log_nonneg hM
    positivity
  · have := Finset.single_le_sum (f := fun l => |C l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    linarith [hC l σ y, le_abs_self (C l)]
  · obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ : Fin (D + 1) => (1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1 : ℝ)) (g := fun l => P.nu e 0 σ y (x l)) (by
        refine le_trans (le_of_eq ?_) ((hκ₀ σ).trans (hκ' σ y))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp)
    exact ⟨l, hl⟩

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2DefiniteStatement
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posDef_of_l2_definite : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) → (gram μ v).PosDef := by
  first | exact @GlobalTheory.HSAmp.gram_posDef | exact GlobalTheory.HSAmp.gram_posDef | (intros; apply GlobalTheory.HSAmp.gram_posDef <;> assumption)
end

