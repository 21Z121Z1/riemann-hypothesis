import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ActsUnitarilyOfClauses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBot
section
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CovTop.ne_bot_of_isLattice_coords {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) {d : ℕ} (hd : 0 < d) (b : Fin d → V) (hb : LinearIndependent K b)
    (hM : Submodule.IsLattice K (M.comap ((Fintype.linearCombination K b).restrictScalars O))) : M ≠ ⊥ := by
  rintro rfl
  have hinj : Function.Injective (Fintype.linearCombination K b) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by rwa [Fintype.linearCombination_apply] at hc))
  have h0 : (⊥ : Submodule O V).comap ((Fintype.linearCombination K b).restrictScalars O) = ⊥ := by
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 hinj
  have h := hM.span_eq_top
  rw [h0] at h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp at h

theorem GlobalTheory.CovTop.latGood_ne_bot_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, latGood p.R.toRealDat p.F.lv2 i ≠ ⊥ := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  exact GlobalTheory.CovTop.ne_bot_of_isLattice_coords (latGood p.R.toRealDat p.F.lv2 i)
    (show 0 < (p.S false).dW i from hD.symm ▸ hpos) (p.R.toRealDat.bL p.F.lv2 false i) hli (hp.prim.mLat i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem geoUnitary_tied : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i σ g x y
  have hm := p.charW.base.models
  exact GlobalTheory.UnitaryActionTest.geometric_unitary p.R.toRealDat hp.prim.unif hm.HW hm.gW
    (GlobalTheory.UnitaryActionTest.actsUnitarily_of_clauses p.R.toRealDat hm.HE hm.gE hm.ν0 hm.HW hm.gW hm.νW
      p.charW.base.fam.tie hm.cX hm.cV) i _ g x y

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartProperties
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.Ind

theorem pRows_of_parts : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Ind.Part D O c), Ind.PFire D O c b → Ind.PRB D O c b →
    Ind.PPA D O c b → Ind.PFrames D O c b → Ind.PDiv D O c b → Ind.PNmj D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.Ties →
    Ind.PRows D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := GlobalTheory.T.base_level_rows_eq_dimension_all D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }

end GlobalTheory.Fc.Ind
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

namespace GlobalTheory.RunSizes

set_option maxHeartbeats 2000000 in

theorem core (f r k m PP TO T : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hm : 0 < m) (hkm : m ≤ k)
    (hPP : f * r ^ 2 ≤ PP) (hTO : PP ^ 4 * (f * (r * (r - 1) / 2)) ^ 3 * k / m ≤ TO) (hT0 : 0 ≤ T)
    (hT : T ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m + 1) :
    (f * (r * (r - 1) / 2) + 3) * ((f * (r * (r - 1) / 2) + 1) * (f * (r * (r - 1) / 2)) / 2 + 4 * r +
        f * (r * (r - 1) / 2) + 3) * (T + f * (r * (r - 1) / 2) + 1) + 4 ≤ TO ∧
      22 * f ^ 2 * r ^ 4 + 2 * r + 1 ≤ TO ∧
      f * (r * (r - 1) / 2) + 1 ≤ PP ^ 2 * (f * (r * (r - 1) / 2)) ^ 2 * k / m := by
  set d := f * (r * (r - 1) / 2) with hd
  have hr1 : 5 ≤ r - 1 := by linarith
  have hrr : 5 * r ≤ r * (r - 1) := by nlinarith
  have hd5 : 5 * r ≤ d := by rw [hd]; nlinarith
  have hd30 : 30 ≤ d := by linarith
  have hdr2 : d ≤ f * r ^ 2 / 2 := by rw [hd]; nlinarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hkm' : 1 ≤ k / m := (one_le_div hm).2 hkm
  set A := PP ^ 2 * d ^ 2 * k / m with hA
  have hA' : A = PP ^ 2 * d ^ 2 * (k / m) := by rw [hA]; ring
  have hPP2 : 1 ≤ PP ^ 2 := by nlinarith
  have hAd : d ^ 2 ≤ A := by
    rw [hA']
    have h0 : 0 ≤ d ^ 2 := by positivity
    have : d ^ 2 ≤ PP ^ 2 * d ^ 2 := by nlinarith
    calc d ^ 2 ≤ PP ^ 2 * d ^ 2 := this
      _ = PP ^ 2 * d ^ 2 * 1 := by ring
      _ ≤ PP ^ 2 * d ^ 2 * (k / m) := by gcongr
  have hTO' : PP ^ 2 * d * A ≤ TO := by
    have : PP ^ 4 * d ^ 3 * k / m = PP ^ 2 * d * A := by rw [hA]; ring
    linarith
  have hG : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) ≤ d ^ 3 := by nlinarith
  have hT2 : T + d + 1 ≤ 2 * A := by nlinarith
  have hGnn : 0 ≤ (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) := by
    have : 0 ≤ r := by linarith
    positivity
  have h3d : 3 * d ^ 2 ≤ PP ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by nlinarith
  have hd1 : d + 1 ≤ d ^ 2 := by nlinarith
  refine ⟨?_, ?_, by linarith⟩
  · have h1 : (d + 3) * ((d + 1) * d / 2 + 4 * r + d + 3) * (T + d + 1) ≤ d ^ 3 * (2 * A) :=
      mul_le_mul hG hT2 (by linarith) (by positivity)
    have h4 : 4 ≤ d ^ 3 * A := by nlinarith
    have h2 : d ^ 3 * (2 * A) + 4 ≤ PP ^ 2 * d * A := by
      have : 3 * d ^ 2 * (d * A) ≤ PP ^ 2 * (d * A) := by
        apply mul_le_mul_of_nonneg_right h3d; positivity
      nlinarith
    linarith
  · have hP2 : (f * r ^ 2) ^ 2 ≤ PP ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hPP
    have hd900 : (30 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) hd30 2
    have hA1 : 1 ≤ A := by linarith
    have hdA : 30 ≤ d * A := by
      calc (30 : ℝ) = 30 * 1 := by ring
        _ ≤ d * A := mul_le_mul hd30 hA1 (by norm_num) (by linarith)
    have hr4 : r * 216 ≤ r ^ 4 := by
      have h3 : (6 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
      have : r ^ 4 = r * r ^ 3 := by ring
      rw [this]
      have h216 : (216 : ℝ) ≤ r ^ 3 := by norm_num at h3; linarith
      have hr0 : (0 : ℝ) ≤ r := by linarith
      exact mul_le_mul_of_nonneg_left h216 hr0
    have hf2 : (2 : ℝ) ^ 2 ≤ f ^ 2 := pow_le_pow_left₀ (by norm_num) hf 2
    norm_num at hf2
    have hfr : 2 * r + 1 ≤ f ^ 2 * r ^ 4 := by
      have : 4 * (r * 216) ≤ f ^ 2 * r ^ 4 := mul_le_mul hf2 hr4 (by positivity) (by positivity)
      linarith
    have h30 : (f * r ^ 2) ^ 2 * 30 ≤ PP ^ 2 * (d * A) := by
      apply mul_le_mul hP2 hdA (by norm_num) (by positivity)
    have e1 : (f * r ^ 2) ^ 2 = f ^ 2 * r ^ 4 := by ring
    have e2 : PP ^ 2 * (d * A) = PP ^ 2 * d * A := by ring
    rw [e1, e2] at h30
    linarith

set_option maxHeartbeats 2000000 in

theorem at_point {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Tp : ParamsT D L P) :
    1 ≤ D.R.f * D.R.r.choose 2 ∧
    D.R.f * D.R.r.choose 2 + 1 ≤
      ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = (D.R.f * D.R.r.choose 2 + 3) *
        ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r + D.R.f * D.R.r.choose 2 + 3) →
      T = ⌈Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ →
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤ min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) ∧
      ((G * (T + D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 +
        2 * D.R.r + 1 ≤ LevelStarExponents.h0 L := by
  have hf : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hfR : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hrR : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < D.R.m := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
    linarith
  have hkmR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hDd : ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    push_cast [Nat.cast_choose_two]; ring
  have hdpos : (0 : ℝ) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [← hDd]; positivity

  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1 L.sc.eps_pos.le
  have hZ : 1 ≤ zBase L := by
    unfold zBase
    have : (12 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hPP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ Tp.PP := by
    rw [Tp.PP_eq]
    have h1 : zBase L ^ (2 : ℝ) ≤ zBase L ^ Tp.eP :=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Tp.eP_ge])
    rw [Real.rpow_two] at h1
    have hL2 : 1 ≤ L.sc.L ^ 2 := one_le_pow₀ hL
    have hff : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 * L.sc.L ^ 2 := by nlinarith
    have h3 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2 := by
      unfold zBase
      calc (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ ((D.R.f : ℝ) ^ 2 * L.sc.L ^ 2) * (D.R.r : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hff (sq_nonneg _)
        _ = ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 2 := by ring
    have hCP := Tp.one_le_CP
    have h4 : 0 ≤ zBase L ^ Tp.eP := Real.rpow_nonneg (by linarith) _
    nlinarith

  have hTO : Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k / D.R.m ≤ (Tp.TO : ℝ) := by
    have hTOg := Tp.TO_ge
    rw [Tp.Dp_eq, hDd] at hTOg
    refine le_trans ?_ hTOg
    have hxc : 1 ≤ L.sc.x ^ Tp.Cp := Real.one_le_rpow hx1 Tp.Cp_nonneg
    have hde := L.thickDensity_pos
    have hde1 := L.thickDensity_le_one
    rw [div_le_div_iff₀ hmR (mul_pos hmR hde)]
    have hB : 0 ≤ Tp.PP ^ 4 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 3 * D.R.k := by
      have : (0 : ℝ) ≤ D.R.k := by positivity
      positivity
    have hfx : L.de2 ≤ (D.R.f : ℝ) * L.sc.x ^ Tp.Cp := by nlinarith
    have := mul_le_mul_of_nonneg_left hfx (mul_nonneg hB hmR.le)
    nlinarith
  have hPPnn : 0 ≤ Tp.PP := le_trans (by positivity) hPP
  have hA0 : 0 ≤ Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by positivity
  have hT0 := Nat.ceil_lt_add_one hA0
  rw [hDd] at hT0 hA0
  obtain ⟨c1, c2, c3⟩ := core (D.R.f : ℝ) (D.R.r : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) Tp.PP (Tp.TO : ℝ)
    (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ)
    hfR hrR hmR hkmR hPP hTO (Nat.cast_nonneg _) hT0.le

  have hTOt : Tp.TO ≤ D.R.t := by
    have hs := Tp.split
    have h40 := Tp.nW_40
    have hn0 := Tp.order_ge_rank_bound
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ h40
    have : D.R.r ≤ Tp.TO := le_trans (Nat.le_add_right _ _) hn0
    omega
  have hTON : Tp.TO ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : D.R.t ≤ D.R.m * (D.R.t + 1) := by nlinarith
    omega
  have hgap : (Tp.TO : ℝ) ≤ LevelStarExponents.gapS D P.Cgap := by
    unfold LevelStarExponents.gapS
    have h1 : ((Tp.TO : ℕ) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hTON
    have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ D.R.m by omega))
    have h3 : 0 ≤ P.Cgap * D.R.k * (D.R.m : ℝ) ^ 4 := by
      have := P.Cgap_pos
      positivity
    have h4 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by
      have : (0 : ℝ) ≤ D.R.N D.R.m := by positivity
      nlinarith
    linarith
  have hTO1 : (1 : ℝ) ≤ Tp.TO := by
    have := Tp.TO_40
    have : 1 ≤ Tp.TO := by omega
    exact_mod_cast this
  have hh0 : 2 * (Tp.TO : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := by positivity
    nlinarith
  refine ⟨Nat.mul_pos (by omega) (Nat.choose_pos (by omega)), ?_, ?_⟩
  · have h : ((D.R.f * D.R.r.choose 2 + 1 : ℕ) : ℝ) ≤
        Tp.PP ^ 2 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one, hDd]; exact c3
    exact_mod_cast h.trans (Nat.le_ceil _)
  · intro G T hG hT
    subst hG hT
    rw [hDd]
    have e : ((((D.R.f * D.R.r.choose 2 + 3) * ((D.R.f * D.R.r.choose 2 + 1).choose 2 + 4 * D.R.r +
          D.R.f * D.R.r.choose 2 + 3)) *
        (⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ +
          D.R.f * D.R.r.choose 2 + 1) : ℕ) : ℝ) =
        ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          (((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) / 2 +
            4 * (D.R.r : ℝ) + (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 3) *
          ((⌈Tp.PP ^ 2 * ((D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2)) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) +
            (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) + 1) := by
      push_cast [Nat.cast_choose_two]; ring
    rw [e]
    refine ⟨le_min (by linarith) (by linarith), by linarith⟩

theorem gaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι => at_point (Fm.parT x hx ι)⟩⟩⟩

end GlobalTheory.RunSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
section
noncomputable section

open Filter Asymptotics

namespace GlobalTheory.BigTop.Fun

theorem exists_log_le_two_rpow {eps : ℝ} (he : 0 < eps) : ∃ x0 : ℝ, ∀ y, x0 ≤ y → Real.log y ≤ 2 * y ^ eps := by
  have hev : ∀ᶠ y in atTop, Real.log y ≤ 2 * y ^ eps := by
    have h := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 2)
    filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
    exact (le_abs_self _).trans hy
  exact eventually_atTop.1 hev

theorem existsIntegralMultiple : GlobalTheory.BigTop.Fun.Scale := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := exists_log_le_two_rpow he
  refine ⟨x0, fun x hx hle i p _ => ?_⟩
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hx
  have hZx : p.Z.x = x := hsx
  have hZb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  show 1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
  rw [hZx, hZb, Real.log_exp]
  have h1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1.le he.le
  exact ⟨hx1.le, h1, by linarith [hx0 x hle]⟩

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsL
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc K hK
  obtain ⟨L, hL, hden⟩ := GlobalTheory.T.exists_bounded_denominator_rational_matrices_in_box D V.rank n K hK
  obtain ⟨N, C, hC, hst⟩ := GlobalTheory.T.torusInverse_latticeCount_stacked_eigenprojections D V.rank n r X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) c hc L hL
  refine ⟨N, C, hC, fun t ht a ha => ?_⟩
  obtain ⟨hfin, hrel⟩ := GlobalTheory.T.siegelTorusElement_inv_finitePart_one_dualFrame_eigen D θ hθ V r X Y hXY t ht.1 a ha
  refine le_trans (ENNReal.tsum_le_tsum fun ξ => ?_)
    (hst t ht (fun τ => compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) hrel)
  have e : (GlobalTheory.SiegelFormula.invPt V a ξ : Matrix (Fin V.rank) (Fin n) (AE D)) =
      HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D) : Matrix (Fin V.rank) (Fin n) (AE D)) := rfl
  have hcomp : ∀ τ, compAt θ τ (GlobalTheory.SiegelFormula.invPt V a ξ) =
      compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) * ξ.map (tauE D τ) := by
    intro τ
    have h1 : compAt θ τ (ξ.map (incA D) : Mx D V.rank n) = ξ.map (tauE D τ) := by
      ext i j
      exact (hθ τ).1 (ξ i j)
    rw [e, ← h1]
    exact Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold GlobalTheory.Unf.maj
  split_ifs with hb
  · have hmem : ξ ∈ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E |
        ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} := by
      refine hden _ ξ ?_ hb
      rw [e, Matrix.map_mul, hfin, Matrix.one_mul]
    rw [Set.indicator_of_mem hmem]
    simp only [GlobalTheory.Unf.realSize, hcomp, le_refl]
  · simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singleThetaSeries_K_equivariant_lowest_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (Q' : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q' Ω φ' → ∀ (h : GA D (Vc D i)) (y : (R.cV i).W) (g0 : G) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y (Function.update v τ u)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y v)) := by
  first | exact @GlobalTheory.SeriesKEquiv.singleSeries_kEquiv | exact GlobalTheory.SeriesKEquiv.singleSeries_kEquiv | (intros; apply GlobalTheory.SeriesKEquiv.singleSeries_kEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartNonzeroIndexPlacesTwisted
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
open GlobalTheory.CharRealise
open Formalism.DivisionValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

set_option maxHeartbeats 4000000 in

theorem splitPartFace_baseLevel_indices_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw i p.P.A3.A.μ0 w = ((p.R.toRealDat.toCx (F2 p)).data (F2 p).cr false).Iw i p.P.A3.A.μ0 w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw i _ w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem splitPartFace_baseLevel_jw_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    jw ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).HT i p.P.A3.A.μ0) w ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).Tl i p.P.A3.A.μ0) =
      jw ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).HT i p.P.A3.A.μ0) w
        ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).Tl i p.P.A3.A.μ0) := by
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl

set_option maxHeartbeats 4000000 in

theorem w1_of_inW1_split_part (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (h : p.R.toRealDat.NonzeroIndexPlace (F2 p) w) :
    (p.R.toCx3 p.F).W1 p.F.cr (p.N C CH) w := by
  obtain ⟨w', hw', i, h⟩ := h
  refine ⟨i, ?_⟩
  rcases hw' with rfl | rfl
  · rcases h with h | h | h | h | h
    · exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · exact Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem tupTw_of_w1Row : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p h w hw
  exact h w (w1_of_inW1_split_part p 0 0 w hw)

end GlobalTheory.BigOn

end
end

