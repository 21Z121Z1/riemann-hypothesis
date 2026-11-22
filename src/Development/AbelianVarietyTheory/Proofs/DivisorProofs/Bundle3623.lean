import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3618
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeParametersBound
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

namespace GlobalTheory.HSShortRun

open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) : Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dif_neg hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt_of_wtBig {P : WtPar Dw} (h : WtBig P) : ∀ i, GapGe (FlagTan.dimFlag Dw + 1) (P.wt i) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro i τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg i) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

end Weights

variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}

theorem claim_at (hP : Hypotheses₂) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : Quoted)
    (hN : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hPr : GlobalTheory.Published.Principalisation)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hC : GlobalTheory.Published.ToroidalChartsForFan)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (hE : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) {P : WtPar (T.Q.Dw j)} (hW : WtBig P)
    (hA : ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) {PP κ : ℝ} (hPP : 0 ≤ PP) (hκ : 0 ≤ κ)
    (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂)
    (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) {Λ β : ℝ} (hΛ : 1 ≤ Λ) (hβ : 1 ≤ β)
    (hfr : ∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ)
    (hberg : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ β)
    (hBir : BirOn Y.U Z (wtOf _ P.u₁ 0) ∧ BirOn Y.U Z (wtOf _ P.u₂ 0))
    (h0 : ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)))
    (hsh : ∀ i ≤ P.T, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt i)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt i) 0) σ (v q).1 ≤ Real.exp (PP * κ)) :
    1 ≤ (f₁.n : ℝ) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 P.T (CompHt.dimFlag (T.Q.Dw j)) f₁.n 1 Λ β (Real.exp (PP * κ))
      (Real.exp (PP * κ)) (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) (Y.dg P.u₁ Z) (Y.ht P.u₁ Z)
      (Y.rkC (P.wt P.T) Z) (Y.degC (P.wt P.T) Z) := by
  obtain ⟨TF, R, ω, h⟩ := GlobalTheory.T.deep_model_weight_section hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z P hW hA
  have hPk : 0 ≤ PP * κ := mul_nonneg hPP hκ
  let k : Consts := ⟨Λ, β, Real.exp (PP * κ), Real.exp (PP * κ), 0, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk⟩
  let th : R.L.Sec := 0
  have r₁ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hBir.1
  have r₂ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₂ ⟨R.toModif⟩ hBir.2
  have hΛ₀ : 1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) := Real.one_le_exp (by positivity)
  have sh : ∀ i ≤ P.T, (h.data f₁ f₂ th k).ShortFamily i (Real.exp (PP * κ)) := fun i hi => by
    obtain ⟨m, v, l, s, n⟩ := hsh i hi
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k i hi _ m v l s n
  have s0 : (h.data f₁ f₂ th k).ShortFamily 0 (Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1))) := by
    obtain ⟨m, v, l, s, n⟩ := h0
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k 0 P.T.zero_le _ m v l s n
  have hDT : FlagTan.dimFlag (T.Q.Dw j) ≤ P.T := (Nat.le_succ _).trans h.le_T
  have hyp := GlobalTheory.T.geoHyp_of_ready_of_shortFamily hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z TF P R ω h f₁ f₂ th k _ hW r₁ r₂ hberg hΛ hfr hΛ₀ s0
    (sh _ hDT) (sh _ le_rfl)
  have hC := GlobalTheory.T.hilbertSamuel_component_short_basis_bound hQ _ _ _ _ _ _ _ TF.X Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k _ hyp
  have hrk : Y.rkC (P.wt P.T) Z = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    show ((Formalism.HN.rkK _ : ℕ) : ℝ) = _
    rw [Formalism.HN.rkK, (h.good _ le_rfl).2.2, finrank_top]
  rw [Real.log_exp] at hC
  refine ⟨by exact_mod_cast (h.geo f₁ f₂ th k).one_le_n, ?_⟩
  rw [hrk]
  exact hC

set_option maxHeartbeats 1000000 in

theorem hsClaim_short : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  intro hX h2 hG hQ hS hK hL hDG hSz hF
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply h2
  have H₄ := GlobalTheory.T.good_weight_antitone_gap h2
  have H₃ : Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg
      (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
    apply GlobalTheory.T.log_degree_le_weight_bound <;> assumption
  refine Closed.imp (Closed.and (Closed.and (Closed.and (GlobalTheory.T.exists_cusp_frame_weights h2 hDG hSz hF) (GlobalTheory.T.birational_on_weight_parameters hX hG hQ hS h2 hSz))
    (Closed.and H₃ wtBig_run)) (Closed.and (Closed.and (GlobalTheory.T.weight_parameter_strict_antitone hSz) (GlobalTheory.T.size_bounds_for_family hSz))
    (Closed.and (GlobalTheory.T.lattice_basis_petersson_first h2 hDG hSz hF) (GlobalTheory.T.lattice_basis_petersson_second h2 hDG hSz hF)))) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨_, -, a₃⟩, _, -, a₄⟩, ⟨⟨_, -, a₅⟩, _, -, a₆⟩, ⟨_, -, a₇⟩, _, -, a₈⟩
  obtain ⟨x0, a⟩ := (((a₁.and a₂).and (a₃.and a₄)).and ((a₅.and a₆).and (a₇.and a₈)))
  clear a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨⟨a₁, a₂⟩, a₃, a₄⟩, ⟨a₅, a₆⟩, a₇, a₈⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨⟨f₂⟩, f₁, Λ, β, hΛ, hβ, hn, hlβ, hlΛ, hfr, hberg⟩ := a₁ i hi Y hY Z
  have hW := a₄ i hi
  obtain ⟨hp1, hq1, hE, -⟩ := a₅ i hi
  obtain ⟨hLaw, hIn, -, -, -, -, -, -, -, -, -, -, hPP, -⟩ := a₆ i hi Y hY
  obtain ⟨hPk, hsh⟩ := a₈ i hi Y hY
  have hg := gapGe_wt_of_wtBig hW
  have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hPP
  have hκ0 : 0 ≤ kap p i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, c₂⟩ := claim_at hP hG hQ h2.q15 h2.q16 hS hK.toroidalChartsForFan hL hY.1 hE Z hW
    (fun j _ => (H₄ _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1 _ (fun τ => antitone_of_gapGe (by positivity) (hg j) τ)
      (fun τ => le_trans (by omega) (hg j τ ((dat p i).p - 1) (by omega)))).1)
    hPP0 hκ0 f₂ f₁ hΛ hβ hfr hberg (a₂ i hi Y hY Z) (a₇ i hi Y hY Z) (hsh Z)
  refine ⟨f₁.n, Λ, β, _, _, _, c₁, hΛ, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk, hn, hlβ, a₃ i hi Y hY Z, hlΛ,
    (Real.log_exp _).le, (Real.log_exp _).le, ?_, c₂⟩
  have e₁ : 0 ≤ CompHt.dimFlag (dat p i) * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP + 1) := by
    positivity
  have e₂ : 0 ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP := by positivity
  have e₃ : 0 ≤ 2 * (Fm.parT x hx ι).PP * (kap p i / lenT p i (Fm.parT x hx ι).PP) * CompHt.dimFlag (dat p i) := by
    positivity
  linarith

end GlobalTheory.HSShortRun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_isHeckeMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 →
    ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hEF hg hck M M'
  obtain ⟨o', ψ, hψ⟩ := GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor p D R b g c k N hc hk hN hNp hEF hg hck M'.X M'.s M'.univ
  obtain ⟨π, ⟨hπ, hm⟩, -⟩ := M.toRepFam.rep M'.X M'.s o'
  exact ⟨π, hπ, o', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_chart {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

theorem proper_ample_kTriv {S S' : Scheme.{0}} [IsAffine S'] {f : S' ⟶ S} {t : SAB H S} {u u' : SAB H S'}
    (m : SABMap u t f) (m' : SABMap u' t f) (hP : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L)
    (hK : Out.KTriv u.G u.PP.L) : IsProper u'.G.hom ∧ Out.RelAmple u'.G u'.PP.L ∧ Out.KTriv u'.G u'.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ m')
  obtain ⟨w, hw, -⟩ := n.lin
  exact ⟨MorphismProperty.of_isPullback n.cart.1 hP,
    relAmple_pull n.cart.1 u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S') (fun _ => trivial) hA,
    kTriv_pull n.cart u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem bijective_appLE {X X' : Scheme.{0}} (j : X' ⟶ X) [IsOpenImmersion j] {U : X.Opens} {U' : X'.Opens}
    (h : j ''ᵁ U' = U) (e : U' ≤ j ⁻¹ᵁ U) : Function.Bijective (j.appLE U U' e).hom := by
  subst h
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (j.appIso U').hom

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  rw [← Scheme.Hom.appLE_map m h (homOfLE e).op]
  rfl

theorem app_appLE {X X' G G' : Scheme.{0}} {φ : G' ⟶ G} {p' : G' ⟶ X'} {p : G ⟶ X} {j : X' ⟶ X}
    (sq : φ ≫ p = p' ≫ j) {U : X.Opens} {U' : X'.Opens} (e : U' ≤ j ⁻¹ᵁ U) {O : G.Opens} (h : O ≤ p ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ O ≤ p' ⁻¹ᵁ U') (r : Γ(X, U)) :
    (φ.app O).hom ((p.appLE U O h).hom r) = (p'.appLE U' (φ ⁻¹ᵁ O) h').hom ((j.appLE U U' e).hom r) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 3

theorem valR_comp_appLE {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) {O : Z.Opens}
    {O' : Y.Opens} (e : O' ≤ m ⁻¹ᵁ O) (hz : ⊤ ≤ z ⁻¹ᵁ O') (f : Γ(Z, O)) :
    valR (z ≫ m) O f = valR z O' ((m.appLE O O' e).hom f) := by
  rw [GlobalTheory.CechKS.valR_comp_app, ← GlobalTheory.CechKS.valR_resG z e hz]
  rfl

theorem isKS_of_openImmersion {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} [IsOpenImmersion j]
    (m : SABMap t' t j) (cp : ChartPull t'.PP.L t.PP.L m.φ) (V : X.Opens) (U : X.affineOpens) (hUV : U.1 ≤ V)
    (U' : X'.affineOpens) (hU : j ''ᵁ U'.1 = U.1) (ψ : Γ(X, U.1) ≃+* Γ(X', U'.1)) (e : U'.1 ≤ j ⁻¹ᵁ U.1)
    (hψ : ∀ r, ψ r = (j.appLE U.1 U'.1 e).hom r) (hch : chart U' ≫ j = spMap ψ.toRingHom ≫ chart U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left))
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ m.φ = spMap (dualMap ψ.toRingHom) ≫ v i)
    (D : Γ(X, U.1) → Γ(X, U.1)) (D' : Γ(X', U'.1) → Γ(X', U'.1)) (hD : ∀ r, D' (ψ r) = ψ (D r))
    (Θ : Matrix (Fin n) (Fin n) Γ(X', U'.1)) (h : IsKS t' ⊤ U' v' D' Θ) : IsKS t V U v D (Θ.map ψ.symm) := by
  obtain ⟨J, W, c, d, hcov, hWc, hd, hl, hr⟩ := h
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  rw [inf_top_eq] at hcov
  have hWU : ∀ i, W i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun i => hcov ▸ le_iSup W i
  have hpre : t'.G.hom ⁻¹ᵁ U'.1 = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, sq, Scheme.Hom.comp_preimage, ← hU, Scheme.Hom.preimage_image_eq]
  have hle : ∀ i {O : t.G.left.Opens}, O ≤ m.φ ''ᵁ W i → m.φ ⁻¹ᵁ O ≤ W i := fun i O hO =>
    (m.φ.preimage_mono hO).trans (m.φ.preimage_image_eq (W i)).le
  choose d₂ hd₂ hd₂' using fun i => GlobalTheory.LogKS.isField_image _ _ m.φ (W i) (d i) (hd i)
  refine ⟨J, fun i => m.φ ''ᵁ W i, fun i => cp.idx (c i), d₂, ?_, fun i => ?_, hd₂, fun i hW r => ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hcov, hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_eq_left.2 hUV,
      inf_eq_right]
    apply t.G.hom.preimage_mono
    rw [← hU]
    exact j.image_le_opensRange _
  · rintro _ ⟨y, hy, rfl⟩
    exact cp.le _ (hWc i hy)
  · have hinj : Function.Injective (m.φ.app (m.φ ''ᵁ W i)).hom :=
      (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ W i))).1
    apply hinj
    have h1 := hle i le_rfl
    rw [hd₂' i _ le_rfl, app_appLE sq e hW (h1.trans (hWU i)), app_appLE sq e hW (h1.trans (hWU i)), ← hψ, ← hψ,
      ← hD, ← resG_appLE _ _ (hWU i) h1, (hd i).2.2 _ _ h1 le_rfl, hl i (hWU i), resG_appLE]
  · intro i i' O hO f S _ φ g₀ w hg hO₀ hT
    have hOi : O ≤ m.φ ''ᵁ W i := hO.trans inf_le_left
    have hOi' : O ≤ m.φ ''ᵁ W i' := hO.trans inf_le_right
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : Sp S ⟶ t'.G.left, g₁ ≫ m.φ = g₀ :=
      ⟨IsOpenImmersion.lift m.φ g₀ (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨z, -, hz⟩ := hOi (hO₀ (Set.mem_univ y))
        exact ⟨z, hz⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨φ₁, rfl⟩ : ∃ φ₁ : Γ(X', U'.1) →+* S, φ₁.comp ψ.toRingHom = φ :=
      ⟨φ.comp ψ.symm.toRingHom, RingHom.ext fun r => by simp⟩
    have hg₁ : g₁ ≫ t'.G.hom = spMap φ₁ ≫ chart U' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg, Category.assoc, hch, ← Category.assoc]
      congr 1
      exact Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ₁)
    choose w₁ hw₁ hT₁ using fun a => GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.toRingHom (chart U) (chart U') hch
      (v a) (v' a) (hv a) (hv' a) (hvv a) S φ₁ g₁ hg₁ (w a) (hT a)
    obtain rfl : w = fun a => w₁ a ≫ m.φ := funext fun a => (hw₁ a).symm
    have hO₁ : ⊤ ≤ g₁ ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := hO₀
    have key := hr i i' (m.φ ⁻¹ᵁ O) (le_inf (hle i hOi) (hle i' hOi')) ((m.φ.app O).hom f) S φ₁ g₁ w₁ hg₁ hO₁ hT₁
    have hgc : ⊤ ≤ g₁ ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) :=
      hO₁.trans (g₁.preimage_mono (le_inf ((hle i hOi).trans (hWc i)) ((hle i' hOi').trans (hWc i'))))
    have hwc : ∀ b, ⊤ ≤ w₁ b ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) := fun b =>
      GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ S φ₁ (chart U') g₁ (v' b) (w₁ b) hg₁ (hv' b) (hT₁ b)) hgc
    have hgp := GlobalTheory.chartPull_g_appLE _ _ _ _ m.φ cp (c i) (c i')
    have hgi : ((t'.PP.L.g (c i) (c i'))⁻¹).val = (m.φ.appLE _ _
        (le_inf (inf_le_left.trans (cp.le (c i))) (inf_le_right.trans (cp.le (c i'))))).hom
        ((t.PP.L.g (cp.idx (c i)) (cp.idx (c i')))⁻¹).val :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hgp, ← map_mul, Units.mul_inv, map_one])
    rw [GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂' i O hOi, hd₂' i' O hOi', key]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgp, hgi]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) (congrArg TrivSqZeroExt.snd ?_) ?_))
      (congrArg TrivSqZeroExt.snd ?_)
    · exact (valR_comp_appLE (w₁ b) m.φ _ (hwc b) _).symm
    · exact (valR_comp_appLE g₁ m.φ _ hgc _).symm
    · exact (GlobalTheory.CechKS.valR_comp_app (w₁ a) m.φ O f).symm

def derivMap {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    ((ψ.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp ψ.symm.toAddMonoidHom)) fun a b => by
      simp

theorem derivMap_apply {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) (r : A) :
    derivMap ψ D (ψ r) = ψ (D r) := by
  simp [derivMap]

theorem exists_isKS_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U hUV t' ⟨m'⟩ hP hA hK n v hv hb D
  obtain ⟨u, m, ⟨cp⟩⟩ := exists_pull_chart (chart U) t
  obtain ⟨hP', hA', hK'⟩ := proper_ample_kTriv m' m hP hA hK
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let U' : (Sp Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(X, U.1) ≃+* Γ(Sp Γ(X, U.1), U'.1) := RingEquiv.ofBijective _ (bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v', hvv, hv', hb'⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H X _ t u (chart U) m _ _ ψ.toRingHom (chart U) (chart U') hch n v hv hb
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ u hP' hA' hK' U' n v' hv' hb' (derivMap ψ D)
  exact ⟨_, isKS_of_openImmersion m cp V U hUV U' hU ψ e (fun _ => rfl) hch v v' hv hv' hvv D _
    (derivMap_apply ψ D) Θ hΘ⟩

end GlobalTheory.KSOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelPreservingLatticeIsoOfMembersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelPreserving_latticeIso_of_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (t₀ : X₀ → V₀) (δ₀ : I → X₀ → X₀) (𝔪₀ : GlobalTheory.GSep.GMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔪₀.LatTo 𝔪 := by
  first | exact @GlobalTheory.GSep.Cmp.exists_latTo_of_members | exact GlobalTheory.GSep.Cmp.exists_latTo_of_members | (intros; apply GlobalTheory.GSep.Cmp.exists_latTo_of_members <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_killed_char_of_torus_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.GSep.TorLabel.exists_torus_char | exact GlobalTheory.GSep.TorLabel.exists_torus_char | (intros; apply GlobalTheory.GSep.TorLabel.exists_torus_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmple
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_isNef_shift_pow_tens : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hC hN k _ X _ p D hX L A n hL hLf hA hAn
  obtain ⟨m, N, s, hm, hs⟩ := GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre hN k X p D hX L A n hLf hA
  obtain ⟨t, -, ht⟩ := GlobalTheory.T.nef_shift_of_generated_at_charZero_points hC k X p D hX ((L.pow n).tens A) m N s hm hs
    ((hL.pow n).tens hAn.semiPos) (GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens k X p D hX L A n hLf (nefFib_of_isNef hAn))
  exact ⟨t, ht⟩

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_sec_separating_two_points_of_ample : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hlc hNamp hnum
    hx₁ hx₂ hne hh hvol hsum
  set S : ℚ := ∑ e ∈ Finset.Icc 1 n, h e with hS
  set ε : ℚ := (ρ - S) / (n + 1) with hε
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hn1
  have h1 : ((n : ℚ) + 1) * ε = ρ - S := by rw [hε]; field_simp
  have hsplit : ∑ e ∈ Finset.Icc 1 n, (h e + ε) = S + n * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp [hS]
  obtain ⟨D, d, hd, hQ, hcase⟩ := GlobalTheory.T.twoPoint_induction_kltPair_separation hP hNV hNef X p n hproj hdim Δ m G N ε h x₁ x₂
    hΔ hklt hm hlc hNamp hx₁ hx₂ hne hh hvol hεpos
  have hdρ : d < ρ := by
    have h2 : (n : ℚ) * ε + ε = ρ - S := by rw [← h1]; ring
    linarith
  rcases hcase with ⟨hlc1, hnk2⟩ | ⟨hlc2, hnk1⟩
  · obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₁ x₂ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₁ hne hlc1 hnk2
    exact ⟨s, Or.inl ⟨hs1, hs2⟩⟩
  · obtain ⟨s, hs2, hs1⟩ := GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint hNV X p n hproj hdim M Δ m G N D ρ d x₂ x₁ hM hΔ hm hlc
      hNamp hnum hQ hdρ hx₂ (Ne.symm hne) hlc2 hnk1
    exact ⟨s, Or.inr ⟨hs2, hs1⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_labelled_cover_of_odd_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  first | exact @GlobalTheory.Mum.UCover.labCover | exact GlobalTheory.Mum.UCover.labCover | (intros; apply GlobalTheory.Mum.UCover.labCover <;> assumption)
end

