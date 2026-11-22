import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkBrest
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0100
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0108
import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0010
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0047
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipalStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
  ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' := by
  first | exact @_root_.GlobalTheory.TieLift.lift_principal_alt | exact _root_.GlobalTheory.TieLift.lift_principal_alt | (intros; apply _root_.GlobalTheory.TieLift.lift_principal_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.link_brest_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm), Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm → RemainingDivisionBounds Fm 2 CH :=
  fun 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie =>
    _root_.Formalism.L2.DIV.RestAll.bRest_all_alt 𝒜 2 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowThree
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem rowThreeAt_of_setup_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    RowOnAt L X.ρ (fun l => l = 3 ∧ l ∉ D.host.small) 6000 30000 := by
  rintro i hTw ⟨h3, hs⟩ π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have h2 : D.nd.l i ≠ 2 := by omega
  have hq : D.nd.l i ≠ D.host.q := h3 ▸ (three_ne_q D).1
  have hd : D.nd.l i ≠ D.host.d := h3 ▸ (three_ne_q D).2
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k => h3 ▸ three_ne_g D k
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hle : D.nd.l i ≤ D.host.splitBound := by have := S.split; omega
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small hl).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, D.host.cls_splitK_or_small hl hle hq hd,
    fun _ v hv => GlobalTheory.HubLoc.ramIdx_eq_one D.host hl hN v hv, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := D.host.split_small _ hl h2 hle
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (cycAt_of i fun e => absurd e h2) hL (decl_split D i h2 hj) (locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs0 : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hs
  have hsl : D.nd.s0 i = RowSmall.sl D (D.nd.l i) := by
    unfold RowSmall.sl
    rw [hs0, Nat.factorization_eq_zero_of_not_dvd hN]; rfl
  have hh := h0_le D i dc.col (fun e => absurd e h2) hs0.ge (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine bound_smallPrime_of_splitBound_cyclotomic_of_level_eq L P X.ρ S.kill S.sha i hTw hsl π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
end UpperTheory.N
theorem UpperTheory.N.exists_nonneg_threeC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.rowThreeAt_of_setup_alt hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowTwo
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.onAt_eq_two_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowOnAt L X.ρ (fun l => l = 2) 6000 30000 := by
  intro i hTw h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hs : D.nd.l i ∈ D.host.small := by rw [show D.nd.l i = 2 from h2]; exact UpperTheory.Small.two_mem D.host
  have h4 : 2 ^ 2 ∣ D.host.QS := (pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun _ => (h4.mul_right _).mul_right _) hL (UpperTheory.N.Two.decl_split D i h2)
    (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs2 : 2 ≤ D.nd.s0 i := by
    rw [D.nd.restNLevelExponent_of_two i h2]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization D.host.QS_pos.ne').1 h4
  have hh := UpperTheory.N.h0_le D i dc.col (fun _ => hs2) (by omega) (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_twoC_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.onAt_eq_two_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneMapOfRowsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_of_bundle_setAt_lin_inj_const_formula : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | exact _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions | (intros; apply _root_.GlobalTheory.BigTop.Fun.oneMap_of_bundle_setAt_kernel_conditions <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPath
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.OntoPath
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem onto_path_alt : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' →
    _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon
end GlobalTheory.BigOn.OntoPath
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageStStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.page_estimate_statement' : _root_.GlobalTheory.BigOn.PageStatement := by
  first | exact @_root_.GlobalTheory.BigOn.pageSt_alt | exact _root_.GlobalTheory.BigOn.pageSt_alt | (intros; apply _root_.GlobalTheory.BigOn.pageSt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PolynomialBoundSetup
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_jumps_aux2_of_setup : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  first | exact @_root_.GlobalTheory.TheoremBQD.main_alt_alt | exact _root_.GlobalTheory.TheoremBQD.main_alt_alt | (intros; apply _root_.GlobalTheory.TheoremBQD.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank
local instance  {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}
end General
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem rank_at_twisted_places_of_rec_span (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O)
    (hMax : ∀ v ∈ p.R.twPl, ∀ j,
      GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v))
    (hSp : LeafSpan O) (hD : LeafData O)
    (hCmp : ∀ v ∈ p.R.twPl, ∀ j,
      letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
      GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (hrec.1.ok.laws v).p (fw2 p) j (r.lev j)
        (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v)) :
    GlobalTheory.TraceClassRank.RankAtPlaces O := by
  obtain ⟨hC, hOk, hLU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hX := hOk.irr
  have h1 := hC.grp.levels
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩
  have hProj : LeafProj O := (level_of_tied ⟨z, act, y, ht⟩ hX h1).2.2
  have hd : ∀ j, FormsDetermined (R2 p) j := fun j =>
    formsDetermined_of (GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj.of_char GlobalTheory.LowTypeRestriction.resInj _ _ hC) hC.models.HW hLU
  have hComm : ∀ j (g : Mir (R2 p)), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j := fun j g => by
    obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
    exact tie_e_comm_rho (ht v₁ j).1 (ht v₁ j).2 hOk.irr g
  have key : ∀ v ∈ p.R.twPl, ∀ j, (O.ThJ v j).FG ∧
      O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := fun v hv j => by
    have hv' : v ∈ (R2 p).twPl := hv
    have hdel : ∀ x, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range := fun x => by
      obtain ⟨a, ha⟩ := Formalism.L2.Pj.FO_le _ (hm.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) x)
      exact ⟨a, ha⟩
    have hty := GlobalTheory.T.baseTupleThetaSpan_hasType _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j hLU (hd j) v hv'
      hC.tup.mu_on hdel (fun u => chi_eq_one h1 hC.grp.chiW j u.2)
    exact tie_thetaJ (ht v j).1 (ht v j).2 (mirIncl_injective _) hU (hd j) (hMax v hv j) hty (hrec.1.ok.run v hv' j)
      (hCmp v hv j)
  exact GlobalTheory.T.eigenlattice_local_containment_at_pairs _ _ _ _ _ _ O hSp hD hProj hComm fun w hw =>
    ⟨fun j => key w hw j, fun j => key _ (conjPl_mem_twPl hC hw) j⟩
end Point
end GlobalTheory.BigOn
theorem GlobalTheory.BigOn.rankLocSt_of_max_geo_runs : _root_.GlobalTheory.BigOn.MaximalityStatement → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  intro hM hG hC
  refine ((hM.and hG).and hC).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨x1, H1⟩, ⟨c0, H2⟩⟩, ⟨x3, H3⟩⟩ := H
  refine ⟨c0, fun c hc hb => ?_⟩
  obtain ⟨x2, H2'⟩ := H2 c hc hb
  refine ⟨max x1 (max x2 x3), fun x hx hle i p hR hm r O hrec => ?_⟩
  have hle1 : x1 ≤ x := (le_max_left _ _).trans hle
  have hle2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hle3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hg := H2' x hx hle2 i p hR hm r O hrec
  exact _root_.GlobalTheory.BigOn.rank_at_twisted_places_of_rec_span hR hm hrec (H1 x hx hle1 i p hR hm) hg.2.1 hg.2.2.2.1 (H3 x hx hle3 i p hR hm r hrec.1.ok hrec.2)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem ratHyp0_at_point_alt : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  intro eps Fm x hx i p hp hM t ht hlow j
  obtain ⟨hc, -, hu, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hTie : TieIn p.T p.R.toRealDat p.κ p.v₀ :=
    ⟨p.fw.laws, p.fw.alg_eq, p.fw.kap, p.fw.hv₀, p.fw.chiR, p.fw.x0⟩
  exact
    { size := (Fm.parT x hx i).nV_ge
      host := p.host
      std := GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)
      laws := p.fw.laws
      core :=
        { lev := hc.lev
          grp := ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩
          fam := ⟨hc.fam.tie, hc.fam.Sb, hc.fam.roots, hc.fam.pl_onto, hc.fam.degR, hc.fam.degL, hc.fam.muVal, hc.fam.etaVal⟩
          models := ⟨hc.models.inf, hc.models.vpos, hc.models.cX, hc.models.cV, hc.models.prX, hc.models.HX, hc.models.HV,
            hc.models.HE, hc.models.HW, hc.models.gE, hc.models.gW, hc.models.jX, hc.models.jV, hc.models.νY, hc.models.νY',
            hc.models.ν0, hc.models.νX, hc.models.νV, hc.models.νW, hc.models.BV, hc.models.order⟩
          chain := ⟨hc.chain.ωY, hc.chain.ωX, hc.chain.vY, hc.chain.vX, hc.chain.ptY, hc.chain.ptX, hc.chain.ItY, hc.chain.ItX,
            hc.chain.ioY, hc.chain.ioX, hc.chain.Th⟩
          thP := ⟨hc.thP.ωP, hc.thP.vP, hc.thP.pt_theta, hc.thP.ioP, hc.thP.thF_mem, hc.thP.thF, hc.thP.thG⟩ }
      unif := hu
      fw := ⟨p.fw⟩
      tieIn := hTie
      io := hp.ioExt
      guard := p.qGuard
      fin := GlobalTheory.BigOn.Check.finite_tuples_of_indefiniteSidePoint p
      pins := p.pins j
      phase := p.phase j hu
      galois := (Fm.ties x i).baseField_isGalois
      small := hM.2.2.small
      inUse := ht
      low := hlow }
end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdm
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem recSide_of_twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.RecursiveSide := by
  intro hA
  refine Formalism.MainNotions.Closed.imp hA fun Fm CH _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p hr hm w hw j Z hRat => ?_⟩
  obtain ⟨hOK, -, -⟩ := H x hx h0 i p hr hm w hw j
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hU : p.R.toRealDat.LUnif := hL.2.2.1
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have T := Z.tie ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hAR := GlobalTheory.SeriesTie.actRead_realRd _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ Z.ρ Z.good
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) Z.pin hU hW
  have hS : Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun a => hr.ties.data _ j _ a fun u => ?_
    have hm0 := GlobalTheory.ExportType.thetaSeriesDatum_mem_levelTypeForms T hAR a
    exact sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hm0 u))
  have hb : baseSet (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) =
      Set.range ((Fm.D x i).nexp.th ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) :=
    (range_th T).symm
  have ht : (⋃ a ∈ Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1)
        ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) =
      twSet Z.good (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) ((Fm.ex x hx i).nch.k' w)
        ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) := by
    rw [hS, Set.biUnion_univ, iUnion_thPsi T hOK]
    ext y
    exact ⟨fun ⟨s, h, P, hd, _, hy⟩ => ⟨s, h, P, hd, hy⟩, fun ⟨s, h, P, hd, hy⟩ => ⟨s, h, P, hd, hRat.1 s h P hd, hy⟩⟩
  refine ⟨?_, ?_⟩
  · unfold baseLat
    rw [hb, hS, Set.image_univ, ← Set.range_comp]
    rfl
  · unfold twLat
    rw [ht]
end GlobalTheory.BigOn.Exp
end
end
end

