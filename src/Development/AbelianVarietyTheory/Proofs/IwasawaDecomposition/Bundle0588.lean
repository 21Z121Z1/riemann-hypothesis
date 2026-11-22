import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0517
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRational
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

noncomputable section

namespace GlobalTheory.ChiRatStd

open GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT

set_option maxHeartbeats 1600000 in

theorem chiRatAll_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (L : (I.stp u a i).Cl → Submodule (𝓞 B.host.E) (B.sp.X i).V) (hL : L = I.latAt u a i)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (L c.1)))
    (k : Ch → TC.GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (hfin : ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) (β : Ch) :
    Formalism.L2.G.Cmp.ChiRatAll (K β).lev B.embLL := by
  subst hL
  obtain ⟨c, rfl⟩ := hR.onto β
  intro κ
  have hF : ChiFin I l Z (K (chOf c)).lev := by
    obtain ⟨n, hn, h⟩ := hfin (chOf c)
    exact ⟨n, hn, fun κ _ => h κ⟩
  obtain ⟨x, hx, ⟨q, hq⟩, -⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hP l Z u a i hi bad Ch chOf K k hR c hF κ
  obtain ⟨κ', hg, hq', -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hc := hR.chr c x κ' hg (by rw [hq']; exact hq)
  exact ⟨_, by rw [← hx]; exact hc.symm⟩

set_option maxHeartbeats 1600000 in

theorem chiRatAll_twChart : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch),
    V4.MuIsW (w.st Z) f T Wt w.I.xi →
    ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
    ∀ (u : (w.D Z).what₂.Word) (μ : (w.D Z).what₂.Tup) (hμ : μ ≠ (w.D Z).what₂.mu0) (j : ℕ) (hj : j + 1 ≤ (w.D Z).R.m)
      (β : tt.ch.Ch u μ (j + 1)),
      Formalism.L2.G.Cmp.ChiRatAll (tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (w.D Z).what₂.embLL := by
  intro K B f T w _ _ _ Z t Wt nch n _ tt hstd u μ hμ j hj β
  obtain ⟨k, hR⟩ := hstd.1.reads u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  exact chiRatAll_of_reads w.I w.ok w.pins w.l Z u μ (j + 1) hj _ _ _ (hstd.1.lat u μ (j + 1))
    (fun β => tt.forms.ch u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) k hR
    (fun β => tt.forms.chi_fin u μ hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β) β

end GlobalTheory.ChiRatStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.CmDim

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 4 * D.R.ord := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.toFrame.natCard_GG
  rw [← h2, ← h1, h4]

theorem two_mul_card_psi (φ : Formalism.HC.Frame) : 2 * Nat.card φ.Psi = 4 * φ.ord := by
  classical
  have h4 : Nat.card φ.GG = 4 * φ.ord := φ.natCard_GG
  have hfin : Finite φ.GG := Nat.finite_of_card_ne_zero (by rw [h4]; have := φ.ord_pos; omega)
  have e1 : {g : φ.GG // g ∈ φ.Psi} ≃ {g : φ.GG // ¬ g ∈ φ.Psi} :=
    (Equiv.mulRight φ.cc).subtypeEquiv fun g => mem_Psi_iff_mul_cc_notMem g
  have h1 := Nat.card_congr (Equiv.sumCompl fun g : φ.GG => g ∈ φ.Psi)
  rw [Nat.card_sum, ← Nat.card_congr e1, h4] at h1
  exact (two_mul _).trans h1

theorem card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.E / 2 := by
  have h1 := two_mul_card_psi D.R.toFrame
  have h2 := Nat.card_congr D.eTau
  rw [Nat.card_eq_fintype_card] at h2
  have h3 := finrank_host D
  omega

theorem cmList_nonempty {D : D7} (A : Amb D) : Nonempty (CmList A) := by
  let ψ : D.what₂.Tau → GlobalTheory.AllWt.Psi A.H := fun t => ⟨DV.tauEmb D t, A.cm t⟩
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b h
      exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
    · rintro ⟨τ, hτ⟩
      obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
      have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
      rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt, h3] at hτ
      obtain ⟨t, ht⟩ := (exists_tauEmb_iff D g).2 (((factEmb D.R D.host).2 g).1 hτ)
      exact ⟨t, Subtype.ext ht.symm⟩
  exact ⟨⟨Equiv.ofBijective ψ hb, fun _ => rfl⟩⟩

theorem cm_dim : ∀ (D : D7) (A : Amb D), Nonempty (CmList A) ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧
    ∀ (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (i : s.Comp),
      (Φ.C i).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  intro D A
  refine ⟨cmList_nonempty A, ?_, fun N j S κ s Φ i => ?_⟩
  · rw [finrank_host]
    have h : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right two_pos D.host.two_le_e
    have h' : 2 ^ D.R.e ≤ D.R.ord := by
      exact D.R.toFrame.two_pow_le_ord
    omega
  · rw [Φ.dim_eq i, Formalism.DegreeFormula.dimFl, card_tau]

end GlobalTheory.ShFam.CmDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom.KeyHol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (x₀ : Frame (U.X k).Ψ r)
    (hx₀ : x₀ ∈ (U.X k).dom) :
    ∃ (m : ℕ) (f : Rul Xo c), f ∈ sec Xo c 0 (2 * (m + 1)) ∧ Formalism.L2.PjFree.rdU U f k x₀ ≠ 0 := by
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by norm_num
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (GlobalTheory.EtaForm.LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => U.un k ⟨x₀, hx₀⟩)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → GlobalTheory.EtaForm.LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (GlobalTheory.EtaForm.shiftFam 3 0)
  have hpos : 0 < Nat.card (GlobalTheory.EtaForm.LevGrp Dw (3 ^ 4)) := Nat.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨m, f, by have := hsec f hrule; rwa [hm] at this, ?_⟩
  have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) (U.un k ⟨x₀, hx₀⟩)
    (hT _ _)).1
  have h0 := hne 0 _ hv
  have e1 : Formalism.L2.PjFree.rdU U f k x₀ = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x₀, hx₀⟩)) := dif_pos hx₀
  rw [e1]
  exact h0

end GlobalTheory.CuspFrom.KeyHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.UntwSat

theorem stepW_seed_fixed : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      (∃ F₀, SeedW K B.toPre f B.KsC F₀ px Set.univ ⊤) → ∃ F₀, SeedW K B.toPre f B.KsC F₀ px ↑T.pl B.fixedCoefficientFieldInComplex := by
  refine evG_all fun K => ?_
  choose S S₁ hS₁ hS using GlobalTheory.T.exists_uniform_normalisedAdelicSeeds K
  refine ⟨fun P f F => S₁ P f F, fun P f F _ => S P f F ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun _ _ _ _ _ => ∅, fun P f F => hS₁ P f F, by simp, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => ?_⟩
  obtain ⟨F₀, h⟩ := hS _ _ _ px hs
  refine ⟨F₀, h.mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.1 z hz

theorem isBaseEnlargementFixedCoefField_of_same_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hLL : B₀.LLC ≤ B.fixedCoefficientFieldInComplex) : Enl0 B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, -, rfl⟩
    exact (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (B.fixedField_le_coefficientField (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩)))

theorem dat_saturated_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧
        DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧
        (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧
        ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep).and stepW_seed_fixed).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨F₀, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, -, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ :=
    hsd w.px ⟨_, hs⟩
  have hE : Enl0 B₀ B := isBaseEnlargementFixedCoefField_of_same_fields hB₀ hKs hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  have hsub : ∀ x : (w₀.D Z₀).what₂.LL, ∃ y ∈ (w.D Z).LL0, (w.D Z).what₂.embLL y = (w₀.D Z₀).what₂.embLL x :=
    fun x => (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine', ?_, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl
  · intro v₁ v₂ hov hv₁
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).1 hv₁ with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v₁
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v₁ hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).2 (Or.inl h))
      have hB₂ := GlobalTheory.T.placesOverFixedField_same_coefficient_place (w₀.D Z₀) (w.D Z) hsub v v₁ v₂ hov hB
      have hv₂ := (hExt.W1 v v₂ hB₂).1 hv
      rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).1 hv₂ with h₂ | h₂
      · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inl h₂)
      · obtain ⟨j, y, -, hne⟩ := h₂
        exact absurd rfl hne
    · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inr (GlobalTheory.Mem.SatForced.mem_W1F_of_overOne K (w.D Z) v₁ v₂ hov h))

end GlobalTheory.Mem.R3.Rw.UntwSat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmSwap

theorem rename_swap_antisymm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι)
    (i j : Fin (m τ)), i ≠ j →
      rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  intro ι _ _ m Q τ i j hij
  set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu
  have hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))
        = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m) := by
    intro w
    funext ⟨t, k⟩
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]
    by_cases ht : t = τ
    · subst ht
      simp only [hu, Function.update_self]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩ := fun h => ht (congrArg Sigma.fst h)
      have h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩ := fun h => ht (congrArg Sigma.fst h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]
      rfl
  have hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1 := by
    rw [Fintype.prod_eq_single τ]
    · simp [hu, Equiv.Perm.sign_swap hij]
    · intro t ht
      simp [hu, Function.update_of_ne ht]
  have hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t) := by
    intro w
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]
  unfold GlobalTheory.GoodMetric.antisymm
  rw [map_sum]
  simp_rw [map_zsmul, rename_rename, hf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_
  intro w _
  simp only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]

end GlobalTheory.AntisymmSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory

theorem X_sub_X_dvd_sub_aeval_update_variable {σ : Type} [DecidableEq σ] (a b : σ) (P : MvPolynomial σ ℝ) :
    (X b - X a : MvPolynomial σ ℝ) ∣ P - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [aeval_C]
  | add p q hp hq =>
    have h := dvd_add hp hq
    rw [map_add]
    convert h using 1
    ring
  | mul_X p c hp =>
    rw [map_mul, aeval_X]
    have h2 : (X b - X a : MvPolynomial σ ℝ) ∣ X c - Function.update X b (X a) c := by
      by_cases h : c = b
      · subst h; simp
      · simp [Function.update_of_ne h]
    have e : p * X c - aeval (Function.update X b (X a)) p * Function.update X b (X a) c
        = (p - aeval (Function.update X b (X a)) p) * X c
          + aeval (Function.update X b (X a)) p * (X c - Function.update X b (X a) c) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right h2 _)

theorem swap_odd_dvd : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ,
    rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  intro σ _ a b hab P hP
  have hcomp : (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) ∘ (Equiv.swap a b)
      = Function.update X b (X a) := by
    funext i
    simp only [Function.comp_apply]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hab]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, Function.update_of_ne hab, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have h1 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = - aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P := by
    have := congrArg (aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a))) hP
    rw [aeval_rename, hcomp, map_neg] at this
    exact this
  have h0 : aeval (Function.update (X : σ → MvPolynomial σ ℝ) b (X a)) P = 0 := self_eq_neg.mp h1
  have := X_sub_X_dvd_sub_aeval_update_variable a b P
  rwa [h0, sub_zero] at this
end GlobalTheory
end

