import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadingRealSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0801
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0777
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0791
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0793
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0780
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0788
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0719
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0799
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0013
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

theorem ncard_eq_of_splits {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq E p hp fun P hP hpP => ?_
  have := hP.isPrime
  refine ⟨h ⟨P, hP.isPrime, fun h0 => ?_⟩ hpP, GlobalTheory.Mem.RaySplit.not_mem_sq hp hpP
    ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 hd P hP.isPrime hpP)⟩
  rw [h0] at hpP
  exact hp.ne_zero (by simpa using hpP)

theorem exists_preTie : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Rw : RowSide D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D R.C Rw (lowAll D) Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → (∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)) → (∀ j : Fin D.R.m, (R.FW j).IsKsForm) → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → TauTrue Bs.exp → CharSide D R.C → ValLL0 D R.C → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → (∀ v, NG.OverPl (Pq v) v) → IsChoice (D := D) (Set.range Pq) → (∀ t, ∀ P ∈ R.Q t, P ∈ Set.range Pq) → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) → (∀ j, FWT.VStd D j) → Nonempty (GlobalTheory.HeightCounting.SerCopy.PreTie (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ Bs.exp hF Pq) := by
  intro hA D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG kKs hk Rw Pq hL eig θ Bs Sb v₀ hF pins intersectionNumber_baseChange hv hK hH hSb hτ cs hV hsp hPq hch hQ
    ⟨Z, hZ⟩ hstd
  have hC : R.Char3 F := RealDat3.characterisation_of_weak pins.char intersectionNumber_baseChange.aux.ex
  obtain ⟨p1, -, d1, n1⟩ := hZ.places.splits D.host.pde (by simp)
  obtain ⟨p2, -, d2, n2⟩ := hZ.places.splits D.host.pde' (by simp)
  have hq : ∀ p : ℕ, ¬ (p : ℤ) ∣ discr D.host.E → p ≠ D.host.q := fun p h e =>
    h (Int.natCast_dvd.2 (e ▸ SetupPin.q_dvd_discr D))
  have h2 : 2 ∈ lowAll D := by simp [lowAll, lowPr]
  have hd : (discr D.host.E).natAbs.primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp)))
  have hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)))
  obtain ⟨ρ, hρ, hp, hlv, hρch, hbad⟩ := GlobalTheory.SeriesTie.ComplexCh.exists_setup_ch R cG F hC GlobalTheory.weilRepresentationUnitaryPair
    (SetupPin.goodSetup_badPlaces_conj _ Bs.tw) (SetupPin.goodSetup_placesOverTwo_subset _ Bs.tw h2) (SetupPin.goodSetup_count_eq_zero_off_badPlaces _ Bs.tw h2 hd hc)
    (SetupPin.exists_art_gal hA _ Bs.deltaRead) (SetupPin.mk_frac_Ok Bs.twF)
    ⟨ncard_eq_of_splits p1 d1 n1, ncard_eq_of_splits p2 d2 n2⟩ ⟨hq _ d1, hq _ d2⟩ (fun _ => Set.range Pq) (fun _ => hch)
    (fun i P ⟨t, h1, _⟩ => hQ t P h1)
  have hch' : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq) := fun i P _ => by rw [hρch]
  choose ν hν using fun i j b => exists_isScalar (ysOf Bs) v₀ hρ i j b
  have hFa : ∀ i j b, Faithful (realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) := fun i j b =>
    GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ R cG _ (ysOf Bs) v₀ ρ hρ i j b _ (hν i j b).ne intersectionNumber_baseChange.prim.unif hC.models.HW
      (hv j) (hK (idxOf D ((j : ℕ) + 1)))
  choose PV₀ hPV₀ _ using fun j => GlobalTheory.MtRead.exists_idFrame D hF j (hstd j)
  obtain ⟨rdV, hon, hjoin⟩ := GlobalTheory.MtRead.exists_reading hA D R.C Rw (lowAll D) Pq _ hL eig θ Bs hτ cs hV hsp hPq Γ Pl0 I0 T A3 Ks R F
    cG hC.lev rfl pins.keep hF PV₀ hPV₀ ρ hρ hp hlv hch'
  obtain ⟨Dat, th, lev, thPsi, h1, thU, thP, MtLat, g2, g3, -, t, ht⟩ := GlobalTheory.SeriesInstall.exists_tie_withSeries D ρ hρ
    (fun i j b => realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) hFa hlv (GlobalTheory.SeriesTie.latFG_of_good D _ _ ρ hρ) rdV hon
  refine ⟨{
    Dat := Dat, th := th, lev := lev, thPsi := thPsi, h1 := h1, thU := thU, thP := thP, MtLat := MtLat, h2 := g2, h3 := g3
    ρ := ρ, good := hρ, pin := hp, vec := hv, ν := ν, scalar := hν, tie := t
    hecke := fun i j b => (heckeRead_iff_tie.1 (GlobalTheory.T.secondStep_heckeOperators_normalisedSums D Γ Pl0 I0 T A3 Ks R cG kKs hk R.C Rw (lowAll D) Pq hL eig θ Bs Sb v₀
      ρ hρ hp hC.lev hC.allPl hH hSb i j b (ν i j b))).1
    bad := hbad, ch := hch'
    join := fun PV hPV i j b k Q ψ hAd hT => ?_ }⟩
  obtain ⟨ω, hω, he⟩ := hjoin i j b k Q ψ hAd hT
  refine ⟨ω, hω, fun f g => ?_⟩
  rw [← he f g, GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices D _ _ hF (PV j) (PV₀ j) (hPV j) (hPV₀ j) g]
  exact congrFun (congrArg (fun r => r k Q ψ f) (ht i j b)) _

end GlobalTheory.HeightCounting.SerCopy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedRealizationPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open RealOfReading

theorem tied_of_layer : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ X : GlobalTheory.NRows.Tied hL (w.D Z), PinAt c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  intro hP hL
  refine Model.AtMem.imp (Model.AtMem.and (GlobalTheory.T.exists_local_langlands_place_datum hP hL) (Model.AtMem.and (GlobalTheory.T.coefficient_field_eq_level hP hL)
    (Model.AtMem.and (GlobalTheory.T.xi_character_matches_type hP hL) (Model.AtMem.and (GlobalTheory.T.theta_eigenvalue_gap_bound hP hL)
    (Model.AtMem.and (GlobalTheory.T.types_true_local hP hL) (Model.AtMem.and (GlobalTheory.T.exists_eigen_index_labeling_at_member hP hL)
    (Model.AtMem.and (GlobalTheory.T.nonempty_agree_real_of_read_galois hP hL) (GlobalTheory.T.realOfRead_goodIdempotent_of_labelling hP hL)))))))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hC, htup, ⟨hPar, hGap⟩, hTT, ⟨Xd, E, ⟨labPi⟩⟩, hAg, hE0⟩
  have hg : GlobalTheory.LiftRows.Given t.r.z.R.toRealDat t.r.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1, hPar, t.r.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ t.r.z.pins.char.base.lev hTT, t.r.z.pins.keep.guard, hGap⟩
  obtain ⟨ag⟩ := hAg hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP
  obtain ⟨T0, hT0, hR⟩ := exists_tied P (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi
    t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP) hPin.cf_eq hPin.C_eq hPin.tp_eq
    hPin.M_eq (hPin.rep_eq.trans c.row.rep_eq) ag (hE0 hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP)
  exact ⟨T0, by rw [hT0]; exact hPin, hR⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarryAll

theorem carry_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ C.Y.X), p ≫ C.π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ C.π ≫ genι Z), C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C K _ χ p hp
  let y : C.Y.X := p (IsLocalRing.closedPoint K)
  let ψ : C.Y.X.presheaf.stalk y →+* K := (Scheme.stalkClosedPointTo p).hom
  have hfac : p = spMap ψ ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  obtain ⟨φ, fr, t, hT, -⟩ := C.gr_spec y
  obtain ⟨g, hg⟩ := EigFrame.exists_baseChange E H Dw l Xo c O β Z _ K φ (stalkPt C.Y y ≫ C.π ≫ genι Z) fr ψ
  have hs : stalkPt C.Y y ≫ C.π ≫ genStr Z = spMap φ := by
    obtain ⟨s', hs'⟩ : ∃ s' : c.F →+* C.Y.X.presheaf.stalk y, spMap s' = stalkPt C.Y y ≫ C.π ≫ genStr Z :=
      ⟨(Spec.preimage (stalkPt C.Y y ≫ C.π ≫ genStr Z)).hom, Spec.map_preimage _⟩
    rw [← hs']
    congr 1
    have ha : Function.Injective (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) :=
      IsFractionRing.injective _ _
    have h2 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp s' = constF e C.Y := by
      apply GlobalTheory.ShFam.EigLoc.spMap_inj
      rw [GlobalTheory.ShFam.TieBase.spMap_trans, hs', ← GlobalTheory.ShFam.TieBase.genericPt_str e C.Y C.π C.π_str,
        GlobalTheory.ShFam.TieBase.genericPt_eq C.Y y]
      simp only [Category.assoc]
    refine RingHom.ext fun r => ha ?_
    have := DFunLike.congr_fun (h2.trans hT.2.1) r
    exact this
  have hφ : χ = ψ.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [GlobalTheory.ShFam.TieBase.spMap_trans, ← hs, ← hp, hfac]
    simp only [Category.assoc]
  subst hφ
  have key : ∀ q : Sp K ⟶ C.Y.X, q = spMap ψ ≫ stalkPt C.Y y →
      ∃ g : EigFrame Z (ψ.comp φ) (q ≫ C.π ≫ genι Z), C.Carries q g := by
    intro q hq
    subst hq
    refine ⟨g, y, ψ, φ, fr, t, 1, rfl, hT, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
    have e' : (fun k => spMap (dualMap ψ) ≫ fr.v τ k) = g.v τ := funext fun k => (hg τ k).symm
    rw [e']
    exact isCombAtG_single Z.t _ (g.tan τ) i
  exact key p hfac

theorem carries_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj hstr f hf K _ _ χ x hx g
  have hm : Mono j := by have := hj; infer_instance
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  have tr : ∀ (C : FlagCpt Z e) (p : Sp K ⟶ C.Y.X) (a b : Sp K ⟶ Z.X) (h : a = b) (g₀ : EigFrame Z χ a),
      C.Carries p g₀ → C.Carries p (h ▸ g₀) := by
    intro C p a b h g₀ hg; subst h; exact hg
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_flagComponent_point_over_geometricBasePoint E H Dw l Xo c O β Z F e σ N U Φ k X j hj hstr f hf (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ)
    (fun i K _ χ p h => carry_some E H Dw l Xo c O β Z F e (Φ.C i) K χ p h) K χ x hx
  have hπ : p ≫ (Φ.C k).π = x ≫ j := by rw [← hf, ← Category.assoc, hp]
  obtain ⟨g₀, hg₀⟩ := carry_some E H Dw l Xo c O β Z F e (Φ.C k) K χ p (by rw [← Category.assoc, hπ, Category.assoc]; exact hx)
  have h1 : p ≫ (Φ.C k).π ≫ genι Z = (x ≫ j) ≫ genι Z := by rw [← Category.assoc, hπ]
  obtain ⟨p', hp', hc⟩ := GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β Z F e σ N U Φ k K χ (x ≫ j) hx' (h1 ▸ g₀) g p hπ (tr _ p _ _ h1 g₀ hg₀)
  obtain ⟨q, -, hqu⟩ := Φ.lifts K χ (x ≫ j) hx' g
  have e' := hqu ⟨k, p'⟩ ⟨hp', hc⟩
  refine ⟨p', ⟨(cancel_mono j).1 (by rw [Category.assoc, hf, hp']), hc⟩, fun p₂ ⟨h₂, c₂⟩ => ?_⟩
  have e₂ := hqu ⟨k, p₂⟩ ⟨by rw [← hf, ← Category.assoc, h₂], c₂⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 (e₂.trans e'.symm)).2

end GlobalTheory.CarryAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlgOfFlagClSpec
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem flgOf_flagCl_spec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (Z : ct.Mdl) (s : (flgOf ct P).FlagData Z), IsFlagCl Z s.1 ((flgOf ct P).flagCl Z s) := by
  intro D A N j S κ p ct P Z s
  have hid : ∀ Z : ct.Mdl, ∃ f, IsMap Z Z f := fun Z =>
    ⟨𝟙 _, MapComp.corr_refl Z, fun k _ w hw => by simpa using GlobalTheory.ProjBlowup.natImg_refl Z w hw⟩
  refine ct.isFlagCl_flagCl Z s.1 (hid Z) (fun h => ?_) (GlobalTheory.T.exists_flag_closure _ _ _ _ _ _ ct.hp ct.hW _ _ Z _ fun t ht => ?_)
  · obtain ⟨f, hf⟩ := h.2.2.1
    have hty (σ) : Z.ty σ ∪ stepTy (allSteps (Lat.top Z)) σ = Finset.range (S.Dw.mult σ + 1) := by
      rw [stepTy_allSteps, Finset.union_eq_right, ← h.2.1.1 σ]
      exact hf.1.2.2 σ
    refine ⟨h.1, fun σ => (h.2.1.1 σ).trans (hty σ).symm, ⟨f, hf⟩,
      GlobalTheory.T.allSteps_hold_of_hasDR _ _ _ _ _ _ ct.hp ct.hW _ _ Z _ h.2.1 ⟨f, hf⟩, fun Z'' hg hs => ?_⟩
    obtain ⟨Z₀, h₀⟩ := GlobalTheory.T.exists_flag_closure _ _ _ _ _ _ ct.hp ct.hW _ _ Z (allSteps (Lat.top Z)) fun t ht => by
      obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
      exact hid Z
    obtain ⟨a, ha⟩ := h₀.2.2.2.2 Z'' hg hs
    obtain ⟨b, hb⟩ := h.2.2.2 Z₀ (GlobalTheory.T.hasDR_of_allSteps_hold _ _ _ _ _ _ ct.hp ct.hW _ _ Z Z₀ (fun σ => (h₀.2.1 σ).trans (hty σ)) h₀.2.2.2.1) h₀.2.2.1
    exact ⟨a ≫ b, MapComp.isMap_comp ha hb⟩
  · rcases (s.2 t ht).1 with h | h
    · exact h ▸ hid t.B
    · exact h

end GlobalTheory.LocM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricLawsAllStatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_laws_all_states : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  first | exact @GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 | exact GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 | (intros; apply GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralPointClassEqOneStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_pointClass_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), intGr H Dw (pointPoly H Dw) = 1 := by
  first | exact @GlobalTheory.GrassTop.intGr_pointPoly | exact GlobalTheory.GrassTop.intGr_pointPoly | (intros; apply GlobalTheory.GrassTop.intGr_pointPoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLattices
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by unfold Places.S0; rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by unfold Places.depth; rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  unfold lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

theorem hasGrid_of_full (p : PtAt ex Csz) (CF : ℝ) (hp : p.Ties)
    (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hpw : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (G : Grid p CF) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D)) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (hF : Full p.R.toRealDat G) : HasGrid (@Fld) p CF := by
  have hfit := gridFit_of_parts hs hc hpw hp.real.valLL0 h2 hp.real.psiChoice h4
  obtain ⟨W, M, ρ, ξ, cv, rm, S, rp, n, e, c, hIs, hOK, hSq⟩ := hF
  exact ⟨G, W, hIs.weil, hfit, n, ⟨M, ρ, ξ, cv, rm, S, rp, e, c⟩, ⟨hIs, hp.eSer, hOK, hSq⟩⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

theorem rowE_hasGrid_fld : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s) (IsLinked (prmR (NEa hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.Ties → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  intro hL CF N S Γ hN
  refine ((GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.twists_at_linked hL (prmR (NEa hL N (GridA CF)) S Γ) (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s)).and
    ((rowE_pinned_grid hL CF N S Γ hN).and (rowE_full_grid hL CF N S Γ))).imp fun κ K β c b _ _ _ H t ht => ?_
  obtain ⟨hw1, hw2, hcond, hpow⟩ := H.1
  obtain ⟨G₀, hF₀, hT₀⟩ := H.2.1 t ht
  obtain ⟨G, hv, hw, hch, hFull⟩ := H.2.2 t ht G₀
  exact hasGrid_of_full _ CF ht ⟨hw1, fun w w' a b c => (hw2 w w' a b c).2.2⟩ hcond hpow G (fieldHas_of_same hv hch hF₀)
    (lamOf_of_same hw hch ▸ hT₀) hFull

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPolyhedralCoverBalancedFormsCMFieldStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPolyhedralCover_balancedForms_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], HasRedCover H.bar X := by
  first | exact @GlobalTheory.RedTh.hasRedCover | exact GlobalTheory.RedTh.hasRedCover | (intros; apply GlobalTheory.RedTh.hasRedCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heq_rational_data_of_eigen : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  first | exact @GlobalTheory.RowTriple.Lay.EigCopy.eig_atMem | exact GlobalTheory.RowTriple.Lay.EigCopy.eig_atMem | (intros; apply GlobalTheory.RowTriple.Lay.EigCopy.eig_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundaryStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  first | exact @GlobalTheory.LieBase.isMetricOn_lieGram | exact GlobalTheory.LieBase.isMetricOn_lieGram | (intros; apply GlobalTheory.LieBase.isMetricOn_lieGram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandardStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_finE_mem_divisor_standard : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b := by
  first | exact @GlobalTheory.FrameInt.main | exact GlobalTheory.FrameInt.main | (intros; apply GlobalTheory.FrameInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_model_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ i : Idx H p, i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z false st x) := by
  first | exact @GlobalTheory.FlagEmb.DR.exists_lineModel | exact GlobalTheory.FlagEmb.DR.exists_lineModel | (intros; apply GlobalTheory.FlagEmb.DR.exists_lineModel <;> assumption)
end

