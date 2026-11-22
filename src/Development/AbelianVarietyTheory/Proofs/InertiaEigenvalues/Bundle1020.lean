import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0802
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0839
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0996
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisSide
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.GalLoc

set_option maxHeartbeats 4000000 in

theorem triple_withLoc (hP : PrN) (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hl : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (Bs : SideB D cf Rw low Pq S hl eig θ) (L : LocAll (lay0 D))
    (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ (withLoc L).ntw.S0 i)
    (ks : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (chiT : ChiTOk (withLoc L) (cfL L cf)) (grp : GrpSide (withLoc L)) (chr : CharSide (withLoc L) (cfL L cf))
    (val : ValLL0 (withLoc L) (cfL L cf))
    (roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 (withLoc L)).fieldRange)
    (hstar : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0)
    (T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut) (cg : CGTrue hL (withLoc L) T)
    (eT : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.EigTrue (withLoc L) (cfL L cf) Rw' Sb eig)
    (eO : GlobalTheory.TwInputs.EigOcc (withLoc L) ({ S with } : RatDat (withLoc L).ntw) θ hl Sb eig)
    (rp : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw')
    (rt : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.EigTie.ResTied (withLoc L) Rw')
    (nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L)) (exT : NExpTied (withLoc L)) (cm : GlobalTheory.TwInputs.CommAll (withLoc L))
    (fa : GlobalTheory.TwInputs.FullAll (withLoc L)) :
    GlobalTheory.Triple.IsTriple (withLoc L) := by
  obtain ⟨Rw', hR, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf Rw low Pq S hl eig θ Bs L ψ hψ
  have hg := GlobalTheory.GalAway.galoisReps_of_cgTrue hL hP.what₂.fin hP.what₂.gal _ T cg
  have hm := GlobalTheory.T.stableGoodForms_meet_generic_type hP.greenC _ exT grp
  have hs := GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem _ _ _ _ _ _ _ _ _ Bs' nf hm cm fa
  exact GlobalTheory.T.side_eigen_export hP.what₂.cheb hP.what₂.art _ _ _ _ _ _ _ _ _ Bs' Sb hSb ks chiT grp chr val roots hstar (eT Rw' hR) eO
    (rp Rw' hR) (rt Rw' hR) hg hs

end GlobalTheory.GalLoc

namespace GlobalTheory.GalLoc

set_option maxHeartbeats 4000000 in

theorem triple_at (hP : PrN) (hS : SerN) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hE : AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig)
    (hF : AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0))
    (hR : AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw)
    (hC : AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z)) :
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.Triple.IsTriple (w.D Z) := by
  have hT := GlobalTheory.T.residual_compatible_rows hP hL
  refine atMem_imp (atMem_and hE (atMem_and hF (atMem_and hR (atMem_and hC hT)))) ?_
  intro K B f T w Z Wt p0 t nch n xd c hN H
  obtain ⟨⟨Sb, hSb, eT, eO⟩, ⟨val, roots, hstar⟩, rp, ⟨cm, fa⟩, rt⟩ := H
  obtain ⟨e⟩ := hN
  have eq := c.a.nt.eq
  have pk := c.a.nt.pack
  let L := c.a.nt.L

  have hψ : ∃ ψ : (withLoc L).nd.Loc → NC.HC (withLoc L).host.E,
      ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0 := by
    have h0 : ∃ ψ : (w.D Z).nd.Loc → NC.HC (w.D Z).host.E,
        ∀ a, NC.ReadC (w.D Z).nd.plOm.1 ((w.D Z).ntw.psiL a) (NC.iotaC (w.D Z) a) (ψ a) 0 :=
      ⟨c.a.all.chiD.psi, c.a.all.chi.psi⟩
    exact eq ▸ h0
  obtain ⟨ψ, hψ⟩ := hψ
  have cast2 : ∀ P : (D : D7) → CharFrame D → Prop, P (w.D Z) (TC.cf w.I w.l Z) → P (withLoc L) (cfL L c.a.nt.cf) :=
    fun P h => cast (congrArg (fun x : (Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁) => P x.1 x.2.1) pk) h
  have chr : Nonempty (CharSide (withLoc L) (cfL L c.a.nt.cf)) :=
    cast2 (fun D cf => Nonempty (CharSide D cf)) ⟨{ c.a.chrN with }⟩
  obtain ⟨chr⟩ := chr
  have val' : ValLL0 (withLoc L) (cfL L c.a.nt.cf) := cast2 (fun D cf => ValLL0 D cf) val
  have roots' : ∀ (k : Fin 2) (z : ℂ), z ^ ((withLoc L).host.g k * ((withLoc L).host.g k - 1)) = 1 →
      z ∈ (embLL0 (withLoc L)).fieldRange := eq ▸ roots
  have star' : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0 := eq ▸ hstar
  have grp : Nonempty (GrpSide (withLoc L)) := by
    have g0 : Nonempty (GrpSide (w.D Z)) := by
      let Ty := c.a.all.types
      exact ⟨⟨Ty.tA, Ty.tκ, Ty.teichC_def, Ty.ζ, Ty.ζ_gen, Ty.O, Ty.eSer_def, Ty.kv, Ty.tg_tame, Ty.O_equiv, Ty.O_tw⟩⟩
    exact eq ▸ g0
  obtain ⟨grp⟩ := grp
  have rp' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw := eq ▸ rp
  have rt' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.EigTie.ResTied (withLoc L) Rw := eq ▸ rt
  have cm' : GlobalTheory.TwInputs.CommAll (withLoc L) := eq ▸ cm
  have fa' : GlobalTheory.TwInputs.FullAll (withLoc L) := eq ▸ fa
  have exT : NExpTied (withLoc L) := eq ▸ c.a.all.exp
  have nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L) := by
    have h0 : GlobalTheory.TwInputs.NoFormsOff (w.D Z) := fun i j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h)
    exact eq ▸ h0
  rw [eq]
  exact triple_withLoc hP hL c.a.nt.Bs L ψ hψ Sb hSb c.a.ratIn.ks c.a.nt.A.chiT grp chr val' roots' star' { c.a.nt.A.wdT with } { c.a.nt.cg with }
    eT eO rp' rt' nf exT cm' fa'

end GlobalTheory.GalLoc

namespace GlobalTheory.GalLoc

set_option maxHeartbeats 4000000 in

theorem galSide_at : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ G : GlobalTheory.TwInputs.GalSide (w.st Z).toD7, G.cf = (TC.cf w.I w.l Z) ∧ G.lam.C = (TC.cf w.I w.l Z) ∧
      Nonempty (CGTrue hL _ G.wd) := by
  intro hP hS hL
  have htr : AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.Triple.IsTriple (w.D Z) :=
    triple_at hP hS hL (GlobalTheory.T.eigen_occurrence_with_local_data hP hS hL) (GlobalTheory.T.coefficient_field_valuation_facts hP hS hL) (GlobalTheory.T.row_parameter_of_local_langlands hP hS hL) (GlobalTheory.T.commutant_full_of_local_langlands hP hS hL)
  refine (GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices.inter htr).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  obtain ⟨e⟩ := hE
  have hs := H.1 hK T w Z
  exact GlobalTheory.TwInputs.JoinModel.gal_of e (H.2 hK w Z Wt p0 t nch n xd c ⟨e⟩ hX hC) hs.1 hs.2.1

end GlobalTheory.GalLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodModelVector_eq_classSum_baseLevel : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  first | exact @GlobalTheory.TypeClassSum.goodModel_eq_classSum | exact GlobalTheory.TypeClassSum.goodModel_eq_classSum | (intros; apply GlobalTheory.TypeClassSum.goodModel_eq_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAtOfNonemptyExceptionalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_at_of_nonempty_exceptional : GlobalTheory.NLink.Hypotheses₂ → GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → (AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NFacts.Facts (w.D Z) nch) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  first | exact @GlobalTheory.NLink.CloseMem.main | exact GlobalTheory.NLink.CloseMem.main | (intros; apply GlobalTheory.NLink.CloseMem.main <;> assumption)
end

