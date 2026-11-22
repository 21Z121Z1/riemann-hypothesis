import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

def twL {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (Dof x) A) : GlobalTheory.ExportSeries.Twist (DL x L) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def twB {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (DL x L) A) : GlobalTheory.ExportSeries.Twist (Dof x) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def frL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (F : GlobalTheory.ExportSeries.Frame S U) : @GlobalTheory.ExportSeries.Frame (DL x L) ((S)) ((U)) where
  ψ := (by with_unfolding_all exact (F.ψ :))
  θ := (by with_unfolding_all exact (F.θ :))
  sT := (by with_unfolding_all exact (F.sT :))
  BS := (by with_unfolding_all exact (F.BS :))
  BT := (by with_unfolding_all exact (F.BT :))
  ΛS := (by with_unfolding_all exact (F.ΛS :))
  ΛT := (by with_unfolding_all exact (F.ΛT :))
  βS := (by with_unfolding_all exact (F.βS :))
  βT := (by with_unfolding_all exact (F.βT :))
  f₀ := (by with_unfolding_all exact (F.f₀ :))

def tdL {r : ℕ} (G : GlobalTheory.ExportSeries.TypeDat (Dof x) r) : GlobalTheory.ExportSeries.TypeDat (DL x L) r := ⟨(by with_unfolding_all exact (G.Pg :)), (by with_unfolding_all exact (G.P :)), (by with_unfolding_all exact (G.mu :))⟩

def wtL {n : ℕ} (u : GlobalTheory.ExportSeries.Weight (Dof x) n) : GlobalTheory.ExportSeries.Weight (DL x L) n :=
  ⟨(by with_unfolding_all exact (u.p :)), (by with_unfolding_all exact (u.q :)), (by with_unfolding_all exact (u.ap :)), (by with_unfolding_all exact (u.am :)), (by with_unfolding_all exact (u.c :)), (by with_unfolding_all exact (u.lam :))⟩

def baseL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (Z : GlobalTheory.ExportSeries.Base S U) : @GlobalTheory.ExportSeries.Base (DL x L) ((S)) ((U)) where
  hr := (by with_unfolding_all exact (Z.hr :))
  F := frL L Z.F
  G := (by with_unfolding_all exact ((tdL L Z.G) :))
  de := twL L Z.de
  w := (by with_unfolding_all exact ((wtL L Z.w) :))
  mu0 := (by with_unfolding_all exact (Z.mu0 :))
  eta := (by with_unfolding_all exact (Z.eta :))

def setupL (ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw) : GlobalTheory.SeriesTie.Setup (DL x L).ntw where
  rc := ⟨(by with_unfolding_all exact (ρ.rc.κ :)), (by with_unfolding_all exact (ρ.rc.art :))⟩
  ch := (by with_unfolding_all exact (ρ.ch :))
  bad := (by with_unfolding_all exact (ρ.bad :))
  e := (by with_unfolding_all exact (ρ.e :))
  ek := (by with_unfolding_all exact (ρ.ek :))
  B := fun i j b => (by with_unfolding_all exact ((baseL L (ρ.B ((i)) ((j)) b)) : _))
  om := fun i j b χ => (by with_unfolding_all exact ((ρ.om ((i)) ((j)) b ((χ))) : _))
  Cl := fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  finCl := fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  rep := fun i j b t c => (by with_unfolding_all exact ((ρ.rep ((i)) ((j)) b (twB L t) c) : _))
  β := (by with_unfolding_all exact (ρ.β :))
  eG := (by with_unfolding_all exact (ρ.eG :))

theorem twL_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (Dof x) A} (h : t.Good) : (twL L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem twB_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (DL x L) A} (h : t.Good) : (twB L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK_L {Pg Q : Finset (HeightOneSpectrum (𝓞 (Dof x).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (Dof x) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (DL x L) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem placesOK_B {Pg Q : Finset (HeightOneSpectrum (𝓞 (DL x L).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (DL x L) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (Dof x) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem wtL_good {n : ℕ} {u : GlobalTheory.ExportSeries.Weight (Dof x) n} (h : u.Good) : (wtL L u).Good := ⟨(by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.lam_eq :))⟩

theorem frL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {F : GlobalTheory.ExportSeries.Frame S U} (h : F.Good) : (frL L F).Good :=
  { rank_le := (by with_unfolding_all exact (h.rank_le :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    sdS := (by with_unfolding_all exact (h.sdS :))
    sdT := (by with_unfolding_all exact (h.sdT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := by tr_clause x.o.Z (oL x L).Z h.vac }

theorem baseL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {Z : GlobalTheory.ExportSeries.Base S U} (h : Z.Good) : (baseL L Z).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := frL_good L h.frame
    de := twL_good L h.de
    places := (by with_unfolding_all exact ((placesOK_L L h.places) :))
    wt := (by with_unfolding_all exact ((wtL_good L h.wt) :))
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }

theorem setupL_good {ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw} (h : ρ.Good) : (setupL L ρ).Good :=
  { rc := ⟨(by with_unfolding_all exact (h.rc.cont :)), (by with_unfolding_all exact (h.rc.rat :)), (by with_unfolding_all exact (h.rc.loc :)), (by with_unfolding_all exact (h.rc.artin :))⟩
    ch := fun i => ⟨(by with_unfolding_all exact ((h.ch ((i))).pair : _)), (by with_unfolding_all exact ((h.ch ((i))).one : _))⟩
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    base := fun i j b => (by with_unfolding_all exact ((baseL_good L (h.base ((i)) ((j)) b)) : _))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    delta := fun i j b => kc% (congrArg (twL L) (h.delta (kc% i) (kc% j) b))
    weil := fun i j b t ht => by
      delta GlobalTheory.ExportSeries.Base.IsWeil
      tr_leaves x.o.Z (oL x L).Z
      exact (by with_unfolding_all exact ((h.weil ((i)) ((j)) b (twB L t) (twB_good L ht)) : _))
    classes := fun i j b t ht hA =>
      have h' := h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t) (twB_good L ht) ⟨(by with_unfolding_all exact ((placesOK_B L hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩
      ⟨(by with_unfolding_all exact (h'.fin :)), (by with_unfolding_all exact (h'.reps :)), (by with_unfolding_all exact (h'.stab :))⟩ }

theorem pinL (l : LC hL x) : GlobalTheory.SeriesTie.RealPin (datL x L).R (datL x L).cG (setupL L l.b.ser.ex.ρ) :=
  have p := l.b.ser.ex.pin
  ⟨(by with_unfolding_all exact (p.psi :)), (by with_unfolding_all exact (p.inf :)), (by with_unfolding_all exact (p.cartT :)), (by with_unfolding_all exact (p.onbS :)), (by with_unfolding_all exact (p.onbT :)), (by with_unfolding_all exact (p.latS :)), (by with_unfolding_all exact (p.latT :)), (by with_unfolding_all exact (p.frS :)), (by with_unfolding_all exact (p.frT :)), (by with_unfolding_all exact (p.vac :)), (by with_unfolding_all exact (p.Pg :)),
    (by with_unfolding_all exact (p.grp :)), (by with_unfolding_all exact (p.mu0 :)), (by with_unfolding_all exact (p.eta :)), (by with_unfolding_all exact (p.delta :)), (by with_unfolding_all exact (p.deltaPl :)), (by with_unfolding_all exact (p.ap :)), (by with_unfolding_all exact (p.am :))⟩

theorem univL (l : LC hL x) : GlobalTheory.UnivChar.IsUnivChar (DL x L).nexp := (by with_unfolding_all exact (l.b.ser.ex.univ :))

open GlobalTheory.SeriesTie in

theorem theta_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).theta = fun i j b h P => (by exact ρ.theta i j b h P) := by
  funext i j b h P
  delta GlobalTheory.SeriesTie.Setup.theta GlobalTheory.ExportSeries.Base.theta GlobalTheory.ExportSeries.Base.vecBase GlobalTheory.ExportSeries.Base.vecAt
    GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.theta (kc% i) (kc% j) b (kc% h) (kc% P)))

open GlobalTheory.SeriesTie in

theorem isDatum_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsDatum = fun i j b s h P => (by exact ρ.IsDatum i j b s h P) := by
  funext i j b s h P
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.split), (d.off), (d.fin), (d.supp), (d.mem)⟩ : ρ.IsDatum ((i)) ((j)) b ((s)) ((h)) ((P))) : _))
  · exact ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def sgTw (x : St P) (N : TwNew (Dof x)) : SameGrp (B := B) (C := w.C) x.o.Z (oTw x N).Z where
  e _ := Equiv.refl _
  pl _ _ := rfl
  e0 _ := rfl

def datTw (x : St P) (N : TwNew (Dof x)) : Dat (w.st (oTw x N).Z) w.I P.hX T P.Wt :=
  DatCopy.copy (a := x.o.Z) (oTw x N).Z (sgTw x N) x.m.z

def sideTw (x : St P) (N : TwNew (Dof x)) : Side0 (oTw x N) where
  cen := x.s.cen
  tie := x.s.tie
  is := x.s.is
  RR := x.s.RR
  frames := x.s.frames
  jEE := x.s.jEE
  basis := x.s.basis
  norm := x.s.norm

theorem fitsTw (x : St P) (N : TwNew (Dof x)) : (oTw x N).Fits := ⟨x.fits.div, x.fits.grp, ⟨(by with_unfolding_all exact (x.fits.grpAt.pl :)), (by with_unfolding_all exact (x.fits.grpAt.idem :)), (by with_unfolding_all exact (x.fits.grpAt.cen :))⟩,
  fun eR h => ⟨(by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).amb : _)), (by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).mt : _))⟩⟩

def stTw (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) : St P :=
  ⟨oTw x N, fitsTw x N, x.G_eq, x.etaF, x.bk, m, hc, hh, sideTw x N, r, hp⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ j, v j ∈ balForms bar X) → (∀ j y, 0 ≤ v j y y) → (∀ j, InRCone γ (v j)) → genRank v ≤ genRank γ := by
  first | exact @GlobalTheory.PolFan.genRank_le_of_inRCone_cell | exact GlobalTheory.PolFan.genRank_le_of_inRCone_cell | (intros; apply GlobalTheory.PolFan.genRank_le_of_inRCone_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarClosedIntegralLatticeAllStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_closed_integral_lattice_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @GlobalTheory.HeightCounting.Up.fixedField_star_stable_third | exact GlobalTheory.HeightCounting.Up.fixedField_star_stable_third | (intros; apply GlobalTheory.HeightCounting.Up.fixedField_star_stable_third <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentresStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starDepth_le_strictnessGap_off_centres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  first | exact @GlobalTheory.PolFan.StarGap.starDepth_le_gap | exact GlobalTheory.PolFan.StarGap.starDepth_le_gap | (intros; apply GlobalTheory.PolFan.StarGap.starDepth_le_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarMemIntegralLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_integral_lattice : PrN → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @GlobalTheory.HeightCounting.Up.fixedField_star_stable | exact GlobalTheory.HeightCounting.Up.fixedField_star_stable | (intros; apply GlobalTheory.HeightCounting.Up.fixedField_star_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' :=
  isStarOf_of_cover GlobalTheory.T.realCone_covered_by_star_at_point

end GlobalTheory.PolFan.StarCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_range_subset {X : Type} [AddCommGroup X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hsub : Set.range γ ⊆ Set.range γ') {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) : InRCone γ' β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  have hj : ∀ i, ∃ j, γ' j = γ i := fun i => hsub ⟨i, rfl⟩
  choose j hj using hj
  refine ⟨fun k => ∑ i, if j i = k then c i else 0, fun k => Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hc i
    · exact le_refl 0, ?_⟩
  rw [hβ]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (j i) (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_smul]) (by simp), if_pos rfl, hj]

theorem evalZ_zero_form {O : Type} [CommRing O] (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  rw [← evalR_toReal]
  have : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp
  rw [this, evalR_zero]

theorem isStarOf_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone H.bar X,
      ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨hw1, -, hw3⟩ := hw X hX

  let C : Set (LinearMap.BilinForm ℤ X) := {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
    (∀ i, γ i ∈ S) ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  let CT : Set (LinearMap.BilinForm ℤ X) → Set (LinearMap.BilinForm ℤ X) := fun T =>
    {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧
      v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  have hCT : ∀ T, (CT T).Subsingleton := by
    rintro T v₁ ⟨m₁, γ₁, hγ₁, hr₁, hb₁, hp₁, hv₁, hi₁⟩ v₂ ⟨m₂, γ₂, hγ₂, hr₂, hb₂, hp₂, hv₂, hi₂⟩
    exact hw3 m₁ γ₁ hγ₁ v₁ hb₁ hp₁ v₂ hb₂ hp₂ hv₁ hv₂ hi₁
      (inRCone_of_range_subset (by rw [hr₁, hr₂]) hi₂)
  have hC : C.Finite := by
    refine (hS.powerset.biUnion fun T _ => (hCT T).finite).subset ?_
    rintro v ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    refine Set.mem_biUnion (x := Set.range γ) ?_ ⟨m, γ, hγ, rfl, hb, hp, hv, hi⟩
    rintro _ ⟨i, rfl⟩
    exact hγS i
  refine ⟨S ∪ C, hS.union hC, fun B hB => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hBc⟩ := hcov B hB
  by_cases hex : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hb, hp, hv, hi⟩ := hex
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [evalZ_zero_form] at hv
      exact zero_ne_one hv
    obtain ⟨m', s, h, hcut, hpos, t, ht, hBt⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m γ v (pullR e.toLinearMap B) (fun i y z => (hγ.mem i).1 y z) hγ.nonneg hv0 hi ⟨c, hc, hBc⟩
    refine ⟨e, m' + 1, Fin.cons v fun j => γ (s j), t,
      hst.2.1 X hX m γ hγ v hb hp hv hi m' s h hcut hpos, fun i => ?_, ht, hBt⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    · simp only [Fin.cons_succ]
      exact Or.inl (hγS (s j))
  · refine ⟨e, m, γ, c, hst.1 X hX m γ hγ fun β hb hp hi => ?_, fun i => Or.inl (hγS i), hc, hBc⟩
    rcases hw1 β hb hp with h0 | h1
    · exact h0
    · exact (hex ⟨β, hb, hp, h1, hi⟩).elim

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termExpansion_weight_correspondence_at_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → ∀ α' : D'.toPre.X, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  first | exact @GlobalTheory.termMatch_at_level | exact GlobalTheory.termMatch_at_level | (intros; apply GlobalTheory.termMatch_at_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (th : ThetaX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ThT n th → Nonempty (ThT (nchTTr w Z N h n) (thTr (D := w.D Z) N h th)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv | exact GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  ThetaPsi : HEq D.ntw.ThetaPsi N.tw.ThetaPsi
  topO : HEq D.ntw.topO N.tw.topO
  finLam : HEq D.ntw.finLam N.tw.finLam
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs
  res : HEq D.ntw.res N.tw.res
  eLL0 : ∀ g g', HEq g g' → e (N.ex.eLL0 g') = D.nexp.eLL0 g
  twPsi : HEq D.nexp.twPsi N.ex.twPsi
  twDel : HEq D.nexp.twDel N.ex.twDel
  eH : HEq D.nexp.eH N.ex.eH

theorem CopyN.refl (D : D7) : CopyN D (⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, D.nth, D.ntwbr, D.ntwbr_ind⟩ : TwNew D) (RingHom.id _) (RingEquiv.refl _) where
  cp := GlobalTheory.TwInputs.Move.CopyTw.refl D
  ThetaPsi := HEq.rfl
  topO := HEq.rfl
  finLam := HEq.rfl
  jL := HEq.rfl
  s2 := HEq.rfl
  lamG := HEq.rfl
  Xv := HEq.rfl
  qs := HEq.rfl
  res := HEq.rfl
  eLL0 _ _ h := by cases h; rfl
  twPsi := HEq.rfl
  twDel := HEq.rfl
  eH := HEq.rfl

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
  GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem topCoeff_sum' {n : ℕ} {κ : Type} (s : Finset κ) (P : κ → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, P i) = ∑ i ∈ s, topCoeff (P i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_real_smul {n : ℕ} (r : ℝ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (r • P) = (r : ℂ) * topCoeff P := by
  simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem topCoeff_chern_eq_sum_rep : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  intro ι _ m n R
  classical
  have hmem := GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan m n (MvPolynomial (Fin n × Fin n) ℂ)
    (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.1 hmem
  choose ρ hρ using fun i => (g i).2
  refine ⟨Fin k, inferInstance, ρ, f, fun A hA => ?_⟩
  set c : ι × ℕ → MvPolynomial (Fin n × Fin n) ℂ := fun x => (Matrix.charpolyRev (-A x.1)).coeff x.2 with hc
  have hch : ∀ x : ι × ℕ, IsWeightedHomogeneous (1 : Fin n × Fin n → ℕ) (c x) x.2 := fun x =>
    ChernDegree.charpolyRev_coeff_isHomogeneous (-A x.1) (fun i j => (hA x.1 i j).neg) x.2
  have key : ∀ d : ι × ℕ →₀ ℕ, Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d ≠ n →
      topCoeff (aeval c (monomial d (coeff d R))) = 0 := by
    intro d hd
    have h1 : IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) (monomial d (coeff d R))
        (Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    exact ChernDegree.topCoeff_eq_zero (ChernDegree.aeval_isWeightedHomogeneous h1 c hch) hd
  have e1 : topCoeff (aeval c R) = ∑ d ∈ R.support, topCoeff (aeval c (monomial d (coeff d R))) := by
    conv_lhs => rw [R.as_sum]
    rw [map_sum, topCoeff_sum']
  have e2 : topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) =
      ∑ d ∈ R.support with Finsupp.weight (Prod.snd : ι × ℕ → ℕ) d = n,
        topCoeff (aeval c (monomial d (coeff d R))) := by
    rw [weightedHomogeneousComponent_apply, map_sum, topCoeff_sum']
  have e3 : topCoeff (aeval c R) = topCoeff (aeval c (weightedHomogeneousComponent (Prod.snd : ι × ℕ → ℕ) n R)) := by
    rw [e1, e2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rfl
    · exact key d h
  have hval := congrFun hfg A
  simp only [Finset.sum_apply, Pi.smul_apply] at hval
  rw [e3, ← hval, topCoeff_sum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [topCoeff_real_smul, ← hρ i]

end GlobalTheory.GoodMetric.ChernSpan
end
end

