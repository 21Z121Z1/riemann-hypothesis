import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0743
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIso
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.CoefMatch

theorem vvmatch_repr {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (y : VV K lam) (i : VVIdx lam) :
    (Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge).repr (mapVV φ lam y) i = φ ((bVV K lam).repr y i) := by
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  have hy : mapVV φ lam y = ∑ k, φ ((bVV K lam).repr y k) • B' k := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  rw [hy, Module.Basis.repr_sum_self]

theorem wtMatch_of_coef : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam), (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam), (∀ γ x, T' (ρ' γ x) = rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat γ) (T' x)) → GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' := by
  intro L _ _ _ n ι _ K _ φ emb lam W₀ W' _ _ _ _ ρ₀ ρ' T hT T' hT'
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge with hB'
  refine ⟨VVIdx lam, inferInstance, inferInstance, (bVV K lam).map T.symm, B'.map T'.symm, fun γ => ?_⟩
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [hT', hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hj : B' j = mapVV φ lam (bVV K lam j) := Module.Basis.mk_apply _ _ _
  rw [hj, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hB', vvmatch_repr]

end GlobalTheory.CoefMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T → GlobalTheory.PendOf.LabAll D T := by
  first | exact @GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | exact GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | (intros; apply GlobalTheory.LabAllOf.labAll_of_labTrue_labConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr

set_option maxHeartbeats 16000000 in

theorem witMv_of_positionMv : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  intro 𝒮 hS K B f T w Z O x N h hE
  have hR := GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange K.s (w.D Z) x.col.Gt x.col.cmp x.col.g.herm x.col.g.forms N h x.col.isRec
  let col := columnLocalDataTransportDivision w Z N h x.col hR
  obtain ⟨k, hk⟩ := GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange w Z x.col.toColT O.X O.Gy x.ker0 x.ker N h hE
  let n := nchTTr w Z N h x.n
  obtain ⟨dv⟩ := GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange w Z x.n O.X N h x.div
  obtain ⟨th⟩ := GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange w Z x.n O.th N h x.th
  obtain ⟨t, hobj, ⟨rx⟩, ⟨nx⟩, ⟨sx⟩, ⟨ox⟩⟩ := hS K B f T w Z O x N h (O.tr N h) rfl col n
  have hker : (⟨(O.tr N h).gatT, (O.tr N h).cmp, (O.tr N h).tw, (O.tr N h).ker⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h)))
      (cmp : LatCmp (w.D (setDivZ Z N h))) (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy) =
      ⟨col.Gt, col.cmp, w.tw (setDivZ Z N h), kerTr w Z N h x.ker0⟩ := by
    have e := congrArg (fun s : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)), KerFam (w.D Z) Gt cmp tw O.Gy =>
      (⟨gatTr (D := w.D Z) N h s.1, cmpTr (D := w.D Z) N h s.2.1, twTr (D := w.D Z) N h s.2.2.1,
        fun u v g => { s.2.2.2 u v g with }⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h))) (cmp : LatCmp (w.D (setDivZ Z N h)))
          (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy)) x.ker_eq
    exact e
  have herr : (O.tr N h).errX = Formalism.L2.Herm.toErrXS col.full.1 := by
    show errTr (D := w.D Z) N h O.errX = _
    rw [x.errX]; rfl
  refine ⟨{
      isOver := x.isOver
      forced := x.forced
      Wt := x.Wt
      pin := x.pin
      coh := x.coh
      vol := x.vol
      col := col
      what₂ := t
      rx := rx
      lev := x.lev
      errX := herr
      n := n
      nx := nx
      sx := sx
      ker0 := kerTr w Z N h x.ker0
      ker_eq := hker
      ker := k
      div := dv
      th := th
      obj := hobj
      ox := ox
      real := { x.real with }
      dsig_eq := x.dsig_eq
      gauge := x.gauge
      good := GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange (w.D Z) O.nch O.xd N h x.good }, hk⟩

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XiCharacterMatchesType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up

theorem xiH_tupT_layer : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ n _ => ∀ μ, Used0 (w.D Z) μ → t.r.z.R.toLevCh.xiH (t.r.Y.tupT μ) = n.tp.xi μ := by
  intro _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ μ hμ => ?_
  have a := t.r.z.lev.xiH (t.r.Y.tupT μ)
  have b := t.r.Y.tupTie μ hμ
  have d := congrFun n.xi μ
  refine a.trans (Eq.trans ?_ d.symm)
  exact congrArg w.I.xi ((t.r.tup_ix _).symm.trans b)

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XiHTupTThird
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Up.ThirdTied

theorem xiH_tupT_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ μ, Formalism.IndefR.RecTie.Used0 (withLoc L) μ → m.z.R.toLevCh.xiH (r.Y.tupT μ) = (tpL L l.c.tp).xi μ := by
  intro hL hP hX
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  intro l big L _ _ m _ _ s r _ μ hμ
  refine (m.z.lev.xiH (r.Y.tupT μ)).trans ?_
  have b := r.Y.tupTie μ hμ
  rw [r.tup, m.tup] at b
  rw [b]
  exact (congrFun l.c.xi_eq μ).symm

end GlobalTheory.HeightCounting.Up.ThirdTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.SerCopy

def NoOff (D : D7) : Prop := ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HkAd (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host))
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat R Sb (idxOf D j) k P α Rr → ∀ x : Fin (R.nW (idxOf D j)) → D.what₂.LL,
    (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (hL j k P x)) =
      hkNorm R (idxOf D j) k P • Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) Rr
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x))

variable {R : RealDat3 D A3 Ks} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}

def ysOf {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x} {cf Rw low Pq hL eig θ}
    (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) : NExpRealS R cG (ratDatR R cG kKs hk) where
  fi := fun i => SideTies.fiOf R (idxOf D ((i : ℕ) + 1)) i (idxOf_succ D i)
  geq := fun i g => congrArg (fun y => cG (R.eG y)) (SideTies.fiOf_eG R _ i (idxOf_succ D i) g)
  rho := Bs.rho
  chi := Bs.chiL
  eF := Bs.eF
  bsup := fun i j b h1 h2 => ⟨1, one_ne_zero, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx, fun x hx => by
    rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩
  act := Bs.act

theorem ysOf_fi {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {cf Rw low Pq hL eig θ} (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (i x) : HEq (((ysOf Bs).fi i).e x) x :=
  SideTies.fiOf_heq _ _ _ _ x

variable {S : RatDat D.ntw}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure PreTie (YS : NExpRealS R cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (X : NExpTied D)
    (hF : D.host.F = maximalRealSubfield D.host.E)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Dat : D.ntw.Tw → ℕ → Bool → Type
  th : ∀ i j b, Dat i j b → D.nexp.Fm i j b
  lev : ∀ i j b, Dat i j b → Finset (PlE D.host)
  thPsi : ∀ i j b k (_ : Finset (PlE D.host)) (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Dat i j b →
    Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  h1 : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] th i j b d}
  thU : ∀ i j b (Q : Finset (PlE D.host)) (M : ℕ), Dat i j b →
    D.nexp.Fm i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M)
  thP : ∀ i j b k Q ψ, D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)
  MtLat : ∀ i j b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i j b k Q ψ)
  h2 : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG
  h3 : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (D.ntw.Ok i k)) (MtLat i j b k Q ψ : Set (D.nexp.MtV i j b k Q ψ)) = ⊤
  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin R cG ρ
  vec : ∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)
  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)
  tie : Comparison₂ good (Y := keepEx D Dat th lev thPsi h1 thU thP MtLat h2 h3) fun i j b => realRd YS v₀ good i j b (ν i j b)
  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))
  bad : ∀ i, ρ.bad i = normProd (D.ntw.S0 i)
  ch : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq)
  join : ∀ PV : ∀ j : Fin D.R.m, principalLevelFrame.RowPsi (Vc D j) D.R.nV, (∀ j, GlobalTheory.MtRead.IdFrame hF (PV j)) →
    ∀ i (j : Fin D.R.m) b k Q ψ (hA : NX.AdmTw D i k Q ψ), TwOK i k Q ψ →
      ∃ ω : (X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).W →ₛₗ[ρ.ek i b k] PolF D (Wc D j).rank (Vc D j).rank,
        Function.Injective ω ∧ ∀ f g, (tie i j b).rdV k Q ψ f ((finHom _).rangeRestrict ((PV j).ψ g)) =
          ω (((X.mtV i (j.1 + 1) b k Q ψ (by omega) (by omega) hA).real f).1 g)

namespace PreTie

variable {YS : NExpRealS R cG S} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec} {X : NExpTied D} {hF Pq}
  (p : PreTie YS v₀ X hF Pq)

abbrev ex : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw := keepEx D p.Dat p.th p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3

theorem hU : ∀ i j b M (d : p.Dat i j b), 1 ≤ j → j ≤ D.R.m →
    p.thU i j b ∅ M d = p.th i j b d ⊗ₜ[D.ntw.O i] (1 : AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) ∅ M)) := by
  intro i j b M d h1 h2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (p.tie i ⟨n, h2⟩ b).thU_empty M d

def nth : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw p.ex :=
  { D.nth with datPhi := fun _ _ _ _ => 0, datP := fun _ _ _ _ => 0 }

end PreTie

end GlobalTheory.HeightCounting.SerCopy

end
end

