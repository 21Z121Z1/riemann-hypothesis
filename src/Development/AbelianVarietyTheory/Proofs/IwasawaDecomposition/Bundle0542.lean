import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IntertwinersExistScalarUpdateInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DeepElementConjRationalAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}

set_option maxHeartbeats 4000000 in

def geoR (z : Dat X I hX T Wt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) :
    GlobalTheory.RealGeo.GeoHalf z.core ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3).toRealDat fun _ => 1 :=
  ⟨(z.resGeo h).κ, (z.resGeo h).v₀,
    GlobalTheory.RealGeo.Upd.updFWT z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).fw,
    (z.resGeo h).bar,
    fun i => GlobalTheory.RealGeo.Upd.updO z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 ((z.resGeo h).O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).O i ((z.resGeo h).pins i),
    (z.resGeo h).rhoGeo, (z.resGeo h).equivAll, (z.resGeo h).cTie, (z.resGeo h).phase⟩

set_option maxHeartbeats 4000000 in

def res (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := (z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3
  cG := z.cG
  geo := geoR z Wt' h
  pins := pins_resK z h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set X.B.places.Pl} (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')

set_option maxHeartbeats 4000000 in

theorem res_exAt : (res z e Wt' h hc).R.toRealDat.ExAt := intertwinersExist_scalar_update_invariant (exAt_res z h e) _ _

set_option maxHeartbeats 4000000 in

theorem res_inGeo (hi : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (res z e Wt' h hc).geo := by
  have h' := (z.inGeo_resGeo_iff h).2 hi
  exact ⟨h'.jEvExists, h'.jEvBar, h'.evInj, h'.jUnif, h'.geoAct, h'.latFull, h'.dimMatch⟩

set_option maxHeartbeats 4000000 in

theorem restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces (F0) : (res z e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  exact (nz_updS (z.resR h) _ _ _ F0 _).trans (exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _))

set_option maxHeartbeats 4000000 in

theorem res_std (hs : z.Std) : (res z e Wt' h hc).Std := by
  obtain ⟨⟨c, h1, h2, h5⟩, hV⟩ := hs
  refine ⟨⟨c, h1, fun hc' t φ g x hm => h2 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h5⟩, fun i => ?_⟩
  obtain ⟨cv, h3, h4, h6⟩ := hV i
  exact ⟨cv, h3, fun hc' t φ g x hm => h4 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h6⟩

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem of_diag {n : ℕ} {P : Fin n → Fin n → Prop} (H : ∀ i, P i i) (i i' : Fin n) (h : (i : ℕ) = i') : P i i' :=
  (Fin.ext h : i = i') ▸ H i

set_option maxHeartbeats 4000000 in

theorem res_ext (z : Dat (w.st Z) w.I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set B.places.Pl} (h : Wt' ⊆ Wt)
    (hc : ConjStable (w.st Z) Wt') : Ext z (res z e Wt' h hc) where
  H := HEq.rfl
  l := HEq.rfl
  c := HEq.rfl
  Dw := HEq.rfl
  Xo := HEq.rfl
  U := HEq.rfl
  V := HEq.rfl
  dict := HEq.rfl
  mu := HEq.rfl
  Kf := HEq.rfl
  cE := HEq.rfl
  chiW := HEq.rfl
  x₀ := HEq.rfl
  iota := HEq.rfl
  ψ := HEq.rfl
  θ := HEq.rfl
  βW := HEq.rfl
  βY := HEq.rfl
  nW := HEq.rfl
  βV := HEq.rfl
  ΛV := HEq.rfl
  ΛW := HEq.rfl
  Pg := HEq.rfl
  eG := HEq.rfl
  Sb := HEq.rfl
  BV i i' hi := by
    obtain rfl : i = i' := Fin.ext hi
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  MW i i' hi := by
    obtain rfl : i = i' := Fin.ext hi
    refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun φ φ' hφ => ?_⟩
    have hT : (type_of% φ') = (type_of% φ) := rfl
    have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
    subst h2
    exact HEq.rfl
  forms i i' hi φ φ' hφ k k' hk := by
    obtain rfl : i = i' := Fin.ext hi
    have hT : (type_of% φ') = (type_of% φ) := rfl
    have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
    subst h2
    have hN : (type_of% k') = (type_of% k) := rfl
    have hnn : (res z e Wt' h hc).R.nW i = z.R.nW i := rfl
    have h3 : cast hN k' = k := (cast_eq_iff_heq).2 ((Fin.heq_ext_iff hnn).2 hk.symm)
    subst h3
    rfl
  W1 v v' hv := by
    have e' : v = v' := (w.D Z).plEq.injective (HeightOneSpectrum.ext (Ideal.ext fun x => hv x x rfl))
    subst e'
    rw [restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces]
  cV i i' hi := by
    obtain rfl : i = i' := Fin.ext hi
    exact ⟨HEq.rfl, HEq.rfl⟩
  pb := HEq.rfl
  ΛY := (HEq.refl z.R.ΛY)
  κ := by
    refine of_diag fun i => ⟨?_, ?_, ?_⟩
    · exact (HEq.refl (z.geo.κ i).aP)
    · exact (HEq.refl (z.geo.κ i).aM)
    · exact (Eq.refl (z.geo.κ i).n)
  ref := by
    refine of_diag fun i => ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (HEq.refl (z.R.vP i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.HV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.thF i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.thG i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.νV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.fdV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
    · exact (HEq.refl (z.R.νW i))
    · exact (HEq.refl (z.R.fdW i))
  jL := by
    refine of_diag fun i => ?_
    intro ok ok' φ φ' hφ
    have hT : (type_of% φ') = (type_of% φ) := rfl
    have h2 : cast hT φ' = φ := Subtype.ext (funext fun d => Subtype.ext
      (MvPolynomial.map_injective _ (RingHom.injective _) (eq_of_heq (hφ d d HEq.rfl))))
    subst h2
    exact (by with_unfolding_all exact (HEq.refl (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok (cast hT φ') :)))) :))

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.Rw

theorem stepW_keep_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

set_option maxHeartbeats 4000000 in

theorem exists_pre2_of_fine_of_resChar_mem : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.CuspRapidDecay → WeightCaseCondition → StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G → GrpTrue Z.N f → GrpAt (w.st Z) w.I →
      DV.KapDef (w.D Z) → Fine z → (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) →
      (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) →
      ∃ P : Pre2 K w, P.Z₀ = Z ∧ P.Wt = z.W1 (F0K K.s (w.D Z)) ∧ Ext z P.z := by
  intro hWe hDS hHC hCR hHW
  have hInp := GlobalTheory.LinksInputs.inputs_of_hypotheses hWe hDS hHC hCR
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hAll := hId.and (hHW.and (stepW_keep_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start))
  refine hAll.trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨-, -, hCoh⟩, hHW', hHost⟩ := H
  intro Z hX z hG2 hGT hGA hKap hFine hsub hSp
  obtain ⟨hEx, hGeo, hCore, hStd⟩ := hFine
  have hle : z.W1 (F0K K.s (w.D Z)) ⊆ {v | B.places.resChar v ∈ T.pl} := hsub
  have hc : ConjStable (w.st Z) (z.W1 (F0K K.s (w.D Z))) := fun v hv => z.nonzero_index_places_conj_stable _ v hv
  let z' := ResStd.res z hEx _ hle hc
  have hW : z'.W1 (F0K K.s (w.D Z)) = z.W1 (F0K K.s (w.D Z)) := ResStd.restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces z hEx hle hc _
  have hEx' : z'.R.toRealDat.ExAt := ResStd.res_exAt z hEx hle hc
  have hGeo' : GlobalTheory.RealGeo.InGeo z'.geo := ResStd.res_inGeo z hEx hle hc hGeo
  have hCore' : CoreP z' := hCore
  have hStd' : z'.Std := ResStd.res_std z hEx hle hc hStd
  have hH : Holds z'.R z'.F := hHW' Z hX _ z' hGT hGA hKap hEx' hGeo' hCore' hG2 hW.symm hsub
  have hcs : ∀ v, B.places.conj v ∈ z'.W1 (F0K K.s (w.D Z)) ↔ v ∈ z'.W1 (F0K K.s (w.D Z)) := fun v =>
    ⟨fun h => by simpa only [B.places.conj_conj] using z'.nonzero_index_places_conj_stable _ _ h, fun h => z'.nonzero_index_places_conj_stable _ v h⟩
  obtain ⟨-, hFmax, -, -, hSt, -⟩ := hHost (w.st Z) hO
  obtain ⟨q⟩ := GlobalTheory.T.nonempty_rowLiftFamily_over_columnChoices B f T w Z hX _ z' (hInp _) hFmax (hSt 0).1 (fun i => (hSt _).2.2 (by omega) i.2) hH hcs
  exact ⟨{
    Z₀ := Z
    hX := hX
    Wt := _
    z := z'
    q := q
    g := hG2
    coh := hCoh
    grp := hGT
    grpAt := hGA
    kap := hKap
    intersectionNumber_baseChange := hH
    exAt := hEx'
    inGeo := hGeo'
    core := hCore'
    exact := hW.symm
    sub := hsub
    supp := hSp
    std := hStd' }, rfl, rfl, ResStd.res_ext z hEx hle hc⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DeepElementConjRationalAtBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deepElement_conj_rational_at_badPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a kk fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) x = bc (prV (E := (I.rec7 l Z).host.E) v) κ → ∀ N : ℕ, ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ∧ ∃ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' ∧ ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.DeepElt.main | exact GlobalTheory.Mem.Col2.AdT.DeepElt.main | (intros; apply GlobalTheory.Mem.Col2.AdT.DeepElt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorEmbeddingKappaEqRowsKappaAtInfinitePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorEmbedding_kappa_eq_rowsKappa_at_infinitePlace : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → (∀ σ, Xd.kapR σ = kapSharp D) → ∀ e : D.what₂.LL →+* ℂ, Xd.kapR e = (s1Of R F).κ (InfinitePlace.mk e) := by
  first | exact @GlobalTheory.KapRow.kapR_eq_rows_kappa | exact GlobalTheory.KapRow.kapR_eq_rows_kappa | (intros; apply GlobalTheory.KapRow.kapR_eq_rows_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStagesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spectralLevel_objects_replacedStages : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (F0 : ∀ u, Forms0 D u) (P : SPack D F0) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), GapHyp D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied D → RealTied D → D.what₂.Dstar = StandardLattice.DstarD D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c ∧ SeeAt R F P.X P.inst t ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ R eE P.X P.inst P.G t j ∧ ∀ (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (hh : D.what₂.Word → ℝ) (F' : ∀ u, Forms0 (reD D ⟨P.toNew hD j, N, hh⟩) u) (hs : SameForms0LevelsAndValues ⟨P.toNew hD j, N, hh⟩ F0 F'), ∃ (hF : FinX (reY ⟨P.toNew hD j, N, hh⟩ P.Y)) (S : SRest (P.re ⟨P.toNew hD j, N, hh⟩ hs hF)), S.j = j.trans (eEECre ⟨P.toNew hD j, N, hh⟩ P.G) := by
  first | exact @GlobalTheory.Mem.SRe.exists_sRest_top | exact GlobalTheory.Mem.SRe.exists_sRest_top | (intros; apply GlobalTheory.Mem.SRe.exists_sRest_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitTwistPlaceOverProductCharacterRamifieStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitTwistPlace_over_productCharacter_ramified : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
  first | exact @GlobalTheory.TwistSplitPlace.exists_splitPlace_of_mem_qPl | exact GlobalTheory.TwistSplitPlace.exists_splitPlace_of_mem_qPl | (intros; apply GlobalTheory.TwistSplitPlace.exists_splitPlace_of_mem_qPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩

set_option maxHeartbeats 1000000 in

theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLeOfAntilinear
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    ∀ τ k, 1 ≤ (κ i).aP τ k := by
  intro τ k
  rw [(h i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hk2 := k.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (D.R.k + i - 1 - k) k (by simp only [Ranks.r]; omega)
  have h4 : Formalism.L2.NTheta.lamAt (D.hc τ) (k + (D.R.k + i - 1 - k)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have h5 := (D.hc τ).gap_be i
  have h6 : ((D.R.k + i - 1 - k : ℕ) : ℚ) = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (k + 1) := by
    rw [show D.R.k + i - 1 - k = (D.R.sigW ((i : ℕ) + 1)).1 - (k + 1) by omega, Nat.cast_sub hk2]
    push_cast
    rfl
  rw [h4, h6] at h3
  simp only [aPl, if_pos k.2]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem finrank_le_of_antilinear {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [FiniteDimensional ℂ H'] (e : H ≃ₗ⋆[ℂ] H') : Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  have b := Module.finBasis ℂ H'
  have h : Submodule.span ℂ (Set.range fun k => e.symm.toLinearMap (b k)) = ⊤ := by
    rw [← span_range_eq_basis b e.symm.toLinearMap, show Set.range e.symm.toLinearMap = Set.univ from Set.range_eq_univ.2 e.symm.surjective, Submodule.span_univ]
  rw [← finrank_top, ← h]
  exact (finrank_range_le_card _).trans (Fintype.card_fin _).le

theorem adel_rdU_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      (rdU (T.U j σ) f) = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ)⁻¹ • phiC T hV a f := by
  subst hV
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  exact (inv_smul_smul₀ hl _).symm

set_option maxHeartbeats 1000000 in

theorem evAt_mem_span (hP : GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels)
    (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i)
    (x : (R.HW i σ).H) : evAt R i σ (v₀ i σ) x ∈
      Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) := by
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hM.HW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity hP D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hs hw (ht.hv₀ i σ).1 _ _ _ hx
  rw [show levChi _ (R.βW i) (R.datWp i R.triv) = fun _ => 1 from funext (GlobalTheory.ConjEval.levChi_principal R i)] at h1
  obtain ⟨P, hP0, hPb, hP⟩ := GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg _ h1
  have hc := GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg P hPb (hP.symm ▸ h2)
  have hτ : D.what₂.Tau := D.eTau.symm ⟨1, Subgroup.one_mem _⟩
  have hmem := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T ht.laws _ (inR i) (κ i) (fun τ k _ => lastPos_of_kapIs ht.kap i τ k)
    ((ht.kap i hτ).2.2.symm ▸ hn) _ hσ ⟨holCusp_mem_holSub _ _ hc, hP0⟩
  have h3 := Submodule.mem_map_of_mem (f := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))) hmem
  rw [hP, Submodule.map_span] at h3
  refine Submodule.span_le.2 ?_ h3
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  rw [adel_rdU_eq T hV (wtA (κ i)) f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem jUnif : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ → JEvBar T R κ → EvInj T R v₀ → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro hP D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp hJ hB hI hn
  refine jUnif_of T R κ v₀ ht.laws hJ hB hI (GlobalTheory.PhiIndep.phiC_indep D T κ ht.laws)
    (evAt_mem_span hP T R κ v₀ hL hM ht hp hn) fun i σ hσ => ?_
  obtain ⟨e⟩ := (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).1 i σ hσ
  exact finrank_le_of_antilinear e

end GlobalTheory.ReadingSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fittingLaterStages_row_is_constructionState : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over, o.Fits → o.G = P.Z₀.G → o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → BkLaw (w.D o.Z) → ∃ x : St P, x.o = o := by
  first | exact @GlobalTheory.Mem.R3.Rw.st_of_fits | exact GlobalTheory.Mem.R3.Rw.st_of_fits | (intros; apply GlobalTheory.Mem.R3.Rw.st_of_fits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  first | exact @GlobalTheory.Mem.ThRead.thDef3_thTheta | exact GlobalTheory.Mem.ThRead.thDef3_thTheta | (intros; apply GlobalTheory.Mem.ThRead.thDef3_thTheta <;> assumption)
end

