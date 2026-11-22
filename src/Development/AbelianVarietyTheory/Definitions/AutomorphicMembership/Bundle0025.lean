import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cx_zs_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) (κ lam e) : (reErr (reScal Y κ lam) e).zs = Y.zs := rfl

theorem cx_liftMat_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) : (reErr (reScal Y κ lam) e).liftMat cr b j t = Y.liftMat cr b j t := by
  have h : (reErr (reScal Y κ lam) e).liftMatC cr b j t = Y.liftMatC cr b j t := by
    unfold CxData.liftMatC
    rfl
  exact congrArg (kMat Bs.v0.embedding) h

theorem cx_Iw_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    ((reErr (reScal Y κ lam) e).data cr b).Iw j t w = (Y.data cr b).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M b j) (Formalism.DivisionValues.matLat M ((lv (fc Y.zs) b).Tl j t))) (cx_liftMat_scal Y cr κ lam e b j t)

theorem definiteComplexNonzeroIndexPlaces_rescale_errors {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : (reErr (reScal Y κ lam) e).W1 cr N w ↔ Y.W1 cr N w :=
  exists_congr fun j => or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _)))
    (or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _))) Iff.rfl)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} (Y : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
  (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc Dc' : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
  (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Sp' : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc' Zs))
  (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem cx_tC_face (j : Fin m) (t : T) :
    Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t := rfl

theorem cx_liftMat_face (j : Fin m) (t : T) :
    Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t :=
  congrArg (fun g => kMat A3.fam3.base3.v0.embedding (relMat (Y.w0C false j) g)) (cx_tC_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem cx_Iw_face (j : Fin m) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false).Iw j t w = (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M false j) (Formalism.DivisionValues.matLat M ((A3.side3 P0 ψ0 Y.zs).Tl j t)))
    (cx_liftMat_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem definiteSide_nonzeroIndexPlaces_any_columns_scale (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 K)) :
    Y.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') N w ↔ ∃ j : Fin m,
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 w ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) w ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨ N.F0 w j ≠ 0) ∨
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 (Formalism.DivisionValues.conjPl w) ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) (Formalism.DivisionValues.conjPl w) ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨
          N.F0 (Formalism.DivisionValues.conjPl w) j ≠ 0) := by
  refine exists_congr fun j => ?_
  rw [← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j, ← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j]
  have key : ∀ a b c d e f : Prop, (a ∨ b ∨ c ∨ d ∨ e ∨ f) ↔ (a ∨ c ∨ e) ∨ (b ∨ d ∨ f) := fun _ _ _ _ _ _ => by tauto
  exact key _ _ _ _ _ _

end Cx

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def NzAt (R : RealDat3 D A3 Ks) (F : Face3 D A3) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (s0Of R F).Iw j A3.A.μ0 w ≠ 0 ∨
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 (zsOf R F)).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 (zsOf R F)).Tl j A3.A.μ0) ≠ 0 ∨ F0 w j ≠ 0

set_option maxHeartbeats 1000000 in

theorem toCx3_upd_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc) = reErr (reScal (R.toCx3 F) (fun _ => kap) lam) err := rfl

set_option maxHeartbeats 1000000 in

theorem complexSide_nonzeroIndexPlaces_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (N : IndefNum A3.fam3.base3)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).W1 (reFace F Dc Sp Zsc).cr N w ↔
      ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  rw [e]
  exact (definiteComplexNonzeroIndexPlaces_rescale_errors (R.toCx3 F) _ _ _ _ N w).trans (definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc Dc F.Sp Sp F.Zsc Zsc N w)

set_option maxHeartbeats 1000000 in

theorem complexSide_nonzeroIndexPlaces_iff_self (R : RealDat3 D A3 Ks) (F : Face3 D A3) (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (R.toCx3 F).W1 F.cr N w ↔ ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) :=
  definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Dc F.Sp F.Sp F.Zsc F.Zsc N w

set_option maxHeartbeats 1000000 in

theorem nzAt_res {f : T' → T} {μ : T'} (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (Res.dat3 f μ R mu tw) (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w ↔ NzAt R (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w := Iff.rfl

set_option maxHeartbeats 1000000 in

theorem complexSide_numberContents_eq_scaleAtSubspaces (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (C CH : ℝ) :
    (((R.updS kap lam).withErr err).num (reFace F Dc Sp Zsc) C CH).F0 = (Zsc (zsOf R F)).F0 := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  have e2 : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs e).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have e3 : ∀ (F' : Face3 D A3) (s : DefSub A3.fam3.amb3), ((F'.fc s).Z.num C CH).F0 = (F'.Zsc s).F0 := fun _ _ => rfl
  exact (e3 (reFace F Dc Sp Zsc) _).trans (congrArg (fun s => (Zsc s).F0) e2)

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem _root_.GlobalTheory.Mem.R3.columnChoiceReferenceFace_eq_bareFaceTwoLevels (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    face0 X I hX U Xg tr = Res.bare3 (famR X I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) := rfl

set_option maxHeartbeats 2000000 in

def resGeo (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resR h).toRealDat fun _ => 1 :=
  Res.geoHalf (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') z.geo

set_option maxHeartbeats 2000000 in

theorem pins_resR (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) (hB : z.R.PThmB) :
    Pins (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact Res.pins (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I) (mu := z.resMu h) (tw := z.resTw Wt')
    (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e hB (z.newTup h hc)

set_option maxHeartbeats 2000000 in

theorem holds_resR (h : Wt' ⊆ Wt) (hH : Holds z.R z.F) : Holds (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) := by
  have hp := z.pins.char
  have hH' : Holds z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) := hH
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp hH' ⊢
  exact Res.intersectionNumber_baseChange (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I) (z.resMu h) (z.resTw Wt')
    (inclU_injective (usedOf_mono I T h)) hp hH'

set_option maxHeartbeats 2000000 in

theorem levOf_resR (h : Wt' ⊆ Wt) : LevOf X I (usedOf I T Wt') (z.resR h).toLevCh where
  is := Res.levCh_is (L := z.R.toLevCh) (inclU_injective (usedOf_mono I T h)) z.lev.is
  C := z.lev.C
  xiH t := z.lev.xiH (inclU I (usedOf_mono I T h) t)
  Pg := z.lev.Pg
  Q t := z.lev.Q (inclU I (usedOf_mono I T h) t)
  beta := z.lev.beta

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesTransferAlongSameFiniteGroup
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.RealGeo GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Tr

variable {B : Base} {C : Cols B} {a b : Late B C} {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : Top.TwDat B}
  {Wt : Set B.places.Pl}

def SameGrp.ofGrpTrue {f : Top.Fr B.toPre} (h : Top.GrpTrue a.N f) (h' : Top.GrpTrue b.N f) : SameGrp a b where
  e := Top.plEquiv a.N.naut b.N.naut
  pl := Top.TypesTrue.plGw_plEquiv h h'
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

theorem LevOf.transfer (b : Late B C) {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) :
    LevOf b.st I U (levCh b L) :=
  ⟨levIs_tr b h.is, (by with_unfolding_all exact ((congrArg (chFr b) h.C) :)), (by with_unfolding_all exact (h.xiH :)), (by with_unfolding_all exact (h.Pg :)), (by with_unfolding_all exact (h.Q :)), (by with_unfolding_all exact (h.beta :))⟩

theorem GoodSet.transfer (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : ∀ g, b.D.ntypes.e0.coeff ((eR.trans s.iso) g) = a.D.ntypes.e0.coeff (eR g) := fun g => s.e0 (eR g)
  obtain ⟨h1, h2⟩ := (goodSet_iff a.st (px := px) eR Xg).1 h
  refine (goodSet_iff b.st (px := px) _ Xg).2 ⟨fun χ => (h1 χ).trans (and_congr_right fun _ => ?_), fun g => (h2 g).trans (e g).symm⟩
  exact Eq.congr_left (Finset.sum_congr rfl fun g _ => congrArg (· * B.embLL (χ g)) (e g).symm)

theorem GrpAt.pl_transfer (s : SameGrp a b) (h : GrpAt a.st I) :
    ∃ plg : (Σ k : Fin 2, b.D.nd.PlG k) ≃ (B.primes px).vGs,
      ∀ kv, ((plg kv).1 : Pl b.D.host.E) = b.D.naut.plGw kv.1 kv.2 ∧ I.C.P.Div kv.1 (plg kv).1 := by
  obtain ⟨plg, h1⟩ := h.pl
  exact ⟨s.back.trans plg, fun kv => ⟨(h1 (s.back kv)).1.trans (s.pl_back kv), (h1 (s.back kv)).2⟩⟩

def Dat.transfer (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((Tr.alg (a := a) b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := (by with_unfolding_all exact ((real3 (a := a) b z.R) :)))
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf (a := a) b z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr (a := a) b s z.pins) :)))
    (lev := (by with_unfolding_all exact ((z.lev.transfer b) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((GoodSet.transfer s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

namespace Dat

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem transfer_Xg : (z.transfer s).Xg = z.Xg := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).Xg)) :))

theorem transfer_tr : (z.transfer s).tr = z.tr := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).tr)) :))

theorem transfer_field : ((z.transfer s).core.Q.c.F : Type) = z.core.Q.c.F := (by with_unfolding_all exact ((Eq.refl (((z.transfer s).core.Q.c.F : Type))) :))

theorem transfer_mu : (z.transfer s).R.mu = (z.R.mu) := (Eq.refl (transfer s z).R.mu)

theorem transfer_twPl : (z.transfer s).R.twPl = (z.R.twPl) := (Eq.refl (transfer s z).R.twPl)

theorem transfer_kap : (z.transfer s).R.kap = z.R.kap := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).R.kap)) :))

theorem transfer_liftScalars : (z.transfer s).R.lam3 = (z.R.lam3) := (Eq.refl (transfer s z).R.lam3)

theorem transfer_errorTerms : (z.transfer s).R.err0 = (z.R.err0) := (Eq.refl (transfer s z).R.err0)

theorem transfer_phs : (z.transfer s).R.phs = (z.R.phs) := (Eq.refl (transfer s z).R.phs)

theorem transfer_Pg : (z.transfer s).R.Pg = (z.R.Pg) := (Eq.refl (transfer s z).R.Pg)

theorem transfer_eG : (z.transfer s).R.eG = (z.R.eG) := (Eq.refl (transfer s z).R.eG)

theorem transfer_cG : (z.transfer s).cG = (by with_unfolding_all exact ((z.cG.trans s.iso) :)) := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).cG)) :))

theorem transfer_nW : (z.transfer s).R.nW = (z.R.nW) := (Eq.refl (transfer s z).R.nW)

theorem transfer_FW : (z.transfer s).R.FW = (z.R.FW) := (Eq.refl (transfer s z).R.FW)

theorem transfer_HX : (z.transfer s).R.HX = (z.R.HX) := (Eq.refl (transfer s z).R.HX)

theorem transfer_HV : (z.transfer s).R.HV = (z.R.HV) := (Eq.refl (transfer s z).R.HV)

theorem transfer_HE : (z.transfer s).R.HE = (z.R.HE) := (Eq.refl (transfer s z).R.HE)

theorem transfer_HW : (z.transfer s).R.HW = (z.R.HW) := (Eq.refl (transfer s z).R.HW)

theorem transfer_Th : (z.transfer s).R.Th = (z.R.Th) := (Eq.refl (transfer s z).R.Th)

theorem transfer_thG : (z.transfer s).R.thG = (z.R.thG) := (Eq.refl (transfer s z).R.thG)

theorem transfer_zs : zsOf z.R z.F = (by with_unfolding_all exact ((zsOf (z.transfer s).R (z.transfer s).F) :)) :=
  (by with_unfolding_all exact ((congrArg Cx.CxData.zs (toCx3_eq (a := a) b z.R z.F)) :))

theorem transfer_EEat : z.R.toRealDat.EEat = ((transfer s z).R.EEat) := (eeat_eq b z.R.toRealDat)

theorem transfer_Wall : z.R.toRealDat.Wall = ((transfer s z).R.Wall) := (wall_eq b z.R.toRealDat)

theorem transfer_Wat : z.R.toRealDat.Wat = ((transfer s z).R.Wat) := (wat_eq b z.R.toRealDat)

theorem transfer_CC : z.R.toRealDat.CC = ((transfer s z).R.CC) := (cc_eq b z.R.toRealDat)

theorem eigenspace_eq_of_transfer : z.R.EEp3 = ((transfer s z).R.EEp3) := (realAdelicInertTransport_typeRows_eq b z.R)

theorem transfer_formParts : z.R.Wp3 = ((transfer s z).R.Wp3) := (wp3_apply_eq_sq_mul_sub_sq_mul b z.R)

theorem transfer_toCx3 : z.R.toCx3 z.F = ((transfer s z).R.toCx3 (transfer s z).F) := (toCx3_eq b z.R z.F)

theorem transfer_s0Of : HEq (s0Of z.R z.F) (s0Of (z.transfer s).R (z.transfer s).F) :=
  (by with_unfolding_all exact ((congr_arg_heq (fun X : type_of% (z.R.toCx3 z.F) => X.data z.F.cr false) (toCx3_eq (a := a) b z.R z.F)) :))

theorem transfer_s1Of : HEq (s1Of z.R z.F) (s1Of (z.transfer s).R (z.transfer s).F) :=
  (by with_unfolding_all exact ((congr_arg_heq (fun X : type_of% (z.R.toCx3 z.F) => X.data z.F.cr true) (toCx3_eq (a := a) b z.R z.F)) :))

theorem nonzeroIndexPlaces_transferAlongSameFiniteGroup (F0 : HeightOneSpectrum (𝓞 B.LL) → Fin B.R.m → ℝ) : z.W1 F0 = (z.transfer s).W1 F0 :=
  (by with_unfolding_all exact ((congrArg (fun X : type_of% (z.R.toCx3 z.F) => {w : B.places.Pl | ∃ j,
    ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
      IndefData.Iw (Df := (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs) (((X.data z.F.cr false))) j
          (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
        Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
                  (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
          (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
            (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}) (toCx3_eq (a := a) b z.R z.F)) : _))

variable {z}

theorem holds_transfer (h : Holds z.R z.F) : Holds (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((holds_tr (a := a) b h) :))

theorem exAt_transfer (h : z.R.toRealDat.ExAt) : (z.transfer s).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr (a := a) b h) :))

theorem inGeo_transfer (h : InGeo z.geo) : InGeo (z.transfer s).geo := (by with_unfolding_all exact ((inGeo_tr (a := a) b h) :))

theorem errEq_transfer (h : ErrEq z.R z.F) : ErrEq (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((errEq_tr (a := a) b h) :))

end Dat

theorem nonempty_dat_iff (s : SameGrp a b) : Nonempty (Dat a.st I hX T Wt) ↔ Nonempty (Dat b.st I hX T Wt) :=
  ⟨fun ⟨z⟩ => ⟨z.transfer s⟩, fun ⟨z⟩ => ⟨z.transfer s.symm⟩⟩

def Dat.transferTo {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {W' : RowsRest X.B X.C} {V' : DivStage X.B X.C W'} {S' : SStage X.B X.C W'} {N' : NStage X.B X.C W'}
    {G' : GJStage X.B X.C} (s : SameGrp X.toLate ⟨W', V', S', N', G'⟩) (z : Dat X I hX T Wt) :
    Dat ⟨X.B, X.C, W', V', S', N', G'⟩ I hX T Wt :=
  Dat.transfer (a := X.toLate) s z

section Rows

variable {ix : C.Tup ≃ I.ι} {p0 : BaseLevelRowSide a.D}

def RowsAre.tr (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0) : RowsAre c.to.st I hX T Wt ix (baseLevelRowSideTransport c p0) :=
  @RowsAre.mk c.to.st px I hX T Wt ix (baseLevelRowSideTransport c p0)
    (z := r.z.transfer c.same)
    (intersectionNumber_baseChange := Dat.holds_transfer c.same r.intersectionNumber_baseChange)
    (Y := (by with_unfolding_all exact ((read c r.Y) :)))
    (Z := (by with_unfolding_all exact ((readL c r.Z) :)))
    (tup_ix := (by with_unfolding_all exact (r.tup_ix :)))

namespace RowsAre

variable (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0)

theorem tr_z_eq_transfer : (r.tr c).z = r.z.transfer c.same := rfl

theorem tr_tup : (r.tr c).Y.tup = (r.Y.tup) := (Eq.refl (tr c r).Y.tup)

theorem tr_jA : (r.tr c).Y.jA = (r.Y.jA) := (Eq.refl (tr c r).Y.jA)

theorem transfer_baseForms : (r.tr c).Y.jA0 = (r.Y.jA0) := (Eq.refl (tr c r).Y.jA0)

theorem tr_eMt : (r.tr c).Y.eMt = (r.Y.eMt) := (Eq.refl (tr c r).Y.eMt)

theorem tr_eE : (r.tr c).Y.eE = (r.Y.eE) := (Eq.refl (tr c r).Y.eE)

theorem tr_jW : (r.tr c).Z.jW = (r.Z.jW) := (Eq.refl (tr c r).Z.jW)

theorem tr_eRR : HEq r.Z.eRR (r.tr c).Z.eRR :=
  (by with_unfolding_all exact ((congr_arg_heq (eRRu r.Z) (parts_eq (a := a) c.to r.z.R r.z.F)) :))

theorem transfer_rowLattice : HEq r.Z.eRR0 (r.tr c).Z.eRR0 :=
  (by with_unfolding_all exact ((congr_arg_heq (riemannRochSpaceCoordinateEquiv r.Z) (parts_eq (a := a) c.to r.z.R r.z.F)) :))

end RowsAre

def RowsAre.trSG (r : RowsAre a.st I hX T Wt ix p0) (S : SStage B C a.W) (G : GJStage B C) :
    RowsAre ⟨B, C, a.W, a.V, S, a.N, G⟩ I hX T Wt ix ((baseLevelRowSideTransport (Refill.ofSG a S G) p0)) :=
  (by with_unfolding_all exact ((r.tr (Refill.ofSG a S G)) :))

theorem Refill.ofDiv_D (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) :
    (Refill.ofDiv a L h).to.D = GlobalTheory.EX.OB.setDiv a.D L h := rfl

theorem Refill.refill_divisionSide (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide a.D) :
    baseLevelRowSideTransport (Refill.ofDiv a L h) p0 = (@BaseLevelRowSide.mk (EX.OB.setDiv (@Late.D B C a) L h) (@EX.OB.sideTr (@Late.D B C a) L h (@Rows.Data.EE0 (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0 (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0i (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0f (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@BaseLevelRowSide.s (@Late.D B C a) p0))) :=
  (by with_unfolding_all exact ((Eq.refl (baseLevelRowSideTransport (Refill.ofDiv a L h) p0)) :))

def RowsAre.trDiv (r : RowsAre a.st I hX T Wt ix p0) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) :
    RowsAre (Refill.ofDiv a L h).to.st I hX T Wt ix (baseLevelRowSideTransport (Refill.ofDiv a L h) p0) :=
  r.tr (Refill.ofDiv a L h)

end Rows

example (a : Late B C) (g : G0g a.D.nd) : (SameGrp.ofN a.N a.V a.V a.S a.S a.G a.G).iso g = g := rfl

example (a : Late B C) : (Refill.ofSG a a.S a.G).to = a := rfl

example (s : SameGrp a b) (g : G0g a.D.nd) (k : Fin 2) (v : b.D.nd.PlG k) : s.iso g ⟨k, v⟩ = g ⟨k, (s.e k).symm v⟩ := rfl

example (s : SameGrp a b) (z : Dat a.st I hX T Wt) : ((z.transfer s).transfer s.symm).R.twPl = z.R.twPl :=
  (by with_unfolding_all exact ((Eq.refl z.R.twPl) :))

end GlobalTheory.Mem.R3

end
end

