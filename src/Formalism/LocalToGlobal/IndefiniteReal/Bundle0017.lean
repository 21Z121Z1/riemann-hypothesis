import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0014

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPart
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

structure CxPrims (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (cv : CrdV A.fam.amb) (s : ℕ)
    (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop)
    (ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  kerStabR : X.KerStabR

  kerStabL : X.KerStabL

  adjClosedR : X.AdjClosedR

  adjClosedL : X.AdjClosedL

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  jIsoR : X.JIsoR cv

  jIsoL : X.JIsoL cv

  ok : A.fam.Ok s

  sep : A.fam.TypesSep

  heckeR : HeckeRatR A

  heckeL : HeckeRatL A

  eig0 : LiftsEig A X P0 ψ0 C0

  eig1 : LiftsEig A X P1 ψ1 C1

  typ0 : LiftsTyp A C0

  typ1 : LiftsTyp A C1

  pos : ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  w1 : ∀ w, X.W1 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  h4pos : X.H4pos

  isoR : ∀ b, X.IsoR (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZ : ∀ b, X.CrdZ (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  coordinates_in_good_part : ∀ b, X.CoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLev : ∀ b, X.RatLev (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLev : ∀ b, X.DnLev cv b

  upLev : ∀ b, X.UpLev cv b

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  ratMu : ∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3 : ∀ b, X.H3 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  isoL : ∀ b, X.IsoL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  crdZL : ∀ b, X.CrdZL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  lift_coordinates_in_good_part : ∀ b, X.LiftCoordinatesInGoodPart (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  ratLevL : ∀ b, X.RatLevL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b

  dnLevL : ∀ b, X.DnLevL cv b

  upLevL : ∀ b, X.UpLevL cv b

  thmAop : ∀ b, X.ThmAop b

  partsW : ∀ b, X.PartsW b

  ratTh : ∀ b, X.RATth (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  h3W : ∀ b, X.H3W (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  galD : ∀ b, X.GalD (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b

  dimParts : ∀ b, X.DimParts b

  l3 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  btVanish : X.BtVanish (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

  mi0 : X.MatrixIdentityOffBase (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ

  zetaOK : X.ZetaOK ζ

  l1e : (X.colOf (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

  passage : Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
    (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

  fun0 : (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

section All

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {X : CxData A.fam.amb} {cv : CrdV A.fam.amb} {s : ℕ}
  {C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop}
  {ζ : (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A.fam.base.Tup → K}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH}
  {C CH : ℝ}

theorem CxPrims.stable (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) : X.zs.Stable :=
  CxData.cutStable X hP.kFormR hP.kFormL hP.kerStabR hP.kerStabL hP.adjClosedR hP.adjClosedL

theorem CxPrims.wf (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A.side_WF hP.ok P0 ψ0 X.zs hP.stable hP.inBlock hP.sep
  | true => A.side_WF hP.ok P1 ψ1 X.zs hP.stable hP.inBlock hP.sep

theorem links_of_prims (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE) C CH := by
  have hW := hP.wf
  have hst := hP.stable
  have what₂ := fun b => cutRows (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.isoR b) (hP.crdZ b)
    (hP.coordinates_in_good_part b) (hP.ratLev b) (hP.dnLev b) (hP.upLev b) (hP.thmBop b) (hP.partsE b)
  have lifts := fun b => CxData.cutLifts X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) cv b (hW b) hP.h4pos (hP.kForm b)
    (hP.isoL b) (hP.crdZL b) (hP.lift_coordinates_in_good_part b) (hP.ratLevL b) (hP.dnLevL b) (hP.upLevL b) (hP.thmAop b) (hP.partsW b)
  have types := cutTypes A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.sep hst hP.eig0 hP.eig1 hP.typ0 hP.typ1
  exact
    { stable := hst
      inBlock := hP.inBlock
      ratZ := hP.ratZ
      pos := hP.pos
      proviso := cutProviso A X P0 ψ0 P1 ψ1 Dc Sp Zsc s C0 C1 hP.ok hP.heckeL hP.eig0 hP.eig1
      types := types
      partsOrth := cutPartsOrth A X P0 ψ0 P1 ψ1 Dc Sp Zsc s hP.ok hP.heckeR hst
      h0 := hP.h0
      h2 := fun b => (what₂ b).1
      ratMu := hP.ratMu
      h3 := hP.h3
      h4pos := hP.h4pos
      h4 := fun b => (what₂ b).2
      kForm := hP.kForm
      mLat := hP.mLat
      ewNorm := hP.ewNorm
      h5 := fun b => (lifts b).1
      ratTh := hP.ratTh
      h3W := hP.h3W
      thmA := fun b => (lifts b).2
      galD := hP.galD
      l1d := fun b => CxData.cutDims X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b (hW b) hP.h4pos (hP.kForm b) (hP.ewNorm b)
        (types b) (what₂ b).1 (hP.ratMu b) (hP.h3 b) (lifts b).1 (hP.ratTh b) (hP.h3W b) (hP.partsE b) (hP.partsW b)
        (hP.dimParts b)
      l3 := hP.l3
      on := hP.on
      l6 := hP.l6
      l1b := CxData.cutPairing X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) ζ sEE (hW true) (what₂ true).1 hP.btVanish hP.mi0 hP.zetaOK
      l1e := hP.l1e
      untw := CxData.cutTuples2 X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH hP.h0 hP.w1
      passage := hP.passage
      fun0 := hP.fun0 }

def cxPkgPrims (hP : CxPrims A P0 ψ0 P1 ψ1 Dc Sp Zsc X cv s C0 C1 ζ sEE C CH) :
    IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH :=
  cxPkgF A hP.ok hP.sep P0 ψ0 P1 ψ1 Dc Sp Zsc X _ C CH (links_of_prims hP)

end All

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem definite_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZ (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b <;> exact toF_mem_Z _ _ _

theorem definite_coordinates_in_good_part (X : CxData A3.fam3.amb3) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem lift_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b <;> exact toF_mem_Z _ _ _

theorem lift_coordinates_in_good_part_family (X : CxData A3.fam3.amb3) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem definite_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y
  · rw [hJ t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y

theorem lift_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ j t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y
  · rw [hJ j t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y

theorem definite_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl p'))
      fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr k'))
      fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.what₂ t).act g f f'⟩

theorem lift_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH j t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inl p))
      (Sum.inl (Sum.inl p')) fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH j t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inr k))
      (Sum.inl (Sum.inr k')) fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f'⟩

end Concrete3

section Equiv3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

theorem coordinates_mem_subspace {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  exact toF_mem_Z ℓ Z y

theorem part_iff_rows3 (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (p : A3.fam3.base3.Ix)
    (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.R A3.fam3.F.μ0).dZ ℓ (X.Z A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ (X.Z A3.fam3.F.μ0) p.1 ↔
      X.Θ A3.fam3.F.μ0 (X.jR A3.fam3.F.μ0 ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ (X.Z A3.fam3.F.μ0) y)) ∈ X.EEp p := by
  have : FiniteDimensional K (A3.fam3.F.R A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.R A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts p]
  exact mem_eigSum_iff_map ((X.Θ A3.fam3.F.μ0).comp (X.jR A3.fam3.F.μ0)) (hOk.what₂ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.what₂ _) (hOk.what₂ _)) hH.comm
    (fun i v => by
      show X.Θ _ (X.jR _ (A3.fam3.amb3.opR _ (Sum.inl i) v)) = _
      rw [X.jR_opR hR, hH.intw]; rfl)
    (DefFam3.stable3_rows hst A3.fam3.F.μ0) (fun z hz h0 => X.theta_jR_inj hR _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

theorem part_iff_lifts3 (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (j : Fin m)
    (p : A3.fam3.base3.Ix) (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.L j A3.fam3.F.μ0).dZ ℓ (X.Zl j A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.LI j A3.fam3.F.μ0).part3 ℓ (X.Zl j A3.fam3.F.μ0) (A3.fam3.tr3 j p.1) ↔
      X.θ' j A3.fam3.F.μ0 (X.jL j A3.fam3.F.μ0 ((A3.fam3.F.L j A3.fam3.F.μ0).toF ℓ (X.Zl j A3.fam3.F.μ0) y)) ∈ X.Wp j p := by
  have : FiniteDimensional K (A3.fam3.F.L j A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.L j A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts j p]
  exact mem_eigSum_iff_map ((X.θ' j A3.fam3.F.μ0).comp (X.jL j A3.fam3.F.μ0)) (hOk.lifts _ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.lifts _ _) (hOk.lifts _ _))
    (hH.comm j)
    (fun i v => by
      show X.θ' _ _ (X.jL _ _ (A3.fam3.amb3.opL _ _ (Sum.inl i) v)) = _
      rw [X.jL_opL hL, hH.intw]; rfl)
    (DefFam3.stable3_lifts hst j A3.fam3.F.μ0) (fun z hz h0 => X.theta_jL_inj hL j _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
  (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem definite_equivariance_of_primitive (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (b : Bool) :
    X.H3 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro p x
  rw [CxData.iC_cpt_eq]
  cases b
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P0 ψ0) x
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P1 ψ1) x

theorem lift_equivariance_of_primitive (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (b : Bool) :
    X.H3W (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j p x
  rw [CxData.tC_cpt_eq]
  cases b
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P0 ψ0) x
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P1 ψ1) x

end Equiv3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PHeisThC
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Filter Topology
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

theorem eq_one_of_re_pow_gt (u : ℂ) (hu : ‖u‖ = 1) (h : ∀ n : ℕ, 1 / 2 < (u ^ n).re) : u = 1 := by
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖u - 1‖)
  have h1 : ‖u ^ N - 1‖ ≤ 2 := by
    calc ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hu]; norm_num
  have h2 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ _i ∈ Finset.range N, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => (h i).le
  have h3 : (N : ℝ) / 2 * ‖u - 1‖ ≤ 2 := by
    calc (N : ℝ) / 2 * ‖u - 1‖ ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = ‖u ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ 2 := h1
  have h4 : 4 / ‖u - 1‖ * ‖u - 1‖ = 4 := div_mul_cancel₀ _ hpos.ne'
  nlinarith [mul_lt_mul_of_pos_right hN hpos]

theorem psiOpen : PsiOpenP := by
  intro F _ _ ψ hψ
  obtain ⟨hcont, hnorm, -, -⟩ := hψ
  let g : Af F → ℂ := fun y => ψ (pairA F 0 y)
  have hp : Continuous (pairA F 0) := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  have hg : Continuous g := hcont.comp hp
  have gzero : g 0 = 1 := by
    show ψ (pairA F 0 0) = 1
    have e : pairA F 0 0 = 0 := rfl
    rw [e, AddChar.map_zero_eq_one]
  have gadd : ∀ a b, g (a + b) = g a * g b := by
    intro a b
    show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairA
    show ((0 : Ainf F), a + b) = ((0 + 0 : Ainf F), a + b)
    rw [add_zero]
  have gnsmul : ∀ (n : ℕ) a, g (n • a) = g a ^ n := by
    intro n a
    induction n with
    | zero => simp [gzero]
    | succ n ih => rw [succ_nsmul, gadd, ih, pow_succ]
  let G : AddSubgroup (Af F) :=
    { carrier := {y | ∀ z ∈ Ohat F, g (z * y) = 1}
      zero_mem' := by
        intro z _
        rw [mul_zero]; exact gzero
      add_mem' := by
        intro a b ha hb z hz
        rw [mul_add, gadd, ha z hz, hb z hz, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := gadd (z * -a) (z * a)
        rw [← mul_add, neg_add_cancel, mul_zero, gzero, ha z hz, mul_one] at h1
        exact h1.symm }
  refine ⟨G, ?_, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    have key : ∀ᶠ d in 𝓝 (0 : Af F), ∀ z ∈ Ohat F, 1 / 2 < (g (z * d)).re := by
      refine (isCompact_Ohat F).eventually_forall_of_forall_eventually fun z _ => ?_
      have hc : Continuous fun p : Af F × Af F => (g (p.2 * p.1)).re :=
        Complex.continuous_re.comp (hg.comp (continuous_snd.mul continuous_fst))
      have h0 : 1 / 2 < (g (z * 0)).re := by rw [mul_zero, gzero]; norm_num
      exact (isOpen_lt continuous_const hc).mem_nhds h0
    refine Filter.mem_of_superset key fun d hd z hz => ?_
    apply eq_one_of_re_pow_gt _ (hnorm _)
    intro n
    have hnz : n • z ∈ Ohat F :=
      SetLike.mem_coe.mpr (nsmul_mem (SetLike.mem_coe.mp hz) n)
    have := hd _ hnz
    rwa [smul_mul_assoc, gnsmul] at this
  · intro y hy z hz w hw
    show g (w * (z * y)) = 1
    rw [← mul_assoc]
    exact hy _ (SetLike.mem_coe.mpr (mul_mem (SetLike.mem_coe.mp hw) (SetLike.mem_coe.mp hz)))
  · intro y hy
    have := hy 1 (SetLike.mem_coe.mpr (one_mem _))
    rwa [one_mul] at this

theorem psiSmooth : PsiSmoothP := by
  intro D ψ hψ k s hs
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := hψ
  have h := hall θ hθ
  have hc : ∀ ρ, ContDiff ℝ ∞ fun t : Fin k → ℝ => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro ρ
    let L : (Fin k → ℝ) →+ ℂ :=
      { toFun := fun t => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))
        map_zero' := by simp
        map_add' := fun a b => by simp [map_add, TensorProduct.add_tmul] }
    have hL : Continuous L := (hθ ρ).2.comp hs
    exact (L.toRealLinearMap hL).contDiff
  have e : (fun t => ψ (pairA D.host.F (s t) 0)) = fun t =>
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
        ∑ ρ, θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    funext t; exact h (s t)
  rw [e]
  exact (contDiff_const.mul (ContDiff.sum fun ρ _ => hc ρ)).cexp

end Formalism.IndefR.PHeisTh

end
end

