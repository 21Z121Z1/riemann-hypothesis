import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistEqResc
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Ex.NumD

variable {O : Type} [CommRing O] (N : NumD O)

def resc (h : N.X → Oˣ) (t : N.X → N.X → Oˣ) (h_add : ∀ x y, h (x + y) = h x * h y * t x y) (h_neg : ∀ x, h (-x) = h x)
    (t_add : ∀ x x' y, t (x + x') y = t x y * t x' y) : NumD O :=
  { N with ψ := fun χ => N.ψ χ * h χ
           even := fun χ => by rw [h_neg, mul_right_comm, N.even χ]
           bimult := fun a a' b => by
             have e : ∀ x y : N.X, N.ψ (x + y) * h (x + y) / (N.ψ x * h x) / (N.ψ y * h y) =
                 N.ψ (x + y) / N.ψ x / N.ψ y * t x y := fun x y => by
               rw [h_add]
               apply Additive.ofMul.injective
               simp only [ofMul_mul, ofMul_div]; abel
             rw [e, e, e, mul_right_comm, N.bimult a a' b, t_add]
             exact mul_mul_mul_comm _ _ _ _ }

end GlobalTheory.Ex.NumD

namespace GlobalTheory.LocM.MultiPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Terms

variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [Field C] [Algebra (FractionRing R) C] (A : ArcF D R C)

def vec (m : ℕ) (x : D.La) (χ : A.N.X) : A.D₀.X := A.ν.eX ((A.q (m ^ 2) x).1.1.toAdd + m • χ)

def txR (Q : ℕ → A.D₀.X → Cˣ) (m : ℕ) (x : D.La) (χ : A.N.X) : C :=
  (Q (m ^ 2) (vec A m x χ) : C) * A.N.txT m (A.q (m ^ 2) x) χ

def evR (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) (m j : ℕ) (z x : D.La) (χ : A.N.X) : C :=
  ((Q (m ^ 2) (vec A m x χ) * T j (A.ν.eX (A.q j z).1.1.toAdd) (vec A m x χ) : Cˣ) : C) *
    A.N.evT m (A.q (m ^ 2) x) (A.q j z).1.2 χ

end Terms

def GReal {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C] [Algebra (FractionRing R) C] (o : Full D C)
    (A : ArcF D R C) (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) : Prop :=
  o.ρ = A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = A.I.ζ n) ∧ ∀ m, Odd m → o.Theta m (fun x => ∑' χ, txR A Q m x χ) ∧
    ∀ j, 0 < j → ∀ z, o.Coord m (o.I.ev j z) fun x => ∑' χ, evR A Q T m j z x χ

def mQ {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (w : X) : Cˣ := ∏ i, ρ i n ^ (δ i w w / 2)

def mT {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (y w : X) : Cˣ := ∏ i, ρ i n ^ δ i y w

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasPt (Y : Model Xo c β) (m : ℕ) {κ : Type} [Field κ] (x : Sp κ ⟶ Xo.XF c) (ζ : κ) (v : D.La → κ)
    (w : D.La → D.La → κ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (f : κ →+* Ω) (o : Full D Ω), FullAt Y (spMap f ≫ x) o ∧ (o.I.ζ (m ^ 2) : Ω) = f ζ ∧
    o.Theta m (fun a => f (v a)) ∧ ∀ z, o.Coord m (o.I.ev l.M' z) fun a => f (w z a)

def reform {A₀ : Type} [CommRing A₀] [IsDomain A₀] {b : O →+* A₀} {a : ArcIn D l β A₀ b} {F : Type} [Field F]
    [Algebra (FractionRing A₀) F] (A : Lift a F) (ga : levelForms H l.M' a.D₀.X) (h : ga ∈ admitted H l.M' a.D₀.X) :
    Lift (withForm a ga h) F :=
  { A with
    be := { be := ga.1.comp A.ν.eX.toIntLinearEquiv.toLinearMap A.ν.eX.toIntLinearEquiv.toLinearMap
            symm := fun _ _ => ga.2.1 _ _
            pos := fun y hy => h.1 _ ((map_ne_zero_iff _ A.ν.eX.injective).2 hy)
            dvd := fun _ _ => h.2 _ _ }
    be_eq := fun _ _ => rfl }

end GlobalTheory.LocM.MultiPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  have key : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (R.toCx3 F).zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (R.toCx3 F).zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j h1 h2
    subst h1
    cases h2
    exact C.pt
  exact ⟨⟨C.wU, C.bij, C.eNu, C.NuC, C.nu, key Y₁.tup Y₁.jA h1 h2⟩⟩

end GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem.R3 in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Top.Bl.zeU_prmR_NEb : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (prmR N S Γ).s := by
  intro hPr hL N S Γ hN K q
  have hK : ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t := by
    obtain ⟨B, f, T, w, Z, O, x⟩ := q
    obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
    obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
    obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
    simp only [ofObj, extraObj] at ker_eq
    cases ker_eq
    obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
      ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
        nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
      kT.unf kT.ok kT.served
    exact ⟨t1, (StdModel.stdKer_iff w.I w.l Z t1).2 s1, o1, heq_of_eq e1, a1, p1⟩
  obtain ⟨t, ht⟩ := hK
  obtain ⟨Dc, Sp₀, Zsc₀, C₀, -⟩ := GlobalTheory.Mem.R3.SelC.cols_of_witnesses _ K q t ht ⟨q.x.rx⟩
  obtain ⟨kap, lam, err, hP, hH, -, -, -, Y', Z', htup, -, hjA, -⟩ := GlobalTheory.Mem.R3.reFace_scalars_errors_readings _ _ _ _ _ _ _
    q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.Z Dc Sp₀ q.x.what₂.r.z.F.Zsc (fun _ => Or.inl rfl)
    q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange
  obtain ⟨C'⟩ := GlobalTheory.Mem.R3.readC_reFace_updS _ _ _ Dc Sp₀ Sp₀ Zsc₀ q.x.what₂.r.z.F.Zsc kap lam err C₀ Y' htup hjA
  obtain ⟨nb⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
  have hBk : BkLaw (q.w.D q.Z) := nb.2.down
  have hRat := GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH
  exact GlobalTheory.Mem.R3.zeTied_of_read hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH (hBk hRat)
end

