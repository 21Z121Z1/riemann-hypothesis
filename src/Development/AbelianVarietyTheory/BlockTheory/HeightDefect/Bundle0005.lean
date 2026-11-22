import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj (dualMap FrPt Gx PPx IsCombAt embK)
open scoped CategoryTheory.Obj

section Bundles

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def GenThrough (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  (∀ k, φ' k ≫ F = h ≫ φ k) ∧ PMaps w φ' φ ε a t h

def SecThrough (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) : Prop :=
  ∀ (j : L.ι) (k : L'.ι) (V : X'.Opens) (h₁ : V ≤ F ⁻¹ᵁ L.U j) (h₂ : V ≤ (LB.div (L.pull F) L').U (fun _ => j, k))
    (h₃ : V ≤ L'.U k), (F.appLE _ _ h₁).hom (s.f j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ h₃ (s'.f k)

end Bundles

section Tangent

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

abbrev EpsPt (D₀ : Out.DegPre A) : Type := Out.GtPt D₀ (epsR A)

def IsTanGt (ν : EpsPt D₀) : Prop :=
  IsTangent ν.b ∧ ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
    (LB.pullGen D₀.P.L _ _ (ν.s x) (spMap (TrivSqZeroExt.fstHom A A A).toRingHom)) (LB.oneGen D₀.P.L)

def IsSmulGt (r : A) (ν ν' : EpsPt D₀) : Prop := Out.GtPt.IsPull (spMap (epsMul r)) ν ν'

def IsCombGt {m : ℕ} (ν : Fin m → EpsPt D₀) (r : Fin m → A) (ω : EpsPt D₀) : Prop :=
  ∃ (u : Fin m → EpsPt D₀) (s : Fin (m + 1) → EpsPt D₀), (∀ i, IsSmulGt (r i) (ν i) (u i)) ∧ (s 0).IsZero ∧
    (∀ i : Fin m, Out.GtPt.IsAdd (s i.castSucc) (u i) (s i.succ)) ∧ s (Fin.last m) = ω

def ActGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) {T : Over (Sp A)} (a : O)
    (g g' : Out.GtPt D₀ T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D₀.P.L (Out.rosatiφ D₀.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (Out.zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
      ∀ x, LB.Gen.Corr D₀.P.L _ _ _ _
        (LB.mulGen D₀.P.L _ _ _ _ (g.s (star a • x))
          (LB.pullGen D₀.P.L _ _ u (lift (Out.DegPre.cT D₀ T x) g.b).left)) (g'.s x)

def IsEigGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) (ν : EpsPt D₀) : Prop :=
  ∀ a : O, ∃ ν' : EpsPt D₀, IsSmulGt (t a) ν ν' ∧ ActGt oa a ν ν'

def IsEigBasisGt {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (oa : D₀.OAct O) (t : O →+* A) {m : ℕ}
    (ν : Fin m → EpsPt D₀) : Prop :=
  (∀ i, IsTanGt (ν i)) ∧ (∀ i, IsEigGt oa t (ν i)) ∧
    ∀ ω : EpsPt D₀, IsTanGt ω → IsEigGt oa t ω → ∃! r : Fin m → A, IsCombGt ν r ω

def IsMulSec (r : A) (th th' : D₀.P.L.Sec) : Prop :=
  ∀ j, th'.f j = constFn D₀.P.A.hom (D₀.P.L.U j) r * th.f j

def FibrewiseNe (th : D₀.P.L.Sec) : Prop :=
  ∀ s : Sp A, ∃ x : D₀.P.A.left, D₀.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th

def IsGenSec (th : D₀.P.L.Sec) : Prop := ∀ th' : D₀.P.L.Sec, ∃! r : A, IsMulSec r th th'

end Tangent

section BaseChange

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {g : A →+* A'}
  {D₀ : Out.DegPre A} {D₁ : Out.DegPre A'}

abbrev prOf (pd : Out.IsPullDeg g D₀ D₁) : D₁.P.A.left ⟶ D₀.P.A.left :=
  pd.e.hom.left ≫ pullback.fst D₀.P.A.hom (Out.specOf g)

def LetterBC (pd : Out.IsPullDeg g D₀ D₁) (ν : EpsPt D₀) (ν' : EpsPt D₁) : Prop :=
  ν'.b.left ≫ prOf pd = spMap (dualMap g) ≫ ν.b.left ∧
    ∀ x, GenThrough pd.w Out.DegPre.gtε (ν'.s x) (ν.s (pd.xe x)) (spMap (dualMap g))

def SecBC (pd : Out.IsPullDeg g D₀ D₁) (th : D₀.P.L.Sec) (th' : D₁.P.L.Sec) : Prop := SecThrough pd.w th th'

def fracMap (g : A →+* A') (hg : Function.Injective g) : FractionRing A →+* FractionRing A' :=
  IsFractionRing.lift (g := (algebraMap A' (FractionRing A')).comp g) ((IsFractionRing.injective A' _).comp hg)

theorem fracMap_algebraMap (hg : Function.Injective g) (r : A) :
    fracMap g hg (algebraMap A _ r) = algebraMap A' _ (g r) := IsFractionRing.lift_algebraMap _ r

def QkBC (pd : Out.IsPullDeg g D₀ D₁) (hg : Function.Injective g) {k : ℕ} (p : Out.QkPt D₀ (FractionRing A) k)
    (p' : Out.QkPt D₁ (FractionRing A') k) : Prop :=
  ∃ q : Out.QkPt D₁ (FractionRing A') k, pd.xe q.y = p.y ∧
    q.g.b.left ≫ prOf pd = spMap (fracMap g hg) ≫ p.g.b.left ∧
    (∀ x, GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x)) (spMap (fracMap g hg))) ∧
    Out.QkPt.Equiv D₁ (FractionRing A') q p'

end BaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Inputs

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}

def IsLetters (a : ArcIn D l β A b) (io : c.F →+* FractionRing A)
    (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) : Prop :=
  letI := H.starRing
  io.comp β = (algebraMap A (FractionRing A)).comp b ∧
    ∀ τ, ∃ t : 𝓞 E →+* A, (algebraMap A (FractionRing A)).comp t = io.comp (embK c τ) ∧ IsEigBasisGt a.oa t (ν τ)

def InputBC (g : A →+* A') (a : ArcIn D l β A b) (a' : ArcIn D l β A' b') (pd : Out.IsPullDeg g a.D₀ a'.D₀) : Prop :=
  letI := H.starRing
  b' = g.comp b ∧ (∀ (r : 𝓞 E) x, pd.xe (r • x) = r • pd.xe x) ∧
    (∀ r : 𝓞 E, (a'.oa.onB.act r).left ≫ prOf pd = prOf pd ≫ (a.oa.onB.act r).left) ∧
    (∀ x z, a'.be x z = a.be (pd.xe x) (pd.xe z)) ∧
    ∃ hg : Function.Injective g, (∀ v, QkBC pd hg (a.etaA v) (a'.etaA v)) ∧
      ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), QkBC pd hg (a.eta v) (a'.eta v)

abbrev Wit (Y : Model Xo c β) (a : ArcIn D l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) :=
  ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := A)) PowerSeries.X χ

variable {Y : Model Xo c β}

def WitBC (g : A →+* A') {a : ArcIn D l β A b} {a' : ArcIn D l β A' b'} (pd : Out.IsPullDeg g a.D₀ a'.D₀)
    {χ : Sp (PowerSeries A) ⟶ Y.X} {χ' : Sp (PowerSeries A') ⟶ Y.X} (W : Wit Y a χ) (W' : Wit Y a' χ') : Prop :=
  InputBC g a a' pd ∧ χ' = spMap (PowerSeries.map g) ≫ χ ∧
    ∃ (hD : Out.IsPullDeg (PowerSeries.map g) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (Out.specOf (PowerSeries.map g))).obj W.t.G),
      IsMonHom bc.hom ∧ Out.IsPullUnif (PowerSeries.map g) hD bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf (PowerSeries.map g))) ≫ W.m.φ ∧
      W'.φ ≫ prOf pd = prOf hD ≫ W.φ ∧ (∀ x, hD.xe (W'.e x) = W.e (pd.xe x)) ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ W'.P.D.toPre.P.A.left) (z : Z) (j : a.D₀.P.L.ι) (i : W.P.D.toPre.P.L.ι)
        (i' : a'.D₀.P.L.ι) (k : W'.P.D.toPre.P.L.ι), (f ≫ prOf hD ≫ W.φ) z ∈ a.D₀.P.L.U j →
        (f ≫ prOf hD) z ∈ W.P.D.toPre.P.L.U i → (f ≫ W'.φ) z ∈ a'.D₀.P.L.U i' → f z ∈ W'.P.D.toPre.P.L.U k →
        gw W.w (f ≫ prOf hD) z j i * gw hD.w f z i k = gw pd.w (f ≫ W'.φ) z j i' * gw W'.w f z i' k

variable {a : ArcIn D l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

abbrev Trunc (A : Type) [CommRing A] (n : ℕ) : Type :=
  PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1)

def LieId (W : Wit Y a χ) (ν : EpsPt a.D₀) (v : epsR (PowerSeries A) ⟶ W.t.G) : Prop :=
  IsTanGt ν ∧ ∀ n : ℕ, ∃ vn : Sp (DualNumber (Trunc A n)) ⟶
      (Out.thickObj (PowerSeries A) (Ideal.span {PowerSeries.X}) n W.t.G).left,
    vn ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap (dualMap (Ideal.Quotient.mk _)) ≫ v.left ∧
    vn ≫ (W.P.U.gt n).pG.left ≫ W.φ = spMap (dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))) ≫ ν.b.left ∧
    ∀ x, GenThrough W.w Out.Oinvε (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn)
      (show LB.Gen (LB.LinComb a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR A) ν.b x) Out.Oinvε) from ν.s x)
      (spMap (dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))))

def ThetaId (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) : Prop :=
  ∃ fam : ∀ x, W.P.D.toPre.SecB 1 x, (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    ∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)

variable {S : Type} [CommRing S] [Algebra c.F S]

def PointAlong (Y : Model Xo c β) (χ : Sp (PowerSeries A) ⟶ Y.X) (ρ : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X)
    (yF : Sp S ⟶ Xo.XF c) : Prop :=
  yF ≫ pullback.fst _ _ = x ∧ yF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) ∧ yF ≫ Y.j = spMap ρ ≫ χ

def VecAlong (W : Wit Y a χ) (ρ : PowerSeries A →+* S) (yF : Sp S ⟶ Xo.XF c) (ν : EpsPt a.D₀)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ (v : epsR (PowerSeries A) ⟶ W.t.G) (uF : Sp (DualNumber S) ⟶ Y.oF.t.G.left), LieId W ν v ∧
    uF ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ yF ∧ uF ≫ Y.m0.toSABMap.φ = u ∧
    uF ≫ Y.m.φ = spMap (dualMap ρ) ≫ v.left ≫ W.m.φ

def ThetaAlong (W : Wit Y a χ) (ρ : PowerSeries A →+* S) {x : Sp S ⟶ Xo.X} (yF : Sp S ⟶ Xo.XF c)
    (th : a.D₀.P.L.Sec) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (σ : Out.H0 W.P.U.LG.L 1) (g₁ : Gx x ⟶ Y.oF.t.G.left) (g₂ : Gx x ⟶ W.t.G.left)
    (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ))
    (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)),
    ThetaId W th σ ∧
    g₁ ≫ Y.m0.toSABMap.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
    g₁ ≫ Y.oF.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ yF ∧
    g₂ ≫ W.m.φ = g₁ ≫ Y.m.φ ∧ g₂ ≫ W.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap ρ ∧
    IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧
    IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧
    ∀ (j : Y.t.PP.L.ι) (k : W.P.U.LG.L.ι) (k₁ : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (V : (Gx x).Opens)
      (h₀ : V ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k₁))
      (h₁ : V ≤ g₁ ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k₁))
      (h₂ : V ≤ g₂ ⁻¹ᵁ (LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k))
      (h₃ : V ≤ g₂ ⁻¹ᵁ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k))
      (h₄ : V ≤ (PPx x).U (fun _ => j₀)),
      (g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀)) =
        (g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val * (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val *
          (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))

def IsArcFrPt (W : Wit Y a χ) (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) (th : a.D₀.P.L.Sec)
    (ρ : PowerSeries A →+* S) (y : FrPt Xo c S) : Prop :=
  ∃ yF : Sp S ⟶ Xo.XF c, PointAlong Y χ ρ y.x yF ∧ (∀ τ i, VecAlong W ρ yF (ν τ i) (y.u τ i)) ∧
    ThetaAlong W ρ yF th y.s

def IsArcFrPtIn (W : Wit Y a χ) (ν : ∀ τ : E →+* ℂ, Fin (D.mult τ) → EpsPt a.D₀) (th : a.D₀.P.L.Sec)
    (ρ : PowerSeries A →+* S) (ξ : ∀ τ : E →+* ℂ, Fin (D.mult τ) → Fin (D.mult τ) → S) (y : FrPt Xo c S) : Prop :=
  ∃ yF : Sp S ⟶ Xo.XF c, PointAlong Y χ ρ y.x yF ∧
    (∃ u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      (∀ τ k, VecAlong W ρ yF (ν τ k) (u τ k)) ∧ ∀ τ i, IsCombAt y.x (u τ) (ξ τ i) (y.u τ i)) ∧
    ThetaAlong W ρ yF th y.s

end Inputs

example {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A} (ν : Fin 0 → EpsPt D₀) (r : Fin 0 → A) (ω : EpsPt D₀) :
    IsCombGt ν r ω ↔ ω.IsZero :=
  ⟨fun ⟨_, _, _, h₀, _, h⟩ => h ▸ h₀, fun h => ⟨Fin.elim0, fun _ => ω, fun i => i.elim0, h, fun i => i.elim0, rfl⟩⟩

example {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A} (th : D₀.P.L.Sec) : IsMulSec 1 th th := fun j => by
  simp [constFn]

end GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaWeightHeightConstants
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

open Formalism.BasicNotions NumberField

def Lift (R : Ranks) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

def pSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).1

def qSig {R : Ranks} (j : Lift R) : ℕ := (R.sigW j.1).2

theorem pSig_pos {R : Ranks} (j : Lift R) : 0 < pSig j := by
  have := R.m_add_three_le_k; have := j.2.1
  simp only [pSig, Ranks.sigW]; omega

theorem pSig_add_qSig {R : Ranks} (j : Lift R) : pSig j + qSig j = R.r := by
  have := R.m_add_three_le_k; have := j.2.1; have := j.2.2
  simp only [pSig, qSig, Ranks.sigW, Ranks.r]; omega

def IsTotIsotropic {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (U : Submodule E S.V) : Prop := ∀ x ∈ U, ∀ y ∈ U, S.hD x y = 0

def isotropicDims {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Set ℕ :=
  {n | ∃ U : Submodule E S.V, IsTotIsotropic S U ∧ Module.finrank E U = n}

def wittIndexOf {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : ℕ :=
  sSup (isotropicDims S)

theorem wittIndexOf_isGreatest {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsGreatest (isotropicDims S) (wittIndexOf S) := by
  have hb : BddAbove (isotropicDims S) := by
    refine ⟨Module.finrank E S.V, ?_⟩
    rintro n ⟨U, -, rfl⟩
    exact Submodule.finrank_le U
  have hn : (isotropicDims S).Nonempty := by
    refine ⟨_, ⊥, ?_, rfl⟩
    intro x _ y hy
    rw [(Submodule.mem_bot E).1 hy]
    simp [HSpace.hD]
  exact ⟨Nat.sSup_mem hn hb, fun n h => le_csSup hb h⟩

def wittIndex (D : D7) (j : Lift D.R) : ℕ :=
  letI := D.host.cmStar; wittIndexOf (D.sp.W j.1)

def rho {R : Ranks} (j : Lift R) : ℕ := R.m - j.1

theorem rho_eq_qSig {R : Ranks} (j : Lift R) : rho j = qSig j := rfl

def WittIndexEq : Prop := ∀ (D : D7) (j : Lift D.R), wittIndex D j = rho j

def dPrime {R : Ranks} (j : Lift R) : ℕ := 2 * R.f * rho j

theorem dPrime_le {R : Ranks} (j : Lift R) : dPrime j ≤ 2 * R.f * R.m :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

def dimBase {R : Ranks} (j : Lift R) : ℕ := R.f * pSig j * qSig j

def dimFlag {R : Ranks} (j : Lift R) : ℕ :=
  dimBase j + R.f * (pSig j * (pSig j - 1) / 2 + qSig j * (qSig j - 1) / 2)

def DimFlagEq : Prop := ∀ (R : Ranks) (j : Lift R), dimFlag j = R.f * R.r.choose 2

def RR (D : D7) : ℝ := D.host.rdE ^ 7

def PP {D : D7} (L : SizeData₂ D) (C e : ℝ) : ℝ := C * ((D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L) ^ e

theorem PP_eq_params {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    PP L T.CP T.eP = T.PP := T.PP_eq.symm

def lrd (D : D7) : ℝ := Real.log D.host.rdE

def lc (D : D7) : ℝ := Real.log (Ideal.absNorm D.host.ccK : ℝ)

def logG (D : D7) : ℝ := Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)

def PU (D : D7) (n : ℕ) : ℝ :=
  (D.R.f : ℝ) * n * (2 * lrd D + 2 * Real.log ((D.R.f : ℝ) * n) + 3)

def primePairSetFirst (D : D7) : ℝ := 2 * PU D D.R.r + Real.log (2 * (D.R.m : ℝ)) + lc D

def PPcnt (D : D7) : ℝ := logG D + 2 * lrd D + primePairSetFirst D + 1

def FirstNormConstantMax (D : D7) : ℝ := 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2

def Pdeg {D : D7} (L : SizeData₂ D) : ℝ := (1 + |L.logOm|) / 2

def heightConstantExplicitFormula {D : D7} (L : SizeData₂ D) : ℝ :=
  3 * lrd D + 4 * Real.pi * (FirstNormConstantMax D * (PPcnt D + Real.log (4 * FirstNormConstantMax D)) + 4) + primePairSetFirst D +
    2 * Real.log (2 * (D.R.f : ℝ) * (D.R.r : ℝ)) + 1 + Pdeg L

def heightConstantMaxForm {D : D7} (L : SizeData₂ D) (C₄ : ℝ) : ℝ := max (heightConstantExplicitFormula L) (Pdeg L + C₄ * zBase L)

def heightConstantAffineSum {D : D7} (L : SizeData₂ D) (C₄ : ℝ) : ℝ := heightConstantExplicitFormula L + (Pdeg L + C₄ * zBase L)

def PolynomialFractionProfile (D : D7) (x : ℝ) : ℝ := 3 * x + 3 * lrd D + 3

def degreeThreePolynomialMajorant {D : D7} (L : SizeData₂ D) (C : ℝ) (e : ℕ) : ℝ :=
  C * ((D.R.f : ℝ) * (D.R.r : ℝ) + Real.log L.sc.b + logdE D + |L.logOm|) ^ e

theorem log_b {D : D7} (L : SizeData₂ D) : Real.log L.sc.b = L.sc.L := Real.log_exp _

def SizeRows {D : D7} (L : SizeData₂ D) : Prop :=
  D.R.m ^ 2 ≤ D.R.r ∧ (∀ i, Real.log (D.host.g i : ℝ) ≤ 9 * L.sc.L + 1) ∧ lc D ≤ L.sc.L

def HeightConstantLePolynomial : Prop := ∀ C₄ : ℝ, 0 ≤ C₄ → ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (L : SizeData₂ D), SizeRows L →
  heightConstantMaxForm L C₄ ≤ heightConstantAffineSum L C₄ ∧ heightConstantAffineSum L C₄ ≤ degreeThreePolynomialMajorant L C 3

def HeightConstantDegreeThree : Prop := ∀ C₄ c : ℝ, 0 ≤ C₄ → ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (L : SizeData₂ D),
  SizeRows L → lrd D ≤ L.sc.L → Real.log (D.R.f : ℝ) ≤ L.sc.L → Real.log (D.R.r : ℝ) ≤ L.sc.L →
  |L.logOm| ≤ c * zBase L → heightConstantAffineSum L C₄ ≤ PP L C 3

@[ext] structure ThetaWeight (D : D7) (j : Lift D.R) where
  plus : D.what₂.Tau → Fin (pSig j) → ℤ
  minus : D.what₂.Tau → Fin (qSig j) → ℤ
  plus_anti : ∀ τ, Antitone (plus τ)
  minus_anti : ∀ τ, Antitone (minus τ)
  n : ℕ

namespace ThetaWeight

variable {D : D7} {j : Lift D.R}

def add (G G' : ThetaWeight D j) : ThetaWeight D j where
  plus := G.plus + G'.plus
  minus := G.minus + G'.minus
  plus_anti τ := (G.plus_anti τ).add (G'.plus_anti τ)
  minus_anti τ := (G.minus_anti τ).add (G'.minus_anti τ)
  n := G.n + G'.n

def nsmul (N : ℕ) (G : ThetaWeight D j) : ThetaWeight D j where
  plus τ i := N * G.plus τ i
  minus τ i := N * G.minus τ i
  plus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.plus_anti τ h) (by positivity)
  minus_anti τ _ _ h := mul_le_mul_of_nonneg_left (G.minus_anti τ h) (by positivity)
  n := N * G.n

def DF (G : ThetaWeight D j) : ℤ := ∑ τ, ((∑ i, G.plus τ i) + ∑ i, G.minus τ i)

def size (G : ThetaWeight D j) : ℤ :=
  G.DF + ((D.R.f * max (rho j) 1 * D.R.r * G.n : ℕ) : ℤ) + 1

def plusLast (G : ThetaWeight D j) (τ : D.what₂.Tau) : ℤ :=
  G.plus τ ⟨pSig j - 1, Nat.sub_lt (pSig_pos j) one_pos⟩

def Dominant (G : ThetaWeight D j) : Prop := ∀ τ, (∀ i, 0 ≤ G.plus τ i) ∧ ∀ i, 0 ≤ G.minus τ i

def PlusLastPos (G : ThetaWeight D j) : Prop := ∀ τ, 1 ≤ G.plusLast τ

def PlusLastPosAtOne (G : ThetaWeight D j) : Prop := ∃ τ, 1 ≤ G.plusLast τ

theorem size_add (G G' : ThetaWeight D j) : (G.add G').size = G.size + G'.size - 1 := by
  simp only [size, DF, add, Pi.add_apply, Finset.sum_add_distrib]
  push_cast; ring

theorem size_nsmul_le (N : ℕ) (hN : 1 ≤ N) (G : ThetaWeight D j) :
    (G.nsmul N).size ≤ N * G.size := by
  have h : (G.nsmul N).DF = N * G.DF := by
    simp only [DF, nsmul, Finset.mul_sum, mul_add]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hn : (G.nsmul N).n = N * G.n := rfl
  unfold size
  rw [h, hn]; push_cast; nlinarith

theorem one_le_size {G : ThetaWeight D j} (h : G.Dominant) : 1 ≤ G.size := by
  have : 0 ≤ G.DF := Finset.sum_nonneg fun τ _ =>
    add_nonneg (Finset.sum_nonneg fun i _ => (h τ).1 i) (Finset.sum_nonneg fun i _ => (h τ).2 i)
  unfold size; omega

end ThetaWeight

def EvenThetaWeight (D : D7) (j : Lift D.R) : Type := {G : ThetaWeight D j // Even G.n}

def DomEvenThetaWeight (D : D7) (j : Lift D.R) : Type :=
  {G : ThetaWeight D j // G.Dominant ∧ Even G.n}

def SizeLower : Prop := ∀ (D : D7) (j : Lift D.R) (G : ThetaWeight D j),
  G.DF + ((D.R.f * D.R.r * G.n : ℕ) : ℤ) ≤ G.size ∧ G.DF + ((D.R.f * rho j * G.n : ℕ) : ℤ) ≤ G.size

def staircase (D : D7) (j : Lift D.R) : ThetaWeight D j where
  plus _ i := (pSig j : ℤ) - i.1
  minus _ i := (qSig j : ℤ) - i.1
  plus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  minus_anti _ a b h := by have : a.1 ≤ b.1 := h; simp only; omega
  n := 2

example (D : D7) (j : Lift D.R) :
    (staircase D j).Dominant ∧ (staircase D j).PlusLastPos ∧ Even (staircase D j).n := by
  refine ⟨fun τ => ⟨fun i => ?_, fun i => ?_⟩, fun τ => ?_, by simp [staircase]⟩
  · have := i.2; simp only [staircase]; omega
  · have := i.2; simp only [staircase]; omega
  · have := pSig_pos j; simp only [ThetaWeight.plusLast, staircase]; omega

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightHeightConstants

end
end

