import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFrames
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsEigenLatticeBasis (Dw : Datum H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V))
    (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) : Prop :=
  (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
    ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w

def IsEigenBasisAt (Xo : Moduli Dw l) (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X)
    (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) : Prop :=
  (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
    ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x u a w

def IsGenericFibre {Xo : Moduli Dw l} {T : CDVR} {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X}
    (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (w : epsOver T.V T.V ⟶ G.G) (v : Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m₁.φ = v ∧
    u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ w.left

def IntegralUpToTriangular (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (yt : Sp T.V ⟶ Y.X) (yF : Sp T.Fr ⟶ Xo.XF c),
      yF ≫ pullback.snd _ _ = spMap io → spMap (algebraMap T.V T.Fr) ≫ yt = yF ≫ Y.j →
      letI := io.toAlgebra
      ∀ y : FrPt Xo c T.Fr, y.x = yF ≫ pullback.fst _ _ →
        ∃ (y₀ : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀.1 y

def EigenLatticesFree (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = sOf c T.Fr →
    ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ : E →+* ℂ),
      (∃ ub, IsEigenLatticeBasis Dw c T io G τ ub) ∧
      ∀ u, IsEigenBasisAt Xo c x τ u →
        ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
          (v : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
          IsEigenLatticeBasis Dw c T io G τ ub ∧ (∀ i, IsGenericFibre m₁ m₂ (ub i) (v i)) ∧
          ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x v cf (u i)

def FieldPointsFromTest (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

def IntegralFramesAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  IntegralUpToTriangular Xo c ∧ EigenLatticesFree Xo c ∧ FieldPointsFromTest Xo c

def IntegralFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), IntegralFramesAt Xo c

theorem isEigenBasisAt_frPt {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) : IsEigenBasisAt Xo c y.x τ (y.u τ) :=
  ⟨y.tan τ, y.eig τ, y.basis τ⟩

theorem exists_basis_of_integral {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∀ τ, ∃ ub, IsEigenLatticeBasis Dw c T io G τ ub ∧
        ∀ i, IsGenericFibre m₁ m₂ (ub i) (y.u τ i) := by
  obtain ⟨G, t', m₁, m₂, ⟨ub, h1, h2, h3, h4⟩, -⟩ := h
  exact ⟨G, t', m₁, m₂, fun τ => ⟨ub τ, ⟨h1 τ, h2 τ, h3 τ⟩, h4 τ⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ThetaFramePullback
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaFramePullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Notions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsGenOver {V : Type} [CommRing V] (G : SAB H (Sp V)) (θ : LB.Sec G.PP.L) : Prop :=
  ∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i,
    σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ V a)) * θ.f i

variable {Xo : Moduli Dw l}

def IsGenAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s.f i

def GenMatch {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w₁ : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w₂ : LB.Iso t'.PP.L (G.PP.L.pull m₂.φ))
    (σ : LB.Sec t'.PP.L) (s₁ : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ₂ : LB.Sec (G.PP.L.pull m₂.φ)),
    RigIso m₁ w₁ ∧ RigIso m₂ w₂ ∧ IsoMaps w₁ σ s₁ ∧ IsoMaps w₂ σ θ₂ ∧ PullSec m₂.φ θ θ₂ ∧
    ∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m₁.φ →
      g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s₁.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

variable {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def GenericIn (Y : Model Xo c β) {T : CDVR} (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c)
    (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  xF ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ ξ ∧ xF ≫ pullback.fst _ _ = x

def Tied (Y : Model Xo c β) {T : CDVR} {ξ : Sp T.V ⟶ Y.X} (xF : Sp T.Fr ⟶ Xo.XF c) {x : Sp T.Fr ⟶ Xo.X}
    {G : SAB H (Sp T.V)} (mG : SABMap G Y.t ξ) {t' : SAB H (Sp T.Fr)} (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : Prop :=
  ∃ n : t'.G.left ⟶ Y.oF.t.G.left, n ≫ Y.oF.t.G.hom = t'.G.hom ≫ xF ∧ n ≫ Y.m0.toSABMap.φ = m₁.φ ∧
    n ≫ Y.m.φ = m₂.φ ≫ mG.φ

def IsPushGenOn {X : Scheme.{0}} (G : Over X) (L : LB G.left) (V : X.Opens)
    (θ₀ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop :=
  θ₀ ∈ secOn L (G.hom ⁻¹ᵁ V) ∧
    ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
      s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ₀ i)

def IsPullOf {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (V : S.Opens)
    (θ₀ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ V ⊓ t.PP.L.U i)) (θ : LB.Sec t'.PP.L) : Prop :=
  ∃ (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (θ₁ : LB.Sec (t.PP.L.pull m.φ)), RigIso m w ∧ IsoMaps w θ θ₁ ∧
    ∀ j (h : (t.PP.L.pull m.φ).U j ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ V ⊓ t.PP.L.U (j PUnit.unit))),
      θ₁.f j = (m.φ.appLE _ _ h).hom (θ₀ (j PUnit.unit))

end Notions

def GenericFibre : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (mG : SABMap G Y.t ξ),
      (∃ t' : SAB H (Sp T.Fr), Nonempty (SABMap t' G (spMap (algebraMap T.V T.Fr)))) ∧
      ∀ (t' : SAB H (Sp T.Fr)) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))),
        ∃ m₁ : SABMap t' Xo.univ.t x, Tied Y xF mG m₁ m₂

def ThetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (_ : SABMap G Y.t ξ),
      ∃ θ : LB.Sec G.PP.L, IsGenOver G θ ∧
        ∀ (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
          (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))),
          ∃ s : LB.Sec (PPx x), GenMatch m₁ m₂ θ s ∧ IsGenAt x s ∧
            ∀ s₀ : LB.Sec (PPx x), IsGenAt x s₀ →
              ∃ u : T.Frˣ, ∀ i, s.f i = scal x (u : T.Fr) i * s₀.f i

def PullsBack : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (mG : SABMap G Y.t ξ) (V : Y.X.Opens)
      (θ₀ : ∀ i, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U i)),
      ⊤ ≤ ξ ⁻¹ᵁ V → IsPushGenOn Y.t.G Y.t.PP.L V θ₀ →
      (∃ θ, IsPullOf mG V θ₀ θ) ∧ ∀ θ, IsPullOf mG V θ₀ θ → IsGenOver G θ

def Claim : Prop := ThetaFrame ∧ GenericFibre

section Basic₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

example {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : IsGenAt y.x y.s := y.gen

example (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L),
      IsGenOver G θ ∧ GenMatch m₁ m₂ θ y.s := by
  obtain ⟨G, t', m₁, m₂, -, θ, h₁, h₂⟩ := h
  exact ⟨G, t', m₁, m₂, θ, h₁, h₂⟩

example {X : Scheme.{0}} (G : Over X) (L : LB G.left) (h : PushInvertible G L) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ₀, IsPushGenOn G L V θ₀ := by
  obtain ⟨V, hV, θ, h₁, h₂, -⟩ := h x
  exact ⟨V, hV, θ, h₁, h₂⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaFramePullback
end
end

