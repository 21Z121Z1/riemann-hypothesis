import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoveringAbelianLocusSmooth
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section OneModel

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsChartAt (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) :
    Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    ξ (IsLocalRing.closedPoint R) = x ∧ (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)

def CoveredByCharts (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ x : Y.X, ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i))
    (_ : ∀ i, IsLocalRing (R i)) (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsChartAt Y x (R i) (ξ i)) ∧
    ∀ (V C : Type) [CommRing V] [IsLocalRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
      [IsAlgClosed C] [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (f : R i →+* V), IsLocalHom f ∧ spMap f ≫ ξ i = y

def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)

theorem IsChartAt.unif {Y : Model Xo c β} (hY : Y.N3) {x : Y.X} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsChartAt Y x R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, h1, h2, h3, -, h5, t, m, S, hS⟩ := h
  exact ⟨t, m, hY R h1 h2 h3 ξ t m h5 ⟨S, hS⟩⟩

end OneModel

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → CoveredByCharts (Y i) p

def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)

def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma

theorem goodPrime_iff (l : Level H) {p : ℕ} (hp : p.Prime) :
    GoodPrime l p ↔ ¬ (p : ℤ) ∣ discr E ∧ ¬ p ∣ l.M' := by
  unfold GoodPrime
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]

end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoveringAndSmoothness
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsUnifBase (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) : Prop :=
  CharZero R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
    (ξ ⁻¹' abLocus Y.t.G).Nonempty ∧
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ) (S : SplitExt (Sp (IsLocalRing.ResidueField R))),
      S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)

def CovAt (Y : Model Xo c β) (p : ℕ) (x : Y.X) : Prop :=
  ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsLocalRing (R i))
    (ξ : ∀ i, Sp (R i) ⟶ Y.X),
    (∀ i, IsUnifBase Y (R i) (ξ i) ∧ ξ i (IsLocalRing.closedPoint (R i)) = x) ∧
    ∀ (C V : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [CommRing V] [IsLocalRing V] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 →
      ∀ y : Sp V ⟶ Y.X, y (IsLocalRing.closedPoint V) = x →
        Set.range (spMap (algebraMap V C) ≫ y) ⊆ abLocus Y.t.G →
        ∃ (i : Fin n) (φ : R i →+* V), IsLocalHom φ ∧ spMap φ ≫ ξ i = y

def AbLocusSmooth (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s)

theorem IsUnifBase.out {Y : Model Xo c β} (h3 : Y.N3) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsUnifBase Y R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, hn, hi, hc, hU, t, m, S, hS⟩ := h
  exact ⟨t, m, h3 R hn hi hc ξ t m hU ⟨S, hS⟩⟩

theorem AbLocusSmooth.smooth {Y : Model Xo c β} (h : AbLocusSmooth Y) (U : Y.X.Opens)
    (hU : (U : Set Y.X) = abLocus Y.t.G) : SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s) := by
  obtain ⟨U', hU', hs⟩ := h
  obtain rfl : U = U' := SetLike.coe_injective (hU.trans hU'.symm)
  exact hs

end One

def GoodPrime (l : Level H) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) ∧ ¬ p ∣ l.M'

def CoveringLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ (i : Idx H p) (x : (Y i).X), CovAt (Y i) p x

def SmoothnessLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, GoodPrime i.l p → AbLocusSmooth (Y i)

def CoveringAndSmoothness : Prop := CoveringLemma ∧ SmoothnessLemma

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.DVRSplitting
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def IsFinUnram (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] : Prop :=
  Function.Injective (algebraMap V W) ∧ Module.Finite V W ∧ Algebra.FormallyUnramified V W

theorem IsFinUnram.map_maximalIdeal {V W : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] (h : IsFinUnram V W) :
    IsLocalHom (algebraMap V W) ∧ (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
  obtain ⟨hi, hf, hu⟩ := h
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).mpr hi
  have : IsLocalHom (algebraMap V W) := inferInstance
  exact ⟨this, Algebra.FormallyUnramified.map_maximalIdeal⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def SplitsOver {Y : Model Xo c β} (P : ValPt Y) (W : Type) [CommRing W] [IsLocalRing W] [Algebra P.V W] : Prop :=
  ∃ S : SplitExt (Sp (ResidueField W)),
    S.IsGt ((Over.pullback (spMap ((residue W).comp (algebraMap P.V W)))).obj P.G.G)

def UnifOver {Y : Model Xo c β} (P : ValPt Y) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra P.V W] :
    Prop :=
  (∃ t : SAB H (Sp W), Nonempty (SABMap t P.G (spMap (algebraMap P.V W)))) ∧
    ∀ (t : SAB H (Sp W)) (_ : SABMap t P.G (spMap (algebraMap P.V W))),
      UniformisationConclusion t ((spMap (algebraMap P.V W) ≫ P.yt) ⁻¹' abLocus Y.t.G)

def SplitAtPts (Y : Model Xo c β) : Prop :=
  ∀ P : ValPt Y, ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra P.V W),
    IsFinUnram P.V W ∧ SplitsOver P W

def UnifAtPts (Y : Model Xo c β) : Prop :=
  ∀ (P : ValPt Y) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra P.V W],
    IsFinUnram P.V W → SplitsOver P W → UnifOver P W

def DvrOut (Y : Model Xo c β) : Prop :=
  ∀ P : ValPt Y, ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra P.V W),
    IsFinUnram P.V W ∧ SplitsOver P W ∧ UnifOver P W

def DvrIn (Y : Model Xo c β) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    ∀ (b : O →+* V), IsLocalHom b → ∀ (ϖ : V), Irreducible ϖ → ∀ a : ArcIn D l β V b,
      ∃ y : Sp V ⟶ Y.X, y ≫ Y.s = spMap b ∧ Set.range (Out.jK V ≫ y) ⊆ Set.range Y.j ∧
        Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ y

def DvrData : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    (Y.SplitFibres → SplitAtPts Y) ∧ (Y.N3 → UnifAtPts Y) ∧ (Y.N4 → DvrIn Y)

end GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

def GtTors (k : ℕ) {T : Over (Sp R)} (g : Out.GtPt D T) : Prop :=
  ∃ h : Out.GtPt D T, Out.GtPt.IsNsmul k g h ∧ h.IsZero

def GtActT {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) {T : Over (Sp R)}
    (g g' : Out.GtPt D T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Out.rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (Out.DegPre.cT D T χ) g.b).left)) (g'.s χ)

def unitGen {X Y : Scheme.{0}} (L : LB X) (z : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top z

def TorusVal {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (z : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L z)

end Points

section Formal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEq (U : Out.UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : Out.GtPt D.toPre T) : Prop :=
  ∀ e : ℕ,
    (Out.fstG I e T).left ≫ g.b.left =
        ((Over.pullback (Out.thick R I e)).map x).left ≫ (U.gt e).pG.left ∧
      ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
        (LB.pullGen D.toPre.P.L _ _ (g.s χ) (Out.fstG I e T).left)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (Out.thick R I e)).map x).left)

structure IsFinitePart (U : Out.UnifPre I D A G) (k : ℕ) (N : Over (Sp R)) (g₀ : Out.GtPt D.toPre N)
    (x₀ : N ⟶ G) : Prop where
  finite : IsFinite N.hom
  flat : Flat N.hom
  gt_tors : GtTors k g₀
  gt_univ : ∀ (T : Over (Sp R)) (g : Out.GtPt D.toPre T), GtTors k g →
    ∃! h : T ⟶ N, Out.GtPt.IsPull h.left g₀ g
  g_tors : x₀ ^ k = 1
  g_mono : Mono x₀
  g_univ : ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ G, x ^ k = 1 → ∃ h : T ⟶ N, h ≫ x₀ = x
  formal : FormalEq U x₀ g₀

end Formal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Flat

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

def TorsFiniteFlat (G : Over (Sp R)) [GrpObj G] (W : (Sp R).Opens) (k : ℕ) : Prop :=
  ∃ (N : Over W.toScheme) (n : Out.overW W N ⟶ G), IsFinite N.hom ∧ Flat N.hom ∧ n ^ k = 1 ∧
    ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ G), x ^ k = 1 →
      ∃! h : T ⟶ N, (Over.map W.ι).map h ≫ n = x

structure IsFlatIso (P : PELUnif I t) {W : (Sp R).Opens} (ψW : Out.PsiOn P.D.toPre W) (k : ℕ)
    (f : ∀ T : Over W.toScheme, Out.QkPtW P.D.toPre W ψW k T → (Out.overW W T ⟶ t.G)) : Prop where
  tors : ∀ T p, f T p ^ k = 1
  natural : ∀ (T T' : Over W.toScheme) (h : T' ⟶ T) p p', Out.QkPtW.IsPull h p p' →
    f T' p' = (Over.map W.ι).map h ≫ f T p
  add : ∀ T p p' p'', Out.QkPtW.IsAdd p p' p'' → f T p'' = f T p * f T p'
  lin : letI := H.starRing
    ∀ (a : 𝓞 E) T (p p' : Out.QkPtW P.D.toPre W ψW k T), p'.y = a • p.y → GtActT P.oD a p.g p'.g →
      f T p' = f T p ≫ t.act.act a
  inj : ∀ T : Over W.toScheme, Nonempty T.left → ∀ p p', f T p = f T p' ↔ Out.QkPtW.Equiv p p'
  surj : ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ t.G), x ^ k = 1 → ∀ s : T.left,
    ∃ V : T.left.Opens, s ∈ V ∧ ∃ p, f (Out.overRes V) p = (Over.map W.ι).map (Out.overResι V) ≫ x
  generic : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over W.toScheme) (x : Sp F ⟶ T.left),
    x ≫ (Out.overW W T).hom = Out.jFK (R := R) F ≫ Out.jK R →
    ∀ p (q : Out.QkPt P.D.toPre F k), Out.QkPtW.IsPullF F x p q →
      ∀ a : Out.TFK (R := R) F ⟶ P.A.A,
        a.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) = x ≫ (f T p).left → P.ToA F k q a
  onGt : ∃ (N : Over (Sp R)) (g₀ : Out.GtPt P.D.toPre N) (x₀ : N ⟶ t.G),
    IsFinitePart P.U.toUnifPre k N g₀ x₀ ∧
    ∀ (T : Over W.toScheme) (h : Out.overW W T ⟶ N) (p : Out.QkPtW P.D.toPre W ψW k T), p.y = 0 →
      Out.GtPt.IsPull h.left g₀ p.g → f T p = h ≫ x₀
  onY : ∀ (T : Over W.toScheme) (p p' : Out.QkPtW P.D.toPre W ψW k T) (z : Γ((Out.overW W T).left, ⊤)ˣ),
    p.y = 0 → TorusVal p.g p'.y z → Out.WeilIs t.G t.PP.L (k : ℤ) (f T p) (f T p') z

def FlatTorsion (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∃ ψW : Out.PsiOn P.D.toPre W,
    (∀ y, ∃ g : Out.GtPt P.D.toPre (Out.overW W (𝟙_ (Over W.toScheme))), Out.GtPt.IsIotaW ψW y g) ∧
    ∀ k : ℕ, 1 ≤ k → TorsFiniteFlat t.G W k ∧ ∃ f, IsFlatIso P ψW k f

def Concl (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  (∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R))) ∧ P.TorsionIso ∧ FlatTorsion P W

def IsPowOf {t' : SAB H (Sp R)} (P' : PELUnif I t') (P : PELUnif I t) (j : ℕ) : Prop :=
  letI := H.starRing
  ∃ (pG : Out.IsPowGrp t'.G t.G j) (pD : Out.IsPowDeg P'.D.toPre P.D.toPre j) (pA : Out.IsPowPolAV P'.A P.A j),
    Nonempty (Out.UnifPowOf3 pD pA pG P'.U P.U) ∧
    (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧
    (∀ a i, P'.oA.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧
    (∀ a i, P'.oD.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧
    ∀ (a : 𝓞 E) x i, pD.xe (a • x) i = a • pD.xe x i

def Products (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∀ j : ℕ, ∃ (t' : SAB H (Sp R)) (P' : PELUnif I t'), IsPowOf P' P j ∧ Concl P' W

end Flat

def FullOut {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (U : Set (Sp R)) : Prop :=
  ∃ (W : (Sp R).Opens) (P : PELUnif (IsLocalRing.maximalIdeal R) t),
    (W : Set (Sp R)) = U ∧ Concl P W ∧ Products P W

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ModelFull (Y : Model Xo c β) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      FullOut t (ξ ⁻¹' abLocus Y.t.G)

end GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Data

variable {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R}

structure GtTors (D : Out.DegPre R) (k : ℕ) (T : Over (Sp R)) where

  g : Out.GtPt D T

  tors : ∃ z : Out.GtPt D T, Out.GtPt.IsNsmul k g z ∧ z.IsZero

def GtSmul {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) {T : Over (Sp R)} (a : O)
    (g g' : Out.GtPt D T) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Out.rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (Out.DegPre.cT D T χ) g.b).left)) (g'.s χ)

def unitGen {X Y : Scheme.{0}} (L : LB X) (c : Γ(Y, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top c

def TorusValue {T : Over (Sp R)} (g : Out.GtPt D T) (χ : D.X) (c : Γ(T.left, ⊤)ˣ) : Prop :=
  g.b = Out.DegPre.zeroT D T ∧ LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (unitGen D.P.L c)

def CoordOf {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gc : Out.GtCoord I D e G)
    {T : Over (Sp (R ⧸ I ^ (e + 1)))} (x : T ⟶ Out.thickObj R I e G)
    (g : Out.GtPt D ((Over.map (Out.thick R I e)).obj T)) : Prop :=
  g.b = (Over.map (Out.thick R I e)).map x ≫ gc.pG ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.pullGen D.P.L _ _ (gc.t χ) x.left)

def torsScheme {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ) : Over S :=
  pullback ((𝟙 G : G ⟶ G) ^ k) η[G]

abbrev resι {S : Scheme.{0}} {T : Over S} (V : T.left.Opens) : Out.overRes V ⟶ T := Out.overResι V

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

structure FinitePart (P : PELUnif I t) (k : ℕ) where

  h : ∀ T : Over (Sp R), GtTors P.D.toPre k T → (T ⟶ t.G)
  tors : ∀ T g, h T g ^ k = 1
  pull : ∀ (T T' : Over (Sp R)) (φ : T' ⟶ T) (g : GtTors P.D.toPre k T) (g' : GtTors P.D.toPre k T'),
    Out.GtPt.IsPull φ.left g.g g'.g → h T' g' = φ ≫ h T g
  add : ∀ T (g g' g'' : GtTors P.D.toPre k T), Out.GtPt.IsAdd g.g g'.g g''.g → h T g'' = h T g * h T g'
  lin : letI := H.starRing
    ∀ T (a : 𝓞 E) (g g' : GtTors P.D.toPre k T), GtSmul P.oD a g.g g'.g → h T g' = h T g ≫ t.act.act a
  inj : ∀ T, Function.Injective (h T)
  onto : ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ t.G, x ^ k = 1 → ∃ g, h T g = x
  red : ∀ (e : ℕ) (T : Over (Sp (R ⧸ I ^ (e + 1)))) (x : T ⟶ Out.thickObj R I e t.G)
    (g : GtTors P.D.toPre k ((Over.map (Out.thick R I e)).obj T)), CoordOf (P.U.gt e) x g.g →
    h _ g = (Over.map (Out.thick R I e)).map x ≫ Out.fstG I e t.G

structure FlatIso (P : PELUnif I t) {W : (Sp R).Opens} (ψW : Out.PsiOn P.D.toPre W) (k : ℕ) (φ : FinitePart P k) where
  finite : IsFinite ((torsScheme t.G k).hom ∣_ W)
  flat : Flat ((torsScheme t.G k).hom ∣_ W)

  f : ∀ T : Over W.toScheme, Out.QkPtW P.D.toPre W ψW k T → (Out.overW W T ⟶ t.G)
  tors : ∀ T p, f T p ^ k = 1
  pull : ∀ (T T' : Over W.toScheme) (m : T' ⟶ T) (p : Out.QkPtW P.D.toPre W ψW k T)
    (p' : Out.QkPtW P.D.toPre W ψW k T'), Out.QkPtW.IsPull m p p' → f T' p' = (Over.map W.ι).map m ≫ f T p
  add : ∀ T (p p' p'' : Out.QkPtW P.D.toPre W ψW k T), Out.QkPtW.IsAdd p p' p'' → f T p'' = f T p * f T p'
  lin : letI := H.starRing
    ∀ T (a : 𝓞 E) (p p' : Out.QkPtW P.D.toPre W ψW k T), p'.y = a • p.y → GtSmul P.oD a p.g p'.g →
      f T p' = f T p ≫ t.act.act a
  inj : ∀ T : Over W.toScheme, Nonempty T.left → ∀ p p' : Out.QkPtW P.D.toPre W ψW k T,
    f T p = f T p' ↔ Out.QkPtW.Equiv p p'
  onto : ∀ (T : Over W.toScheme) (x : Out.overW W T ⟶ t.G), x ^ k = 1 → ∀ s : T.left,
    ∃ V : T.left.Opens, s ∈ V ∧ ∃ p : Out.QkPtW P.D.toPre W ψW k (Out.overRes V),
      f _ p = (Over.map W.ι).map (resι V) ≫ x
  generic : ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over W.toScheme) (s : Sp F ⟶ T.left)
    (p : Out.QkPtW P.D.toPre W ψW k T) (p' : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := R) F ⟶ P.A.A),
    Out.QkPtW.IsPullF F s p p' →
    x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) = s ≫ (f T p).left → P.ToA F k p' x
  onGt : ∀ (T : Over W.toScheme) (p : Out.QkPtW P.D.toPre W ψW k T) (g : GtTors P.D.toPre k (Out.overW W T)),
    p.y = 0 → g.g = p.g → f T p = φ.h _ g
  onY : ∀ (T : Over W.toScheme) (p p' : Out.QkPtW P.D.toPre W ψW k T) (c : Γ((Out.overW W T).left, ⊤)ˣ),
    p.y = 0 → TorusValue p.g p'.y c → Out.WeilIs t.G t.PP.L k (f T p) (f T p') c

def FlatForm (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  letI := H.starRing
  ∃ ψW : Out.PsiOn P.D.toPre W,
    (∃ io : P.D.toPre.X → Out.GtPt P.D.toPre (Out.overW W (Over.mk (𝟙 W.toScheme))),
      (∀ y, Out.GtPt.IsIotaW ψW y (io y)) ∧ (∀ y y', Out.GtPt.IsAdd (io y) (io y') (io (y + y'))) ∧
      ∀ (a : 𝓞 E) y, GtSmul P.oD a (io y) (io (a • y))) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ φ : FinitePart P k, Nonempty (FlatIso P ψW k φ)

structure IsPowTriple {S : Scheme.{0}} (t' t : SAB H S) (j : ℕ) where

  pw : Out.IsPowGrp t'.G t.G j
  act : ∀ a i, t'.act.act a ≫ pw.pr i = pw.pr i ≫ t.act.act a

  w : LB.Iso t'.PP.L (Out.boxLB t.PP.L pw.pr)
  w_gen : w.IsGen
  w_rig : ∃ b : LB.Gen (LB.LinComb t.PP.L (K := Fin j) (fun i => eSec t'.G ≫ (pw.pr i).left) (fun _ => 1)),
    Out.GeneratorPullback.MapsAt t.PP.L t'.PP.L (fun i => (pw.pr i).left) w (eSec t'.G) 1 t'.PP.rig b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ b
      (Out.GeneratorPullback.finProdGen t.PP.L (J := Fin j) (fun _ _ => eSec t.G) (fun _ _ => 1) (fun _ => t.PP.rig))

def IsPowUnif {t' : SAB H (Sp R)} {j : ℕ} (pt : IsPowTriple t' t j) (P' : PELUnif I t') (P : PELUnif I t) : Prop :=
  letI := H.starRing
  ∃ (pD : Out.IsPowDeg P'.D.toPre P.D.toPre j) (pA : Out.IsPowPolAV P'.A P.A j),
    Nonempty (Out.UnifPowOf3 pD pA pt.pw P'.U P.U) ∧
    (∀ (a : 𝓞 E) x i, pD.xe (a • x) i = a • pD.xe x i) ∧
    (∀ a i, P'.oD.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧
    ∀ a i, P'.oA.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a

def Conclusion (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  (∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R))) ∧ P.TorsionIso ∧ FlatForm P W

def Products (P : PELUnif I t) (W : (Sp R).Opens) : Prop :=
  ∀ j : ℕ, (∃ t' : SAB H (Sp R), Nonempty (IsPowTriple t' t j)) ∧
    ∀ (t' : SAB H (Sp R)) (pt : IsPowTriple t' t j), ∃ P' : PELUnif I t', IsPowUnif pt P' P ∧ Conclusion P' W

end Unif

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def TorsionAndProducts (Y : Model Xo c β) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      ∃ W : (Sp R).Opens, (W : Set (Sp R)) = ξ ⁻¹' abLocus Y.t.G ∧
        ∃ P : PELUnif (IsLocalRing.maximalIdeal R) t, Conclusion P W ∧ Products P W

example (Y : Model Xo c β) (h : TorsionAndProducts Y) : Y.N3 := by
  intro R _ _ _ _ h1 h2 h3 ξ t m hne hs
  obtain ⟨W, hW, P, hP, -⟩ := h R h1 h2 h3 ξ t m hne hs
  exact ⟨P, hW ▸ hP.1, hP.2.1⟩

end GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism
end
end

