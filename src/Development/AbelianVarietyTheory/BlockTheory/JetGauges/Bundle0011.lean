import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalActionLiftPull
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalActionLiftPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS pt ev comp1 addOf FB)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Scalar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def nn (Dw : Datum H) {l : Level H} (c : Coeff l) (α : 𝓞 E) (a : (E →+* ℂ) × ℕ → ℕ) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ (∑ i : Fin (Dw.mult τ), a (τ, i))

example (Dw : Datum H) {l : Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) : nn Dw c 1 a = 1 := by
  simp [nn]

example (Dw : Datum H) {l : Level H} (c : Coeff l) (α β : 𝓞 E) (a : (E →+* ℂ) × ℕ → ℕ) :
    nn Dw c (α * β) a = nn Dw c α a * nn Dw c β a := by
  simp [nn, mul_pow, Finset.prod_mul_distrib]

end Scalar

section Gauge

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

structure IsBalancedGauge (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, FB.toK k (B.ad a) = FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

end Gauge

def prodVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (N : ℤ) {n : ℕ} (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L N (ptO Xo y.x)))
    (P : MvPolynomial (LtN Dw n) S) : S :=
  ∑ m ∈ P.support, P.coeff m * ∏ b, nab y N (F b) (colOf m b)

def GaugeLemma : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l),
  letI := H.starRing
  ∀ (k : Type) [Field k] [CharZero k] [Algebra c.F k] (y : FrPt Xo c k) (C : ChartAt Xo c y)
    (h' : PS k 2 C.d), IsBalancedGauge C.B k h' →
  ∀ (N n : ℕ) (P : MvPolynomial (LtN Dw n) k),
    P ∈ harmK Dw.mult n k ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    (∀ f : PS k n C.d,
      nabValN C.B k h' H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) P =
        nabValN C.B k C.h H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) P) ∧
    ∀ nab : NabV Xo c, IsNab Xo c nab →
      ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L N (ptO Xo y.x))) (f : Fin n → PS k 1 C.d),
        (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP N (F b) (f b)) →
        prodVal nab y (N : ℤ) F P =
          nabValN C.B k h' H.w0 N (∏ b, ev (n := n) ![pt k C.d b] (f b)) (fun ℓ => ℓ.2.2)
            (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) P

section Alpha

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsLiftPull (φ : A ⟶ A) (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (b : T ⟶ A)
    (F : LB.Sec (LPow A L.L (N : ℤ) T)) : Prop :=
  ∃ (β₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(N : ℤ), -1]))
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(N : ℤ), -1]))
    (s₁ : LB.Sec (LPow A L.L (N : ℤ) T)) (U : ThetaGrp A L.L (N : ℤ) T),
    β₀.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ β₀ (eSec A))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig (N : ℤ)) (LB.invGen L.L _ _ L.rig)) ∧
    LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ β₀ (snd T A).left) ∧
    IsTwistPull A L.L (lift (fst T A) (snd T A ≫ φ)) (snd T A ≫ φ) (lift_snd _ _) (N : ℤ) 1 β s s₁ ∧
    SymLift A L.L (N : ℤ) N b U ∧ IsActOf A L.L (N : ℤ) U s₁ F

end Alpha

def AlphaForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l),
  letI := H.starRing
  ∀ nab : NabV Xo c, IsNab Xo c nab →
  ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb ≤ Ideal.span {H.bar α} →
  ∀ (k : Type) [Field k] [CharZero k] [Algebra c.F k] (y : FrPt Xo c k) (n : ℕ) (x : Fin n → Dw.La)
    (b : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)),
    (∀ j, b j ≫ Xo.univ.t.act.act (H.bar α) = 1) →
    (∀ j, b j ≫ Xo.univ.t.act.act α = levPt Xo y.x (x j)) →
  ∀ F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo y.x)),
    (∀ j, IsLiftPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M y.s (b j) (F j)) →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    (∃ w, ThValAt Xo c nab y x P w) ∧
    ∀ w, ThValAt Xo c nab y x P w →
      prodVal nab y (l.M : ℤ) F (MvPolynomial.map (algebraMap c.F k) P) = algebraMap c.F k (nn Dw c α a) * w

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O]

def IsDiagAct {D' D : DegPre R} {n : ℕ} (pD : IsPowDeg D' D n) [Module O D'.X] [Module O D.X]
    (oa' : D'.OAct O) (oa : D.OAct O) : Prop :=
  (∀ (a : O) (x : D'.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧
    ∀ (a : O) (i : Fin n), oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a

def QkKilledBy {D : DegPre R} [Module O D.X] (oa : D.OAct O) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} (a : O) (p : QkPt D F k) : Prop :=
  ∃ (z : D.X) (g' : GtPtF D F), a • p.y = k • z ∧ GtAct oa a p.g g' ∧ GtPtF.IsIota z g'

end Deg

def nabAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (C : IntegralChartA3 Xo c T io y) (F : Type) [Field F] [Algebra T.Fr F] (q : ℕ) {n : ℕ}
    (h : PS F n (chD C.ch)) (P : MvPolynomial (LtN Dw n) c.F) : F :=
  letI := io.toAlgebra
  letI : Algebra ℚ F := ((algebraMap T.Fr F).comp (algebraMap ℚ T.Fr)).toAlgebra
  nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ => ℓ.2.2)
    (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j))
    (MvPolynomial.map ((algebraMap T.Fr F).comp io) P)

def Generators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l),
  letI := H.starRing
  ∀ nab : NabV Xo c, IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), g.Prime → g'.Prime → g ≠ g' → l.M = g * g' →
    π * H.bar π = (g : 𝓞 E) → π' * H.bar π' = (g' : 𝓞 E) →
    l.Mb ≤ Ideal.span {π} → l.Mb ≤ Ideal.span {π'} →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → (g : T.V) ∈ maximalIdeal T.V →
  ∀ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q →
  ∀ n : ℕ, 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oa' : D'.toPre.OAct (𝓞 E)),
    IsDiagAct pD oa' P.oD →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ σ : Fam D'.toPre F g', NuGe D' (sumQ pD.xe Q) F v g' σ 0 →
  ∀ s₁ : Fam D'.toPre F (g' * g), PullAl D' F oa' (H.bar π) g' g σ s₁ →
  ∀ (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g)))) (ζ : F),
    QkKilledBy oa' π p → w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
  ∀ t s₂ : Fam D'.toPre F (g' * g), PhiRel D'.toPre F (g' * g) p w s₁ t → Fam.IsSmul D'.toPre F ζ t s₂ →
  ∀ σ' : U'.toUnifPre.SecGF F (g' * g), U'.toUnifPre.ExpandsG F (g' * g) σ' s₂ →
  ∀ h : PS F n (chD C.ch), IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
  ∀ a : (E →+* ℂ) × ℕ → ℕ,
    ∃ (u : F) (m : ℕ) (cf : Fin m → F) (x : Fin m → Fin n → Dw.La),
      v u = v (algebraMap T.Fr F (io (nn Dw c (H.bar π * H.bar π') a))) ∧ (∀ i, 0 ≤ v (cf i)) ∧
      ∀ Ph ∈ harmA c a n, ∀ f : Fin m → Rul Xo c, (∀ i, IsThRule Xo c nab (x i) Ph (f i)) →
        nabAt C F (g' * g) h Ph = u * ∑ i, cf i * algebraMap T.Fr F (evI y (f i))

def GeneratorsWithAlphaFormAndGauge : Prop := GaugeLemma ∧ AlphaForm ∧ Generators

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalActionLiftPull
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.RigidNormaliserGenerators
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt comp1 addOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

section Ops

variable {S : Scheme.{0}}

def diagEnd {G' G : Over S} [GrpObj G'] [GrpObj G] {n : ℕ} (p : IsPowGrp G' G n) (f : G ⟶ G) : G' ⟶ G' :=
  p.lim.lift (Fan.mk G' fun i => p.pr i ≫ f)

variable (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsRigPull (φ : A ⟶ A) (k N : ℤ) {T : Over S} (s : LB.Sec (LPow A L.L k T)) (s' : LB.Sec (LPow A L.L N T)) :
    Prop :=
  ∃ α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![N, -k]),
    α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α (ptSecT A (1 : T ⟶ A)).left) (rigT A L.L L.rig T (N - k)) ∧
    IsTwistPull A L.L (T ◁ φ) (snd T A ≫ φ) (whiskerLeft_snd _ _) N k α s s'

def HasFinOrder {k : ℤ} {T : Over S} (ga : ThetaGrp A L.L k T) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ga.pt ^ M = 1 ∧
    LB.Gen.Corr L.L _ _ _ _ (ReciprocityTheory.ChartRestriction.G.Out.powGen A L.L k ga M) (LB.oneGen L.L)

end Ops

section Two

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R)))
  (F : Type) [Field F] [Algebra (FractionRing R) F]

def cmp : (UnifPre.GF (R := R) (G := G) F).left ⟶ (TF (R := R) F ⊗ G).left :=
  pullback.lift (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (UnifPre.gFK (R := R) (G := G) F) (by
    have h : (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ jFK (R := R) F =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.snd G.hom (jK R) :=
      pullback.condition
    show _ ≫ jFK (R := R) F ≫ jK R = (_ ≫ pullback.fst G.hom (jK R)) ≫ G.hom
    rw [← Category.assoc, h, Category.assoc, Category.assoc, pullback.condition])

theorem cmp_snd : cmp G F ≫ (snd (TF (R := R) F) G).left = UnifPre.gFK (R := R) (G := G) F :=
  pullback.lift_snd _ _ _

variable {G} {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  [GrpObj G] [IsCommMonObj G]

def SameSec (U : UnifPre I D A G) (k : ℕ) (σ : LB.Sec (LPow G U.LG.L (k : ℤ) (TF (R := R) F)))
    (σ' : U.SecGF F k) : Prop :=
  GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (R := R) (G := G) F) (fun _ => (k : ℤ)) σ'
    (fun _ : Fin 1 => (snd (TF (R := R) F) G).left) (fun _ => (k : ℤ)) σ (cmp G F) 1

end Two

section Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def normaliser (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E) : c.F :=
  ∏ τ : E →+* ℂ, embK c τ α ^ ∑ i : Fin (Dw.mult τ), a (τ, i)

example (α : 𝓞 E) : normaliser Dw c 0 α = 1 := by simp [normaliser]

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def nablaAt (C : IntegralChartA3 Xo c T io y) (F : Type) [Field F] [Algebra T.Fr F] [CharZero F] (k : ℕ) {n : ℕ}
    (f : PS F n (chD C.ch)) (P : MvPolynomial (LtN Dw n) F) : F :=
  letI := io.toAlgebra
  nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 k f (fun ℓ => ℓ.2.2)
    (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j)) P

def HasGerm (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) {n : ℕ}
    {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' C.I.G.G n)
    {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (k : ℕ)
    (σ : LB.Sec (LPow G' U'.LG.L (k : ℤ) (TF (R := T.V) F))) (f : PS F n (chD C.ch)) : Prop :=
  ∃ σ' : U'.toUnifPre.SecGF F k, SameSec F U'.toUnifPre k σ σ' ∧
    IsGermN P C.xT C.actT C.eT C.wPT pG PU F k σ' f

variable (Xo c) in

def IsThetaValue (nab : NabV Xo c) (y : IntFr Xo c T io) {n : ℕ} (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (w : T.Fr) : Prop :=
  letI := io.toAlgebra
  ThValAt Xo c nab y.1 x P w ∧ ∀ f : Rul Xo c, IsThRule Xo c nab x P f → evI y f = w

def IsLevelPt (I : letI := io.toAlgebra; IntData Xo c T io y.1) (F : Type) [Field F] [Algebra T.Fr F]
    (t : TF (R := T.V) F ⟶ I.G.G) (x : Dw.La) : Prop :=
  letI := io.toAlgebra
  ∃ p : Sp F ⟶ I.t'.G.left, p ≫ I.m2.φ = t.left ∧
    p ≫ I.m1.φ = spMap (algebraMap T.Fr F) ≫ (levPt Xo y.1.x x).left

end Val

def Oriented {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (g g' : ℕ)
    (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g * g' ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb ≤ Ideal.span {π} ∧ l.Mb ≤ Ideal.span {π'}

def Generators : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → (g : T.V) ∈ maximalIdeal T.V →
  ∀ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q →
  ∀ n : ℕ, 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (σ : LB.Sec (LPow G' U'.LG.L (g' : ℤ) (TF (R := T.V) F))) (σ' : U'.toUnifPre.SecGF F g')
    (s : Fam D'.toPre F g'), SameSec F U'.toUnifPre g' σ σ' → U'.toUnifPre.ExpandsG F g' σ' s →
    NuGe D' (sumQ pD.xe Q) F v g' s 0 →
  ∀ (ga : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)),
    ga.pt ≫ diagEnd pG (C.I.G.act.act π) = 1 → HasFinOrder G' U'.LG ga →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π))) (g' : ℤ) (l.M : ℤ) σ σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) ga σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ a : (E →+* ℂ) × ℕ → ℕ,
    ∃ (u : F) (m : ℕ) (cf : Fin m → F) (x : Fin m → Fin n → Dw.La),
      v u = v (algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')))) ∧ (∀ i, 0 ≤ v (cf i)) ∧
      ∀ Pl ∈ harmA (Dw := Dw) c a n, ∃ w : Fin m → T.Fr, (∀ i, IsThetaValue Xo c nab y (x i) Pl (w i)) ∧
        nablaAt C F l.M h (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pl) =
          u * ∑ i, cf i * algebraMap T.Fr F (w i)

def GeneratorsLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → (g : T.V) ∈ maximalIdeal T.V →
  ∀ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q →
  ∀ n : ℕ, 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (σ : LB.Sec (LPow G' U'.LG.L (g' : ℤ) (TF (R := T.V) F))) (σ' : U'.toUnifPre.SecGF F g')
    (s : Fam D'.toPre F g'), SameSec F U'.toUnifPre g' σ σ' → U'.toUnifPre.ExpandsG F g' σ' s →
    NuGe D' (sumQ pD.xe Q) F v g' s 0 →
  ∀ (ga : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)),
    ga.pt ≫ diagEnd pG (C.I.G.act.act π) = 1 → HasFinOrder G' U'.LG ga →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π))) (g' : ℤ) (l.M : ℤ) σ σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) ga σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pl : MvPolynomial (LtN Dw n) F),
    Pl ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
    (∀ e, 0 ≤ v (Pl.coeff e)) →
    ∃ (u : F) (m : ℕ) (cf : Fin m → F) (f : Fin m → Rul Xo c),
      v u = v (algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')))) ∧ (∀ i, 0 ≤ v (cf i)) ∧
      (∀ i, f i ∈ thGen Xo c nab a n) ∧
      nablaAt C F l.M h Pl = u * ∑ i, cf i * algebraMap T.Fr F (evI y (f i))

def AlphaForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
  ∀ (g g' : ℕ) (π π' : 𝓞 E), Oriented l g g' π π' →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
    (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (n : ℕ), 1 ≤ n →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [CharZero F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (f₀ : PS T.Fr 1 (chD C.ch)) (s : LB.Sec (LPow G' U'.LG.L ((1 : ℕ) : ℤ) (TF (R := T.V) F))),
    (letI := io.toAlgebra; IsGerm y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP 1 y.1.s f₀) →
    HasGerm C P pG PU.toUnifPowOf F 1 s
      (∏ i : Fin n, ev (n := n) ![pt F (chD C.ch) i] (MvPowerSeries.map (algebraMap T.Fr F) f₀)) →
  ∀ (b : TF (R := T.V) F ⟶ G') (U : ThetaGrp G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F)) (x : Fin n → Dw.La),
    b ≫ diagEnd pG (C.I.G.act.act (π * π')) = 1 → SymLift G' U'.LG.L (l.M : ℤ) l.M b U →
    (∀ i, IsLevelPt C.I F (b ≫ pG.pr i ≫ C.I.G.act.act (H.bar π * H.bar π')) (x i)) →
  ∀ (σ₁ σ₂ : LB.Sec (LPow G' U'.LG.L (l.M : ℤ) (TF (R := T.V) F))) (h : PS F n (chD C.ch)),
    IsRigPull G' U'.LG (diagEnd pG (C.I.G.act.act (H.bar π * H.bar π'))) ((1 : ℕ) : ℤ) (l.M : ℤ) s σ₁ →
    IsActOf G' U'.LG.L (l.M : ℤ) U σ₁ σ₂ → HasGerm C P pG PU.toUnifPowOf F l.M σ₂ h →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ Pl ∈ harmA (Dw := Dw) c a n, ∃ w : T.Fr, IsThetaValue Xo c nab y x Pl w ∧
    nablaAt C F l.M h (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pl) =
      algebraMap T.Fr F (io (normaliser Dw c a (H.bar π * H.bar π')) * w)

structure IsBalancedGauge {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : Germ.FB.toK k B.ph1 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h +
    ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : Germ.FB.toK k B.ph2 = Germ.FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h +
    ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, Germ.FB.toK k (B.ad a) = Germ.FB.expS k
    (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

def FrameIndep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (K : Type) [Field K] [CharZero K] [Algebra c.F K] (y : FrPt Xo c K) (C : ChartAt Xo c y)
    (h' : PS K 2 C.d), IsBalancedGauge C.B K h' →
  ∀ (n N : ℕ) (f : PS K n C.d) (Pl : MvPolynomial (LtN Dw n) K),
    Pl ∈ harmK Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    nabValN C.B K C.h H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) Pl =
      nabValN C.B K h' H.w0 N f (fun ℓ => ℓ.2.2) (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) Pl

end GlobalTheory.IndefiniteRowSideFullHecke.RigidNormaliserGenerators
end
end

