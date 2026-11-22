import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
section
set_option autoImplicit false

namespace GlobalTheory.Mean4O

theorem Setup.Core.dualRef {D : Formalism.BasicNotions.D7} {O : Setup D} (h : O.Core) : O.DualRef :=
  fun c σ _ _ _ hf => h.referenceMetric_mul_dual_eq_one c σ _ hf

end GlobalTheory.Mean4O
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic

namespace GlobalTheory.Discrepancy

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

abbrev fnPull (s : Y ⟶ X) [IsDominant s] : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (functionFieldMap s).toMonoidHom

def pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) : CartierDiv Y :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose

theorem isEqn_pullCart (s : Y ⟶ X) [IsDominant s] {D : CartierDiv X} {y : Y} {g : X.functionFieldˣ}
    (h : D.IsEqn (s y) g) : (pullCart s D).IsEqn y (fnPull s g) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.2 y g h

theorem toPic_pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) :
    toPic (pullCart s D) = CechPic.pull s (toPic D) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.1

theorem pullCart_add (s : Y ⟶ X) [IsDominant s] (D E : CartierDiv X) :
    pullCart s (D + E) = pullCart s D + pullCart s E :=
  CartierDiv.ext_of_isEqn fun y =>
    have ⟨g, hg⟩ := D.exists_isEqn (s y)
    have ⟨g', hg'⟩ := E.exists_isEqn (s y)
    ⟨_, isEqn_pullCart s (hg.add hg'),
      (map_mul (fnPull s) g g').symm ▸ (isEqn_pullCart s hg).add (isEqn_pullCart s hg')⟩

def pullCartHom (s : Y ⟶ X) [IsDominant s] : CartierDiv X →+ CartierDiv Y :=
  AddMonoidHom.mk' (pullCart s) (pullCart_add s)

variable {k : Type} [Field k]

def DivOver.Over {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p) :
    Prop :=
  ∀ f, f ∈ E.ring ↔ functionFieldMap s f ∈ E'.ring

structure IsLogRes (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) : Prop where

  smooth : SmoothOfRelativeDimension n (s ≫ p)

  proj : IsProjOver (s ≫ p)

  bir : Function.Bijective (functionFieldMap s)

  div : IsDivOfForm K (EtaleKlt.ratPull p s n η)

  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)

  supp : (pullCart s G - m • K).supp ≤ B

structure IsLogMult (p : X ⟶ Sp k) (n : ℕ) (Δ : X → ℚ) (η : RatForms p n) (m : ℕ)
    (G : CartierDiv X) : Prop where

  ne_zero : η ≠ 0

  pos : 0 < m

  eqn : ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

theorem IsLogCanonicalMultiple.exists_isLogMult {p : X ⟶ Sp k} {n : ℕ} {Δ : X → ℚ} {m : ℕ}
    {G : CartierDiv X} (h : IsLogCanonicalMultiple p n Δ m G) (hm : 0 < m) :
    ∃ η, IsLogMult p n Δ η m G :=
  have ⟨η, h₁, h₂⟩ := h; ⟨η, h₁, hm, h₂⟩

def InMultAt (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (x : X)
    (u : X.functionFieldˣ) : Prop :=
  ∀ g, G.IsEqn x g → ∀ E : DivOver p, E.Through x → -1 < (E.ord u : ℚ) + discrep E η m g

def IsMultIdeal (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (J : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔
    ∀ (x : X) (hx : x ∈ U.1) (u : X.functionFieldˣ),
      (u : X.functionField) = fnOf U.1 (gen_mem hx) f → InMultAt p n η m G x u

theorem IsMultIdeal.unique {p : X ⟶ Sp k} {n : ℕ} {η : RatForms p n} {m : ℕ} {G : CartierDiv X}
    {J J' : X.IdealSheafData} (h : IsMultIdeal p n η m G J) (h' : IsMultIdeal p n η m G J') :
    J = J' :=
  Scheme.IdealSheafData.ext (funext fun U => Ideal.ext fun f => (h U f).trans (h' U f).symm)

structure IsSncChart [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) (B : Closeds Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
    (u : Fin n → Y.functionFieldˣ) : Prop where

  frame : IsFrame (dOn q z)

  val : ∀ j ∈ J, (u j : Y.functionField) = fnOf U (gen_mem hy) (z j)

  spec : ∀ j ∈ J, w j ⤳ y

  coheight : ∀ j ∈ J, Order.coheight (w j) = 1

  inj : Set.InjOn w J

  ord_self : ∀ j ∈ J, Scheme.ord (u j : Y.functionField) (w j) = 1

  ord_other : ∀ j ∈ J, ∀ v, v ⤳ y → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0

  mem : ∀ v, v ⤳ y → Order.coheight v = 1 → (v ∈ B ↔ ∃ j ∈ J, v = w j)

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

def UPoinOn (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

def UPoinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
          (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S), UPoinOn Xo c φ zs i OZ N d J π j BD

variable {Xo : Moduli D l} {c : Coeff l}

theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

theorem UPoinOn.exists_extension {φ : InvFun (𝓞 E)} {Z : Scheme.{0}} {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z}
    {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} {j : Xo.XF c ⟶ S} {BD : EffCartierData S}
    (h : UPoinOn Xo c φ zs i OZ N d J π j BD) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℚ R]
    (hR : GlobalTheory.Mum.Base R) {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) {y : Sp (FractionRing R) ⟶ Xo.XF c}
    (hy : GenOf Xo c y t) : ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i := by
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  obtain ⟨σ, hσ⟩ := (exists_over_iff y).2 fun n hn => by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  exact (h.2.2.1 R hR t ⟨P⟩ y hy σ hσ).imp fun _ h => h.1

example {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) : UValOn Xo c j φ ⊤ 0 :=
  fun _ _ _ _ _ _ _ χ _ _ _ _ _ _ _ _ _ _ => ⟨0, by simp, (idlAlong_top χ).trans (by simp)⟩

example (hq : D.q = 0) (φ : InvFun (𝓞 E)) : IsPolFan H.bar (min D.p D.q) φ ∧ NoSelfInt H.bar (min D.p D.q) φ := by
  rw [hq, Nat.min_zero]
  exact ⟨isPolFan_zero, noSelfInt_zero⟩

example (p : ℕ) [hp : Fact p.Prime] : (GlobalTheory.Mum.Base (PowerSeries ℚ) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : PowerSeries ℚ)) ∧
    ∀ (y : Sp (FractionRing ℤ_[p]) ⟶ Xo.XF c) (σ : Sp ℤ_[p] ⟶ Sp c.F), jK ℤ_[p] ≫ σ ≠ y ≫ pullback.snd _ _ := by
  refine ⟨⟨GlobalTheory.Mum.base_powerSeries, fun n hn => ?_⟩, fun y σ h => ?_⟩
  · rw [← map_natCast (algebraMap ℚ (PowerSeries ℚ))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  · exact PadicInt.irreducible_p.not_isUnit ((exists_over_iff y).1 ⟨σ, h⟩ p hp.out.ne_zero)

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasPolChartOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Act

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

structure Data.Act (O : Type) [Ring O] [StarRing O] (Q : Data R) [Module O Q.X] where

  onB : RingAct Q.B O
  rosati : ∀ a : O, RosatiAdj Q.B Q.M.L (onB.act a) (onB.act (star a))
  c_lin : ∀ (a : O) (y : Q.X), Q.c (a • y) = Q.c y ≫ onB.act a
  tau_bal : ∀ (a : O) (u : LB.Gen (LB.LinComb Q.M.L (rosatiφ Q.B (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr Q.M.L _ _ _ _ (LB.pullGen Q.M.L _ _ u (zero2 Q.B)) (LB.oneGen Q.M.L) → ∀ y y' z J, Good Q.M.L z J →
      val (Q.tau (a • y) y') (𝟙 _) z J * val u (lift (toUnit (TK R) ≫ Q.c y) (toUnit (TK R) ≫ Q.c y')).left z J =
        val (Q.tau y (star a • y')) (𝟙 _) z J

def HalfAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ)
    (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T ⟶ D.P.A) (1 : T ⟶ D.P.A)).left z J J' = 1) ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)) =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

theorem half_iff {Q : Data R} {ρ : R →+* R'} {D : DegPre R'} {e : D.X ≃+ Q.X} {f : D.X → D.X → (FractionRing R')ˣ} :
    Half Q ρ D e f ↔ ∃ β, HalfAt Q ρ D e f β := Iff.rfl

def IsPrim {S : Scheme.{0}} (P : PolAV S) (w : P.A ⟶ P.A) : Prop :=
  letI := P.isAb.comm
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(padd P.A (𝟙 _) w).left, 𝟙 P.A.left, w.left, (toUnit P.A ≫ η[P.A]).left]
    ![1, -2, -1, 2]), u.IsGen

def RefinesAct {O : Type} [Ring O] [StarRing O] (Q : Data R) [Module O Q.X] (qa : Q.Act O) (D : DegPre R) [Module O D.X]
    (oa : D.OAct O) (e : D.X ≃ₗ[O] Q.X) : Prop :=
  ∃ β, HalfAt Q (RingHom.id R) D e.toAddEquiv (fun _ _ => 1) β ∧ ∀ a, (oa.onB.act a).left ≫ β = β ≫ (qa.onB.act a).left

end Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {o : Type} [CommRing o] {b : o →+* c.F}

def IsMumfordAct (Z : Model Xo c b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (χ : Sp R ⟶ Z.X) (Q : Data R)
    [Module (𝓞 E) Q.X] (qa : letI := H.starRing; Q.Act (𝓞 E)) : Prop :=
  letI := H.starRing
  ∀ (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (oa : D.toPre.OAct (𝓞 E)) (e : D.toPre.X ≃ₗ[𝓞 E] Q.X),
    RefinesAct Q qa D.toPre oa e → TraceFormTwistIso D.toPre oa H.w0 →
      ∃ (t : SAB H (Sp R)) (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (U : Unif (maximalIdeal R) D A t.G),
        Nonempty (SABMap t Z.t χ) ∧ U.LG = t.PP ∧ U.toUnifPre.OLinear (𝓞 E) oa oA t.act.toRingAct

def HasPolChartOf (φ : InvFun (𝓞 E)) (Z : Model Xo c b) (BD : EffCartierData Z.X) (d : ℕ) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (ξ : Sp (ChartRing k m e) ⟶ gen Z) (Q : Data (ChartRing k m e))
    (_ : Module (𝓞 E) Q.X) (_ : Module.Finite (𝓞 E) Q.X) (qa : letI := H.starRing; Q.Act (𝓞 E))
    (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m e i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m e i ∈ p.asIdeal) ∧
    IsMumfordAct Z (ξ ≫ genι Z) Q qa ∧ Q.IsMonomialTau (bdParam k m e) (fun i => (l.M' : ℤ) • δ i) ∧
    Module.finrank (𝓞 E) Q.X ≤ min Dw.p Dw.q ∧ IsCone H.bar φ δ ∧ (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i)) ∧
    idlAlong BD.idealSheaf (ξ ≫ genι Z) = Ideal.span {∏ i, bdParam k m e i ^ a i}

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def SharpRef (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X) : Prop :=
  ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
    (∀ a, IsMonHom (pr a)) ∧
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
    w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
    ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b

def IsThetaTerms (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c))) ∧
    ∃ c, T 0 c = 1

section Real

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z) {N₁ : ℕ} (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁))

def HasTraits : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMember [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X)
    (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms D N₁ e₈ fun mu c => Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) fun a => e.symm (mu a)

end Real

def Elements {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (φ : InvFun O) (d : ℕ)
    (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (O' : Subring (Φ.V y)) (g₀ : Φ.V y) (b : Fin (Φ.m y) → ℕ), (∀ h ∈ O', ev h ∈ k₀ ∧ (h ∈ maximalIdeal (Φ.V y) → ev h = 0)) ∧
    (∀ k, (b k : ℝ) = d * φ.evalZ (Φ.δ y k)) ∧ Associated g₀ (∏ k, Φ.t y k ^ b k) ∧
    ∀ (D l : ℕ) (a : Fin l × Fin s → Φ.X y), Dominant bar φ (D * d) N₁ W ga a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ h ∈ O',
      h * g₀ ^ D - Φ.coefT y a c * Φ.monoT y a ∈
        Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

def Values {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  (∀ k, ev (Φ.t y k) = 0) ∧
  (∀ mu c c', IsUnit (Φ.u y mu c') → ∃ r ∈ k₀, ev (Φ.u y mu c) = r * ev (Φ.u y mu c')) ∧
  ∀ lam : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ, (∀ k, lam (Φ.δ y k) = 0) →
    ∃ (l l' M : ℕ) (a : Fin l × Fin s → Φ.X y) (a' : Fin l' × Fin s → Φ.X y) (c : Fin l → Φ.Q) (c' : Fin l' → Φ.Q), 1 ≤ M ∧
      IsUnit (Φ.coefT y a c) ∧ IsUnit (Φ.coefT y a' c') ∧ (∀ β ∈ balForms bar (Φ.X y), lin W a β - lin W a' β = M * lam β) ∧
      ∃ r ∈ k₀, ev (Φ.coefT y a c) = r * ev (Φ.coefT y a' c')

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem exists_tauIn {Q : Data V} {N : ℕ} {s : Fin N → V} {ε : Fin N → LinearMap.BilinForm ℤ Q.X}
    (h : Q.IsMonomialTau s ε) : ∃ τ₀ : Gens Q, TauIn Q τ₀ s ε := by
  have h' : ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ Q.TauCoord a b k := h

  choose k hk hc using h'
  refine ⟨fun a b => Exists.choose (hc a b), fun a b => ⟨(Exists.choose_spec (hc a b)).1, k a b, hk a b, ?_⟩⟩
  exact (Exists.choose_spec (hc a b)).2

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

theorem tate_tauIn (k : ℤ) :
    ∃ τ₀ : Gens (Wit.tate k), TauIn (Wit.tate k) τ₀ ![PowerSeries.X] ![k • mulForm] :=
  exists_tauIn (Wit.tate_isMonomialTau k)

theorem defOver_top {K : Type} [Field K] {Y : Scheme.{0}} (P : Sp K ⟶ Y) : DefOver (⊤ : Subfield K) P := by
  refine ⟨spMap ((Subfield.topEquiv (K := K)).symm : K →+* (⊤ : Subfield K)) ≫ P, ?_⟩

  have hid : (⊤ : Subfield K).subtype.comp ((Subfield.topEquiv (K := K)).symm : K →+* (⊤ : Subfield K)) =
      RingHom.id K := by
    ext x
    rfl
  rw [← Category.assoc]
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end GlobalTheory.Poinc.Sep.Model
end
end

