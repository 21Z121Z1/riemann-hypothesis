import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CMCurveHermitianForms
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Pairings

variable {S : Scheme.{0}} {A B G G' : Over S} [GrpObj A] [GrpObj B] [GrpObj G] [GrpObj G']

def lamPull (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) : LB (A ⊗ B).left :=
  cubeLB G ![fst A B ≫ f₁, snd A B ≫ f₂] L

def LamEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  LBIso (lamPull L f₁ f₂) (lamPull L' g₁ g₂)

def WeilEqAt (k : ℕ) (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') :
    Prop :=
  ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B), x ^ k = 1 → y ^ k = 1 → ∀ c : Γ(T.left, ⊤)ˣ,
    Out.WeilIs G L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs G' L' k (x ≫ g₁) (y ≫ g₂) c

def WeilEq (L : LB G.left) (f₁ : A ⟶ G) (f₂ : B ⟶ G) (L' : LB G'.left) (g₁ : A ⟶ G') (g₂ : B ⟶ G') : Prop :=
  ∀ k : ℕ, 0 < k → WeilEqAt k L f₁ f₂ L' g₁ g₂

end Pairings

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Zw (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))

def wz (H : Host E) : Zw H := ⟨H.w0, Algebra.self_mem_adjoin_singleton ℤ H.w0⟩

structure CMCurve (H : Host E) (R : Type) [CommRing R] (ω : R) where

  P : Out.PolAV (Sp R)
  dim : P.g = 1

  act : OAct (Zw H) P.A

  v : epsR R ⟶ P.A
  basis : IsLieBasis (G := P.A) ![v]
  eigen : (v ≫ act.act (wz H)).left = spMap (epsScaleR ω) ≫ v.left

variable {H : Host E}

structure IsPrincipal {S : Scheme.{0}} (t : SAB H S) : Prop where
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L

def SigAt (H : Host E) (p q : ℕ) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G)
    {k : Type} [Field k] (x : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act x τ p) ∧ (τ H.rt ≠ ρ → LieMult act x τ q)

def HasSig (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (act : OAct (𝓞 E) G)
    (ρ : R) : Prop :=
  ρ ^ 2 = -(H.d : R) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k), SigAt H p q act (spMap β) (β ρ)

def herm (D : Datum H) (x y : D.La) : Zw H :=
  ((D.EF (H.w0 • x) y - D.EF x y : ℤ) : Zw H) + ((D.EF x y : ℤ) : Zw H) * wz H

open Classical in

def posSign (D : Datum H) : ℤˣ := if (0 < H.rt0.im ↔ D.q = 0) then 1 else -1

structure IsTensorMap {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (h : La → La → Zw H) (t : SAB H (Sp R)) (φ : La → (C.P.A ⟶ t.G)) : Prop where
  hom : ∀ x, IsMonHom (φ x)
  add : ∀ x y, φ (x + y) = φ x * φ y
  lin : ∀ (a : 𝓞 E) x, φ (a • x) = φ x ≫ t.act.act a
  bal : ∀ (b : Zw H) x, φ ((b : 𝓞 E) • x) = C.act.act b ≫ φ x

  onto : ∀ (T : Over (Sp R)) (y : T ⟶ t.G), ∃ (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    y = (List.ofFn fun i => c i ≫ φ (x i)).prod

  inj : ∀ (T : Over (Sp R)) (n : ℕ) (x : Fin n → La) (c : Fin n → (T ⟶ C.P.A)),
    (List.ofFn fun i => c i ≫ φ (x i)).prod = 1 →
      ∀ ℓ : La →ₗ[Zw H] Zw H, (List.ofFn fun i => c i ≫ C.act.act (ℓ (x i))).prod = 1

  pol : ∀ x y, LamEq t.PP.L (φ x) (φ y) C.P.L (C.act.act (h x y)) (𝟙 C.P.A)

def IsTensorSgn (ε : ℤˣ) (D : Datum H) {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω)
    (t : SAB H (Sp R)) : Prop :=
  ∃ φ : D.La → (C.P.A ⟶ t.G), IsTensorMap C (fun x y => (((ε : ℤ) : Zw H)) * herm D x y) t φ

def IsTensor (D : Datum H) {R : Type} [CommRing R] {ω : R} (C : CMCurve H R ω) (t : SAB H (Sp R)) : Prop :=
  IsTensorSgn (posSign D) D C t

example (D : Datum H) {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {k : Type} [Field k]
    (x : Sp k ⟶ S) (ρ : k) : SigAt H D.p D.q act x ρ ↔ DetCond D act x ρ := Iff.rfl

example (D : Datum H) (x : D.La) : herm D x x = ((D.EF (H.w0 • x) x : ℤ) : Zw H) := by
  simp [herm, D.alt]

theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have hr : H.bar H.rt = -H.rt := by
    have h2 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [← H.bar_eq, h] at h3
      have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
      have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun a : 𝓞 E => φ (a : E)) H.rt_sq
        simpa using this
      have h5 := congrArg Complex.re h4
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      simp [sq, him] at h5
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
    · exact h
  have h2 : (2 : 𝓞 E) * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [hr, sub_eq_add_neg, map_ofNat] using this
  have : (2 : 𝓞 E) * (H.bar H.w0 - (1 - H.w0)) = 0 := by linear_combination h2 + H.two_weight_eq_one_add_root
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left two_ne_zero)

theorem herm_conj (D : Datum H) (x y : D.La) : (herm D y x : 𝓞 E) = H.bar (herm D x y : 𝓞 E) := by
  have hb : H.bar H.w0 = 1 - H.w0 := cmHost_bar_halfIntegerGenerator H
  have sk : ∀ a b, D.EF a b = - D.EF b a := fun a b => by
    have := D.alt (a + b)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
    rw [D.adj, hb, sk y, sub_smul, one_smul, map_sub, LinearMap.sub_apply]; ring
  simp only [herm, wz, h1, sk y x]
  simp [hb]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.CMCurveHermitianForms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FractionGeneratorsArcs
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

def GeneratesFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  ∀ x : F, ∃ r s : O, β s ≠ 0 ∧ x * β s = β r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def UnivCompat {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂) {S : Scheme.{0}} {t : SAB H S} {χ₁ : S ⟶ Y₁.X} {χ₂ : S ⟶ Y₂.X}
    (m₁ : SABMap t Y₁.t χ₁) (m₂ : SABMap t Y₂.t χ₂) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y₁.oF.t.G.left) (g₂ : T ⟶ Y₂.oF.t.G.left),
    g ≫ m₁.φ = g₁ ≫ Y₁.m.φ → g₁ ≫ Y₁.m0.toSABMap.φ = g₂ ≫ Y₂.m0.toSABMap.φ →
    g₁ ≫ Y₁.oF.t.G.hom = g₂ ≫ Y₂.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y₂.m.φ

def SameWitness {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂) : Prop :=
  ∃ (m₂ : SABMap W₁.t Y₂.t χ₂) (h : _),
    W₂ = { t := W₁.t, m := m₂, P := W₁.P, φ := W₁.φ, he := W₁.he, w := W₁.w, e := W₁.e, spec := h } ∧
    UnivCompat Y₁ Y₂ W₁.m m₂

def OneArc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ O₁ O₂ : Type) [CommRing O₀] [CommRing O₁] [CommRing O₂]
    (β₀ : O₀ →+* c.F) (β₁ : O₁ →+* c.F) (β₂ : O₂ →+* c.F) (b₁ : O₀ →+* O₁) (b₂ : O₀ →+* O₂)
    (Y₀ : Model Xo c β₀) (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂),
    β₁.comp b₁ = β₀ → β₂.comp b₂ = β₀ → GeneratesFrac β₁ → GeneratesFrac β₂ →
    Dominates Y₀ Y₁ b₁ → Dominates Y₀ Y₂ b₂ →
    ∀ (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
      (χ₁ : Sp (PowerSeries k) ⟶ Y₁.X)
      (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
      (y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
      χ₁ ≫ Y₁.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β₁) →
      y ≫ Y₁.j = Out.jK (PowerSeries k) ≫ χ₁ →
      ∃ (χ₂ : Sp (PowerSeries k) ⟶ Y₂.X)
        (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂),
        χ₂ ≫ Y₂.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β₂) ∧
        y ≫ Y₂.j = Out.jK (PowerSeries k) ≫ χ₂ ∧ SameWitness W₁ W₂

example {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂)
    (h : SameWitness W₁ W₂) : W₂.t = W₁.t ∧ HEq W₂.P W₁.P := by
  obtain ⟨m, h', rfl, -⟩ := h
  exact ⟨rfl, HEq.rfl⟩

example {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ : Type} [CommRing O₁] {β₁ : O₁ →+* c.F} {Y₁ : Model Xo c β₁} {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁) :
    SameWitness W₁ W₁ := by
  refine ⟨W₁.m, W₁.spec, rfl, ?_⟩
  intro T g g₁ g₂ h₁ h₂ h₃
  have : g₁ = g₂ := Y₁.m0.toSABMap.cart.1.hom_ext h₂ h₃
  rw [h₁, this]

end GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.L2SquaredNorms
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Norms

variable {K₁ : Type} [Field K₁]

def hermSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  (z ⬝ᵥ Hm.mulVec (star z)).re

def IsL2SquareIntegralProblem (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (P.L.pull (eSec P.A))) (σ : K₁ →+* ℂ)
    (s : P.L.Sec) (v : ℝ) : Prop :=
  rig.IsGen ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (Fd : Set (Fin P.g → ℂ)),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    (∀ i : P.L.ι, ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i) →
      u.fr (fun _ => i) 0 =
        σ (valR (A := K₁) (𝟙 (Sp K₁)) ((P.L.pull (eSec P.A)).U (fun _ => i)) (rig.s (fun _ => i)).val)) ∧
    (∀ (i : P.L.ι) (z : Fin P.g → ℂ), ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valAt' ((u.ex z).left ≫ φ) (P.L.U i) (s.f i) = θ z * u.fr (fun _ => i) z) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧ volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
    IntegrableOn (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) Fd volume ∧
    v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) / (volume Fd).toReal

def IsLogNormPiH (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (σ : K₁ →+* ℂ) (t : epsR K₁ ⟶ P.A) (v : ℝ) : Prop :=
  IsTangent t ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (t' : epsR ℂ ⟶ A') (w : Fin P.g → ℂ),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    t'.left ≫ φ = spMap (dualMap σ) ≫ t.left ∧ u.IsDiff w t' ∧ w ≠ 0 ∧
    v = Real.log (Real.sqrt (Real.pi * hermSq Hm w))

theorem IsL2SquareIntegralProblem.nonneg {P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)} {rig : LB.Gen (P.L.pull (eSec P.A))}
    {σ : K₁ →+* ℂ} {s : P.L.Sec} {v : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v) : 0 ≤ v := by
  obtain ⟨_, A', _, φ, u, Hm, χ, θ, Fd, _, _, _, _, _, _, _, _, hv⟩ := h
  rw [hv]
  exact div_nonneg (MeasureTheory.integral_nonneg (fun z => by positivity)) ENNReal.toReal_nonneg

end Norms

section Line

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def valLineLogNorm (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (thSq : ℝ) (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log thSq - mu.sum fun x m => (m : ℝ) * ℓ x.1 x.2.2

variable {K₁ : Type} [Field K₁]

def IsLetterLogNorm (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (σ : K₁ →+* ℂ) :
    Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)) → ℝ → Prop
  | none, v => v = 0
  | some (.inl t), v => IsLogNormPiH A₁ σ t v
  | some (.inr t), v => IsLogNormPiH A₂ σ t v

def IsValLineLogNorm (B : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (B.L.pull (eSec B.A))) (th : B.L.Sec)
    (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁))
    (src : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)))
    (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (σ : K₁ →+* ℂ) (a : ℝ) : Prop :=
  ∃ (thSq : ℝ) (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ), 0 < thSq ∧ IsL2SquareIntegralProblem B rig σ th thSq ∧
    (∀ τ k, IsLetterLogNorm A₁ A₂ σ (src τ k) (ℓ τ k)) ∧ a = valLineLogNorm n mu thSq ℓ

def IsValLineLogNormAt (B : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (B.L.pull (eSec B.A))) (th : B.L.Sec)
    (A₁ A₂ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁))
    (src : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Option ((epsR K₁ ⟶ A₁.A) ⊕ (epsR K₁ ⟶ A₂.A)))
    (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (w : InfinitePlace K₁) (a : ℝ) : Prop :=
  ∃ σ : K₁ →+* ℂ, InfinitePlace.mk σ = w ∧ IsValLineLogNorm B rig th A₁ A₂ src n mu σ a

example (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (c : ℝ) :
    valLineLogNorm (Dw := Dw) 2 0 (Real.exp c) ℓ = -c := by
  simp [valLineLogNorm]

example (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (n : ℤ) (x : ArcLt Dw) (m : ℕ) :
    valLineLogNorm n (Finsupp.single x m) 1 ℓ = -(m * ℓ x.1 x.2.2) := by
  simp [valLineLogNorm]

end Line

end GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LieLiftsTangentReduction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj

abbrev epsRed (R : Type) [CommRing R] : Sp R ⟶ Sp (DualNumber R) :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom

def IsGtTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (ν : GtPt D (epsR R)) : Prop :=
  epsRed R ≫ ν.b.left = eSec D.P.A ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (ν.s χ) (epsRed R)) (LB.oneGen D.P.L)

theorem IsGtTangent.isTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ν : GtPt D (epsR R)}
    (h : IsGtTangent ν) : IsTangent ν.b := h.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def LieLifts {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
    {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ) : Prop :=
  ∀ ν : GtPt a.D₀ (epsR K₁), IsGtTangent ν →
    ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsTangent v ∧ IsLieImage W ν v

variable (Xo c) in

def ArcLieLift : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K₁ : Type) [Field K₁] (b : O →+* K₁)
    (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ), LieLifts W

end GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
end
end

