import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HodgeGramEqRiemann
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeometrySectionsEqRiemannRoch
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VarietyWithModels
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def comb (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O) : InvFun O where
  toFun n B := a * ψ.toFun n B + b * φ.toFun n B
  inv n m r hr B := by rw [ψ.inv n m r hr, φ.inv n m r hr]
  zero B := by rw [ψ.zero, φ.zero]; simp

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

def FormAt (Dg : DegPre R) {W : Type} [CommRing W] (f : R →+* W) (ϖ : W) (be : LinearMap.BilinForm ℤ Dg.X) : Prop :=
  ∀ y, ∃ (r : R) (n : ℕ), PsiCoord Dg y r ∧ be y y = 2 * n ∧ Associated (f r) (ϖ ^ n)

def InCone (Dg : DegPre R) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ Dg.X) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (f : R →+* W)
    (be : LinearMap.BilinForm ℤ Dg.X), (∀ y z, be y z = be z y) → FormAt Dg f ϖ be →
    ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal be = ∑ i, c i • toReal (γ i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasCones (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) : Prop :=
  ∀ z : Z.X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R))
    (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R ∧ ξ (closedPoint R) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
    Cn P.D.toPre.X m γ ∧ InCone P.D.toPre γ

def ConeZ (E : Type) [Field E] [NumberField E] (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  IsCone id φ γ

def ConeO (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop := IsCone H.bar φ γ

def PolRay (ψ φ : InvFun (𝓞 E)) (k : ℕ) (Z : Model Xo c β) : Prop :=
  ∃ b N T₀ : ℕ, 0 < b ∧ 0 < N ∧ ∀ T, T₀ ≤ T → ∃ BD, IsPol (comb (N * T) ψ b φ) (N * T * k) Z BD

def GenTor (Z : Model Xo c β) : Prop :=
  SmoothOfRelativeDimension D.dim (genStr Z) ∧ FinalTheorems.Snc (genBdIdeal Z) ∧ ∀ x ∈ genBd Z, HasToricChart Z x

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

abbrev GMod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} (Xo : Moduli D l)
    (c : Coeff l) : Type 1 := Model Xo c (algebraMap (𝓞 c.F) c.F)

def SiegLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (g : ℕ) (φs : InvFun ℤ), Module.finrank ℚ E * min D.p D.q ≤ g ∧ IsPolFan id g φs ∧
      IsTame φs ∧ ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) →
        ∃ (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F) (b : ∀ i, 𝓞 c.F →+* R i)
          (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model (Xo l) c (ω i)), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω ∧
          ∀ i, HasCones (ConeZ E φs) (C i) ∧ PolRay (comb 0 (resInt _ φs) 0 (resInt _ φs)) (resInt _ φs) 1 (C i)

def PolGlueSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (I : Type) (_ : Finite I) (R : I → Type) (_ : ∀ i, CommRing (R i)) (a : I → 𝓞 c.F)
    (b : ∀ i, 𝓞 c.F →+* R i) (ω : ∀ i, R i →+* c.F) (C : ∀ i, Model Xo c (ω i)) (ψ φ : InvFun (𝓞 E)) (k : ℕ)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop),
    IsTwInv H ψ → IsTwInv H φ → IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, HasCones Cn (C i) ∧ PolRay ψ φ k (C i)) → ∃ Z : GMod Xo c, HasCones Cn Z ∧ PolRay ψ φ k Z

def PhiDivZSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    HasCones (ConeZ E φs) Z → ∀ a b : ℕ, ∃ BD, IsPhiDiv (comb a (comb 0 (resInt _ φs) 0 (resInt _ φs)) b (resInt _ φs)) Z BD

def PhiDivOSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)),
    Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeO H φ) Z →
    ∀ a d b : ℕ, ∃ BD, IsPhiDiv (comb a (comb d (resInt _ φs) 0 φ) b φ) Z BD

def UniformSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (ψ φ : InvFun (𝓞 E)) (k : ℕ)
      (Z : ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → GMod (Xo l) c), IsTwInv H ψ → IsTwInv H φ →
      (∀ l c hg, PolRay ψ φ k (Z l c hg) ∧ ∀ a b, ∃ BD, IsPhiDiv (comb a ψ b φ) (Z l c hg) BD) →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∀ l c hg, ∃ BD, IsPol (comb a ψ b φ) (a * k) (Z l c hg) BD

def RefineSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ),
    Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → (∀ N ∈ 𝒩, 0 < N) → ∃ φ, Refines H q φs 𝒩 φ

def GenFanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min D.p D.q) φ → NoSelfInt H.bar (min D.p D.q) φ →
      ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ),
        0 < d ∧ GenTor Y ∧ HasCones (ConeO H φ) Y ∧ IsPol (comb 0 φ d φ) k Y BD

def GenMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E))
    (d k : ℕ) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX → HasCones (ConeO H φ) Y →
    ∃ ρ : gen Y ⟶ gen X, Y.jQ ≫ ρ = X.jQ

def IsBlowOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X)
    (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n : ℕ) : Prop :=
  0 < n ∧ Z.j ≫ π = X.j ∧ π ≫ X.s = Z.s ∧ Y.jQ ≫ e.hom = Z.jQ ∧ EX.idealSheaf = J.comap π ∧
    EX.idealSheaf.comap (e.hom ≫ genι Z) = (BY.idealSheaf ^ n).comap (genι Y) ∧
    J = ((BY.idealSheaf ^ n).comap (genι Y)).map (e.hom ≫ genι Z ≫ π) ∧
    ∀ L : LB X.X, GlobalTheory.IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (L.pull π) T) (GlobalTheory.CechPic.dual EX.lb))

def BlowExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (k : ℕ) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    ∃ (Z : GMod Xo c) (π : _) (e : _) (J : _) (EX : _) (n : ℕ), IsBlowOf X Z Y BY π e J EX n

def BlowOrdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : _) (e : _) (J : _) (EX : _)
    (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X),
    Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X →
    X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n →
    IsPhiDiv (comb 0 φ (n * d') φ) Z EX ∧ HasCones (ConeO H φ) Z

def BlowPolSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : _) (e : _) (J : _) (EX : _)
    (n k b : ℕ) (ψ φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), IsPol ψ k X DX → IsBlowOf X Z Y BY π e J EX n → 0 < b →
    IsPhiDiv (comb 0 φ b φ) Z EX → GenTor Y → PolRay ψ φ k Z ∧ GenTor Z

def ConeArcSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ (X : GMod (Xo l) c) (ψ : InvFun (𝓞 E)) (k : ℕ) (DX : EffCartierData X.X), IsTame ψ → IsPol ψ k X DX → X.N4

def DomSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l, ∃ (s : Sys Xo) (𝒩 : Finset ℕ), (∀ N ∈ 𝒩, 0 < N) ∧
      ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Z : GMod (Xo l) c),
        HasCones (fun _ _ _ _ _ γ => ∀ N ∈ 𝒩, IsFine N γ) Z → DomAll s hg Z

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open scoped ComplexOrder

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.TrueGeo GlobalTheory.TrueCx
open scoped ContDiff

def cutoff (y : ℝ) : ℝ := Real.smoothTransition (3 - y) ^ 2

theorem cutoff_mem (y : ℝ) : cutoff y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem cutoff_of_le {y : ℝ} (h : y ≤ 2) : cutoff y = 1 := by
  rw [cutoff, Real.smoothTransition.one_of_one_le (by linarith), one_pow]

theorem cutoff_of_ge {y : ℝ} (h : 3 ≤ y) : cutoff y = 0 := by
  rw [cutoff, Real.smoothTransition.zero_of_nonpos (by linarith), zero_pow two_ne_zero]

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff ∧ ContDiff ℝ ∞ fun y => √(cutoff y) := by
  have h : ContDiff ℝ ∞ fun y : ℝ => Real.smoothTransition (3 - y) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  exact ⟨h.pow 2, by simpa only [cutoff, Real.sqrt_sq (Real.smoothTransition.nonneg _)] using h⟩

def cutWt (κ R r : ℝ) : ℝ := cutoff (Real.log r / Real.log R) / (1 + (r / R) ^ κ)

theorem cutWt_mem (κ : ℝ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) : cutWt κ R r ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Real.rpow_nonneg (div_nonneg hr hR) κ
  exact ⟨div_nonneg (cutoff_mem _).1 (by linarith), (div_le_one (by linarith)).2 ((cutoff_mem _).2.trans (by linarith))⟩

theorem cutWt_of_ge (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (h : R ^ 3 ≤ r) : cutWt κ R r = 0 := by
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  rw [cutWt, cutoff_of_ge ((le_div_iff₀ (Real.log_pos (by linarith))).2 (by exact_mod_cast h1)), zero_div]

theorem cutWt_of_le (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) : cutWt κ R r = 1 / (1 + (r / R) ^ κ) := by
  have h1 := Real.log_le_log hr h
  rw [Real.log_pow] at h1
  rw [cutWt, cutoff_of_le ((div_le_iff₀ (Real.log_pos (by linarith))).2 (by exact_mod_cast h1))]

example (κ : ℝ) {R : ℝ} (hR : 2 ≤ R) : cutWt κ R R = 1 / 2 := by
  rw [cutWt_of_le κ hR (by linarith) (by nlinarith), div_self (by linarith), Real.one_rpow, one_add_one_eq_two]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (σ : c.F →+* ℂ)

def OddPrimesWithRootsOfUnity.eigMet : EigMet Z σ := .ofForm (x.met σ) (x.met_smooth σ).1

theorem OddPrimesWithRootsOfUnity.eigMet_gram : (x.eigMet σ).gram = x.gram := rfl

theorem OddPrimesWithRootsOfUnity.smoothOn_eigMet : (x.eigMet σ).SmoothOn (manifold Z σ) Set.univ := fun V _ F τ a b _ =>
  have ⟨g, h1, h2, h3⟩ := x.gram_smooth (σ := σ) V F τ a b
  ⟨g, h1.mono Set.inter_subset_right, h2.mono Set.inter_subset_right, fun y _ hy f hf => h3 y hy f (hf τ)⟩

theorem OddPrimesWithRootsOfUnity.exp_le_r (y : CxPts (genStr Z) σ) : Real.exp 1 ≤ x.r σ y :=
  le_sub_self_iff _ |>.2 (Real.log_nonpos (sq_nonneg _) (pow_le_one₀
    (Finset.prod_nonneg fun i _ => ((x.nrm_div σ i).1 y).1)
    (Finset.prod_le_one (fun i _ => ((x.nrm_div σ i).1 y).1) fun i _ => ((x.nrm_div σ i).1 y).2)))

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem xiR_pos (D : D7) : 0 < xiR D :=
  norm_embedding_xi_zero D D.host.φ₀ ▸ norm_pos_iff.2 ((map_ne_zero _).2 (cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D))

variable (s) in

theorem FinalTheorems.im_neg_xi (σ : κ.c.F →+* ℂ) (k : (s.U σ).Comp) (τ : ((s.U σ).X k).Ψ) :
    (τ.1 (-((s.U σ).X k).ξ0)).im = xiR D := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · have h1 := A.im_neg_xi_neg τ.1 ((((s.unf σ h).1.2.1 k).2 _).1 τ.2)
    have h2 := s.xiAbs σ k τ.1
    rw [← s.xi_eq σ k] at h1
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.2 (GlobalTheory.FrameNormLie.re_xi _ _)] at h2
    rw [← h2, abs_of_pos (by simpa using h1)]
  · exact ((s.unif.isEmpty_comp h).false k).elim

namespace ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ)

def hodge : EigMet s.T.Z σ :=
  .hodge s.U (2 * Real.pi * xiR D) (mul_pos Real.two_pi_pos (xiR_pos D)) (x.eigMet σ)

variable {σ} {y : CxPts (genStr s.T.Z) σ}

theorem _root_.GlobalTheory.ShFam.FinalTheorems.exists_isHodgeFrame_iff : (∃ f, IsHodgeFrame s.U y f) ↔ ¬ LiesIn y (genBd s.T.Z) :=
  ⟨fun ⟨_, h⟩ => h.not_liesIn, exists_isHodgeFrame fun σ h => (s.unf σ h).1⟩

theorem hodge_gram {f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)} (hf : IsHodgeFrame s.U y f)
    (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram y g τ = ((2 * Real.pi * xiR D : ℝ) : ℂ) • ((f.co g τ)ᴴ * f.co g τ) :=
  hf.gram_eq (fun σ h => (s.unf σ h).1) (xiR_pos D) s.im_neg_xi g τ

theorem hodge_gram_of_liesIn (h : LiesIn y (genBd s.T.Z)) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram y g τ = x.gram y g τ := dif_neg fun h' => FinalTheorems.exists_isHodgeFrame_iff.1 h' h

theorem hodge_gram_riemann (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) (W : UnfWit (s.U σ)) {i : Fin W.F.n}
    {P : (W.F.Di i).La →+ (Fin W.g → ℂ)} (hP : IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P)
    {Hm : Matrix (Fin W.g) (Fin W.g) ℂ} (hH : IsRiem W.F i P Hm) {q : FrPt s.Xo κ.c (CAt σ)}
    {z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)} (hq : AnLie W.F i P q z) (τ : D.host.E →+* ℂ) :
    (x.hodge σ).gram (cxPt s.T.Z q) (cxFrame s.T.Z q) τ = (Real.pi : ℂ) • of fun b b' => hermForm Hm (z τ b') (z τ b) :=
  hodge_gram_eq_riemann (fun σ h => (s.unf σ h).1) (xiR_pos D) s.im_neg_xi hσ W hP hH hq τ _

theorem hodge_gram_lieFrame (L : CmList A) (k : s.Comp) {f : (s.fd k).dom} (hf : IsOrth (s.fd k) f.1) (t : D.what₂.Tau)
    (τ : D.host.E →+* ℂ) : (x.hodge κ.σ₀).gram (s.framePt k f) (s.lieFrame k f) τ =
      (hodgeC (s.fd k) (s.lab L k) t : ℂ) • 1 := by
  rw [x.hodge_gram (f := s.lieFrame k f) (isHodgeFrame_cxFrame κ.good_σ₀ hf), EigFrame.co_self, conjTranspose_one,
    Matrix.mul_one, hodgeC, Data.c, s.xiAbs, mul_left_comm, _root_.mul_assoc]

def IsMuExp (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ), ¬ LiesIn y (genBd s.T.Z) →
    ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ),
      x.r σ y ^ (-C) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ∧
        (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ≤ x.r σ y ^ C * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re

example (h : ∀ σ, x.eigMet σ = x.hodge σ) : x.IsMuExp 0 :=
  ⟨le_rfl, fun σ y _ g τ v => by simp [← h, x.eigMet_gram]⟩

def muExp : ℝ := Classical.epsilon x.IsMuExp

theorem isMuExp_muExp (h : ∃ C, x.IsMuExp C) : x.IsMuExp x.muExp := Classical.epsilon_spec h

def kap : ℝ := 2 * x.muExp + 3

theorem lt_kap : 2 * x.muExp + 2 < x.kap := by rw [kap]; linarith

open Classical in
variable (σ) in

def wt (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : ℝ :=
  if LiesIn y (genBd s.T.Z) then 0 else cutWt x.kap (max R 2) (x.r σ y)

theorem wt_mem (R : ℝ) (y : CxPts (genStr s.T.Z) σ) : x.wt σ R y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold wt
  split_ifs
  exacts [⟨le_rfl, zero_le_one⟩, cutWt_mem _ (le_max_of_le_right zero_le_two) ((Real.exp_pos 1).le.trans (x.exp_le_r σ y))]

theorem wt_eq {R : ℝ} (hR : 2 ≤ R) (h : ¬ LiesIn y (genBd s.T.Z)) : x.wt σ R y = cutWt x.kap R (x.r σ y) := by
  rw [wt, if_neg h, max_eq_left hR]

theorem wt_eq_zero {R : ℝ} (hR : 2 ≤ R) (h : LiesIn y (genBd s.T.Z) ∨ R ^ 3 ≤ x.r σ y) : x.wt σ R y = 0 := by
  by_cases h' : LiesIn y (genBd s.T.Z)
  · exact if_pos h'
  · rw [x.wt_eq hR h', cutWt_of_ge _ hR (h.resolve_left h')]

variable (σ) in

def eigMetAt : Option ℝ → EigMet s.T.Z σ
  | none => x.hodge σ
  | some R => .interp (x.wt σ R) (x.wt_mem R) (x.eigMet σ) (x.hodge σ)

end ToroidalCompactificationData

variable (x : ToroidalCompactificationData s) (Φ : s.Flag)

def metsOf : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL) := fun k R σ n => (Φ.C k).met (x.eigMetAt (embOf κ.e σ) R) n

def refMet : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n) :=
  fun k σ n => (Φ.C k).met (x.eigMet (embOf κ.e σ)) n

def rFlag : ∀ k σ, Pts (Φ.C k).Y σ → ℝ := fun k σ p => x.r (embOf κ.e σ) ((Φ.C k).down p)

variable (k : s.Comp) (R : Option ℝ) (σ : D.what₂.LL →+* ℂ) (n n' : Letter S.Dw → ℤ)

theorem posSet_metsOf : Met.posSet (metsOf x Φ k R σ n) = Set.univ := FlagCpt.posSet_met _ _

theorem posSet_refMet : Met.posSet (refMet x Φ k σ n) = Set.univ := FlagCpt.posSet_met _ _

theorem pn_metsOf_add : (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k R σ (n + n')) =
    (cxSt D.what₂.LL).pn _ σ _ ((cxSt D.what₂.LL).mAdd _ σ _ _ (metsOf x Φ k R σ n) (metsOf x Φ k R σ n')) :=
  FlagCpt.pn_met_add _ _ _

theorem pn_refMet_add : (cxSt D.what₂.LL).pn _ σ _ (refMet x Φ k σ (n + n')) =
    (cxSt D.what₂.LL).pn _ σ _ ((cxSt D.what₂.LL).mAdd _ σ _ _ (refMet x Φ k σ n) (refMet x Φ k σ n')) :=
  FlagCpt.pn_met_add _ _ _

variable {x Φ k σ n} {p : Pts (Φ.C k).Y σ}

theorem pn_metsOf {g : (Φ.C k).FrameAt p} {f : (Φ.C k).Y.Fn} {a : ℂ} (h : IsCoord (Φ.C k) p.1 g n f a) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k R σ n) ((cxSt D.what₂.LL).cx _ σ f) p =
      ‖a‖ ^ 2 * ∏ z : Letter S.Dw, grSq ((x.eigMetAt _ R).gram _ g z.1) z.2 ^ n z := FlagCpt.pn_met _ _ h

theorem pn_metsOf_none {g : (Φ.C k).FrameAt p} (hg : IsHodgeFrame s.U _ g) {f : (Φ.C k).Y.Fn} {a : ℂ}
    (h : IsCoord (Φ.C k) p.1 g n f a) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k none σ n) ((cxSt D.what₂.LL).cx _ σ f) p =
      ‖a‖ ^ 2 * ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ n z := by
  rw [pn_metsOf none h]
  refine congrArg _ (Finset.prod_congr rfl fun z _ => congrArg (· ^ n z) ?_)
  rw [ToroidalCompactificationData.eigMetAt, x.hodge_gram hg, EigFrame.co_self, conjTranspose_one, Matrix.mul_one, smul_one_eq_diagonal,
    grSq_diagonal fun _ => (mul_pos Real.two_pi_pos (xiR_pos D)).ne']

theorem metsOf_some_eq {R : ℝ} (hR : 2 ≤ R) (h : (Φ.C k).π (base p) ∈ genBd s.T.Z ∨ R ^ 3 ≤ rFlag x Φ k σ p)
    (a : (Φ.C k).Y.Fnˣ) : Met.h (metsOf x Φ k (some R) σ n) a p = Met.h (refMet x Φ k σ n) a p :=
  FlagCpt.met_congr (x.eigMetAt _ (some R)) n (G' := x.eigMet _)
    (fun g _ => EigMet.interp_gram_zero (hs := x.wt_mem R) g (x.wt_eq_zero hR h)) a

theorem exp_le_rFlag : Real.exp 1 ≤ rFlag x Φ k σ p := x.exp_le_r _ _

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

variable {D : D7}

def KitClass.Ex (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC, jC.Pinned → ∃ k d, Q A N j S κ s L jC k d

def KitClass.Loc (Q : KitClass D) : Prop :=
  ∀ A N j S κ s L jC k d, jC.Pinned → Q A N j S κ s L jC k d →
    ∃ (F : StFam S κ) (cts : Ats S κ), cts.Over jC ∧ LocSt.ofPkg k.pad = locStOf F cts

structure FamOver (Q : KitClass D) (T : Top D) (h : LawsP T) (c : ℕ) : Type 1 where
  F : SrcFam (ambOf T.Q h.pins.1)
  t : ParTie T.Q h.pins.1 F
  exp : F.κs.l.A = 15 ^ c
  L : CmList (ambOf T.Q h.pins.1)
  jC : JC D
  pin : jC.Pinned
  k : Kits F L (cxSt D.what₂.LL) jC ngTrue
  d : ∀ N j hN hj κ, (F.src N j hN hj κ).Comp → D.what₂.Tau → ℝ
  mem : ∀ N j hN hj κ, Q _ N j _ κ (F.src N j hN hj κ) L jC (k N j hN hj κ) (d N j hN hj κ)
  hg : F.κg.primes = Finset.univ.image D.host.g
  P : FormsOver (cutSt _) (resSt _) k
  forms : FormsAre h t (cutSt _) (resSt _) k P
  prov : ∃ (I : Type) (dat : I → Dat D (Lv (ambOf T.Q h.pins.1))) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I),
    (∀ w : Dat D (Lv (ambOf T.Q h.pins.1)), w.Indef → ∃ i, (dat i).N = w.N ∧ (dat i).j = w.j ∧ (dat i).κ = w.κ) ∧
    (∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) ∧
    T.G.P = indefiniteDataFamily (shimOf (cutSt _) (resSt _) k) I dat hI ∧ ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)

namespace FamOver

variable {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ} (Φ : FamOver Q T h c)

def fam : ShimFam D (geoTrue D.what₂.LL) (Lv (ambOf T.Q h.pins.1)) := famOf (cutSt _) (resSt _) Φ.k Φ.hg Φ.P

def dH (j : ℕ) : (Φ.fam.Uw j).Comp → D.what₂.Tau → ℝ :=
  Φ.d _ _ (datW D Φ.F.κg j).two_le (datW D Φ.F.κg j).j_le (datW D Φ.F.κg j).κ

theorem locTie : LocTie h Φ.k := by
  obtain ⟨I, dat, hI, iW, -, h1, h2, h3⟩ := Φ.prov
  exact LocTie.localTie_of_provisional (cutSt _) (resSt _) h1 h2 h3

def Reads (X₀ : DivX D)
    (iM : ∀ j (a : (Φ.fam.Uw j).Comp), (X₀.MjH j).V →ₗ[D.what₂.LL] (geoTrue D.what₂.LL).Fn ((Φ.fam.Uw j).alg.Yv a)) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (∀ x, (∀ a, iM j a x = 0) → x = 0) ∧
    ∃ (w : WeightFamilies.Wt D j) (s : Submodule Φ.P.KO (Φ.P.Cusp j w)) (φ : s →ₛₗ[Φ.P.sig0] D.what₂.Mj j),
      w.n = D.R.nV ∧ Formalism.L2.Geo.wtOf w = DV.kapW D j ∧ Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
      (∀ x : s, (x : Φ.P.Cusp j w) ∈ Φ.P.Mlat j w ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
      (∃ vol : ℝ, ∀ x : s, ‖φ x‖ = Real.sqrt (vol * dimKap D j) * Φ.P.l2NormAlt j w Φ.P.sig0 x) ∧
      ∀ (f : s) x, X₀.jM j x = φ f → ∀ a, iM j a x = Φ.P.cmp j w a f

end FamOver

def IsGeoOf (Q : KitClass D) (J : Core D) (c : ℕ) (X : DivX D) : Prop :=
  ∃ (T : Top D) (h : LawsP T) (Φ : FamOver Q T h c) (X₀ : DivX D) (iM : _) (hiM : _), T.toCore = J ∧
    X = GlobalTheory.VarietyModelRecord.record X₀ Φ.fam iM hiM Φ.dH ∧ Φ.Reads X₀ iM ∧ X.vdd = fun p _ => vDiff D.host.E p

def SameSurf (X Y : DivX D) : Prop :=
  X.Surf = Y.Surf ∧ HEq X.surfCh2 Y.surfCh2 ∧ HEq X.surfDegOm Y.surfDegOm ∧ X.SurfFp = Y.SurfFp ∧ HEq X.surfFpCh2 Y.surfFpCh2

def LargeFor (Q : Par D) (h : Q.PinHost) (c : ℕ) : Prop :=
  IsLargeFor (ambOf Q h) (D.host.g 0 * D.host.g 1) ∧ IsLargeFor (ambOf Q h) (Nat.lcm (D.host.g 0 * D.host.g 1) (15 ^ c))

end GlobalTheory.ShFam
end
end

