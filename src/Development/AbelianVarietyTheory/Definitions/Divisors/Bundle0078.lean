import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev RootFn (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type 1 :=
  ∀ (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D' → D'

variable {A : Over (Sp R)} [GrpObj A]

variable (A) in

def HasRoots (n : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
    (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ n = spOver ψ ≫ x

def IsTorsChar (n : ℕ) (b : Fn0 A) : Prop :=
  (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (w : Pt A D),
    w ^ n = 1 → b D' (spOver φ ≫ w) = φ (b D w)) ∧
  ∀ (D : Type) [CommRing D] [Algebra R D] (w w' : Pt A D), w ^ n = 1 → w' ^ n = 1 → b D (w * w') = b D w + b D w'

def IsSec (n : ℕ) (b : Fn0 A) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) (s : RootFn A D) : Prop :=
  (∀ (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D')
    (ψ : D' →ₐ[R] D'') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z)) ∧
  ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'),
    z ^ n = spOver φ ≫ x → w ^ n = 1 → s D' φ (z * w) = s D' φ z + b D' w

abbrev SecFam (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → RootFn X D

def IsSecDiff (n : ℕ) (S : SecFam A) (u : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E) (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
    ψ (u D D' φ x) = S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z

def IsSecAdd (n : ℕ) (S : SecFam A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (z w : Pt A E), z ^ n = spOver ψ ≫ x → w ^ n = spOver ψ ≫ y →
    ψ (g D x y) = S D (x * y) E ψ (z * w) - S D x E ψ z - S D y E ψ w

theorem hasRoots_one : HasRoots A 1 := fun D _ _ x ↦
  ⟨D, inferInstance, inferInstance, AlgHom.id R D, x, RingHom.FaithfullyFlat.of_bijective Function.bijective_id, by
    rw [pow_one, spOver_id, Category.id_comp]⟩

theorem isTorsChar_zero (n : ℕ) : IsTorsChar (A := A) n fun _ _ _ _ ↦ 0 :=
  ⟨fun _ _ _ _ _ _ φ _ _ ↦ (map_zero φ).symm, fun _ _ _ _ _ _ _ ↦ (add_zero _).symm⟩

theorem isSec_zero (n : ℕ) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    IsSec n (fun _ _ _ _ ↦ 0) x fun _ _ _ _ _ ↦ 0 :=
  ⟨fun _ _ _ _ _ _ _ ψ _ _ ↦ (map_zero ψ).symm, fun _ _ _ _ _ _ _ _ ↦ (add_zero _).symm⟩

variable (R) in

def diagSum (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) : D ⊗[R] D →ₗ[R] D :=
  ∑ i ∈ Finset.range m, (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D)
    fun _ _ ↦ Commute.all _ _).toLinearMap

theorem diagSum_tmul (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) (a b : D) :
    diagSum R D m (a ⊗ₜ b) = ∑ i ∈ Finset.range m, mulBy R D i a * b := by
  simp [diagSum, LinearMap.sum_apply]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChernReg GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovHt GlobalTheory.LieHt

namespace GlobalTheory.HeightParts

def KernelSt : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (a : ChartForm p σ d) (E : ChartMap p σ d), IsKaehlerForm (AnRead.all p σ d) a → IsExph a E →
    ∀ (c : AlgChart p σ d) (Kc : Set (V d)), IsCompact Kc → Kc ⊆ c.e.target →
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.ball (c.e y) (C * t) ⊆ c.e.target ∧
      (∀ ξ, a c y ξ < 1 → E c y (t • ξ) ∈ c.e.source ∧ c.e (E c y (t • ξ)) ∈ Metric.ball (c.e y) (C * t)) ∧
      ∀ f : CxPts p σ → ℝ, IntegrableOn (f ∘ c.e.symm) (Metric.ball (c.e y) (C * t)) →
        Integrable (fun ξ => f (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)) ∧
        |rho a E f y t| ≤ C / t ^ (2 * d) * ∫ v in Metric.ball (c.e y) (C * t), |f (c.e.symm v)|

def OnCore (Q : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s), PolOf x O.Φ → Prop) : Prop :=
  ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) →
    (∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H)) → Q D O x P

abbrev psi {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N) :
    Pts (O.var c) σ → ℝ := phW (metsOf x O.Φ) (refMet x O.Φ) c σ (fund τ i)

def SizeSt : Prop := OnCore fun _ O x _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ c σ τ i, ∀ y ∈ offBd O.Φ c σ,
  -(C * Real.log (O.met.r c σ y)) ≤ psi O x c σ τ i y ∧ psi O x c σ τ i y ≤ C

def ConstSt : Prop := OnCore fun _ O x P => CommonConst (metsOf x O.Φ) (refMet x O.Φ) P.om P.exph P.a P.K P.δ

def GradSt : Prop := OnCore fun _ O x P => ∃ C μ : ℝ, 0 ≤ C ∧ 0 ≤ μ ∧ ∀ c σ τ i (ch : AlgChart (O.var c).str σ (O.var c).dim),
  ∀ y ∈ ch.e.source, y ∈ offBd O.Φ c σ → DifferentiableAt ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ∧
    ∀ ξ : V (O.var c).dim, |fderiv ℝ (psi O x c σ τ i ∘ ch.e.symm) (ch.e y) ξ| ≤
      C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp)

def LowSt : Prop := OnCore fun _ O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∀ y,
    -(C * Real.log (Real.log (1 / t))) ≤ P.regFund c σ τ i t y ∧ P.regFund c σ τ i t y ≤ C ∧
      (y ∈ offBd O.Φ c σ → psi O x c σ τ i y ≤ P.regFund c σ τ i t y)

def HessSt : Prop := OnCore fun _ O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ((O.var c).an σ).SmoothOn Set.univ (P.regFund c σ τ i t) ∧
    ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      -(C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) * P.om c σ ch y ξ) ≤
        thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (P.regFund c σ τ i t) ch y ξ

def CloseSt : Prop := OnCore fun _ O x P => ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
  ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∀ y ∈ offBd O.Φ c σ, O.met.r c σ y ≤ Real.log (1 / t) →
    P.regFund c σ τ i t y ≤ psi O x c σ τ i y + t ^ ((1 : ℝ) / 3)

def CentSt : Prop := OnCore fun _ O x _ => ∀ c σ τ (i : Fin O.N), (i : ℕ) + 1 = O.N →
  ((O.var c).an σ).SmoothOn Set.univ (extBd O.Φ (psi O x c σ τ i)) ∧
    ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      thW (refMet x O.Φ) c σ (fund τ i) ch y ξ + ddcForm (extBd O.Φ (psi O x c σ τ i)) ch y ξ = 0

section Heights

variable {D : D7} (O : Setup D) (m : ∀ c, Mets (O.Φ.C c) (cxSt D.what₂.LL)) (y : Pt O.s)

def stepHt (τ : D.host.E →+* ℂ) (k : ℕ) : ℝ :=
  -∑ i ∈ Finset.range k, (adlOf (O.Φ.C _) (m _) (Finsupp.single (ArIn.ind ∅, none, .inl (τ, i)) 1)).ht (basePt O.Φ y)

def omHt : ℝ := (adlOf (O.Φ.C _) (m _) (detOmSym D.host.E (D.R.f * O.N))).ht (basePt O.Φ y)

def ReadsAt {K : Type} [Field K] [NumberField K] {g : ℕ} (h : HermFam K (Fin g → K)) (L : Submodule (𝓞 K) (Fin g → K))
    (C : ℝ) : Prop :=
  |deg h L + omHt O m y| ≤ C ∧ ∀ τ, ∀ k ≤ O.S.Dw.mult τ, ∃ W ≤ L, latRank K W = k ∧ |deg h W + stepHt O m y τ k| ≤ C

abbrev ref0 : ∀ c, Mets (O.Φ.C c) (cxSt D.what₂.LL) := fun c _ => O.met.h0 c

example : omHt O O.met.hm y = O.faltAt _ (basePt O.Φ y) := rfl

end Heights

def PtInt : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int →
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)),
    F.P₀.g = D.R.f * O.N ∧ F.IsHerm h ∧ ReadsAt O O.met.hm y h F.lieLat C

def PtBd : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Pt O.s, y ∉ H.int →
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (r : ℕ)
    (ε : Fin r → Fin (D.R.f * O.N) → K) (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)),
    F.IsHerm h' ∧ ReadsAt O (ref0 O) y h L C ∧ TorusExt h L ε q h' F.lieLat C

def StepInt : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Pt O.s, y ∈ H.int →
  -H.falt y ≤ C * Real.log (2 + max (H.falt y) 0) ∧
    ∀ τ, ∀ k ≤ O.S.Dw.mult τ, -(C * Real.log (2 + max (H.falt y) 0)) ≤ stepHt O O.met.hm y τ k

def StepBd : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Pt O.s, y ∉ H.int → -C ≤ H.hA y ∧
  ∀ τ, ∀ k ≤ O.S.Dw.mult τ, -(C * Real.log (2 + C + H.hA y)) - C ≤ stepHt O (ref0 O) y τ k

open Classical in

def FlatHt : Prop := OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ (τ : D.what₂.Tau) (y : Pt O.s),
  |H.h0 (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C ∧ (y ∈ H.int → |H.hH (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ C)

def OmCmp : Prop := OnObj fun _ O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, |omHt O (ref0 O) y| ≤ C * (|H.hA y| + 1)

def FaltSt : Prop := OnObj fun _ _ _ _ H _ => HtFalt H

end GlobalTheory.HeightParts

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotExistsDataOfNotSymm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautBaseModel

theorem exists_tautBase {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (b : o →+* W)
    (P : PolAV (Sp W)) (r : ℕ) (x : Fin r → (𝟙_ (Over (Sp W)) ⟶ P.A)) :
    ∃ T : TautBase o W, T.b = b ∧ T.g = P.g ∧ ∃ (hB : T.B = P.A) (hr : T.r = r), HEq T.grp P.grp ∧ HEq T.M.L P.L ∧
      ∀ i : Fin T.r, HEq (T.c₀ (Pi.single i 1)) (x (Fin.cast hr i)) := by
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let M : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  have hC : CubeSt := GlobalTheory.abelianSchemeLaws_all.1.cube
  obtain ⟨cub⟩ := (hC (Sp W) P M rfl).1
  let c : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ P.A) := fun a => ∏ i, x i ^ a i
  have hc : ∀ a a', c (a + a') = c a * c a' := fun a a' => by
    simp only [c, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  obtain ⟨τ, h₁, h₂, h₃⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c hc
  refine ⟨{ b := b, B := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, M := M, cub := cub,
            ample := P.ample, ktriv := P.ktriv, r := r, c₀ := c, c₀_add := hc, τ₀ := τ, τ₀_gen := h₁,
            τ₀_symm := h₂, τ₀_add := h₃ }, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, fun i => heq_of_eq ?_⟩
  show ∏ j, x j ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) j = x i
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp)]
  simp

theorem exists_tautBase_curve {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (b : o →+* W)
    (h37 : IsUnit (37 : W)) : ∃ T : TautBase o W, T.b = b ∧ T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  let E : _root_.WeierstrassCurve W := ⟨0, 0, 1, -1, 0⟩
  haveI : E.IsElliptic := ⟨by
    have : E.Δ = 37 := by
      norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
    rw [this]
    exact h37⟩
  have he : E.toAffine.Equation 0 0 := by
    rw [WeierstrassCurve.Affine.equation_iff]; simp [E]
  let P : PolAV (Sp W) := GlobalTheory.WeierstrassCurve.ellPolAV E
  let x : 𝟙_ (Over (Sp W)) ⟶ P.A :=
    Over.homMk (GlobalTheory.WeierstrassCurve.pt E (A := W) ![0, 0, 1] (GlobalTheory.WeierstrassCurve.isUnimodularSol_some he))
      ((GlobalTheory.WeierstrassCurve.pt_toSpec E _ _).trans (Spec.map_id _))
  have hx : x ≠ 1 := fun e => GlobalTheory.WeierstrassCurve.pt_some_ne_zero E he (by
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    rw [← GlobalTheory.WeierstrassCurve.eSec_ellPolAV E, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rfl)
  obtain ⟨T, hb, hg, hB, hr, hgrp, hL, hc⟩ := exists_tautBase b P 1 (fun _ => x)
  refine ⟨T, hb, hg, hr, ?_⟩
  obtain ⟨b', B, isAb, g, sm, M, cub, am, kt, r, c, ca, τ, τg, τs, τa⟩ := T
  dsimp only at hg hB hr hgrp hL hc
  subst hB hr
  cases hgrp
  refine ⟨?_, Pi.single 0 1, fun e => hx ((eq_of_heq (hc 0)).symm.trans e)⟩
  show ∀ t : M.L.Gen, ¬ t.IsGen
  rw [eq_of_heq hL]
  exact GlobalTheory.WeierstrassCurve.not_isGen_ellPolAV E

theorem exists_tautBase_rat : ∃ T : TautBase ℤ ℚ, T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  obtain ⟨T, -, h⟩ := exists_tautBase_curve (Int.castRingHom ℚ) (Ne.isUnit (by norm_num))
  exact ⟨T, h⟩

theorem exists_tautBase_two_adic : ∃ T : TautBase ℤ ℤ_[2], T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  have h : IsUnit (37 : ℤ_[2]) := by
    have := (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 37)).2 (by norm_num)
    exact PadicInt.isUnit_iff.2 (by exact_mod_cast this)
  obtain ⟨T, -, h⟩ := exists_tautBase_curve (Int.castRingHom ℤ_[2]) h
  exact ⟨T, h⟩

variable {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)

theorem c₀_zero : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero (a : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 a) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem τ₀_add_right (a a' a'' : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) :
    val (T.τ₀ a (a' + a'')) (𝟙 _) z J * cubV T.cub z J (T.c₀ a) (T.c₀ a') (T.c₀ a'') =
      val (T.τ₀ a a') (𝟙 _) z J * val (T.τ₀ a a'') (𝟙 _) z J := by
  have h := isCub_cubV T.cub hJ
  rw [T.τ₀_symm a _ z J hJ, T.τ₀_symm a a' z J hJ, T.τ₀_symm a a'' z J hJ, h.s01, h.s12]
  exact T.τ₀_add a' a'' a z J hJ

theorem exists_good_choice : ∃ (z : (𝟙_ (Over (Sp W))).left) (J : _), Good T.M.L z J := by
  choose J hJ using fun ψ : (𝟙_ (Over (Sp W))).left ⟶ T.B.left => exists_chart T.M.isLB (ψ (closedPoint W))
  exact ⟨closedPoint W, J, hJ⟩

theorem val_τ₀_torus (b : o →+* W) (r : ℕ) (u : Γ((𝟙_ (Over (Sp W))).left, ⊤)ˣ)
    (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ a a', β a a' = β a' a) (a a' : Fin r → ℤ) (z J)
    (hJ : Good (TautBase.torus b r u β hβ).M.L z J) :
    val ((TautBase.torus b r u β hβ).τ₀ a a') (𝟙 _) z J = gm (𝟙 _) z ⊤ (u ^ β a a') :=
  gm_res _ z _ (hJ.mem _ _) _

theorem prod_lamPts_symm {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {Z : Over S} (x y : Z ⟶ B) {U : Type}
    [CommGroup U] (h : (Z.left ⟶ B.left) → U) : ∏ i, h (lamPts x y i) ^ negε i = ∏ i, h (lamPts y x i) ^ negε i := by
  simp only [Fin.prod_univ_four]
  show h (x * y).left ^ (-1 : ℤ) * h x.left ^ (1 : ℤ) * h y.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ) =
    h (y * x).left ^ (-1 : ℤ) * h y.left ^ (1 : ℤ) * h x.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ)
  rw [mul_comm y x, mul_right_comm _ (h x.left ^ (1 : ℤ))]

open InhTate in

theorem tauCoord_symm {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X)
    (k k' : (FractionRing R)ˣ) (h : Q.TauCoord a b k) (h' : Q.TauCoord b a k') :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (k : FractionRing R) * algebraMap R _ x = k' * algebraMap R _ x' := by
  obtain ⟨u, hu, e⟩ := h
  obtain ⟨u', hu', e'⟩ := h'
  obtain ⟨jj, hjj⟩ := GlobalTheory.TauLocal.exists_chart_all Q.M
  have key : ∀ (p q : 𝟙_ (Over (Sp R)) ⟶ Q.B) (t : LB.Gen (LB.LinComb Q.M.L (lamPts p q) negε)), t.IsGen →
      ∃ w : Γ(Sp R, ⊤)ˣ, ∀ z J, Good Q.M.L z J → val t (toUnit (TK R)).left z J =
        gm (𝟙 (TK R).left) z ⊤ (pullTop (jK R) w) * ∏ i, (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
          (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ))) (lamPts p q i) ^ negε i := by
    intro p q t ht
    have htop : (⊤ : (𝟙_ (Over (Sp R))).left.Opens) ≤ LB.wchart Q.M.L (lamPts p q) (fun i => jj (lamPts p q i)) :=
      fun y _ => Set.mem_iInter.2 fun i => hjj _ y
    refine ⟨res htop (t.s (fun i => jj (lamPts p q i))), fun z J hJ => ?_⟩
    refine (gen_trans ht _ z (hJ.mem _ _) (htop trivial)).trans ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gm_res _ z htop trivial _).symm.trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK R) z ⊤ trivial _).symm)
    rfl
  obtain ⟨w, hw⟩ := key _ _ u hu
  obtain ⟨w', hw'⟩ := key _ _ u' hu'
  have k₁ : unitOn k * pullTop (jK R) w = unitOn k' * pullTop (jK R) w' := GlobalTheory.TauLocal.eq_of_gm Q.M.isLB fun z J hJ => by
    have s := Q.tau_symm a b z J hJ
    rw [e z J hJ, e' z J hJ, hw z J hJ, hw' z J hJ, ← _root_.mul_assoc, ← _root_.mul_assoc] at s
    rw [map_mul, map_mul]
    refine mul_right_cancel (s.trans (congrArg₂ (· * ·) rfl ?_))
    exact prod_lamPts_symm (Q.c b) (Q.c a) (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
      (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ)))
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w'.val,
    w.isUnit.map _, w'.isUnit.map _, ?_⟩
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w'))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k'.val

theorem not_exists_data_of_not_symm [IsDomain (MvPowerSeries (Fin 1) ℚ)] :
    ∃ ε : Fin 1 → LinearMap.BilinForm ℤ (Fin 2 → ℤ), ¬ ∃ (Q : Data (MvPowerSeries (Fin 1) ℚ)) (e : Q.X ≃+ (Fin 2 → ℤ)),
      ∀ a b, ∃ k : (FractionRing (MvPowerSeries (Fin 1) ℚ))ˣ,
        (k : FractionRing (MvPowerSeries (Fin 1) ℚ)) = Taut.perFactor ℚ 1 1 1 2 ε (e a) (e b) ∧ Q.TauCoord a b k := by
  refine ⟨fun _ => (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1), fun ⟨Q, e, h⟩ => ?_⟩
  obtain ⟨k, hk, c⟩ := h (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1))
  obtain ⟨k', hk', c'⟩ := h (e.symm (Pi.single 1 1)) (e.symm (Pi.single 0 1))
  obtain ⟨x, x', -, hx', e₁⟩ := tauCoord_symm Q _ _ k k' c c'
  rw [hk, hk'] at e₁
  simp [Taut.perFactor, Taut.coordT] at e₁
  rw [← map_mul] at e₁
  have e₂ := IsFractionRing.injective _ _ e₁
  have := (e₂ ▸ hx').map (MvPowerSeries.constantCoeff (σ := Fin 1) (R := ℚ))
  simp at this

theorem not_forall_exists_data : ¬ ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (T : TautBase o W) (N m n : ℕ) [IsDomain (MvPowerSeries (Fin N) W)]
    (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ)),
    ∃ (Q : Data (MvPowerSeries (Fin N) W)) (e : Q.X ≃+ (Fin T.r → ℤ)) (β : Q.B.left ⟶ T.B.left),
      IsGrpPullback Q.B T.B (spMap MvPowerSeries.C) β ∧
      (∀ a, (Q.c a).left ≫ β = spMap MvPowerSeries.C ≫ (T.c₀ (e a)).left) ∧
      ∀ a b, ∃ k : (FractionRing (MvPowerSeries (Fin N) W))ˣ,
        (k : FractionRing (MvPowerSeries (Fin N) W)) = Taut.perFactor W m N n T.r ε (e a) (e b) ∧ Q.TauCoord a b k := by
  intro h
  haveI : IsDomain (MvPowerSeries (Fin 1) ℚ) := NoZeroDivisors.to_isDomain _
  obtain ⟨ε, hε⟩ := not_exists_data_of_not_symm
  obtain ⟨Q, e, -, -, -, h₁⟩ := h (TautBase.torus (RingHom.id ℚ) 2 1 0 (fun _ _ => rfl)) 1 1 1 ε
  exact hε ⟨Q, e, h₁⟩

end GlobalTheory.PolDeg.TautBaseModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def Fn1.pull {X Y : Over (Sp R)} (q : Y ⟶ X) (u : Fn1 X) : Fn1 Y := fun D _ _ D' _ _ φ y ↦ u D D' φ (y ≫ q)

section Alg

variable {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']

def ptAlg (z : Pt (SpAlg R D) E) : D →ₐ[R] E :=
  { (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom with
    commutes' := fun r ↦ by
      have h : CommRingCat.ofHom (algebraMap R D) ≫
          Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left =
          CommRingCat.ofHom (algebraMap R E) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact Over.w z
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h }

theorem spOver_ptAlg (z : Pt (SpAlg R D) E) : spOver (ptAlg z) = z :=
  Over.OverMorphism.ext (Spec.map_preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left)

theorem ptAlg_spOver (α : D →ₐ[R] E) : ptAlg (spOver α) = α := by
  refine AlgHom.ext fun r ↦ ?_
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) (Spec.preimage_map (CommRingCat.ofHom (α : D →+* E)))

theorem ptAlg_comp (ψ : E →ₐ[R] E') (z : Pt (SpAlg R D) E) : ptAlg (spOver ψ ≫ z) = ψ.comp (ptAlg z) := by
  conv_lhs => rw [← spOver_ptAlg z, spOver_comp]
  exact ptAlg_spOver _

def epsEv (e : Pt (epsR R) E) : DualNumber E →ₐ[R] E :=
  DualNumber.lift ⟨(AlgHom.id R E, ptAlg (D := DualNumber R) e DualNumber.eps), by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩

end Alg

section Param

variable {A B : Over (Sp R)} {J : Type} [Fintype J] {D : Type} [CommRing D] [Algebra R D]

def sumMul (d : J → D) (b : J → Fn1 B) : Fn1 (SpAlg R D ⊗ B) := fun E _ _ E' _ _ ψ z ↦
  ∑ i, ψ (ptAlg (z ≫ fst _ _) (d i)) * b i E E' ψ (z ≫ snd _ _)

def IsCupCob {K : Type} (W : K → (A ⊗ B).left.Opens) (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) : Prop :=
  ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
    [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), Sm W z →
    ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) =
      ∑ i, ψ (a i E E' φ (z ≫ fst _ _)) * b i E' E'' ψ (spOver φ ≫ z ≫ snd _ _)

def parCoc (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (x : Pt A D) : Fn1 (SpAlg R D ⊗ B) :=
  fun E _ _ E' _ _ ψ z ↦ n E E' ψ (z ≫ x ▷ B) -
    ∑ i, ψ (a i D E (ptAlg (z ≫ fst _ _)) x) * b i E E' ψ (z ≫ snd _ _)

def parCov {K : Type} (W : K → (A ⊗ B).left.Opens) (x : Pt A D) : K → (SpAlg R D ⊗ B).left.Opens :=
  fun i ↦ (x ▷ B).left ⁻¹ᵁ W i

end Param

section Change

variable {R' : Type} [CommRing R'] (σ : R →+* R')

@[reducible] def algVia (E : Type) [CommRing E] [Algebra R' E] : Algebra R E :=
  ((algebraMap R' E).comp σ).toAlgebra

def homVia {E E' : Type} [CommRing E] [Algebra R' E] [CommRing E'] [Algebra R' E'] (ψ : E →ₐ[R'] E') :
    @AlgHom R E E' _ _ _ (algVia σ E) (algVia σ E') :=
  @AlgHom.mk R E E' _ _ _ (algVia σ E) (algVia σ E') (ψ : E →+* E') fun r ↦ ψ.commutes (σ r)

variable {σ} {X : Over (Sp R)} {X' : Over (Sp R')} {q : X'.left ⟶ X.left}

def ptVia (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E : Type} [CommRing E] [Algebra R' E] (y : Pt X' E) :
    @Pt R _ X E _ (algVia σ E) :=
  Over.homMk (y.left ≫ q) (by
    have h : y.left ≫ X'.hom = spMap (algebraMap R' E) := Over.w y
    change (y.left ≫ q) ≫ X.hom = spMap ((algebraMap R' E).comp σ)
    rw [Category.assoc, w, ← Category.assoc, h, Cris.spMap_comp])

def bcPull (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) : Fn1 X' := fun E _ _ E' _ _ ψ y ↦
  @u E _ (algVia σ E) E' _ (algVia σ E') (homVia σ ψ) (ptVia w y)

end Change

section Gen

variable {X Y : Over (Sp R)}

def IsPtGen (L : LB X.left) (q : Y ⟶ X)
    (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → IsUnit (t E z i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E)
    (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → t E' (spOver ψ ≫ z) i = ψ (t E z i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i j : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i →
    ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U j → t E z i = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val * t E z j

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def IsEpsGen (P : LB (A ⊗ B).left) (v : epsR R ⟶ B)
    (T : ∀ (E : Type) [CommRing E] [Algebra R E], Pt A E → P.ι → DualNumber E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → IsUnit (T E x i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (x : Pt A E)
    (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → T E' (spOver ψ ≫ x) i = epsHom ψ (T E x i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i j : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
    ⊤ ≤ x.left ⁻¹ᵁ chartsA P j → T E x i = evU (ptV v x).left (P.U i ⊓ P.U j) (P.g i j).val * T E x j

end Gen

end GlobalTheory.PtExt
end
end

