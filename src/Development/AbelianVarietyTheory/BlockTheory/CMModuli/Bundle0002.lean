import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialDifferential
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PolarizationCorrespondence
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.AbelianLocusModels
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsIntegersOf (V C : Type) [CommRing V] [NormedField C] [Algebra V C] : Prop :=
  Function.Injective (algebraMap V C) ∧ ∀ x : C, (∃ a : V, algebraMap V C a = x) ↔ ‖x‖ ≤ 1

example (p : ℕ) [Fact p.Prime] : IsIntegersOf ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val_injective, fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩⟩

def primeToPart (p n : ℕ) : ℕ := n / p ^ n.factorization p

example : primeToPart 3 45 = 5 := by
  have h : (45 : ℕ).factorization 3 = 2 := by
    rw [show (45 : ℕ) = 3 ^ 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num), Nat.Prime.factorization (by norm_num)]
    simp
  rw [primeToPart, h]
  norm_num

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def AbelianLocusLevels (p : ℕ) (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧
    (∀ a : D.La, primeToPart p l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → Y.Extends U (Y.oF.eta a)) ∧
    (∀ a : D.La, (∃ b : D.La, primeToPart p l.A • a = l.A • b) → Y.Extends U (Y.oF.etaA a))

def HasGoodReduction (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K]
    (y : Sp K ⟶ Xo.XF c) : Prop :=
  ∃ (B : Over (Sp V)) (_ : GrpObj B) (L : LB B.left),
    IsAbelianScheme B ∧ L.IsLB ∧ ReciprocityTheory.ChartRestriction.G.Out.RelAmple B L ∧
    ∃ (Ay : Over (Sp K)) (_ : GrpObj Ay) (φ : Ay.left ⟶ Y.oF.t.G.left) (ψ : Ay.left ⟶ B.left),
      IsGrpPullback Ay Y.oF.t.G y φ ∧ IsGrpPullback Ay B (spMap (algebraMap V K)) ψ ∧
      LBIso (Y.oF.t.PP.L.pull φ) (L.pull ψ)

def GoodPointsExtend (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (γ : O →+* V) (y : Sp K ⟶ Xo.XF c),
    y ≫ pullback.snd _ _ ≫ spMap β = spMap (algebraMap V K) ≫ spMap γ →
    HasGoodReduction Y V K y →
    ∃ yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap γ ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j ∧
      Set.range yt ⊆ abLocus Y.t.G

structure OneModel (p : ℕ) (Y : Model Xo c β) : Prop where

  acts : Y.LevelActs

  descends : l.A = 1 → Y.Descends

  push : PushInvertible Y.t.G Y.t.PP.L

  abLevels : AbelianLocusLevels p Y

  extDVR : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K],
    GoodPointsExtend Y V K

  extInt : ∀ (V C : Type) [CommRing V] [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], ‖(p : C)‖ < 1 → IsIntegersOf V C → GoodPointsExtend Y V C

end GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicWedgeNormPeriods
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
open scoped Real

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods

abbrev Rule : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyInput K → Kˣ

def IsMultiple {R : Type} [CommRing R] (A : Over (Sp R)) {L : LB A.left} (c : R) (s s' : LB.Sec L) : Prop :=
  ∀ i, s'.f i =
    (A.hom.appLE ⊤ (L.U i) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * s.f i

def reframe {R : Type} [CommRing R] (x : KeyInput R) (th : LB.Sec x.P.L) (hth : NonzeroOnFibres x.P.A th)
    (b : Fin x.P.g → Tan x.P.A) (hb : IsLieBasis b) : KeyInput R :=
  { x with th := th, th_ne := hth, b := b, b_basis := hb }

example {R : Type} [CommRing R] (x : KeyInput R) : reframe x x.th x.th_ne x.b x.b_basis = x := rfl

example {R : Type} [CommRing R] (A : Over (Sp R)) {L : LB A.left} (s : LB.Sec L) : IsMultiple A 1 s s := by
  intro i
  simp

def Homogeneous (ka : Rule) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (x : KeyInput K)
    (th : LB.Sec x.P.L) (hth : NonzeroOnFibres x.P.A th) (b : Fin x.P.g → Tan x.P.A) (hb : IsLieBasis b)
    (c : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K),
    IsMultiple x.P.A c x.th th → (∀ i, b i = linComb (M i) x.b) →
    (ka K (reframe x th hth b hb) : K) * c ^ 8 = (ka K x : K) * M.det ^ 4

def Functorial (ka : Rule) : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K')
    (x : KeyInput K) (x' : KeyInput K'), IsBaseChange f x x' → (ka K' x' : K') = f (ka K x : K)

def Integral (ka : Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (y : KeyInput R) (x : KeyInput K),
    IsBaseChange (algebraMap R K) y x →
    ∃ u : Rˣ, algebraMap R K (u : R) = (ka K x : K) ∧
      ∀ (k : Type) [Field k] [CharZero k] (f : R →+* k), IsLocalHom f →
        ∀ x₀ : KeyInput k, IsBaseChange f y x₀ → (ka k x₀ : k) = f (u : R)

def IsImage {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g) (w : Fin g → ℂ) (v : Tan A) : Prop :=
  ∃ v' : EpsPt A, v'.mor = v.1.left ∧ E.IsDiff w v'

def HasPeriods {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g) (τ : Siegel g) : Prop :=
  ∀ z : Fin g → ℂ, z ∈ E.lat ↔
    ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.1.mulVec (fun i => (n i : ℂ))

def IsHalfIntegral {g : ℕ} (a : Fin g → ℝ) : Prop := ∀ i, ∃ n : ℤ, 2 * a i = n

def ThetaValue (ka : Rule) : Prop :=
  ∀ (x : KeyInput ℂ) (F : Unif x.P.A x.P.L x.P.g) (τ : Siegel x.P.g) (a b : Fin x.P.g → ℝ)
    (w : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
    HasPeriods F.toExp τ → IsHalfIntegral a → IsHalfIntegral b →
    F.IsRig x.rig → F.IsSec x.th (fun z => theta a b z τ) →
    (∀ i, IsImage F.toExp (w i) (x.b i)) → (2 * π * Complex.I) ^ x.P.g * w.det = 1 →
    ka ℂ x = 1

def cubNorm_sq {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (θ : (Fin g → ℂ) → ℂ)
    (z : Fin g → ℂ) : ℝ :=
  ‖θ z‖ ^ 2 * Real.exp (-(π * (D.H z z).re))

def wedgeNorm_sq {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (w : Fin g → Fin g → ℂ) : ℝ :=
  (Matrix.of fun i j => (π : ℂ) * D.H (w i) (w j)).det.re

example {La : Submodule ℤ (Fin 1 → ℂ)} (D : AHDatum La) (w : Fin 1 → Fin 1 → ℂ) :
    wedgeNorm_sq D w = π * (D.H (w 0) (w 0)).re := by
  simp [wedgeNorm_sq]

def NormIdentity (ka : Rule) : Prop :=
  ∀ (x : KeyInput ℂ) (F : Unif x.P.A x.P.L x.P.g) (D : AHDatum F.toExp.lat) (θ : (Fin x.P.g → ℂ) → ℂ)
    (w : Fin x.P.g → Fin x.P.g → ℂ) (μ : Measure (Fin x.P.g → ℂ)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (Fin x.P.g → ℂ)),
    F.IsAH D → F.IsRig x.rig → F.IsSec x.th θ → (∀ i, IsImage F.toExp (w i) (x.b i)) →
    IsAddFundamentalDomain F.toExp.lat 𝓕 μ → μ 𝓕 = 1 →
    ‖(ka ℂ x : ℂ)‖ * (∫ z in 𝓕, cubNorm_sq D θ z ∂μ) ^ 4 = (2 * π) ^ (2 * x.P.g) * wedgeNorm_sq D w ^ 2

def IsKeyRule (ka : Rule) : Prop :=
  Homogeneous ka ∧ Functorial ka ∧ Integral ka ∧ ThetaValue ka ∧ NormIdentity ka

def KeyFormula : Prop := ∃ ka : Rule, IsKeyRule ka

end GlobalTheory.IndefiniteRowSideFullHecke.CubicWedgeNormPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.HeckeIsogenyKernels
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)

def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'

section Fibre

variable {k : Type} [Field k]

abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G

def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1

def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x

def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i

def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}

def IsHeckeIsogeny {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp k ⟶ Sp B}
    (o o'' : Obj D l b s) (p : ℕ) (C : Set (Pts o.t)) (ψ : o.t.G ⟶ o''.t.G) : Prop :=
  IsMonHom ψ ∧ IsFinite ψ.left ∧ Surjective ψ.left ∧
    (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o''.t.act.act a) ∧
    (∀ x : Pts o.t, x ≫ ψ = 1 ↔ x ∈ C) ∧
    LBIso (cubeLB o''.t.G ![fst o.t.G o.t.G ≫ ψ, snd o.t.G o.t.G ≫ ψ] o''.t.PP.L)
      (LB.LinComb (abelian₂ o.t.G o.t.PP.L) (K := PUnit) (fun _ => 𝟙 _) (fun _ => (p : ℤ) ^ 2)) ∧
    (∀ a, o.eta a ≫ ψ = o''.eta a ^ p) ∧
    (∀ a, o.etaA a ≫ ψ = o''.etaA a ^ p)

end Fibre

def HeckeCorrespondence {D : Datum H} {l : Level H} (Xo : Moduli D l) : Prop :=
  ∀ (p : ℕ) (P : Ideal (𝓞 E)), IsSplitPrimeOff l p P → ∀ i : ℕ, i ≤ D.p + D.q →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (o : Obj D l (baseKA l) (y ≫ Xo.s)),
      Nonempty (ObjMap o Xo.univ y) →
      ∀ C₀ : Subgroup (Pts o.t), IsHeckeDatum o.t P i C₀ →
        ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧
          ∃ (o'' : Obj D l (baseKA l) (y ≫ Xo.s)) (ψ : o.t.G ⟶ o''.t.G),
            Nonempty (ObjMap o'' Xo.univ y'') ∧ IsHeckeIsogeny o o'' p (heckeKernel o.t p P C₀) ψ

def HeckeCorrespondenceStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l),
    HeckeCorrespondence Xo

example {k : Type} [Field k] (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) : IsHeckeDatum t P 0 ⊥ := by
  refine ⟨fun a x hx => ?_, fun x hx a _ => ?_, inferInstance, by simp⟩
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, MonObj.one_comp]
  · have := t.act.hom a
    rw [Subgroup.mem_bot] at hx
    rw [hx, MonObj.one_comp]

example {k : Type} [Field k] (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (x : Pts t)
    (hx : x ∈ heckeKernel t p P ⊥) : x ^ p = 1 := by
  obtain ⟨x₁, x₂, x₃, rfl, ⟨h₁, -⟩, ⟨-, h₂⟩, ⟨h₃, -⟩⟩ := hx
  rw [Subgroup.mem_bot] at h₂
  have hc : ∀ u v : Pts t, Commute u v := fun u v => mul_comm u v
  rw [(hc _ _).mul_pow, (hc _ _).mul_pow, h₁, h₂, h₃, _root_.mul_one, _root_.mul_one]

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.HermitianTensorPowers
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : ℂ := z ⬝ᵥ Hm.mulVec (star w)

def factor {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (l z : Fin g → ℂ) : ℂ :=
  c * Complex.exp (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)

def IsThetaFn {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : Λ) (z : Fin g → ℂ), θ (z + l) = factor Hm (χ l) l z ^ n * θ z

abbrev tpow {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

def IsFnPow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ)
    (s : (tpow L n).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (tpow L n).ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (tpow L n).U j →
    valAt' (u.ex z).left ((tpow L n).U j) (s.f j) = θ z * u.fr (j PUnit.unit) z ^ n

def commVal {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v w : Fin g → ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I * (k * ((herm Hm v w).im : ℂ))))) (Complex.exp_ne_zero _)

def ThetaUniformisation : Prop :=
  ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ),

      u.IsAH Hm χ ∧ u.IsRig rig ∧

      (∀ l, χ l = 1 ∨ χ l = -1) ∧
      (∀ l m : u.Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * ((herm Hm l m).im : ℂ))) ∧

      (∀ v : epsR ℂ ⟶ P.A, IsTangent v → ∃! w : Fin P.g → ℂ, u.IsDiff w v) ∧
      (∀ w : Fin P.g → ℂ, ∃! v : epsR ℂ ⟶ P.A, IsTangent v ∧ u.IsDiff w v) ∧

      (∀ f : P.A ⟶ P.A, IsMonHom f → ∃ M : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
        (∀ l ∈ u.Λ, M l ∈ u.Λ) ∧ ∀ z, u.ex (M z) = u.ex z ≫ f) ∧

      (∀ n : ℕ,
        (∀ s : (tpow P.L n).Sec, ∃! θ, IsThetaFn u.Λ Hm χ n θ ∧ IsFnPow u n s θ) ∧
        (∀ θ, IsThetaFn u.Λ Hm χ n θ → ∃! s : (tpow P.L n).Sec, IsFnPow u n s θ)) ∧

      (∀ l m : u.Λ, ∃ a : ℤ, (herm Hm l m).im = a) ∧
      (∀ φ : u.Λ →ₗ[ℤ] ℤ, ∃! l : u.Λ, ∀ m : u.Λ, (herm Hm l m).im = φ m) ∧

      (∀ k : ℕ, 0 < k → ∀ v w : Fin P.g → ℂ, k • v ∈ u.Λ → k • w ∈ u.Λ →
        Out.WeilIs P.A P.L (k : ℤ) (u.ex v) (u.ex w) (unitOn (commVal Hm k v w)))

lemma herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    herm Hm (z + z') w = herm Hm z w + herm Hm z' w := add_dotProduct _ _ _

lemma herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v w : Fin g → ℂ) :
    herm Hm w v = starRingEnd ℂ (herm Hm v w) := by
  simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : starRingEnd ℂ (Hm a b) = Hm b a := h.apply b a
  rw [this]; ring

def shift {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℕ) (v : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(k * Real.pi * herm Hm z v)) * θ (z + v)

lemma shift_comm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (v w : Fin g → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    shift Hm k v (shift Hm k w θ) z = commVal Hm k v w * shift Hm k w (shift Hm k v θ) z := by
  have h1 : herm Hm v w - herm Hm w v = 2 * ((herm Hm v w).im : ℂ) * Complex.I := by
    rw [herm_swap h v w, Complex.sub_conj]; push_cast; ring
  simp only [shift, commVal, Units.val_mk0, herm_add_left]
  rw [add_right_comm z w v, ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _), ← _root_.mul_assoc (Complex.exp _) (Complex.exp _) (θ _),
    ← _root_.mul_assoc (Complex.exp _) _ (θ _), ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  refine congrArg (fun t => Complex.exp t * θ (z + v + w)) ?_
  linear_combination (-(k : ℂ) * Real.pi) * h1

lemma shift_factor {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (k : ℕ) (c : ℂ)
    (v l : Fin g → ℂ) (a : ℤ) (ha : k * (herm Hm v l).im = a) (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ z, θ (z + l) = factor Hm c l z ^ k * θ z) (z : Fin g → ℂ) :
    shift Hm k v θ (z + l) = factor Hm c l z ^ k * shift Hm k v θ z := by
  have h1 : herm Hm v l - herm Hm l v = 2 * ((herm Hm v l).im : ℂ) * Complex.I := by
    rw [herm_swap h v l, Complex.sub_conj]; push_cast; ring
  have ha' : (k : ℂ) * ((herm Hm v l).im : ℂ) = a := by exact_mod_cast ha
  have h2 : Complex.exp (a * (2 * Real.pi * Complex.I)) = 1 := Complex.exp_int_mul_two_pi_mul_I a
  simp only [shift, factor, add_right_comm z l v, hθ, herm_add_left, mul_pow, ← Complex.exp_nat_mul]
  have h3 : Complex.exp (-(k * Real.pi * (herm Hm z v + herm Hm l v))) *
      Complex.exp (k * (Real.pi * (herm Hm z l + herm Hm v l) + Real.pi / 2 * herm Hm l l)) =
      Complex.exp (k * (Real.pi * herm Hm z l + Real.pi / 2 * herm Hm l l)) *
      Complex.exp (-(k * Real.pi * herm Hm z v)) := by
    rw [← mul_one (Complex.exp _ * Complex.exp (-(k * Real.pi * herm Hm z v))), ← h2]
    simp only [← Complex.exp_add]
    congr 1
    linear_combination ((k : ℂ) * Real.pi) * h1 + (2 * Real.pi * Complex.I) * ha'
  linear_combination (c ^ k * θ (z + v)) * h3

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.OpenModelSections
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange

section Push

variable {X : Scheme.{0}} (G : Over X) (L : LB G.left)

structure IsPushGen (V : X.Opens) (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop where
  mem : θ ∈ secOn L (G.hom ⁻¹ᵁ V)
  basis : ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! c : Γ(X, W), ∀ i,
    s i = resG G.left (inf_le_left : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ W) ((G.hom.app W).hom c) *
      resG G.left (inf_le_inf_right _ (fun _ hy => hW hy) : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ V ⊓ L.U i) (θ i)

def NonzeroOnFibre {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X) : Prop :=
  ∃ i, ((Scheme.Hom.fiberι G.hom x).app (G.hom ⁻¹ᵁ V ⊓ L.U i)).hom (θ i) ≠ 0

structure PushInvertible : Prop where
  invertible : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ, IsPushGen G L V θ
  nonzero : ∀ (V : X.Opens) θ, IsPushGen G L V θ → ∀ x ∈ V, NonzeroOnFibre G L θ x

theorem nonzeroOnFibre_iff {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X)
    [IsReduced (Scheme.Hom.fiber G.hom x)] :
    NonzeroOnFibre G L θ x ↔ ∃ (i : L.ι) (g : G.left), G.hom g = x ∧ g ∈ G.left.basicOpen (θ i) := by
  refine exists_congr fun i => ?_
  rw [Ne, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  constructor
  · intro hne
    obtain ⟨y, hy⟩ : ∃ y, y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := by
      by_contra hh
      push_neg at hh
      exact hne (le_bot_iff.mp fun y hy => (hh y hy).elim)
    refine ⟨_, ?_, hy⟩
    have : Scheme.Hom.fiberι G.hom x y ∈ Set.range (Scheme.Hom.fiberι G.hom x) := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨g, hg, hb⟩ h0
    have : g ∈ Set.range (Scheme.Hom.fiberι G.hom x) := by
      rw [Scheme.Hom.range_fiberι]; exact hg
    obtain ⟨y, rfl⟩ := this
    have : y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := hb
    rw [h0] at this
    exact this

end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Model {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀)
    {O : Type} [CommRing O] (φ : O →+* F₀) where

  X : Scheme.{0}

  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s

  j : baseChange str h ⟶ pullback s (spMap φ)
  j_over : j ≫ pullback.snd s (spMap φ) = baseChangeStr str h
  j_open : IsOpenImmersion j
  j_dense : Dense (Set.range j)

  t : SAB H X

  t₀ : SAB H (baseChange str h)

  toUniv : SABMap t₀ univ.t (baseChangeFst str h)

  toModel : SABMap t₀ t (j ≫ pullback.fst s (spMap φ))
  ab : ∀ y : ↥(pullback s (spMap φ)), pullback.fst s (spMap φ) y ∈ abLocus t.G ↔ y ∈ Set.range j

namespace Model

variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀} (m : Model univ h φ)

def incl : baseChange str h ⟶ m.X := m.j ≫ pullback.fst m.s (spMap φ)

theorem incl_over : m.incl ≫ m.s = baseChangeStr str h ≫ spMap φ := by
  rw [incl, Category.assoc, pullback.condition, ← Category.assoc, m.j_over]

def liftSec (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t₀.G.left :=
  m.toUniv.cart.1.lift σ.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w σ)

def secMap (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t.G.left :=
  m.liftSec σ ≫ m.toModel.φ

theorem secMap_over (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : m.secMap σ ≫ m.t.G.hom = m.incl := by
  rw [secMap, Category.assoc, m.toModel.cart.1.w, ← Category.assoc, liftSec, IsPullback.lift_snd, Category.id_comp, incl]

def Extends (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) (U : m.X.Opens) : Prop :=
  ∃ τ : Over.mk U.ι ⟶ m.t.G, (m.incl ∣_ U) ≫ τ.left = (m.incl ⁻¹ᵁ U).ι ≫ m.secMap σ

theorem extends_one (U : m.X.Opens) : m.Extends (toUnit _ ≫ MonObj.one) U := by
  have h1 : m.liftSec (toUnit _ ≫ MonObj.one) = eSec m.t₀.G := by
    apply m.toUniv.cart.1.hom_ext
    · rw [liftSec, IsPullback.lift_fst, m.toUniv.cm.e_comm, m.toUniv.base]; rfl
    · rw [liftSec, IsPullback.lift_snd]; exact (Over.w (MonObj.one (X := m.t₀.G))).symm
  refine ⟨toUnit _ ≫ MonObj.one, ?_⟩
  have h2 : m.secMap (toUnit _ ≫ MonObj.one) = m.incl ≫ eSec m.t.G := by
    rw [secMap, h1]
    have := m.toModel.cm.e_comm
    rw [m.toModel.base] at this
    exact this
  rw [h2, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rfl

def PPPushInvertible : Prop := PushInvertible m.t.G m.t.PP.L

theorem incl_mem_abLocus (y : ↥(baseChange str h)) : m.incl y ∈ abLocus m.t.G := by
  have := (m.ab (m.j y)).mpr ⟨y, rfl⟩
  simpa [incl] using this

end Model

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : Type 1 :=
  Model univ h (algebraMap (𝓞 F₀) F₀)

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) [NumberField F₀]
    (lam : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀)) : Type 1 :=
  Model univ h (lam.valuation F₀).valuationSubring.subtype

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) (a : D.La) :
    Over.mk (baseChangeFst str h) ⟶ univ.t.G := toUnit _ ≫ univ.eta a

end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
end
end

