import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree

section Adelic

variable {L : Type} [Field L] [NumberField L]

def adDeg (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : ℝ :=
  (∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) - (1 / 2) * ∑ σ, Real.log (N σ)) / Module.finrank ℚ L

example : adDeg (L := L) 0 1 = 0 := by simp [adDeg]

example : adDeg (L := L) 0 (fun _ => 4) = -Real.log 2 := by
  have h : (Module.finrank ℚ L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [adDeg, Pi.zero_apply, zero_mul, finsum_zero, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul, h4]
  field_simp
  ring

end Adelic

section Eigen

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]

def IsEigVec (act : OAct O G) (χ : O →+* R) (v : epsR R ⟶ G) : Prop :=
  IsTangent v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis (act : OAct O G) (χ : O →+* R) {m : ℕ} (v : Fin m → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsEigVec act χ (v i)) ∧ ∀ w, IsEigVec act χ w → ∃! c : Fin m → R, IsLieComb c v w

end Eigen

section Local

variable {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] {m : ℕ}

def IsLocOrd (v : Fin m → (epsR L ⟶ A)) (𝔭 : HeightOneSpectrum (𝓞 L)) (r : ℝ) : Prop :=
  ∃ (V K' : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K') (_ : Algebra V K')
    (_ : IsFractionRing V K') (em : L →+* K') (e : ℕ)
    (G : Over (Sp V)) (_ : GrpObj G) (A' : Over (Sp K')) (_ : GrpObj A')
    (φG : A'.left ⟶ G.left) (φA : A'.left ⟶ A.left)
    (v' : Fin m → (epsR K' ⟶ A')) (u : Fin m → (epsR V ⟶ G)) (u' : Fin m → (epsR K' ⟶ A'))
    (M : Matrix (Fin m) (Fin m) K') (n : ℤ),
    0 < e ∧ (∀ x : L, (IsDiscreteValuationRing.maximalIdeal V).valuation K' (em x) = 𝔭.valuation L x ^ e) ∧
    IsSemiAbelian G ∧ IsGrpPullback A' G (spMap (algebraMap V K')) φG ∧ IsGrpPullback A' A (spMap em) φA ∧
    (∀ i, IsVecOver em φA (v i) (v' i)) ∧
    (∀ k, IsTangent (u k) ∧ IsVecOver (algebraMap V K') φG (u k) (u' k) ∧
      ∃ c : Fin m → K', IsLieComb c v' (u' k)) ∧
    (∀ (w : epsR V ⟶ G) (w' : epsR K' ⟶ A'), IsTangent w → IsVecOver (algebraMap V K') φG w w' →
      (∃ c : Fin m → K', IsLieComb c v' w') → ∃! a : Fin m → V, IsLieComb a u w) ∧
    (∀ i, IsLieComb (M i) u' (v' i)) ∧
    (IsDiscreteValuationRing.maximalIdeal V).valuation K' M.det = WithZero.exp (-n) ∧ r = (n : ℝ) / e

def IsArchSq (𝓛 : LB A.left) (v : Fin m → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) : Prop :=
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ A.left) (g : ℕ) (u : HolUnif A' (𝓛.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' : Fin m → (epsR ℂ ⟶ A')) (W : Fin m → Fin g → ℂ),
    IsGrpPullback A' A (spMap σ) φ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver σ φ (v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
    0 < N ∧ (N : ℂ) = (Matrix.of fun i k => (Real.pi : ℂ) * (W i ⬝ᵥ Hm.mulVec (star (W k)))).det

end Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lines

variable {L : Type} [Field L] [NumberField L]

def IsEigLine (t : SAB H (Sp L)) (τ : E →+* L) (m : ℕ) (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : Prop :=
  ∃ v : Fin m → (epsR L ⟶ t.G), IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) v ∧
    (∀ 𝔭, IsLocOrd t.G v 𝔭 (r 𝔭)) ∧ (∀ σ, IsArchSq t.G t.PP.L v σ (N σ)) ∧ (Function.support r).Finite

def IsEigDeg (t : SAB H (Sp L)) (τ : E →+* L) (m : ℕ) (δ : ℝ) : Prop :=
  ∃ r N, IsEigLine t τ m r N ∧ δ = adDeg r N

def ordIdeal (τ : E →+* L) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  FractionalIdeal.count L 𝔭
    ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def ordTwist (H : Host E) (τ : E →+* L) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  (ordIdeal τ (differentIdeal ℤ (𝓞 E)) 𝔭 - ordIdeal τ (Ideal.span {H.rt}) 𝔭) - ordIdeal τ (Ideal.span {H.rt}) 𝔭

def IsFlatDeg (t : SAB H (Sp L)) (τ τ' : E →+* L) (p q : ℕ) (δ : ℝ) : Prop :=
  ∃ r N r' N', IsEigLine t τ p r N ∧ IsEigLine t τ' q r' N' ∧
    δ = adDeg (fun 𝔭 => r 𝔭 - r' 𝔭 - q * (ordTwist H τ 𝔭 : ℝ)) (fun σ => N σ / N' σ)

end Lines

def embIn {l : Level H} (c : Coeff l) {L : Type} [Field L] (j : c.F →+* L) (τ : E →+* ℂ) : E →+* L :=
  j.comp (τ.codRestrict c.F (c.conj τ))

def cOne (H : Host E) (p q : ℕ) (logOm : ℝ) : ℝ :=
  -(((p : ℝ) - q) / 2 * logOm) - q * (2 * Real.log √(H.d : ℝ) - Real.log (rootDiscr E))

def IsHostField (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})

def AtAllPoints (H : Host E)
    (Q : ∀ (L : Type) [Field L] [NumberField L], SAB H (Sp L) → (E →+* L) → (E →+* L) → ℕ → ℕ → Prop) : Prop :=
  ∀ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (L : Type) [Field L] [NumberField L] (j : c.F →+* L)
    (y : Sp L ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap j →
    ∀ (t : SAB H (Sp L)), Nonempty (SABMap t Xo.univ.t (y ≫ pullback.fst _ _)) →
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → Q L t (embIn c j τ) (embIn c j (conjEmb τ)) D.p D.q

def LinesExist (H : Host E) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => (∃ r N, IsEigLine t τ p r N) ∧ ∃ r' N', IsEigLine t τ' q r' N'

def LieDegAt (H : Host E) (logOm : ℝ) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => ∀ δ δ', IsEigDeg t τ p δ → IsEigDeg t τ' q δ' →
    δ - δ' = ((p : ℝ) - q) / 2 * logOm

def FlatDegAt (H : Host E) (logOm : ℝ) : Prop :=
  AtAllPoints H fun _ _ _ t τ τ' p q => ∀ δ, IsFlatDeg t τ τ' p q δ → δ = -cOne H p q logOm

def BoundAt (H : Host E) (logOm : ℝ) : Prop :=
  ∀ p q : ℕ, |cOne H p q logOm + ((p : ℝ) - q) * logOm / 2| ≤ q * Real.log (rootDiscr E)

def DegreeTheorem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsHostField H →
    ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
      LinesExist H ∧ LieDegAt H (CM.logOm E χ).re ∧ FlatDegAt H (CM.logOm E χ).re ∧ BoundAt H (CM.logOm E χ).re

example (H : Host E) (p : ℕ) (x : ℝ) : cOne H p 0 x = -(p / 2 * x) := by simp [cOne]

example {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] (𝓛 : LB A.left)
    (v : Fin 0 → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) (h : IsArchSq A 𝓛 v σ N) : N = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  rw [Matrix.det_isEmpty] at h
  exact_mod_cast h

end GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l

def levDet (Dw : Datum H) (l : Level H) : LevGrp Dw l →* (𝓞 E ⧸ l.Mb)ˣ where
  toFun γ := LinearEquiv.det
    (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ l.Mb) Ideal.Quotient.mk_surjective)
  map_one' := by
    rw [← map_one (LinearEquiv.det (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l))]
    rfl
  map_mul' γ δ := by
    rw [← map_mul]
    rfl

end Level

variable {D : D7}

def idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ b ∈ I, ∃ y ∈ intAE D, z = ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * y}

def CongMod (I : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) (u : 𝓞 D.host.E) : Prop :=
  finPart D (x : AE D) - (1 : Af D.host.F) ⊗ₜ (u : D.host.E) ∈ idealHat D I

def IsInvTame {K : Type} [Field K] (σ : K →+* ℂ) (Mb Mc : Ideal (𝓞 D.host.E)) (μ : (AE D)ˣ →* Circle)
    (χ : (𝓞 D.host.E ⧸ Mb)ˣ →* Kˣ) : Prop :=
  ∀ x : (AE D)ˣ, FinUnit x → ∀ (u : 𝓞 D.host.E) (ub : (𝓞 D.host.E ⧸ Mb)ˣ),
    (ub : 𝓞 D.host.E ⧸ Mb) = Ideal.Quotient.mk Mb u → CongMod Mb x u → CongMod Mc x 1 →
      σ ((χ ub : Kˣ) : K) * ((μ x : Circle) : ℂ) = 1

def IsLevLift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
    ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a) →
      ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = (l.M : ℕ) • w

def iotaAt (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (hr : (T.V j σ).rank = D.R.r) :
    (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (T.V j σ).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def geo (T : CoreJ D) (j : ℕ) (γ : LevGrp (T.Q.Dw j) T.Q.l) : T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ

def adFn (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (c : (T.U j σ).Comp → ℂ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) c) (rdU (T.U j σ) f)

structure GeoActAt (T : CoreJ D) (j : ℕ) (χ : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ) : Prop where

  laws : ActLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l)

  keeps : ∀ a n, Dom a n → ∀ γ, ∀ f ∈ T.cuspA j a n, geo T j γ f ∈ T.cuspA j a n

  lifts : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) (γ : LevGrp (T.Q.Dw j) T.Q.l),
    ∃ κ, IsLevLift T.Q.l (T.V j σ) (iotaAt T j σ hr) γ κ

  equiv : ∀ σ, GoodEmb T.Q.c σ → ∀ (hr : (T.V j σ).rank = D.R.r) (n : ℕ), Even n →
    ∃ c : (T.U j σ).Comp → ℂ, CUnit c ∧ ∀ a, Dom a n → ∀ f ∈ T.cuspA j a n,
      ∀ (γ : LevGrp (T.Q.Dw j) T.Q.l) (κ : GA D (T.V j σ)), IsLevLift T.Q.l (T.V j σ) (iotaAt T j σ hr) γ κ →
        ∀ x, adFn T j σ c (geo T j γ f) x =
          σ ((χ (levDet (T.Q.Dw j) T.Q.l γ) : (T.Q.c.F)ˣ) : T.Q.c.F) * adFn T j σ c f (x * κ)

  integral : ∀ a n, Dom a n → ∀ γ, ∀ f ∈ T.cuspA j a n, ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
    (∀ y : T.PtM j la, T.nrmM j la y f ≤ 1) → ∀ y : T.PtM j la, T.nrmM j la y (geo T j γ f) ≤ 1

def GeoAct : Prop :=
  ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ χ : (𝓞 D.host.E ⧸ T.Q.l.Mb)ˣ →* (T.Q.c.F)ˣ,
    IsInvTame T.σ₀ T.Q.l.Mb (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) (T.chiW j T.σ₀) χ →
      GeoActAt T j χ

example {K : Type} [Field K] (σ : K →+* ℂ) (Mb Mc : Ideal (𝓞 D.host.E)) : IsInvTame (D := D) σ Mb Mc 1 1 := by
  intro x _ u ub _ _ _
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftedCharacterResidue
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stabLat (V : HSp D) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ ∀ z, (finHom V k).1.mulVec z ∈ latHat V ↔ z ∈ latHat V}
  one_mem' := ⟨(GfC V).one_mem, fun z => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(GfC V).mul_mem ha hb, fun z => ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha', hb']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(GfC V).inv_mem ha, fun z => ?_⟩
    rw [← ha' ((finHom V a⁻¹).1.mulVec z), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

def prinLev (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ stabLat V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

abbrev levN (D : D7) : ℕ := D.host.g 0 * D.host.g 1

def jx {j : ℕ} (hj : InR D j) : Fin D.R.m := ⟨j - 1, by have := hj.1; have := hj.2; omega⟩

def IsKappa {j : ℕ} (hj : InR D j) (κ : WeightFamilies.Wt D j) : Prop :=
  κ.n = D.R.r + D.R.t ∧ ∀ τ : D.what₂.Tau,
    (∀ i, (κ.aP τ i : ℚ) + (κ.n : ℚ) / 2 - (D.hc τ).e (jx hj) =
      Formalism.L2.NTheta.kapQ (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inl i)) ∧
    ∀ i, -(κ.aM τ (Fin.rev i) : ℚ) - (κ.n : ℚ) / 2 - (D.hc τ).e (jx hj) =
      Formalism.L2.NTheta.kapQ (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inr i)

variable (T : CoreJ D)

def SitsAt (σ : T.Q.c.F →+* ℂ) (τ ρ : D.what₂.Tau) : Prop := relab T.Q.c σ (tauE D τ) = tauE D ρ

def IsLiftChar {j : ℕ} (hj : InR D j) : Prop :=
  (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = levN D • y) → T.chiW j T.σ₀ x = 1) ∧
    ∀ σ, GoodEmb T.Q.c σ → ∀ τ ρ, SitsAt T σ τ ρ → HasInfExp D (T.chiW j σ) ρ (-(D.hc τ).e (jx hj))

def conjWt (V : HSp D) (lab : D.what₂.Tau → D.what₂.Tau) (ρ : D.what₂.Tau) :
    Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 → ℤ :=
  Formalism.L2.NTheta.kapW (D.hc (lab ρ)) _ _

def iotaW {j : ℕ} (hj : InR D j) : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ T.iota j

def Reduces {j : ℕ} (hj : InR D j) (k : GA D (D.sp.W j)) (u : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) : Prop :=
  ∀ a ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La),
    ∃ w ∈ latGHat (D.sp.W j) 1,
      finVec (D.sp.W j) (iotaW T hj (u a)) - (finHom (D.sp.W j) k).1.mulVec (finVec (D.sp.W j) (iotaW T hj a)) =
        levN D • w

abbrev LevEnd (j : ℕ) : Type :=
  ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)

def IsCover {j : ℕ} (hj : InR D j) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j) :
    Prop :=
  Function.Surjective red ∧ (∀ k : stabLat (D.sp.W j), red k = 1 ↔ (k : GA D (D.sp.W j)) ∈ prinLev (D.sp.W j) (levN D)) ∧
    (∀ k : stabLat (D.sp.W j), Reduces T hj k (lev (red k)).1) ∧ ∀ g, (lev g).2 = LinearMap.id

def KeepsInt (j : ℕ) (κ : WeightFamilies.Wt D j) {G : Type} [Group G] (lev : G → LevEnd T j) : Prop :=
  ∀ g, ∀ f ∈ T.C j κ, (∀ la (y : T.PtM j la), T.nrmM j la y f ≤ 1) →
    ∀ la (y : T.PtM j la), T.nrmM j la y (actLev (Xo := T.Q.Xo j) T.Q.c lev g f) ≤ 1

variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

def IsChiDet {j : ℕ} (σ₀ : LL →+* ℂ) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G) (χ : G →* LLˣ) : Prop :=
  ∀ (k : stabLat (D.sp.W j)) (x : (AE D)ˣ), IsDetRoot (D.sp.W j) k x →
    σ₀ (χ (red k) : LL) = (((T.chiW j T.σ₀ x)⁻¹ : Circle) : ℂ)

abbrev resK (σ : LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F LL)

def Pos (σ : LL →+* ℂ) : Prop := GoodEmb T.Q.c (resK T σ)

abbrev Phases (j : ℕ) : Type := ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ

def UnitPhases {j : ℕ} (c : Phases T j) : Prop := ∀ σ, GoodEmb T.Q.c σ → CUnit (c σ)

def castFun {V V' : HSp D} (h : V = V') : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) :=
  LinearMap.funLeft ℂ ℂ (cast (congrArg (GA D) h.symm))

def readK {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : T.Q.c.F →+* ℂ) (h : T.V j σ = D.sp.W j) :
    T.C j κ →ₛₗ[σ] (GA D (D.sp.W j) → ℂ) :=
  (((lieFac (T.Q.Dw j) (xiR D) (wtA κ) : ℝ) : ℂ) • (castFun h ∘ₗ
      adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (c σ)))).comp
    ((rdU (T.U j σ)).comp (T.C j κ).subtype)

abbrev FormsLL (LL : Type) [Field LL] [Algebra T.Q.c.F LL] (j : ℕ) (κ : WeightFamilies.Wt D j) : Type :=
  LL ⊗[T.Q.c.F] T.C j κ

def readL {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) :
    FormsLL T LL j κ →ₛₗ[σ] (GA D (D.sp.W j) → ℂ) :=
  extJ σ (readK T κ c (resK T σ) h)

def IsoFor {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.W j) S) : Prop :=
  ∃ (v₀ : M.Vec) (J : FormsLL T LL j κ →ₛₗ[σ] Mult θ M (prinLev (D.sp.W j) (levN D)) (fun _ => 1)),
    (∀ ρ, ‖(v₀ ρ : M.H ρ)‖ = 1) ∧
    (∀ Φ ∈ Mult θ M (prinLev (D.sp.W j) (levN D)) (fun _ => 1), Φ v₀ = 0 → Φ = 0) ∧
    (∀ x, (J x : MMap M) v₀ = readL T κ c σ h x) ∧
    (∀ (n : ℕ) (b : Fin n → FormsLL T LL j κ), LinearIndependent LL b → LinearIndependent ℂ fun i => J (b i)) ∧
    Submodule.span ℂ (Set.range J) = ⊤

def IsoAt {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ =>
    AllSome (fun lab : D.what₂.Tau → D.what₂.Tau => ∀ ρ, SitsAt T (resK T σ) (lab ρ) ρ) fun lab =>
      AllSome (fun _ : DSModel (D.sp.W j) (parW (D.sp.W j) (conjWt (D.sp.W j) lab)) => True) fun M =>
        IsoFor T κ c σ h θ M

def EquivAt {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G)
    (lev : G → LevEnd T j) (χ : G →* LLˣ) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) : Prop :=
  ∀ (k : stabLat (D.sp.W j)) (x : FormsLL T LL j κ) (g : GA D (D.sp.W j)),
    readL T κ c σ h (rhoOf LL (KsCore.rhoGeo T.toCore j κ lev) (red k) x) g =
      σ (χ (red k) : LL) * readL T κ c σ h x (g * k)

def UnifWith (hT : LawsJ T) {j : ℕ} (hj : InR D j) (κ : WeightFamilies.Wt D j) (c : Phases T j) {G : Type} [Group G]
    (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j) (χ : G →* LLˣ) : Prop :=
  ∀ (σ : LL →+* ℂ) (hσ : Pos T σ),
    IsoAt T κ c σ (hT.spaceW j hj _ hσ) ∧ EquivAt T κ c red lev χ σ (hT.spaceW j hj _ hσ)

def UnifEvery (hT : LawsJ T) : Prop :=
  ∀ (j : ℕ) (hj : InR D j) (κ : WeightFamilies.Wt D j), IsKappa hj κ → IsLiftChar T hj →
    ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL] (σ₀ : LL →+* ℂ), BaseEmbeddingInclusion T.Q.c.F σ₀ →
      (∀ k ∈ stabLat (D.sp.W j), ∃ u, Reduces T hj k u) ∧
      (∀ c : Phases T j, UnitPhases T c → ∀ (σ : LL →+* ℂ) (hσ : Pos T σ), IsoAt T κ c σ (hT.spaceW j hj _ hσ)) ∧
      ∀ (G : Type) [Group G] (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j), IsCover T hj red lev →
        ActLev (Xo := T.Q.Xo j) T.Q.c lev ∧ KsCore.KeepsCu T.toCore j κ lev ∧ KeepsInt T j κ lev ∧
        AllSome (IsChiDet T σ₀ red) fun χ : G →* LLˣ =>
          ∃ c : Phases T j, UnitPhases T c ∧ UnifWith T hT hj κ c red lev χ

def Unif (D : D7) : Prop := ∀ (T : CoreJ D) (hT : LawsJ T), UnifEvery T hT

end GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue
end
end

