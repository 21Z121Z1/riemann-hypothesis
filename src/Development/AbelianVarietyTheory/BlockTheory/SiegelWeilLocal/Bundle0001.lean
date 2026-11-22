import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.SmoothOnGVIff

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteGapThreshold
section
open MeasureTheory NumberField Matrix
open scoped TensorProduct InnerProductSpace
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

def perp {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (JA : Matrix (Fin n) (Fin n) A)
    (WA : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ x ∈ WA, Formalism.UG.hform s JA x y = 0}

def TrivOnFlag {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (JA : Matrix (Fin n) (Fin n) A)
    (r : ℕ) (WA : ℕ → Submodule A (Fin n → A)) (g : Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i < r, ∀ x ∈ WA (i + 1), (g - 1) *ᵥ x ∈ WA i) ∧
    (∀ y ∈ perp s JA (WA r), (g - 1) *ᵥ y ∈ WA r) ∧
    ∀ i < r, ∀ y ∈ perp s JA (WA i), (g - 1) *ᵥ y ∈ perp s JA (WA (i + 1))

variable (I : AutInst)

def IsIsotFlag (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) : Prop :=
  1 ≤ r ∧ W 0 = ⊥ ∧ (∀ i < r, W i < W (i + 1)) ∧
    ∀ x ∈ W r, ∀ y ∈ W r, Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def flagNA (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) : Set I.GA :=
  {x | (∀ v, TrivOnFlag (starRingEnd ℂ) (I.J.map (I.φ v)) r
      (fun i => Submodule.span ℂ ((fun w : Fin I.n → I.E => fun a => I.φ v (w a)) '' (W i : Set _)))
      (I.P v * uMat (x.1 v) * (I.P v)⁻¹)) ∧
    TrivOnFlag (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) r
      (fun i => Submodule.span (I.E ⊗[I.F] Af I.F)
        ((fun w : Fin I.n → I.E => fun a => Formalism.UG.inclE (F := I.F) (Af I.F) (w a)) '' (W i : Set _)))
      (I.fmat x.2)}

def IsFlagQuotMeas (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) (ν : Measure I.GA) : Prop :=
  IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν (flagNA I r W)ᶜ = 0 ∧
    ∀ S : Set I.GA, MeasurableSet S → (∀ γ ∈ I.GFset ∩ flagNA I r W, ∀ y, γ * y ∈ S ↔ y ∈ S) →
      ∀ n₀ ∈ flagNA I r W, ν {m | m * n₀ ∈ S} = ν S

def ConstTermsVanish (f : I.GA → ℂ) : Prop :=
  ∀ (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)), IsIsotFlag I r W →
    ∀ ν : Measure I.GA, IsFlagQuotMeas I r W ν →
      ∀ x : I.GA, Integrable (fun m => f (m * x)) ν ∧ ∫ m, f (m * x) ∂ν = 0

def IsCuspClass (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (Fv : I.L2 μf fund) : Prop :=
  ∃ f : I.GA → ℂ, Continuous f ∧ (∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) ∧
    (Fv : I.GA → ℂ) =ᵐ[(I.muA μf).restrict fund] f ∧ ConstTermsVanish I f

section Test

variable {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]

def dSigma (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def ph (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => (dSigma I σ w : ℂ) * star (∏ v, coefOn (ε := I.ε v) (σ v) (w v) (w v) (g v))

def phE (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (e : I.Gf → ℂ) :
    I.GA → ℂ :=
  fun g => ph I σ w g.1 * e g.2

end Test

def IsIdemInK (μf : Measure I.Gf) (e : I.Gf → ℂ) : Prop :=
  IsLocallyConstant e ∧ I.convF μf e e = e ∧ (∀ x, e x⁻¹ = star (e x)) ∧ ∀ x, e x ≠ 0 → x ∈ I.Kset

def gapThreshold (C : ℝ) (p q : ℕ) : ℝ :=
  max (120 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (C * ((p + q : ℕ) : ℝ) ^ 2 * ((min p q : ℕ) : ℝ) ^ ((1 : ℝ) / 2))

def ProjectorWith (C : ℝ)
    (Side : ∀ I : AutInst, (InfinitePlace I.F → Fin I.n → ℝ) → Measure I.Gf → (I.Gf → ℂ) → Prop) : Prop :=
  ∀ (I : AutInst) (p q : ℕ), (∀ v, I.pAt v = p ∧ I.qAt v = q) →
  ∀ (lam : InfinitePlace I.F → Fin I.n → ℝ) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v),
    (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) → (∀ v, IsDS (I.ε v) (lam v) (σ v)) →
    (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) →
  ∀ h : ℝ, (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → gapThreshold C p q ≤ h →
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens →
  ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
  ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
  ∀ e : I.Gf → ℂ, Side I lam μf e →
  ∀ Re : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConvF μf fund R e Re →
    Integrable (ph I σ w) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) ∧
    ∃ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConv μf fund R (phE I σ w e) T ∧
      ∃ S : Submodule ℂ (I.L2 μf fund), IsOrthProjOnto T S ∧
        FiniteDimensional ℂ S ∧ FiniteDimensional ℂ (I.eHom σs μf fund R Re) ∧
        Module.finrank ℂ S = I.Dcount σs μf fund R Re ∧
        ∀ Fv ∈ S, IsCuspClass I μf fund Fv ∧ I.IsCuspFn (I.muA μf) (I.ext Fv)

def WideSide (I : AutInst) (_ : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf) (e : I.Gf → ℂ) : Prop :=
  IsIdemInK I μf e

def CountSide (Cg : ℝ) (I : AutInst) (lam : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf)
    (e : I.Gf → ℂ) : Prop :=
  ∃ (b : ℝ) (g g₀ : ℕ), 2 ≤ b ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ Cg ∧
    g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀ ∧ I.IsAdmIdem μf g g₀ e

def GlobalProjectorFor (C : ℝ) : Prop := ProjectorWith C WideSide

def GlobalProjector : Prop := GlobalProjectorFor 40

def GlobalProjectorSome : Prop := ∃ C : ℝ, 0 < C ∧ GlobalProjectorFor C

def CountProjectorFor (C : ℝ) : Prop := ∀ Cg : ℝ, ProjectorWith C (CountSide Cg)

def CountProjector : Prop := CountProjectorFor 40

def CountProjectorSome : Prop := ∃ C : ℝ, 0 < C ∧ CountProjectorFor C

end GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.UnitarySchurProjector
section
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality

section Defs

variable {G : Type} [Group G]
variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsUnitaryRep [TopologicalSpace G] (π : G → (H →L[ℂ] H)) : Prop :=
  π 1 = ContinuousLinearMap.id ℂ H ∧ (∀ a b, π (a * b) = (π a).comp (π b)) ∧
    (∀ g v, ‖π g v‖ = ‖v‖) ∧ ∀ v, Continuous fun g => π g v

def IsTopIrred (σ : G → (Hs →L[ℂ] Hs)) : Prop :=
  ∀ S : Submodule ℂ Hs, IsClosed (S : Set Hs) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤

def SchurOrthogonality [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ u v u' v' : Hs,
    Integrable (fun g => ⟪v, σ g u⟫_ℂ * star ⟪v', σ g u'⟫_ℂ) μ ∧
    ∫ g, ⟪v, σ g u⟫_ℂ * star ⟪v', σ g u'⟫_ℂ ∂μ = (d : ℂ)⁻¹ * ⟪u', u⟫_ℂ * star ⟪v', v⟫_ℂ

def diagCoef (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (g : G) : ℂ := ⟪w, σ g w⟫_ℂ

def testFn (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) (g : G) : ℂ := (d : ℂ) * star (diagCoef σ w g)

def IsIntegratedOp [MeasurableSpace G] (μ : Measure G) (π : G → (H →L[ℂ] H)) (f : G → ℂ)
    (P : H →L[ℂ] H) : Prop :=
  Integrable f μ ∧ ∀ x y : H, ⟪x, P y⟫_ℂ = ∫ g, f g * ⟪x, π g y⟫_ℂ ∂μ

def ketBra (w : Hs) : Hs →L[ℂ] Hs := (innerSL ℂ w).smulRight w

def intertwiners (σ : G → (Hs →L[ℂ] Hs)) (π : G → (H →L[ℂ] H)) : Submodule ℂ (Hs →L[ℂ] H) where
  carrier := {T | ∀ g, T.comp (σ g) = (π g).comp T}
  add_mem' := by
    intro a b ha hb g
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c a ha g
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ha g]

def evalIntertwiner (σ : G → (Hs →L[ℂ] Hs)) (π : G → (H →L[ℂ] H)) (w : Hs) :
    intertwiners σ π →ₗ[ℂ] H where
  toFun T := (T : Hs →L[ℂ] H) w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SchurRelations [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) :
    Prop :=
  (∀ g, star (testFn σ d w g⁻¹) = testFn σ d w g) ∧
    (∀ y, Integrable (fun g => testFn σ d w g * testFn σ d w (g⁻¹ * y)) μ ∧
      ∫ g, testFn σ d w g * testFn σ d w (g⁻¹ * y) ∂μ = testFn σ d w y) ∧
    (∀ x y, Integrable (fun g => testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y) ∂μ = diagCoef σ w x * testFn σ d w y) ∧
    IsIntegratedOp μ σ (testFn σ d w) (ketBra w)

def ProjectorProps (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (π : G → (H →L[ℂ] H)) (P : H →L[ℂ] H) : Prop :=
  P.comp P = P ∧ (∀ x y : H, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ) ∧
    (∀ x, P.comp ((π x).comp P) = diagCoef σ w x • P) ∧
    Function.Injective (evalIntertwiner σ π w) ∧
    LinearMap.range (evalIntertwiner σ π w) = LinearMap.range (P : H →ₗ[ℂ] H)

def ProjectorStatement [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G → (H →L[ℂ] H)), IsUnitaryRep π →
    (∃ P, IsIntegratedOp μ π (testFn σ d w) P) ∧
      ∀ P, IsIntegratedOp μ π (testFn σ d w) P → ProjectorProps σ w π P

end Defs

def AbstractSchurProjector : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    IsUnitaryRep σ → IsTopIrred σ → SchurOrthogonality μ σ d → ‖w‖ = 1 →
    Integrable (testFn σ d w) μ →
    SchurRelations μ σ d w ∧ ProjectorStatement μ σ d w

def realRank {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card

def UnitarySchurProjectorUnder (gap : ∀ n : ℕ, (Fin n → Bool) → (Fin n → ℝ) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    Formalism.QuantumDeterminants.IsHCParam lam → gap n ε lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsLowUnit ε lam σ w →
    Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) σ d →
    SchurRelations (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d w ∧
      ProjectorStatement (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d w

def UnitarySchurProjector : Prop :=
  UnitarySchurProjectorUnder fun n ε lam =>
    Formalism.QuantumDeterminants.GapAtLeast ε lam (120 * (n : ℝ) * (realRank ε : ℝ) ^ (3 / 2 : ℝ))

def UnitarySchurProjectorSharp : Prop :=
  UnitarySchurProjectorUnder fun n ε lam =>
    ∀ a b : Fin n, ε a ≠ ε b → 16 * (n : ℝ) * (realRank ε : ℝ) ^ (3 / 2 : ℝ) < |lam a - lam b|

def SchurProjector : Prop := AbstractSchurProjector ∧ UnitarySchurProjector

example {n : ℕ} (ε : Fin n → Bool) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (d : ℝ) (μ : Measure (Formalism.REAL.UJ ε)) :
    SchurOrthogonality μ (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g)) d ↔ Formalism.MainNotions.S.IsFdeg μ σ d := by
  unfold SchurOrthogonality Formalism.MainNotions.S.IsFdeg Formalism.MainNotions.S.coefOn
  refine and_congr Iff.rfl (forall_congr' fun u => forall_congr' fun v => forall_congr' fun u' =>
    forall_congr' fun v' => and_congr Iff.rfl ?_)
  have : (d : ℂ)⁻¹ * ⟪u', u⟫_ℂ * star ⟪v', v⟫_ℂ = ⟪u', u⟫_ℂ * ⟪v, v'⟫_ℂ / (d : ℂ) := by
    rw [← inner_conj_symm v v', div_eq_mul_inv]
    simp only [RCLike.star_def]
    ring
  rw [this]

example {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (w u : Hs) :
    ketBra w u = ⟪w, u⟫_ℂ • w := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality
end
end

