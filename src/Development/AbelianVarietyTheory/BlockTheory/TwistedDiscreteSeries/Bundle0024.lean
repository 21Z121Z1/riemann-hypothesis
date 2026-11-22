import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {D : D7}

def halfMod {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) : ℝ :=
  ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : NNReal) : ℝ) ^ ((n : ℝ) / 2)

def starAdj (S T : HSp D) (x : WO S T) : Mx D S.rank T.rank :=
  incA D D.host.xi0 • (giA S ⬝ (adj x ⬝ gA T))

def ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) : WO S T :=
  incA D (-D.host.xi0⁻¹) • (giA T ⬝ (adj z ⬝ gA S))

theorem starAdj_ofAdj (S T : HSp D) (z : Mx D S.rank T.rank) : starAdj S T (ofAdj S T z) = z := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul, Matrix.mul_assoc, Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

structure FormulasS {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om₀ : GA D S₀ × GA D T →* Module.End ℂ (WO S₀ T → ℂ))
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) : Prop where

  target : ∀ (h : GA D T) (x : Mx D T.rank ρ),
    d.mixS T ψ μ 𝓕 (om (1, h) f) x = om₀ (1, h) (d.mixS T ψ μ 𝓕 f (mt T h⁻¹ ⬝ x))

  core : ∀ (g₀ : GA D S₀) (x : Mx D T.rank ρ),
    d.mixS T ψ μ 𝓕 (om (d.emb0 g₀, 1) f) x = om₀ (g₀, 1) (d.mixS T ψ μ 𝓕 f x)

  levi : ∀ (a : GL (Fin ρ) (AE D)) (x : Mx D T.rank ρ),
    d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) x =
      ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (halfMod T.rank a : ℂ)) •
        d.mixS T ψ μ 𝓕 f (x ⬝ a.1)

  unip : ∀ (b : Mx D ρ S₀.rank) (x : Mx D T.rank ρ),
    d.mixS T ψ μ 𝓕 (om (d.nB b, 1) f) x = heisO ψ S₀ T (x ⬝ b) (d.mixS T ψ μ 𝓕 f x)

  centre : ∀ (c : skewA D ρ) (x : Mx D T.rank ρ),
    d.mixS T ψ μ 𝓕 (om (d.nC c, 1) f) x =
      ψ (symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1))) • d.mixS T ψ μ 𝓕 f x

structure FormulasT {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (χS : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om₀ : GA D S × GA D T₀ →* Module.End ℂ (WO S T₀ → ℂ))
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) : Prop where

  source : ∀ (g : GA D S) (y : Mx D S.rank ρ),
    d.mixT S ψ μ 𝓕 (om (g, 1) f) y = om₀ (g, 1) (d.mixT S ψ μ 𝓕 f (mt S g⁻¹ ⬝ y))

  core : ∀ (h₀ : GA D T₀) (y : Mx D S.rank ρ),
    d.mixT S ψ μ 𝓕 (om (1, d.emb0 h₀) f) y = om₀ (1, h₀) (d.mixT S ψ μ 𝓕 f y)

  levi : ∀ (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ),
    d.mixT S ψ μ 𝓕 (om (1, d.levi a) f) y =
      (((χS (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) * (halfMod S.rank a : ℂ)) •
        d.mixT S ψ μ 𝓕 f (y ⬝ a.1)

  unip : ∀ (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ),
    d.mixT S ψ μ 𝓕 (om (1, d.nB b) f) y = heisO ψ S T₀ (ofAdj S T₀ (y ⬝ b)) (d.mixT S ψ μ 𝓕 f y)

  centre : ∀ (c : skewA D ρ) (y : Mx D S.rank ρ),
    d.mixT S ψ μ 𝓕 (om (1, d.nC c) f) y = ψ (d.qT S c y) • d.mixT S ψ μ 𝓕 f y

def MixedSource (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (om₀ : GA D S₀ × GA D T →* Module.End ℂ (WO S₀ T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 →
    ∀ f, IsThetaFunO ψ S T f → FormulasS d ψ χT om om₀ μ 𝓕 f

def MixedTarget (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (om₀ : GA D S × GA D T₀ →* Module.End ℂ (WO S T₀ → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T₀ χS χT om₀ →
    ∀ (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 →
    ∀ f, IsThetaFunO ψ S T f → FormulasT d ψ χS om om₀ μ 𝓕 f

def MixedModelFormulas (D : D7) : Prop := MixedSource D ∧ MixedTarget D

def MixedValues (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)),
      IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x, IsThetaFunO ψ S₀ T (d.mixS T ψ μ 𝓕 f x)) ∧
    ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ y, IsThetaFunO ψ S T₀ (d.mixT S ψ μ 𝓕 f y)

def gramSkew (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) : Mx D ρ ρ :=
  (-incA D D.host.xi0) • (adj x ⬝ (gA T ⬝ x))ᵀ

def CentralTerms (D : D7) : Prop :=
  (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    (∀ x : Mx D T.rank ρ, starAdj S T (d.extX T x) ⬝ x = d.jY ⬝ (gramSkew T x).map (cA D)) ∧
    (∀ (c : skewA D ρ) (x : Mx D T.rank ρ), symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) =
      -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
        Algebra.trace (AF D.host.F) (AE D) ((gramSkew T x).map (cA D) ⬝ c.1).trace)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      (∀ (x : Mx D T.rank ρ) (c c' : skewA D ρ), ψ (d.qS T (c + c') x) = ψ (d.qS T c x) * ψ (d.qS T c' x)) ∧
      (∀ x ∈ ratMx D T.rank ρ, ∀ c : skewA D ρ, c.1 ∈ ratMx D ρ ρ → ψ (d.qS T c x) = 1) ∧
      ∀ x ∈ ratMx D T.rank ρ, ∀ x' ∈ ratMx D T.rank ρ,
        (∀ c : skewA D ρ, ψ (d.qS T c x) = ψ (d.qS T c x')) ↔ gramSkew T x = gramSkew T x') ∧
  ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ),
    d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y ⬝ (gA S ⬝ y))) ⬝ c.1).trace)

def HeisenbergTarget (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f →
        (∀ (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ), d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
          ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • d.mixT S ψ μ 𝓕 f y) ∧
        (∀ (w₀ : WO S T₀) (y : Mx D S.rank ρ), d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S w₀) f) y =
          heisO ψ S T₀ w₀ (d.mixT S ψ μ 𝓕 f y)) ∧
        HasSum (fun y : Matrix (Fin S.rank) (Fin ρ) D.host.E => d.mixT S ψ μ 𝓕 f (rat y) 0) (f 0)

theorem halfMod_pos {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) : 0 < halfMod n a := by
  refine Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 fun h => ?_)) _
  have := (GlobalTheory.Doubling.absE D.host.F D.host.E).map_mul (Matrix.GeneralLinearGroup.det a)
    (Matrix.GeneralLinearGroup.det a)⁻¹
  rw [h, zero_mul, mul_inv_cancel, map_one] at this
  exact one_ne_zero this

theorem wittSmallProjection_wittNB_inv_mul_adjointInclusion {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (b : Mx D ρ T₀.rank) (y : Mx D S.rank ρ) :
    d.p0 ⬝ (mt T (d.nB b)⁻¹ ⬝ d.incAdj S y) = ofAdj S T₀ (y ⬝ b) := by
  rw [d.nB_inv, ← Matrix.mul_assoc, d.wittDecomp_projAnisotropic_unipotentMixed, HypDec.incAdj_apply, HypDec.incY_apply, ← Matrix.mul_assoc, Matrix.sub_mul,
    Matrix.mul_assoc _ d.pY, d.p0_jY, d.pY_jY, Matrix.mul_one, zero_sub, plus_neg, neg_neg, ofAdj, plus, adj_mul,
    Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Doubling
open MeasureTheory Matrix
open scoped TensorProduct ContDiff ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def resL (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j))

def resR (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j))

def lagr (A B : HSp D) (w : WO A B) : WO (dblSp A) B :=
  Matrix.of fun i j => Sum.elim (fun k => w i k) (fun k => -w i k) (finSumFinEquiv.symm j)

def delta (A B : HSp D) (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ :=
  fun x => f₁ (resL A B x) * conj (f₂ (-resR A B x))

def ip (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) : ℂ :=
  ∫ w in 𝓕, f₁ w * conj (f₂ w) ∂ν

def evZero (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : ℂ :=
  ∫ w in 𝓕, φ (lagr A B w) ∂ν

def swSec (A B : HSp D) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => evZero A B ν 𝓕 (omh (g, 1) φ)

def sZero (A B : HSp D) : ℂ := ((B.rank : ℂ) - (A.rank : ℂ)) / 2

def IsKFinVec {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Subgroup (GA D S))
    (φ : WO S T → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = om (k, 1) φ})

def IsSmoothOn (V : HSp D) (Φ : GA D V → ℂ) : Prop :=
  Continuous Φ ∧
  (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, Φ (g * k) = Φ g) ∧
  ∀ θ : InfFam D, IsInfFam θ →
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

section Clauses

variable (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
  (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
  (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))

def ThetaClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) ∧
    ∀ (g₁ g₂ : GA D A) (h : GA D B),
      omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
        (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) ∧
      thetaKO omh (io A (g₁, g₂)) h (delta A B f₁ f₂) =
        thetaKO om g₁ h f₁ * conj (thetaKO om g₂ h f₂) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ)

variable (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def SectionClause : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) B φ →
    IntegrableOn (fun w => φ (lagr A B w)) 𝓕 ν ∧
    (∀ h : GA D B, evZero A B ν 𝓕 (omh (1, h) φ) = evZero A B ν 𝓕 φ) ∧
    (∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) =
      (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g) ∧
    IsSmoothOn (dblSp A) (swSec A B omh ν 𝓕 φ) ∧
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → IsKFinVec omh (Khat A a) φ →
      swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B)

def CoefClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ ∧
    ∀ g : GA D A, swSec A B omh ν 𝓕 (delta A B f₁ f₂) (io A (g, 1)) = ip A B ν 𝓕 (om (g, 1) f₁) f₂

end Clauses

def DoublingIso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∃ omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ ThetaClause ψ A B χB om omh ∧
      AllSome (fun m : Measure (WO A B) × Set (WO A B) => IsCovolOne (ratL B A) m.1 m.2) fun m =>
        SectionClause ψ A B χB omh m.1 m.2 ∧ CoefClause ψ A B om omh m.1 m.2

section Basic₂

variable (A B : HSp D)

@[simp] theorem resL_lagr (w : WO A B) : resL A B (lagr A B w) = w := by
  ext i j; simp [resL, lagr]

@[simp] theorem resR_lagr (w : WO A B) : resR A B (lagr A B w) = -w := by
  ext i j; simp only [resR, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.neg_apply]

theorem delta_lagr (f₁ f₂ : WO A B → ℂ) (w : WO A B) : delta A B f₁ f₂ (lagr A B w) = f₁ w * conj (f₂ w) := by
  simp [delta]

theorem evZero_delta (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) :
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ := by
  simp only [evZero, ip, delta_lagr]

example : sZero A B + (A.rank : ℂ) / 2 = (B.rank : ℂ) / 2 := by rw [sZero]; ring

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.MixModel GlobalTheory.Grow
open scoped TensorProduct NNReal ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

variable {D : D7}

abbrev Letter (D : D7) (m n : ℕ) : Type := D.what₂.Tau × Fin m × Fin n × Bool

def Letter.mat {m n : ℕ} (a : Letter D m n) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)

section Semi

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))

def wordOp (w : List (Letter D T.rank S.rank)) (f : WO S T → ℂ) : WO S T → ℂ :=
  w.foldr (fun a φ => dRho (heisO ψ S T) θ a.1 a.mat φ) f

open Classical in

def semiOn (P : D.what₂.Tau → Prop) (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (d + 1), ∑ w : Fin k → Letter D T.rank S.rank,
    if ∀ i, P (w i).1 then eLpNorm (wordOp ψ θ S T (List.ofFn w) f) 2 (μ.restrict 𝓕) else 0

def semi (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ := semiOn ψ θ S T μ 𝓕 (fun _ => True) d f

def HasLevel (U : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f

def coef (f : WO S T → ℂ) (a : WO S T) : ℂ := ∫ w in 𝓕, heisO ψ S T a f w * starRingEnd ℂ (f w) ∂μ

def IsPureAt (τ : D.what₂.Tau) (f : WO S T → ℂ) : Prop :=
  ∀ a b : WO S T, a.map (finPart D) = 0 → (∀ τ', τ' ≠ τ → compAt θ τ' a = 0) → compAt θ τ b = 0 →
    coef ψ S T μ 𝓕 f (a + b) * coef ψ S T μ 𝓕 f 0 = coef ψ S T μ 𝓕 f a * coef ψ S T μ 𝓕 f b

end Semi

section Sums

variable {S S₀ T T₀ : HSp D} {ρ ρ' : ℕ} (ψ : AddChar (AF D.host.F) ℂ)

def absSum (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ μ 𝓕 f x 0‖ₑ

def absSum₂ (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ') (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))
    (μ' : Measure (Mx D ρ' S₀.rank)) (𝓕' : Set (Mx D ρ' S₀.rank)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' x : ratMx D T.rank ρ, ∑' y : ratMx D S₀.rank ρ', ‖d'.mixT S₀ ψ μ' 𝓕' (d.mixS T ψ μ 𝓕 f x) y 0‖ₑ

def comb {n : ℕ} (u : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (l : Fin n → AF D.host.F) : WO S T :=
  ∑ i, algebraMap (AF D.host.F) (AE D) (l i) • (rat (u i) : Mx D T.rank S.rank)

variable (S T) in

def IsLagPair (u u' : Fin (S.rank * T.rank) → Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  ∀ i j, symplO S T (rat (u i)) (rat (u j)) = 0 ∧ symplO S T (rat (u' i)) (rat (u' j)) = 0 ∧
    symplO S T (rat (u i)) (rat (u' j)) = if i = j then 1 else 0

def ratVec (D : D7) (n : ℕ) : AddSubgroup (Fin n → AF D.host.F) :=
  ((algebraMap D.host.F (AF D.host.F)).toAddMonoidHom.compLeft (Fin n)).range

def lagVal {n : ℕ} (u u' : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (μ : Measure (Fin n → AF D.host.F))
    (𝓕 : Set (Fin n → AF D.host.F)) (f : WO S T → ℂ) (l : Fin n → AF D.host.F) : ℂ :=
  ∫ a in 𝓕, heisO ψ S T (comb u' a) (heisO ψ S T (comb u l) f) 0 ∂μ

def lagSum {n : ℕ} (u u' : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E) (μ : Measure (Fin n → AF D.host.F))
    (𝓕 : Set (Fin n → AF D.host.F)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∑' l : ratVec D n, ‖lagVal ψ u u' μ 𝓕 f l‖ₑ

end Sums

section Lift

variable {S T : HSp D}

variable (T) in

def RapidMeas (G : GA D T → ℂ) : Prop :=
  (∀ γ ∈ GQ T, ∀ h, G (γ * h) = G h) ∧ Measurable G ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G h‖ * quotHeight T h ^ N ≤ C

theorem rapidMeas_of_rapidDec {G : GA D T → ℂ} (h : RapidDec T G) : RapidMeas T G :=
  ⟨h.1, h.2.1.measurable, h.2.2⟩

def weightInt (A : ℕ) (ν : Measure (GA D T)) (𝓖 : Set (GA D T)) (G : GA D T → ℂ) : ℝ≥0∞ :=
  ∫⁻ h in 𝓖, ENNReal.ofReal (quotHeight T h ^ A) * ‖G h‖ₑ ∂ν

def lift (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D T)) (𝓖 : Set (GA D T))
    (f : WO S T → ℂ) (G : GA D T → ℂ) : GA D S → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓖 (thetaKO om) f G

def dOm (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (X : Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => deriv (fun t : ℝ => om (oneP θ S τ X t, 1) f w) 0

end Lift

section Statements

variable (A d : ℕ) {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (θ : InfFam D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))

structure PairBounds : Prop where

  semi_ne_top : ∀ k f, IsThetaFunO ψ S T f → semi ψ θ S T μ 𝓕 k f ≠ ∞

  mix : ∀ (S₀ : HSp D) (ρ : ℕ) (e : HypDec S S₀ ρ) (μ₁ : Measure (Mx D T.rank ρ)) (𝓕₁ : Set (Mx D T.rank ρ)),
    IsCovolOne (ratMx D T.rank ρ) μ₁ 𝓕₁ → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      (∀ g h, absSum ψ e μ₁ 𝓕₁ (om (g, h) f) ≤
        C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)) ∧
      ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
        ∀ G, RapidMeas T G → ∀ g, ∫⁻ h in 𝓖, absSum ψ e μ₁ 𝓕₁ (om (g, h) f) * ‖G h‖ₑ ∂ν ≤
          C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal (height S g ^ A) * weightInt A ν 𝓖 G

  mix₂ : ∀ (S₀ T₀ : HSp D) (ρ ρ' : ℕ) (e : HypDec S S₀ ρ) (e' : HypDec T T₀ ρ')
    (μ₁ : Measure (Mx D T.rank ρ)) (𝓕₁ : Set (Mx D T.rank ρ))
    (μ₂ : Measure (Mx D ρ' S₀.rank)) (𝓕₂ : Set (Mx D ρ' S₀.rank)),
    IsCovolOne (ratMx D T.rank ρ) μ₁ 𝓕₁ → IsCovolOne (ratMx D ρ' S₀.rank) μ₂ 𝓕₂ →
    ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f → ∀ g h,
      absSum₂ ψ e e' μ₁ 𝓕₁ μ₂ 𝓕₂ (om (g, h) f) ≤
        C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)

  weight_ne_top : ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
    ∀ G, RapidMeas T G → weightInt A ν 𝓖 G ≠ ∞

  lift_le : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
        ∀ G, RapidMeas T G → ∀ g, IntegrableOn (fun h => thetaKO om g h f * G h) 𝓖 ν ∧
          ‖lift om ν 𝓖 f G g‖ₑ ≤ C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal (height S g ^ A) * weightInt A ν 𝓖 G

  dOm_theta : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, IsThetaFunO ψ S T f →
    (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, 1) f w) (dOm om θ τ X f w) 0) ∧
      IsThetaFunO ψ S T (dOm om θ τ X f) ∧ ∀ U, HasLevel ψ S T U f → HasLevel ψ S T U (dOm om θ τ X f)

  dOm_cont : ∀ τ, ∀ X ∈ lieAt S τ, ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ k : ℕ,
    ∃ (k' : ℕ) (C : ℝ≥0), ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
      semi ψ θ S T μ 𝓕 k (dOm om θ τ X f) ≤ C * semi ψ θ S T μ 𝓕 k' f

  lift_deriv : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, IsThetaFunO ψ S T f →
    ∀ (ν : Measure (GA D T)) (𝓖 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓖 ν →
      ∀ G, RapidMeas T G → ∀ g,
        HasDerivAt (fun t : ℝ => lift om ν 𝓖 f G (g * oneP θ S τ X t)) (lift om ν 𝓖 (dOm om θ τ X f) G g) 0

def LagBound : Prop :=
  ∀ u u' : Fin (S.rank * T.rank) → Matrix (Fin T.rank) (Fin S.rank) D.host.E, IsLagPair S T u u' →
    ∀ (μ₁ : Measure (Fin (S.rank * T.rank) → AF D.host.F)) (𝓕₁ : Set (Fin (S.rank * T.rank) → AF D.host.F)),
      μ₁.IsAddHaarMeasure → IsAddFundamentalDomain (ratVec D (S.rank * T.rank)) 𝓕₁ μ₁ → μ₁ 𝓕₁ = 1 →
      ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
      ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f → ∀ g h,
        lagSum ψ u u' μ₁ 𝓕₁ (om (g, h) f) ≤ C * semi ψ θ S T μ 𝓕 d f * ENNReal.ofReal ((height S g * height T h) ^ A)

def TensorBound : Prop :=
  ∀ τ f, IsThetaFunO ψ S T f → IsPureAt ψ θ S T μ 𝓕 τ f →
    semi ψ θ S T μ 𝓕 d f * eLpNorm f 2 (μ.restrict 𝓕) ≤
      2 ^ d * semiOn ψ θ S T μ 𝓕 (fun τ' => τ' = τ) d f * semiOn ψ θ S T μ 𝓕 (fun τ' => τ' ≠ τ) d f

end Statements

def ForPairs (D : D7) (n : ℕ)
    (P : ∀ {S T : HSp D}, AddChar (AF D.host.F) ℂ → (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) → InfFam D →
      Measure (WO S T) → Set (WO S T) → Prop) : Prop :=
  ∀ S T : HSp D, S.rank * T.rank = n → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
      IsCovolOne (ratMx D T.rank S.rank) μ 𝓕 → P ψ om θ μ 𝓕

def ThetaGrowth : Prop :=
  ∀ deg n : ℕ, ∃ A d : ℕ, ∀ D : D7, Module.finrank ℚ D.host.F = deg →
    ForPairs D n fun ψ om θ μ 𝓕 => PairBounds A d ψ om θ μ 𝓕

def ThetaGrowthAt (D : D7) : Prop :=
  ∀ n : ℕ, ∃ A d : ℕ, ForPairs D n fun ψ om θ μ 𝓕 => PairBounds A d ψ om θ μ 𝓕

def ThetaGrowthFull : Prop :=
  ∀ deg n : ℕ, ∃ A d : ℕ, ∀ D : D7, Module.finrank ℚ D.host.F = deg →
    ForPairs D n fun ψ om θ μ 𝓕 =>
      PairBounds A d ψ om θ μ 𝓕 ∧ LagBound A d ψ om θ μ 𝓕 ∧ TensorBound d ψ θ μ 𝓕

theorem ThetaGrowth.at (h : ThetaGrowth) (D : D7) : ThetaGrowthAt D := fun n =>
  let ⟨A, d, H⟩ := h _ n
  ⟨A, d, H D rfl⟩

theorem ThetaGrowthFull.thetaGrowth (h : ThetaGrowthFull) : ThetaGrowth := fun deg n =>
  let ⟨A, d, H⟩ := h deg n
  ⟨A, d, fun D hD S T hn ψ χS χT om ho θ hθ μ 𝓕 hμ => (H D hD S T hn ψ χS χT om ho θ hθ μ 𝓕 hμ).1⟩

section Basic₂

variable {A d : ℕ} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {θ : InfFam D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

example (f : WO S T → ℂ) : semi ψ θ S T μ 𝓕 0 f = eLpNorm f 2 (μ.restrict 𝓕) := by
  simp [semi, semiOn, wordOp]

theorem PairBounds.rder_lift (H : PairBounds A d ψ om θ μ 𝓕) {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D T)} {𝓖 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓖 : IsFundamentalDomain (GQ T) 𝓖 ν) {G : GA D T → ℂ} (hG : RapidMeas T G) :
    Rder θ S τ X (lift om ν 𝓖 f G) = lift om ν 𝓖 (dOm om θ τ X f) G :=
  funext fun g => (H.lift_deriv τ X hX f hf ν 𝓖 hν h𝓖 G hG g).deriv

theorem PairBounds.modGrowthExp_lift (H : PairBounds A d ψ om θ μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {ν : Measure (GA D T)} {𝓖 : Set (GA D T)} (hν : ν.IsHaarMeasure) (h𝓖 : IsFundamentalDomain (GQ T) 𝓖 ν)
    {G : GA D T → ℂ} (hG : RapidMeas T G) : ModGrowthExp S A (lift om ν 𝓖 f G) := by
  obtain ⟨U, hU, hfU⟩ := hf.level
  obtain ⟨C, hC⟩ := H.lift_le U hU
  have h1 := H.semi_ne_top d f hf
  have h2 := H.weight_ne_top ν 𝓖 hν h𝓖 G hG
  refine ⟨(C * semi ψ θ S T μ 𝓕 d f * weightInt A ν 𝓖 G).toReal, fun g => ?_⟩
  have h3 := (hC f hf hfU ν 𝓖 hν h𝓖 G hG g).2
  rw [mul_right_comm] at h3
  have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h1) h2) ENNReal.ofReal_ne_top) h3
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos (height_pos S g) A).le] at h4

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms

end
end

