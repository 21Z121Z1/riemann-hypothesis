import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

abbrev Chr (D : D7) : Type := (AE D)ˣ →* Circle

def prodSpan {X X₁ X₂ : Type} (e : X → X₁ × X₂) (P₁ : (X₁ → ℂ) → Prop) (P₂ : (X₂ → ℂ) → Prop) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ f₁ f₂, P₁ f₁ ∧ P₂ f₂ ∧ g = fun w => f₁ (e w).1 * f₂ (e w).2}

def UnifLimit {X : Type} (M : Submodule ℂ (X → ℂ)) (f : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ M, ∀ w, ‖f w - g w‖ ≤ ε

structure TensorSource (ψ : AddChar (AF D.host.F) ℂ) {S A B : HSp D} (d : OrthDec S A B) (T : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (d.boxS T fA fB)

  box_zero : ∀ fA fB, d.boxS T fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resS T).symm (u, 0)) (d.boxS T fA fB) = d.boxS T (heisO ψ A T u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resS T).symm (0, v)) (d.boxS T fA fB) = d.boxS T fA (heisO ψ B T v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f

  om_box : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB →
      omS (d.emb (a, b), h) (d.boxS T fA fB) = d.boxS T (omA (a, h) fA) (omB (b, h) fB)

  om_slice : ∀ (χA χB χT : Chr D) (omS : Rep S T) (omA : Rep A T) (omB : Rep B T),
    IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB →
    ∀ a b h f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ A T (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) ∧
      ∀ u, omS (d.emb (a, b), h) f ((d.resS T).symm (u, v)) =
        omA (a, h) (fun u' => omB (b, h) (fun v' => f ((d.resS T).symm (u', v'))) v) u

structure TensorTarget (ψ : AddChar (AF D.host.F) ℂ) {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) : Prop where

  box_theta : ∀ fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB → IsThetaFunO ψ S T (d.boxT S fA fB)

  box_zero : ∀ fA fB, d.boxT S fA fB 0 = fA 0 * fB 0

  heis_box : ∀ fA fB,
    (∀ u, heisO ψ S T ((d.resT S).symm (u, 0)) (d.boxT S fA fB) = d.boxT S (heisO ψ S A u fA) fB) ∧
    ∀ v, heisO ψ S T ((d.resT S).symm (0, v)) (d.boxT S fA fB) = d.boxT S fA (heisO ψ S B v fB)

  slice_theta : ∀ f, IsThetaFunO ψ S T f →
    (∀ v, IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v))) ∧
    ∀ u, IsThetaFunO ψ S B fun v => f ((d.resT S).symm (u, v))

  dense : ∀ f, IsThetaFunO ψ S T f → UnifLimit (prodSpan (d.resT S) (IsThetaFunO ψ S A) (IsThetaFunO ψ S B)) f

  om_box : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b fA fB, IsThetaFunO ψ S A fA → IsThetaFunO ψ S B fB →
      omT (g, d.emb (a, b)) (d.boxT S fA fB) = d.boxT S (omA (g, a) fA) (omB (g, b) fB)

  om_slice : ∀ (χS χA χB : Chr D) (omT : Rep S T) (omA : Rep S A) (omB : Rep S B),
    IsWeilDatumO ψ S T χS (χA * χB) omT → IsWeilDatumO ψ S A χS χA omA → IsWeilDatumO ψ S B χS χB omB →
    ∀ g a b f, IsThetaFunO ψ S T f → ∀ v,
      IsThetaFunO ψ S A (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) ∧
      ∀ u, omT (g, d.emb (a, b)) f ((d.resT S).symm (u, v)) =
        omA (g, a) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) u

def cj {X Y : Type} (e : Y → X) (f : X → ℂ) : Y → ℂ := fun y => starRingEnd ℂ (f (e y))

theorem cj_cj {X Y : Type} (e : Y → X) (e' : X → Y) (h : ∀ x, e (e' x) = x) (f : X → ℂ) : cj e' (cj e f) = f := by
  funext x; simp [cj, h]

def cjEnd {X Y : Type} (e : Y ≃ X) : Module.End ℂ (X → ℂ) →* Module.End ℂ (Y → ℂ) where
  toFun L :=
    { toFun := fun f => cj e (L (cj e.symm f))
      map_add' := fun f f' => by
        have : cj e.symm (f + f') = cj e.symm f + cj e.symm f' := by funext x; simp [cj]
        rw [this, map_add]; funext y; simp [cj]
      map_smul' := fun c f => by
        have : cj e.symm (c • f) = starRingEnd ℂ c • cj e.symm f := by funext x; simp [cj]
        rw [this, map_smul]; funext y; simp [cj] }
  map_one' := LinearMap.ext fun f => cj_cj e.symm e e.symm_apply_apply f
  map_mul' L L' := LinearMap.ext fun f => by
    show cj e (L (L' (cj e.symm f))) = cj e (L (cj e.symm (cj e (L' (cj e.symm f)))))
    rw [cj_cj e e.symm e.apply_symm_apply]

theorem cjEnd_cj {X Y : Type} (e : Y ≃ X) (L : Module.End ℂ (X → ℂ)) (f : X → ℂ) : cjEnd e L (cj e f) = cj e (L f) := by
  show cj e (L (cj e.symm (cj e f))) = _
  rw [cj_cj e e.symm e.apply_symm_apply]

def conjTarget {S T : HSp D} (om : Rep S T) : Rep S (negSp T) :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((MonoidHom.id _).prodMap (negGA T).symm.toMonoidHom))

def conjSource {S T : HSp D} (om : Rep S T) : Rep (negSp S) T :=
  (cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).symm.toMonoidHom.prodMap (MonoidHom.id _)))

def dagger (S T : HSp D) (x : WO S T) : WO T S := giA S ⬝ (adj x ⬝ gA T)

theorem dagger_dagger (S T : HSp D) (x : WO S T) : dagger T S (dagger S T x) = x := by
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]

def daggerEquiv (S T : HSp D) : WO T S ≃ WO S T where
  toFun := dagger T S
  invFun := dagger S T
  left_inv := dagger_dagger T S
  right_inv := dagger_dagger S T

def conjAdjoint {S T : HSp D} (om : Rep S T) : Rep T S :=
  (cjEnd (daggerEquiv S T)).comp (om.comp (MulEquiv.prodComm : GA D T × GA D S ≃* GA D S × GA D T).toMonoidHom)

structure ConjAdjoint (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where

  theta_neg : ∀ f : WO S T → ℂ, (IsThetaFunO ψ S (negSp T) (cj id f) ↔ IsThetaFunO ψ S T f) ∧
    (IsThetaFunO ψ (negSp S) T (cj id f) ↔ IsThetaFunO ψ S T f)

  heis_neg : ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (negSp T) w (cj id f) = cj id (heisO ψ S T w f) ∧
    heisO ψ (negSp S) T w (cj id f) = cj id (heisO ψ S T w f)

  conj_target : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) ∧
    ∀ om' : Rep S (negSp T), IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (g, negGA T h) (cj id f) = cj id (om (g, h) f)

  conj_source : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) ∧
    ∀ om' : Rep (negSp S) T, IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (negGA S g, h) (cj id f) = cj id (om (g, h) f)

  sympl_dagger : ∀ x y : WO S T, symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y

  act_dagger : ∀ g h (x : WO S T), dagger S T (actO S T g h x) = actO T S h g (dagger S T x)

  theta_dagger : ∀ f : WO S T → ℂ, IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f

  heis_dagger : ∀ (w : WO S T) (f : WO S T → ℂ),
    heisO ψ T S (dagger S T w) (cj (dagger T S) f) = cj (dagger T S) (heisO ψ S T w f)

  conj_adjoint : ∀ (χS χT : Chr D) (om : Rep S T), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ T S χT χS (conjAdjoint om) ∧
    ∀ om' : Rep T S, IsWeilDatumO ψ T S χT χS om' → ∀ g h f, IsThetaFunO ψ S T f →
      om' (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f)

def TensorRule (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    (∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), TensorSource ψ d T) ∧
    (∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), TensorTarget ψ d S) ∧
    ∀ S T : HSp D, ConjAdjoint ψ S T

example {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

example {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

example (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

example (χA χB χT : Chr D) (x x' y : (AE D)ˣ) :
    splitFacO (χA * χB) χT (x * x') y = splitFacO χA χT x y * splitFacO χB χT x' y := by
  simp only [splitFacO, map_mul, MonoidHom.mul_apply, _root_.mul_inv_rev]
  ac_rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def nu0 (μ : Measure (GA D B)) (𝓕 : Set (GA D B)) (φ : WO A B → ℂ) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ∑' x : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ‖φ (actO A B 1 h⁻¹ (ratW B A x))‖ₑ ∂μ

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

def schr (ψ : AddChar (AF D.host.F) ℂ) (w : WO (dblSp A) B) (φ : WO A B → ℂ) : WO A B → ℂ := fun x =>
  ψ (symplO (dblSp A) B (onX A B x) (onY A B (yOf A B w)) +
      symplOH (dblSp A) B (onX A B (xOf A B w)) (onY A B (yOf A B w))) * φ (x + xOf A B w)

def thetaFun (ψ : AddChar (AF D.host.F) ℂ) (φ : WO A B → ℂ) : WO (dblSp A) B → ℂ := fun w =>
  ∑' x : Matrix (Fin B.rank) (Fin A.rank) D.host.E, schr A B ψ w φ (ratW B A x)

def dblBox (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ := fun w => f₁ (fstCols A B w) * conj (f₂ (sndCols A B w))

variable {A B}

def IsDblTranslate (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (F : WO (dblSp A) B → ℂ) (g : GA D (dblSp A))
    (φ' : WO A B → ℂ) : Prop :=
  φ' ∈ schwartzA θ B.rank A.rank ∧ thetaFun A B ψ φ' = omh (g, 1) F

def IsKhatFinite (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
    (F : WO (dblSp A) B → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F' | ∃ k ∈ Khat A a, F' = omh (k, 1) F})

def IsFockTensor (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (sA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ) (sB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (bA : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ) (bB : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (f : WO A B → ℂ) : Prop :=
  ∃ (f₀ : WO A B → ℂ) (P : MvPolynomial (FVar D B.rank A.rank) ℂ), IsThetaFunO ψ A B f₀ ∧
    (∀ τ, IsFockVacAt (heisO ψ A B) θ τ (cplxO (sA τ) (sB τ)) f₀) ∧ f = pureTensorO ψ θ A B sA sB bA bB f₀ P

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def DblGrowth : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χB : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsInfFam θ → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
    ∀ φ ∈ schwartzA θ B.rank A.rank, IsKhatFinite omh a (thetaFun A B ψ φ) →
      ∃ (C : ℝ≥0) (N : ℕ), ∀ g : GA D (dblSp A),
        AllSome (IsDblTranslate ψ θ omh (thetaFun A B ψ φ) g) fun φ' =>
          nu0 A B μ 𝓕 φ' ≤ ((C * ht (dblSp A) g ^ N : ℝ≥0) : ℝ≥0∞)

def ThetaIntLe : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ sA sB bA bB (pA pB : D.what₂.Tau → ℕ), Formalism.IndefR.Fock.Sk.PairSetup ψ θ A B sA sB bA bB pA pB →
    ∀ f₁ f₂, IsFockTensor ψ θ sA sB bA bB f₁ → IsFockTensor ψ θ sA sB bA bB f₂ →
      ∀ g₁ g₂ : GA D A, AllSome (IsDblTranslate ψ θ omh (dblBox A B f₁ f₂) (io A (g₁, g₂))) fun φ' =>
        thetaInt om μ 𝓕 f₁ f₂ g₁ g₂ ≤ nu0 A B μ 𝓕 φ'

def ThetaIntGrowth : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
    ∀ sA sB bA bB (pA pB : D.what₂.Tau → ℕ), Formalism.IndefR.Fock.Sk.PairSetup ψ θ A B sA sB bA bB pA pB →
    ∀ f₁ f₂, IsFockTensor ψ θ sA sB bA bB f₁ → IsFockTensor ψ θ sA sB bA bB f₂ →
      ∃ (C : ℝ≥0) (N : ℕ), ∀ g₁ g₂ : GA D A,
        thetaInt om μ 𝓕 f₁ f₂ g₁ g₂ ≤ ((C * (ht A g₁ * ht A g₂) ^ N : ℝ≥0) : ℝ≥0∞)

def PairGrowth : Prop := DblGrowth A B ∧ ThetaIntLe A B ∧ ThetaIntGrowth A B

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

def ModerateGrowthAniso (D : D7) : Prop :=
  ∀ A B : HSp D, 1 ≤ A.rank → A.rank < B.rank → Cusp.wittIndex B = 0 → PairGrowth A B

def ModerateGrowthIso (D : D7) : Prop :=
  ∀ A B : HSp D, 1 ≤ A.rank → 0 < Cusp.wittIndex B → A.rank + Cusp.wittIndex B < B.rank → PairGrowth A B

def ModerateGrowth (D : D7) : Prop := ∀ A B : HSp D, InRange A B → PairGrowth A B

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add, add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7}

def IsRealParam {m n k : ℕ} (L : (Fin k → ℝ) →+ Mx D m n) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

structure IsSchwartzBruhat {m n : ℕ} (φ : Mx D m n → ℂ) : Prop where

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, φ (x + u) = φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, φ x ≠ 0 → x.map (finPart D) ∈ K

  schwartz : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), IsRealParam L → Function.Injective L →
    ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t)

structure IsMixFamily (ψ : AddChar (AF D.host.F) ℂ) (S₀ T₀ : HSp D) {m n : ℕ} (Φ : Mx D m n → WO S₀ T₀ → ℂ) : Prop where

  theta : ∀ x, IsThetaFunO ψ S₀ T₀ (Φ x)

  schwartz : ∀ w₀, IsSchwartzBruhat fun x => Φ x w₀

  level : ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, Φ (x + u) = Φ x

  level₀ : ∃ U : AddSubgroup (WO S₀ T₀), IsOpen (U : Set (WO S₀ T₀)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, heisO ψ S₀ T₀ u (Φ x) = Φ x

  supp : ∃ K : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, Φ x ≠ 0 → x.map (finPart D) ∈ K

  smooth : ∀ (k l : ℕ) (L : (Fin k → ℝ) →+ Mx D m n) (M : (Fin l → ℝ) →+ WO S₀ T₀), IsRealParam L → IsRealParam M →
    ∀ x w₀, ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin l → ℝ) => Φ (x + L p.1) (w₀ + M p.2)

  decay : ∀ (k l : ℕ) (L : (Fin k → ℝ) →+ Mx D m n) (M : (Fin l → ℝ) →+ WO S₀ T₀), IsRealParam L →
    Function.Injective L → IsRealParam M → ∀ x w₀, ∀ (j N : ℕ) (R : ℝ), ∃ C : ℝ,
      ∀ p : (Fin k → ℝ) × (Fin l → ℝ), ‖p.2‖ ≤ R → ‖p.1‖ ^ N *
        ‖iteratedFDeriv ℝ j (fun q : (Fin k → ℝ) × (Fin l → ℝ) => Φ (x + L q.1) (w₀ + M q.2)) p‖ ≤ C

def IsRatSum {m n : ℕ} (φ : Mx D m n → ℂ) (c : ℂ) : Prop :=
  (Summable fun γ : Matrix (Fin m) (Fin n) D.host.E => ‖φ (rat γ)‖) ∧
    HasSum (fun γ : Matrix (Fin m) (Fin n) D.host.E => φ (rat γ)) c

def ExpansionS (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) : Prop :=
  (∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsMixFamily ψ S₀ T (d.mixS T ψ μ 𝓕 f) ∧
    IsRatSum (fun x => d.mixS T ψ μ 𝓕 f x 0) (f 0) ∧
    (∀ x₁ x : Mx D T.rank ρ,
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x₁) f) x = d.mixS T ψ μ 𝓕 f (x + x₁)) ∧
    (∀ (w₁ : WO S₀ T) (x : Mx D T.rank ρ),
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.ext0 T w₁) f) x = heisO ψ S₀ T w₁ (d.mixS T ψ μ 𝓕 f x)) ∧
    (∀ y x : Mx D T.rank ρ,
      d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extY T y) f) x =
        ψ (symplO S T (d.extX T x) (d.extY T y)) • d.mixS T ψ μ 𝓕 f x)) ∧
  ∀ Φ : Mx D T.rank ρ → WO S₀ T → ℂ, IsMixFamily ψ S₀ T Φ →
    ∃! f : WO S T → ℂ, IsThetaFunO ψ S T f ∧ d.mixS T ψ μ 𝓕 f = Φ

def ExpansionT (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) : Prop :=
  (∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsMixFamily ψ S T₀ (d.mixT S ψ μ 𝓕 f) ∧
    IsRatSum (fun y => d.mixT S ψ μ 𝓕 f y 0) (f 0) ∧
    (∀ y₁ y : Mx D S.rank ρ,
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S y₁) f) y = d.mixT S ψ μ 𝓕 f (y + y₁)) ∧
    (∀ (w₁ : WO S T₀) (y : Mx D S.rank ρ),
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S w₁) f) y = heisO ψ S T₀ w₁ (d.mixT S ψ μ 𝓕 f y)) ∧
    (∀ (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ),
      d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
        ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • d.mixT S ψ μ 𝓕 f y)) ∧
  ∀ Φ : Mx D S.rank ρ → WO S T₀ → ℂ, IsMixFamily ψ S T₀ Φ →
    ∃! f : WO S T → ℂ, IsThetaFunO ψ S T f ∧ d.mixT S ψ μ 𝓕 f = Φ

def MixExpansion (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)),
      IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ExpansionS ψ d T μ 𝓕) ∧
    (∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)),
      IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ExpansionT ψ d S μ 𝓕)

theorem MixExpansion.std (h : MixExpansion D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) : ExpansionS ψ d T μ 𝓕 :=
  (h ψ hψ.1).1 S S₀ T ρ d μ 𝓕 hμ

end GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

end
end

