import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PrCloudAddPrNode
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BaseVectorTEqOne
section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.Inh

variable {k r : ℕ}

@[reducible] def uniqueIdxZero : Unique (Idx k r 0) :=
  ⟨⟨⟨∅, rfl⟩⟩, fun I => Subtype.ext (Finset.card_eq_zero.1 I.2)⟩

attribute [local instance] uniqueIdxZero

def detPow (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ :=
  (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

def lamDet (n : ℕ) (m : ℤ) : Fin n → ℝ := fun a => (m : ℝ) + Formalism.QuantumDeterminants.rhoStd n a

def z0 (k : ℕ) : Fin (2 * 0 + k + 1) → ℂ := bvec (wI k 0 (Fin.last k))

def posW (k : ℕ) (i : Fin k) : Fin (2 * 0 + k + 1) := ⟨i.val, by omega⟩

def piDet (k : ℕ) (m : ℤ) (g : Mat k 0) : ℂ →L[ℂ] ℂ :=
  detPow k m (g.submatrix (posW k) (posW k))

def lamN (N : ℕ) : Fin (2 * 0 + 1 + 1) → ℝ := ![-(N : ℝ) - 1 / 2, -(2 * N : ℝ) - 1 / 2]

end GlobalTheory.Mom.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst
section
noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc Matrix MeasureTheory
open scoped Classical

namespace GlobalTheory.SgGlob

section Rat
variable {E : Type} [Field E] [NumberField E]

def IntUp {r : ℕ} (u : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  GlobalTheory.SgAlg.IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)

def Tied (σ : E →+* E) (g : ℕ) {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IntUp u ∧ IntUp u' ∧
    (∀ a b : Fin (r + 1), a < b → (g : E)⁻¹ * (u a b - u' a b) ∈ dInv E ((b : ℕ) - a)) ∧
    Z' = GlobalTheory.SgAlg.cT σ u * Z * u'

def eps (K : Type) [CommRing K] (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal fun b => (-1) ^ (r - (b : ℕ))

def AtPt {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ x : Matrix (Fin (r + 1)) (Fin (r + 1)) E × Matrix (Fin (r + 1)) (Fin (r + 1)) E,
    GlobalTheory.SgAlg.IsLo x.1 ∧ GlobalTheory.SgAlg.IsUp x.2 ∧ Z * eps E r = x.1 * w.mat * x.2

def phaseZ (g : ℕ) {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℂ :=
  if h : AtPt w Z then psiInf (-((g : E)⁻¹ * (simpleLow h.choose.1 + simpleUp h.choose.2))) else 0

def ClsAt (σ : E →+* E) (g : ℕ) {r : ℕ} (w : Pt E (r + 1)) : Type :=
  Quot fun Z Z' : {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E // AtPt w Z} => Tied σ g Z.1 Z'.1

def Xs {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (GlobalTheory.SgAlg.eOf P).mulVecLin

def W0 (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Set (Fin n → E) :=
  {v | (GlobalTheory.SgAlg.cT σ P * J) *ᵥ v = 0 ∧ (GlobalTheory.SgAlg.cT σ P' * J) *ᵥ v = 0}

def nrm (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Fin n → E := P' *ᵥ fun b => (GlobalTheory.SgAlg.pairM σ J P' P)⁻¹ b (Fin.last r)

def ScalarPair (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P₁ P₂ : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  (GlobalTheory.SgAlg.pairM σ J P₁ P)⁻¹ (Fin.last r) (Fin.last r) = (GlobalTheory.SgAlg.pairM σ J P₂ P)⁻¹ (Fin.last r) (Fin.last r) ∧
  nrm σ J P P₁ - nrm σ J P P₂ ∈ Xs P ∧
  ∃ δ : Matrix (Fin n) (Fin n) E, GlobalTheory.SgAlg.IsUn σ J δ ∧ latMap δ Λ = Λ ∧ δ * P₁ = P₂ ∧
    (∀ v ∈ Λ, (GlobalTheory.SgAlg.cT σ (GlobalTheory.SgAlg.eOf P₁) * J) *ᵥ v = 0 →
      ∃ x ∈ Λ, x ∈ Xs P ∧ (g : E)⁻¹ • (δ *ᵥ v - v - x) ∈ Λ) ∧
    (∀ v₁ ∈ W0 σ J P P₁, ∃ v₂ ∈ W0 σ J P P₂, v₁ - v₂ ∈ Xs P ∧ δ *ᵥ v₁ - v₂ ∈ Xs P₂) ∧
    δ *ᵥ nrm σ J P₁ P - nrm σ J P₂ P ∈ Xs P₂

def nPartners (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ) (x : Tri E n r)
    (Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℕ∞ :=
  ENat.card (Quot fun P₂ P₃ : {P₂ : Matrix (Fin n) (Fin (r + 1)) E //
      (x.1, x.2.1, P₂) ∈ GenConf σ J T T' g Z₂ ∧ ScalarPair σ J g x.1 x.2.1 x.2.2 P₂} =>
    ∃ ν, GlobalTheory.SgAlg.InN σ J x.2.1 ν ∧ ν * x.2.1 = x.2.1 ∧ latMap ν x.1 = x.1 ∧ ν * P₂.1 = P₃.1)

def pairMass (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ENNReal :=
  ∑' c : Quot (fun x y : GenConf σ J T T' g Z₁ => ∃ γ, IsoTri σ J γ x.1 y.1),
    (ENat.toENNReal (ENat.card {γ // IsoTri σ J γ (Quot.out c).1 (Quot.out c).1}))⁻¹ *
      ENat.toENNReal (nPartners σ J T T' g (Quot.out c).1 Z₂)
end Rat

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)

def Zloc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  Matrix.of fun a b => algebraMap (X.A p).Fp (X.A p).Ep (X.cP p ^ (-(2 * (r : ℤ) - a - b))) * (X.A p).ιE (Z a b)

def Zmod {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  GlobalTheory.SgDen.zz (X.M p) (X.Zloc p Z) * eps (X.A p).Ep r

def tau (p : HeightOneSpectrum (𝓞 F)) (T T' : F) : (X.A p).Ep :=
  tau0 (X.M p) ((X.A p).ιF T) ((X.A p).ιF T')

def Zplus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (X.A p).Ep :=
  X.Zmod p Z - Matrix.single (Fin.last r) (Fin.last r) (X.tau p T T')

def wtLoc {r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (w : Pt E (r + 1))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  (GlobalTheory.SgLoc.orbMeas (X.M p) (X.ptMod r p w) {xy | ∃ l u, GlobalTheory.SgAlg.IsLo l ∧ GlobalTheory.SgAlg.IsUp u ∧
    GlobalTheory.SgDen.IntR (X.M p) l ∧ GlobalTheory.SgDen.IntR (X.M p) u ∧
    GlobalTheory.SgLoc.orbMat (X.ptMod r p w) xy = l * X.Zmod p Z * u}).toReal

def wt {r : ℕ} (w : Pt E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ := ∏ᶠ p, X.wtLoc p w Z

def gramPlus {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
  let l : (X.A p).Ep := GlobalTheory.SgDen.levInv (X.M p)
  let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) (X.A p).Ep :=
    Matrix.fromBlocks 1 (if (X.M p).split.isSome then (-l) • 1 else 0) 0 (l • 1)
  GlobalTheory.SgDen.ct (X.M p).L A *
    Matrix.fromBlocks (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T))) (X.Zloc p Z)
      (GlobalTheory.SgDen.ct (X.M p).L (X.Zloc p Z)) (GlobalTheory.SgAlg.TF r ((X.A p).ιE (algebraMap F E T'))) * A

def densLoc (n : ℕ) {r : ℕ} (T T' : F) (p : HeightOneSpectrum (𝓞 F))
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  GlobalTheory.SgDen.densF (GlobalTheory.SgDen.resQ (X.A p).Fp) (GlobalTheory.SgDen.eta (X.A p).Ep) n (2 * r + 2)
    (GlobalTheory.SgDen.corank (X.M p).L (X.gramPlus T T' p Z))

def dens (n : ℕ) {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ℝ :=
  ∏' p, X.densLoc n T T' p Z

def admitted {r : ℕ} (T T' : F) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ p, GlobalTheory.SgDen.IntR (X.M p) (X.Zplus T T' p Z)

def KtopZ (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  if ∃ p, KtopLoc (X.M p) (X.tau p T T') (X.ptMod r p w) (X.ptMod r p w') = 0 then 0
  else ∏ᶠ p, KtopLoc (X.M p) (X.tau p T T') (X.ptMod r p w) (X.ptMod r p w')

def KAtopZ (r : ℕ) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  X.KtopZ r T T' w w' / ((X.phi r w * X.phi r w' : ℝ) : ℂ)

def KgsM {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : F) (w w' : Pt E (r + 1)) : ℂ :=
  ∑' c : ClsAt (sig : E →+* E) (g₁ * g₂) w × ClsAt (sig : E →+* E) (g₁ * g₂) w',
    ((X.wt w (Quot.out c.1).1 * X.wt w' (Quot.out c.2).1 *
      (pairMass (sig : E →+* E) J (algebraMap F E T) (algebraMap F E T') (g₁ * g₂)
        (Quot.out c.1).1 (Quot.out c.2).1).toReal : ℝ) : ℂ) *
      phaseZ (g₁ * g₂) w (Quot.out c.1).1 * conj (phaseZ (g₁ * g₂) w' (Quot.out c.2).1)

def IsMassConst (k r : ℕ) (J : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E) (T T' : F) (c : ℝ) : Prop :=
  ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E, TotPos (GZ sig T T' Z) → X.admitted T T' Z →
    Mass (sig : E →+* E) J (algebraMap F E T) (algebraMap F E T') (g₁ * g₂) Z =
      ENNReal.ofReal (c * normInf (GZ sig T T' Z) ^ (k - 1) * X.dens (k + 2 * r + 1) T T' Z)

end ModFam

def SpaceOK {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ} (r : ℕ) (J : Matrix (Fin n) (Fin n) E) : Prop :=
  GlobalTheory.SgAlg.IsHermU σ J ∧ (∃ Λ, SelfDual σ J Λ) ∧
    ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin n) (Fin n) ℂ, IsUnit A.det ∧
      J.map τ = Aᴴ * Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r + 1 then (-1 : ℂ) else 1) * A

end GlobalTheory.SgGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Obj
variable {D : D7} {X : HidaSetting D}

def DbL (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ l ∈ k2ends D j δ, ((Nloc (ddS D) D.R.rS l (δ l) : ℚ) : ℝ)

def AmpAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t ∈ relSet Y u, ‖(Y.tO u u).vec t‖ ≤
    Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))

def PairsAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) ≤
      massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')
end Obj

def TypeP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def AmpP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ Cs : ℝ, 0 ≤ Cs →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → AmpAt large₂ Y u CH Cs C

def PairsP : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Ch Cp : ℝ, 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → PairsAt large₂ Y u CH Ch Cp

def NFExC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ t ∈ relSet Y u,
    ∃ N, AdT t N ∧ N.j = jT t ∧ N.T = Tu D u

def LabC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : GTu Y u) N, AdT t N →
    N.j = jT t ∧ N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = fun l => star (labT t l)

def PerRowC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
      (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧
        labT p.2 = δ'') →
      ENNReal.ofReal (∑ p ∈ S, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) ≤
        ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
          (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞) *
            ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
              GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')

def ProdC : Prop :=
  ∀ Cs : ℝ, 0 ≤ Cs → ∃ C₁ : ℕ, 1 ≤ C₁ ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1)
    (CH : ℝ), Std D large₂ → 0 ≤ CH → 40 * D.R.rS ^ 4 ≤ D.R.k → 5 * D.R.rS ≤ D.R.k → ∀ t ∈ relSet Y u, ∀ hj : jT t ≤ D.R.rS, 1 ≤ jT t →
    ∃ (De : D.what₂.Tau → ℝ) (P : ℝ), 0 < P ∧ k2Del D (jT t) (labT t) = P ^ 2 ∧
      (∀ τ, GlobalTheory.Amp.DeOK D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (De τ)) ∧
      ∏ τ, GlobalTheory.Amp.degBd D.R.k D.R.rS (jT t) (C₁ * D.R.k * D.R.rS) (H1C large₂ CH) (De τ)
          (GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ))
          (GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH)) ≤
        (16 * Real.pi * Real.exp 1 / D.R.k) ^ (jT t * (D.R.k - 1 - jT t) * D.R.f) * (P ^ (D.R.k - 1 - jT t))⁻¹ *
          (8 * D.R.rS * H1C large₂ CH) ^ (80 * D.R.rS ^ 4 * D.R.f) * k2S D (H1C large₂ CH) (jT t) (labT t) ^ (-(Cs * D.R.k))
end GlobalTheory.TypeAsm
end
end

