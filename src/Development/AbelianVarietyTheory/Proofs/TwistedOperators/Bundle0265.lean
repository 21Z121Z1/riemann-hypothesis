import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

def NoLow (X : ProvA) (p q : ℕ) {r s : ℕ} (lam' : Ix r s → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ (MM : GKMod (p - i) (q - i))
    (f : Pol (p - i) (q - i) r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
    Formalism.BasicNotions.TH.IsIntw (X.fock (p - i) (q - i) r s) MM (X.ds r s lam').HK f → f = 0

structure Rule (X : ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop where
  pos : 1 ≤ p + q
  pos' : 1 ≤ r + s
  par : IsParam lam
  par' : IsParam lam'
  down : Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam'
  line : Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam'
  low : NoLow X p q lam'

def RulePar (X : ProvA) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (p q r s : ℕ) (l₁ l₂ l₁' l₂' : List ℚ), l₁.length = p ∧ l₂.length = q ∧ l₁'.length = r ∧ l₂'.length = s ∧
    Rule X (ofBlocks l₁ l₂ : Ix p q → ℚ) (ofBlocks l₁' l₂' : Ix r s → ℚ) ∧
    S = dualPar (signed l₁ l₂ aT) ∧ S' = dualPar (signed l₁' l₂' aS)

def ThetaPar (t : ℕ) (P P' : SPar) (c c' : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, P = signed (al ++ be) (ga ++ de) c ∧
    ((Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ P' = signed (al ++ block t ++ de) (ga ++ be) c') ∨
      (Formalism.MainNotions.SchurIrreducible.DataARm t al be ga de ∧ P' = signed (al ++ de) (ga ++ block t ++ be) c'))

def PairPar (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (t : ℕ) (P P' : SPar), S = dualPar P ∧ S' = dualPar P' ∧
    ((ThetaPar t P P' aT aS ∧ GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) P) ∨ ThetaPar t P' P aS aT)

def partner (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) : SPar :=
  (P.image fun x => (x.1 - c + c', if x.1 < c then !x.2 else x.2)) ∪ (TPar.block c' t).image fun x => (x, b)

def GapOver (P : SPar) (h : ℚ) : Prop := ∀ x ∈ P, ∀ y ∈ P, x.2 ≠ y.2 → h < |x.1 - y.1|

def att (c : ℚ) (n : ℕ) : ℚ := if Odd n then c - 1 / 2 else c

variable {D : D7}

structure Inputs (D : D7) (X : ProvA) : Prop where
  chosen : GlobalTheory.Chain.RealIt.ChosenSeries X
  hc : GlobalTheory.Published.HarishChandraModules
  decay : GlobalTheory.Published.CuspRapidDecay
  bridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D
  vacChar : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D
  lie : LieFockAll D
  cpt : CompactFockAll D
  dense : FockDense D
  laws : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D
  const : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D
  ext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D

def IsWeilExp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (aS aT : D.what₂.Tau → ℚ) (ω : WRep V W) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χS χT ω ∧ ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)

def LowFock (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ), IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
      Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

def LowAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f' : WO V' W → ℂ), IsThetaFunO ψ V' W f' →
      Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def CuspAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (_M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      IsCuspFun V (Lift.liftInt ν 𝓕 (thetaKO ω) f (F v))

def LiftsM (θ : InfFam D) {A B : HSp D} {SA SB : D.what₂.Tau → SPar} (MA : DSModel A SA) (MB : DSModel B SB) {P : Type}
    (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) (K : P → GA D B → GA D A → ℂ) (It : P → SmT MA → SmT MB) : Prop :=
  ∀ F ∈ MultT θ MA ∅ 1, ∃ F' ∈ MultT θ MB ∅ 1, ∀ (p : P) (v : SmT MA) (h : GA D B),
    IntegrableOn (fun g => K p h g * F v g) 𝓕 ν ∧ ∫ g in 𝓕, K p h g * F v g ∂ν = F' (It p v) h

def PairLifts (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (f₀ : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsVacVec ψ θ M M' f₀ →
      IsItW θ M M' ω (ptOf ψ θ M M' f₀) It →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ f, IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f →
      LiftsM θ M' M ν 𝓕 (fun P g h => thetaKO ω g h (ptOf ψ θ M M' f P)) fun P v => It P v

structure IsIntwF {V W : HSp D} {S S' : D.what₂.Tau → SPar} {Z P : Type} (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (pt : P → (Z → ℂ))
    (It : P → SmT M' →ₗ[ℂ] SmT M) : Prop where
  ne : ∃ φ, It φ ≠ 0
  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖
  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))
  eqg : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ Y (It φ v) (It φ' v)
  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v
  invg : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ Y v v' → It φ' v + It φ v' = 0

structure ModelTr (σ : ℂ →+* ℂ) (ε : Bool) (θ : InfFam D) {V : HSp D} {S S₁ : D.what₂.Tau → SPar}
    (M₁ : DSModel (sgn ε V) S₁) (M : DSModel V S) (κ : SmT M₁ ≃+ SmT M) : Prop where
  smul : ∀ (c : ℂ) x, κ (c • x) = σ c • κ x
  cart : ∀ τ, cart M₁ τ = sgnM ε (cart M τ)
  act : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y,
    inclT M₁ y = actT M₁ τ g (inclT M₁ x) ↔ inclT M (κ y) = actT M τ g (inclT M (κ x))
  der : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ x y, DerT M₁ τ Y x y ↔ DerT M τ Y (κ x) (κ y)
  ell : ∀ w₁, ∃ w, ∀ x, ellT M₁ w₁ (inclT M₁ x) = σ (ellT M w (inclT M (κ x)))
  vec : ∀ v₁ : M₁.Vec, ∃ v : M.Vec, κ (PiTensorProduct.tprod ℂ v₁) = PiTensorProduct.tprod ℂ v ∧
    ∀ τ, ‖(v τ : M.H τ)‖ = ‖(v₁ τ : M₁.H τ)‖
  mult : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ M₁ ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))
  mult' : ∀ F₁ ∈ MultT θ M₁ ∅ 1, ∃ F ∈ MultT θ M ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))

structure SgnLaw (θ : InfFam D) (ε : Bool) (V : HSp D) : Prop where
  rat : ∀ g, g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V
  fin : ∀ g, g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V
  inf : ∀ g, g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V
  grp : ∀ τ, Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ)
  lie : ∀ τ, lieAt (sgn ε V) τ = lieAt V τ
  atTau : ∀ τ g, ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g
  meas : ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν

def adjO (S T : HSp D) (y : WO T S) : WO S T :=
  HMul.hMul (HMul.hMul (T.gram⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose)
    (S.gram.map (incA D))

def dag (S T : HSp D) (f : WO S T → ℂ) : WO T S → ℂ := fun y => starRingEnd ℂ (f (adjO S T y))

structure AdjLaw (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where
  invol : ∀ x : WO S T, adjO S T (adjO T S x) = x
  add : ∀ y y' : WO T S, adjO S T (y + y') = adjO S T y + adjO S T y'
  cont : Continuous (adjO S T)
  sympl : ∀ y y' : WO T S, symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y'
  act : ∀ (g : GA D S) (h : GA D T) (y : WO T S), adjO S T (actO T S h g y) = actO S T g h (adjO S T y)
  rat : ∀ y : WO T S, adjO S T y ∈ ratL T S ↔ y ∈ ratL S T
  half : ∀ (e : AE D) (y : WO T S), IsHalf e y → IsHalf (cA D e) (adjO S T y)
  Heisenberg₂ : ∀ (y : WO T S) (f : WO S T → ℂ), heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f)
  theta : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]
      exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases hab : a = b
        · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
        · simp [Formalism.REAL.Jm, hab]
      show _ = gramAt D (neg V) τ
      rw [e, h, ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn ε A).cart τ = sgnM ε (A.cart τ) := by

  have hJ : Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) = sgnM ε (Formalism.REAL.Jm (A.ε τ)) := by
    cases ε
    · simp [sgnM]
    · simp only [sgnM, cond_true, Formalism.REAL.Jm, Bool.true_xor]
      rw [Matrix.diagonal_neg]
      congr 1
      funext a
      cases A.ε τ a <;> simp
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) * A.fr τ = sgnM ε ((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [hJ]
  cases ε
  · rfl
  · simp only [sgnM, cond_true, Matrix.mul_neg, Matrix.neg_mul]

end GlobalTheory.PairLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumInnerEqSumVectorThetaLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftGram

theorem inner_eq_sum_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hirr hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν hy hH v hv U₁ hU₁ U₂ hU₂
    z₁ z₂ h₁ h₂ ι _ b
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  refine (GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)).elim fun μ h0 => h0.elim fun 𝓧 hμ => ?_
  have h5 := (hd.1.models.νW i).1.2.2 R.θ hd.1.models.inf
  refine h5.1.elim fun Fr hFr => (h5.2 Fr hFr).1.elim fun mR hmR => ?_
  have hint : ∀ k, IntegrableOn (fun h =>
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h)) (R.fdV i A.μ0) (R.νV i A.μ0) := fun k =>
    (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hd _ _ hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v v
      (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  have hx := fun z => (SetLike.ext_iff.mp hH.2.1 _).mp (LinearMap.mem_range_self H.e z)
  have e1 := GlobalTheory.AdelicScalar.integral_eq_classSum (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m) hν hy
    (fun h => inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h)) fun γ hγ k hk x =>
      (congrArg₂ (inner ℂ) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₁) hγ k hk x) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₂) hγ k hk x)).trans
        (GlobalTheory.AdelicScalar.inner_law c.ρ hc.2.1 (GlobalTheory.AdelicScalar.norm_levChi _ _ k) _ _ _)
  simp only [GlobalTheory.AdelicScalar.ext_finLift c hc] at e1
  rw [hH.2.2 z₁ z₂]
  unfold Bridge.adInner
  rw [← e1]
  have e2 : ∀ h, inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h) = ∑ k,
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h) := fun h =>
    (b.sum_inner_mul_inner _ _).symm.trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) (h₁ h (b k))
      ((inner_conj_symm _ _).symm.trans (congrArg (starRingEnd ℂ) (h₂ h (b k)))))
  refine (congrArg (fun F => ∫ h in R.fdV i A.μ0, F h ∂(R.νV i A.μ0)) (funext e2)).trans ?_
  exact integral_finsetSum _ fun k _ => hint k

end GlobalTheory.LiftGram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPow
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem trace_eq_sum (y : Fld P) : τ.1 (Algebra.trace E (Fld P) y) = ∑ i, psiL P τ i y := by
  letI : Algebra E ℂ := τ.1.toAlgebra
  haveI : Algebra.IsSeparable E (Fld P) := Algebra.IsAlgebraic.isSeparable_of_perfectField

  let emb : Fin r → (Fld P →ₐ[E] ℂ) := fun i =>
    { psiL P τ i with commutes' := fun e => psiL_algebraMap P τ i e }
  have hinj : Function.Injective emb := by
    intro i j h
    apply cxRoots_injective P τ
    have h' := congrArg (fun f : Fld P →ₐ[E] ℂ => f (alpha P)) h
    simpa [emb] using h'
  have hcard : Fintype.card (Fin r) = Fintype.card (Fld P →ₐ[E] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card, finrank_Fld]
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).2 ⟨hinj, hcard⟩
  have htr := trace_eq_sum_embeddings (K := E) (L := Fld P) (E := ℂ) (x := y)
  rw [show τ.1 (Algebra.trace E (Fld P) y) = algebraMap E ℂ (Algebra.trace E (Fld P) y) from rfl, htr]
  exact (Fintype.sum_bijective emb hbij (fun i => psiL P τ i y) (fun g => g y) (fun i => rfl)).symm

theorem psiL_star (hCM : IsCMExt F E σ) (i : Fin r) (hi : ‖cxRoots τ.1 P i‖ = 1) (y : Fld P) :
    psiL P τ i (star' P y) = conj (psiL P τ i y) := by
  have key : ((psiL P τ i).comp (star' P : Fld P →+* Fld P) : AdjoinRoot P.1 →+* ℂ) =
      ((starRingEnd ℂ).comp (psiL P τ i) : AdjoinRoot P.1 →+* ℂ) := by
    apply AdjoinRoot.ringHom_ext
    · ext e
      show psiL P τ i (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ i (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · show psiL P τ i (star' P (alpha P)) = conj (psiL P τ i (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha]

      have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]
        norm_num
      exact (eq_inv_of_mul_eq_one_right h1).symm
  exact RingHom.congr_fun key y

theorem ext_real (a : w.Completion) (hw : w.IsReal) :
    conj (InfinitePlace.Completion.extensionEmbedding w a) = InfinitePlace.Completion.extensionEmbedding w a := by

  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a, Complex.conj_ofReal]

end GlobalTheory.TrEll.RealTorus

open GlobalTheory.TrEll.RealTorus in

theorem GlobalTheory.TrEll.realTorus_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hc
  have hbij := GlobalTheory.T.completionTensorAllRootsMap_bijective_cm F E σ hCM r P w τ
  have hnorm := GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact F E σ hCM r P w τ hbij hc
  have hw : w.IsReal := hCM.1.isReal w
  refine ⟨RingEquiv.ofBijective (PsiAll P τ) hbij, ?_, ?_, ?_, ?_, cxRoots_injective P τ, hnorm⟩
  · intro y i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show sigR w.Completion (star' P) (a ⊗ₜ[F] y) = a ⊗ₜ[F] star' P y from rfl]
      rw [Psi_tmul, Psi_tmul, psiL_star P τ hCM i (hnorm i), map_mul, ext_real a hw]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro e i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [show algebraMap (w.Completion ⊗[F] E) (w.Completion ⊗[F] Fld P) (a ⊗ₜ[F] e) =
        a ⊗ₜ[F] algebraMap E (Fld P) e from rfl]
      rw [Psi_tmul, infEmb_tmul, psiL_algebraMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  · funext i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply, Psi_tmul, map_one, psiL_alpha, one_mul]
  · intro y
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show trBase P w.Completion (a ⊗ₜ[F] y) = a ⊗ₜ[F] Algebra.trace E (Fld P) y from rfl]
      rw [infEmb_tmul, trace_eq_sum P τ y, Finset.mul_sum]
      simp only [Psi_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def gq (c : ι → ℝ) (z : VCx ι a b) : ℝ := ∑ τ, ∑ i, ∑ j, c τ * ‖z τ i j‖ ^ 2

def bk (c : ι → ℝ) (z₀ z : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, (c τ : ℂ) * z₀ τ i j * conj (z τ i j)

def conjMono (m : DVar ι a b →₀ ℕ) (z : VCx ι a b) : ℂ := m.prod fun k n => conj (z k.1 k.2.1 k.2.2) ^ n

end Pure

variable {D : D7}

def fw (D : D7) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * ‖tauE D τ D.host.xi0‖

def fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  ∑ i, ∑ j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
    ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j))

def fockPt (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (z : VCx D.what₂.Tau S.rank T.rank) : WO S T :=
  GlobalTheory.FockCompare.iotaW σ T S fun τ => fockMat A B τ (z τ)

def rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ) (x : WO S T) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x

theorem fw_pos (D : D7) (τ : D.what₂.Tau) : 0 < fw D τ := by
  unfold fw
  have h : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  positivity

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → ∀ S ∈ EP R F, ∀ y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), X.B.Re (GlobalTheory.RowEvalHH.evF R X h t c S y) = GlobalTheory.RowEvalHH.evF R X h t c S y := by
  first | exact @GlobalTheory.RowEvalHH.Re_evF | exact GlobalTheory.RowEvalHH.Re_evF | (intros; apply GlobalTheory.RowEvalHH.Re_evF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevelStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  first | exact @GlobalTheory.ConjVacua.isVacAt_ptAt | exact GlobalTheory.ConjVacua.isVacAt_ptAt | (intros; apply GlobalTheory.ConjVacua.isVacAt_ptAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  first | exact @GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | exact GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | (intros; apply GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlaceBoundedMatrix_from_conjugateHalfHomLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  first | exact @GlobalTheory.ConjHalfOnto.conj_half_onto | exact GlobalTheory.ConjHalfOnto.conj_half_onto | (intros; apply GlobalTheory.ConjHalfOnto.conj_half_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedRep_conj_maxCompact_intertwines : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v → Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  first | exact @GlobalTheory.GKLie.dRep_conj_Kset | exact GlobalTheory.GKLie.dRep_conj_Kset | (intros; apply GlobalTheory.GKLie.dRep_conj_Kset <;> assumption)
end

