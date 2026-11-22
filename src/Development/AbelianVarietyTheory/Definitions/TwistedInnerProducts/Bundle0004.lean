import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ConjScalarAt (R : RealDat D A Ks) : Prop :=
  ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ →
    ∀ μ' η' c c₁ H j th, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th →
    ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ l : ℝ, ∀ u : H.H, th u ∈ GlobalTheory.LiftLower.partH R i σ ev →
      th (LinearMap.adjoint th (th u)) = (l : ℂ) • th u

theorem conjScalarAt_of (h : ConjScalarThm) (R : RealDat D A Ks) (F : Face D A) (hC : R.Char F) (hψ : IsStdChar D R.ψ (-1))
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) : ConjScalarAt R :=
  h D G Pl0 T0 A Ks R F hC hψ hX

end GlobalTheory.ConjScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (M : DSModel V S) (M' : DSModel W S') :
    ∃ f, IsVacVec ψ θ M M' f :=
  VacVec.exists_isVacVec ψ θ M M' hψ hθ

theorem exists_std_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') :
    ∃ ψ θ f, IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ IsVacVec ψ θ M M' f :=
  VacVec.exists_char_fam_isVacVec M M'

theorem not_isVacVec_zero {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') : ¬ IsVacVec ψ θ M M' 0 := fun h => h.ne rfl

theorem exp_of_even {k : Fin D.R.m} (hk : Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k - 1 / 2 ∧ expT D k τ = -(D.hc τ).e k := by
  simp [expS, expT, hk]

theorem exp_of_odd {k : Fin D.R.m} (hk : ¬ Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k ∧ expT D k τ = -(D.hc τ).e k - 1 / 2 := by
  simp [expS, expT, hk]

theorem hasInfExp_div {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η⁻¹) τ (a - b) := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  refine ⟨n - m, by push_cast; rw [hn, hm]; ring, h1, fun θ hθ x hx hτ => ?_⟩
  have e1 := h2 θ hθ x hx hτ
  have e2 := h3 θ hθ x hx hτ
  set z : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hz
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, e1, e2]
  by_cases h0 : z = 0
  · have a1 : n = 0 := by
      by_contra h; exact (χ x).coe_ne_zero (by rw [e1, h0, zero_zpow _ h])
    have a2 : m = 0 := by
      by_contra h; exact (η x).coe_ne_zero (by rw [e2, h0, zero_zpow _ h])
    simp [a1, a2]
  · rw [zpow_sub₀ h0, div_eq_mul_inv]

theorem isHeckeChar_div {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2]; simp⟩

theorem exists_isStepWeil (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (k : Fin D.R.m)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (V W : HSp D)
    (hV : V.rank % 2 = ((k : ℕ) + 1) % 2) (hW' : W.rank % 2 = (k : ℕ) % 2)
    (μ η : (AE D)ˣ →* Circle) (hμ : IsHeckeChar D μ) (hμe : ∀ τ, HasInfExp D μ τ (-(D.hc τ).e k)) (hμr : ResEta D μ 0)
    (hη : IsHeckeChar D η) (hηe : ∀ τ, HasInfExp D η τ (1 / 2)) (hηr : ResEta D η 1) :
    ∃ ω, IsStepWeil k ψ V W ω := by
  have hq := isHeckeChar_div hμ hη
  have hqr : ResEta D (μ * η⁻¹) (0 + 1) := resEta_mul hμr (resEta_inv hηr)
  by_cases hk : Even (k : ℕ)
  · have hk' := Nat.even_iff.1 hk
    obtain ⟨ω, hω⟩ := hW D ψ V W (μ * η⁻¹) μ hψ hq hμ (resEta_parity hqr (by omega)) (resEta_parity hμr (by omega))
    refine ⟨ω, _, _, hω, fun τ => ?_⟩
    rw [(exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div (hμe τ) (hηe τ), hμe τ⟩
  · have hk' := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hk)
    obtain ⟨ω, hω⟩ := hW D ψ V W μ (μ * η⁻¹) hψ hμ hq (resEta_parity hμr (by omega)) (resEta_parity hqr (by omega))
    refine ⟨ω, _, _, hω, fun τ => ?_⟩
    rw [(exp_of_odd hk τ).1, (exp_of_odd hk τ).2]
    exact ⟨hμe τ, hasInfExp_div (hμe τ) (hηe τ)⟩

theorem rank_parity (D : D7) (k : ℕ) :
    (D.R.r + k * D.R.t) % 2 = (k + 1) % 2 ∧ (D.R.r + (k + 1) * D.R.t) % 2 = k % 2 := by
  have h1 := Nat.odd_iff.1 (r_odd D)
  have h2 := Nat.odd_iff.1 D.R.t_odd
  constructor <;> rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.add_mod, Nat.mul_mod, h, h1, h2]

example : signed [1] [2] (1 / 2) = {(3 / 2, true), (5 / 2, false)} := by
  simp [signed]; norm_num

end GlobalTheory.Chain

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Size GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped ENNReal

namespace GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Fr (V : HSp D) where

  ε : D.what₂.Tau → Fin V.rank → Bool

  fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  fr_unit : ∀ τ, IsUnit (fr τ)
  fr_gram : ∀ τ, (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

namespace Fr

variable {V : HSp D}

def ofModel {S : D.what₂.Tau → SPar} (M : DSModel V S) : Fr V := ⟨M.ε, M.fr, M.fr_unit, M.fr_gram⟩

def cart (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ

def onb (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (A.fr τ)⁻¹

def elt (θ : InfFam D) (A : Fr V) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((A.fr τ)⁻¹ * g * A.fr τ)

end Fr

section Clauses

variable {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)

def ptF (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f

def IsVacF (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f

variable (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau)

def LieFockWith (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ) : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS X • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κT Y • P) z) 0

def CompactFockF (aS aT : ℚ) : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (A.ε τ j) : ℚ) = wtS (B.ε τ) aT (A.ε τ j)) ∧
    (∀ i, (y (B.ε τ i) : ℚ) = wtT (A.ε τ) aS (B.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (A.ε τ), ∀ k ∈ Formalism.REAL.Kset (B.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (A.elt θ τ h, B.elt θ τ k) (ptF ψ θ A B f P) =
        (signBlockDeterminant (A.ε τ) true h ^ x true * signBlockDeterminant (A.ε τ) false h ^ x false *
          (signBlockDeterminant (B.ε τ) true k ^ y true * signBlockDeterminant (B.ε τ) false k ^ y false)) •
          ptF ψ θ A B f (subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) k P)

end Clauses

def LieFockUpTo (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∃ κS κT, ∀ f, IsVacF ψ θ A B f → LieFockWith ψ θ A B ω f τ κS κT

def LieFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f →
      LieFockWith ψ θ A B ω f τ (fun X => -((aT : ℂ) * X.trace)) fun Y => (aS : ℂ) * Y.trace

def CompactFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f → f ≠ 0 →
      CompactFockF ψ θ A B ω f τ aS aT

def fockSpan {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (U : AddSubgroup (WO V W)) : Submodule ℂ (WO V W → ℂ) :=
  Submodule.span ℂ {g | ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ thetaLevel ψ V W U ∧ g = ptF ψ θ A B f₀ P}

def FockDense (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ f, IsThetaFunO ψ V W f →
      ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ thetaLevel ψ V W U ∧
        ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ fockSpan ψ θ A B U, g ∈ thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ

def LowVanishFock (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ),
      IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
        Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

theorem ptF_ofModel {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) :
    ptF ψ θ (Fr.ofModel M) (Fr.ofModel M') f = ptOf ψ θ M M' f := rfl

theorem isVacF_of_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ} (h : IsVacVec ψ θ M M' f) :
    IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f := ⟨h.theta, h.vac⟩

def posFr (D : D7) (n : ℕ) : Fr (posSp D n) where
  ε _ _ := true
  fr _ := 1
  fr_unit _ := isUnit_one
  fr_gram τ := by
    rw [gramAt_posSp]
    ext a b
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply]

end GlobalTheory.ChainFr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SymplecticAdjointInclusionZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer.Check

variable {D : D7}

theorem sympl_left (S T : HSp D) (g : GA D T) (x y : WO S T) :
    symplOH S T (mt T g ⬝ x) (mt T g ⬝ y) = symplOH S T x y := by
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul, Matrix.mul_assoc, cancel₃ (mt_unitary T g)]

section Target

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (n : GA D T) (β : Mx D ρ T₀.rank)
  (y : Mx D S.rank ρ)

def xiT : Mx D ρ S.rank := d.pX ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)

theorem splitT (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    mt T n⁻¹ ⬝ d.incAdj S y = d.incX S (xiT d n y) + d.inc0 S (ptT d S y n) + d.incAdj S y := by
  have h : d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y) = incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S) := by
    rw [cancel₂ h3, d.incAdj_apply, d.incY_apply, cancel₂ d.pY_jY, Matrix.one_mul]
  have h' : d.incAdj S y = d.jY ⬝ (d.pY ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)) := by rw [h]; rfl
  conv_rhs => rw [d.incX_apply, d.wittDecomp_inclAnisotropicHom_apply, xiT, ptT]; arg 2; rw [h']
  rw [← Matrix.mul_assoc d.jX, ← Matrix.mul_assoc d.j0, ← Matrix.mul_assoc d.jY, ← Matrix.add_mul, ← Matrix.add_mul,
    d.sum_eq_one, Matrix.one_mul]

theorem symplectic_adjoint_inclusion_zero (v : WO S T₀) : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v

theorem cenT_eq (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    cenT d S y n = -symplOH S T (d.incX S (xiT d n y)) (d.incAdj S y) := by
  rw [cenT, splitT d n y h3, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, symplectic_adjoint_inclusion_zero,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (w₀ : WO S T₀) :
    mt T n⁻¹ ⬝ d.inc0 S w₀ = d.inc0 S w₀ + d.incX S (β ⬝ w₀) := by
  rw [d.wittDecomp_inclAnisotropicHom_apply, d.incX_apply, cancel₂ h2, Matrix.add_mul, Matrix.mul_assoc]

theorem crossT (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) (w₀ : WO S T₀) :
    symplOH S T₀ w₀ (ptT d S y n) = -symplOH S T (d.incX S (β ⬝ w₀)) (d.incAdj S y) := by
  have h := sympl_left S T n⁻¹ (d.inc0 S w₀) (d.incAdj S y)
  have z : symplOH S T (d.inc0 S w₀) (d.incAdj S y) = 0 := by rw [symplOH_skew, symplectic_adjoint_inclusion_zero, neg_zero]
  have z' : symplOH S T (d.inc0 S w₀) (d.incX S (xiT d n y)) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero]
  rw [splitT d n y h3, moveT d n β h2, z, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, z, z',
    d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, d.symplOH_incX_incX, d.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero, add_zero, zero_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem mixT_comp {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h1 : mt T n⁻¹ ⬝ d.jX = d.jX) (h2 : mt T n⁻¹ ⬝ d.j0 = d.j0 + d.jX ⬝ β) (h3 : d.pY ⬝ mt T n⁻¹ = d.pY) :
    d.mixT S ψ μ 𝓕 (fun w => f (mt T n⁻¹ ⬝ w)) y = jacT ψ d S y n (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have e3 : ∀ ξ, mt T n⁻¹ ⬝ d.incX S ξ = d.incX S ξ := fun ξ => by rw [d.incX_apply, cancel₂ h1]
  have k := covolOne_integral_add hμ
    (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + ptT d S y n)) f)) 0)
    (d.integrandT_periodic hf y (w₀ + ptT d S y n)) (xiT d n y + β ⬝ w₀)
  change d.mixT S ψ μ 𝓕 (fun w => f (mt T n⁻¹ ⬝ w)) y w₀ = ψ (cenT d S y n) * (ψ (symplOH S T₀ w₀ (ptT d S y n)) *
    d.mixT S ψ μ 𝓕 f y (w₀ + ptT d S y n))
  unfold HypDec.mixT
  rw [← k, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [d.integrandT_eq, d.integrandT_eq, Matrix.mul_add, Matrix.mul_add, splitT d n y h3, moveT d n β h2, e3,
    cenT_eq d n y h3, crossT d n β y h2 h3, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  simp only [map_add, GlobalTheory.OrientedHeis.symplOH_add_left]
  congr 2
  · ring
  · abel

end Target

theorem sympl_right (S T : HSp D) (g : GA D S) (x y : WO S T) :
    symplOH S T (x ⬝ mt S g) (y ⬝ mt S g) = symplOH S T x y := by
  have h : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have h1 := mt_mul_inv S g
    rw [mt_inv] at h1
    have h2 := congrArg (· ⬝ giA S) h1
    simpa only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one, Matrix.one_mul] using h2
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc _ _ (mt S g),
    ← Matrix.mul_assoc _ _ (mt S g), trace_mul_comm, Matrix.mul_assoc (adj (mt S g)), cancel₃ h]

section Source

variable {ψ : AddChar (AF D.host.F) ℂ} {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (n : GA D S) (β : Mx D S₀.rank ρ)
  (x : Mx D T.rank ρ)

def etaS : Mx D T.rank ρ := d.extX T x ⬝ mt S n ⬝ d.jY

theorem splitS (h1 : mt S n ⬝ d.jX = d.jX) :
    d.extX T x ⬝ mt S n = d.extY T (etaS d n x) + d.extX T x + d.ext0 T (ptS d T x n) := by
  refine d.mat_ext ?_ ?_ ?_
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, h1, d.pX_jX, d.pY_jX, d.p0_jX,
      Matrix.mul_zero, zero_add, add_zero]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_j0, d.pY_j0, d.p0_j0,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, ptS]
  · simp only [Matrix.add_mul, d.extX_apply, d.extY_apply, d.matrixExtendByZero_apply, Matrix.mul_assoc, d.pX_jY, d.pY_jY, d.p0_jY,
      Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one, etaS]

theorem cenS_eq (h1 : mt S n ⬝ d.jX = d.jX) :
    cenS d T x n = -symplOH S T (d.extY T (etaS d n x)) (d.extX T x) := by
  rw [cenS, splitS d n x h1, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, d.wittDecomp_sympl_extIsotropic_extAnisotropic,
    GlobalTheory.OrientedHeis.symplOH_self, add_zero, add_zero, symplOH_skew]

theorem moveS (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (w₀ : WO S₀ T) :
    d.ext0 T w₀ ⬝ mt S n = d.ext0 T w₀ + d.extY T (w₀ ⬝ β) := by
  rw [d.matrixExtendByZero_apply, d.extY_apply, Matrix.mul_assoc, h2, Matrix.mul_add, Matrix.mul_assoc]

theorem crossS (h1 : mt S n ⬝ d.jX = d.jX) (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (w₀ : WO S₀ T) :
    symplOH S₀ T w₀ (ptS d T x n) = -symplOH S T (d.extY T (w₀ ⬝ β)) (d.extX T x) := by
  have h := sympl_right S T n (d.ext0 T w₀) (d.extX T x)
  have z : symplOH S T (d.ext0 T w₀) (d.extX T x) = 0 := by rw [symplOH_skew, d.wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  have z' : symplOH S T (d.ext0 T w₀) (d.extY T (etaS d n x)) = 0 := by
    rw [symplOH_skew, d.wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  rw [splitS d n x h1, moveS d n β h2, z, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, z, z',
    d.wittDecomp_sympl_extAnisotropic_extAnisotropic, d.symplOH_extY_extY, d.wittDecomp_sympl_extDual_extAnisotropic, zero_add, zero_add, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem mixS_comp {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h1 : mt S n ⬝ d.jX = d.jX) (h2 : d.p0 ⬝ mt S n = d.p0 + β ⬝ d.pY) (h3 : d.pY ⬝ mt S n = d.pY) :
    d.mixS T ψ μ 𝓕 (fun w => f (w ⬝ mt S n)) x = jacS ψ d T x n (d.mixS T ψ μ 𝓕 f x) := by
  funext w₀
  have e3 : ∀ a, d.extY T a ⬝ mt S n = d.extY T a := fun a => by rw [d.extY_apply, Matrix.mul_assoc, h3]
  have k := covolOne_integral_add hμ
    (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T (w₀ + ptS d T x n)) f)) 0)
    (d.integrandS_periodic hf x (w₀ + ptS d T x n)) (etaS d n x + w₀ ⬝ β)
  change d.mixS T ψ μ 𝓕 (fun w => f (w ⬝ mt S n)) x w₀ = ψ (cenS d T x n) * (ψ (symplOH S₀ T w₀ (ptS d T x n)) *
    d.mixS T ψ μ 𝓕 f x (w₀ + ptS d T x n))
  unfold HypDec.mixS
  rw [← k, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [d.integrandS_eq, d.integrandS_eq, Matrix.add_mul, Matrix.add_mul, splitS d n x h1, moveS d n β h2, e3,
    cenS_eq d n x h1, crossS d n β x h1 h2, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  simp only [map_add, GlobalTheory.OrientedHeis.symplOH_add_left]
  congr 2
  · ring
  · abel

end Source

theorem om_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {g : GA D S} (hg : g ∈ GQ S) {h : GA D T} (hh : h ∈ GQ T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hpres : ∀ w, IsThetaFunO ψ S T (heisO ψ S T w f)) (w : WO S T) :
    om (g, h) f (actO S T g h w) = f w := by
  have h1 := congrFun (hom.om_heis g h w f hf) 0
  rw [hom.om_aut g hg h hh _ (hpres w)] at h1
  simpa only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add] using h1.symm

theorem psiE_half (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : psiE ψ (t • half D) = ψ t := by
  rw [psiE, map_smul, half, GlobalTheory.BesselChar.trace_incA]
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by rw [map_div₀, map_one, map_ofNat]
  rw [this, Algebra.trace_algebraMap, h2]
  norm_num

theorem psiBes_three (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) :
    ∃ n ∈ flagN (hypDecThree D), psiBes ψ (hypDecThree D) 1 (fun _ => 1) n = ψ t := by
  refine ⟨(hypDecThree D).nB (Matrix.of fun _ _ => t • half D), (hypDecThree D).nB_mem_NFlag _, ?_⟩
  rw [psiBes_nB, map_one, one_mul, ← psiE_half]
  congr 1
  change ∑ i : Fin 1, ell D 1 i * ∑ j : Fin 1, t • half D * incA D 1 = _
  rw [Fin.sum_univ_one, Fin.sum_univ_one, show ell D 1 0 = 1 from rfl, one_mul, map_one, mul_one]

theorem unip_two {R : Type} [CommRing R] (s : R) : ∃ u : GL (Fin 2) R, u ∈ upperUni 2 R ∧ u.1 0 1 = s := by
  refine ⟨⟨!![1, s; 0, 1], !![1, -s; 0, 1], ?_, ?_⟩, ?_, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro i j; fin_cases i <;> fin_cases j <;> simp

theorem psiUni_two (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ∃ u ∈ UX D 2, psiUni ψ u = ψ t := by
  obtain ⟨u, hu, h⟩ := unip_two (t • half D)
  have e : ∀ T : Mx D 2 2, upSum T = T 0 1 := fun T => by simp [upSum, Fin.sum_univ_two]
  exact ⟨u, mem_UX.2 hu, by rw [psiUni, e, h, psiE_half]⟩

theorem UX_one (u : UX D 1) : u = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact ((mem_UX.1 u.2) 0 0).2

theorem isUnitU_one : IsUnitU D 1 (Measure.dirac 1) := by
  haveI : Unique (UX D 1) := ⟨⟨1⟩, UX_one⟩
  haveI : BorelSpace (UX D 1) := ⟨rfl⟩
  refine ⟨?_, Set.univ, ?_, measure_univ⟩
  · haveI : (Measure.dirac (1 : UX D 1)).IsMulLeftInvariant := ⟨fun g => by
      rw [UX_one g]; simp only [one_mul]; exact Measure.map_id⟩
    haveI : (Measure.dirac (1 : UX D 1)).IsOpenPosMeasure :=
      ⟨fun U _ hU => by rw [Subsingleton.eq_univ_of_nonempty hU, measure_univ]; exact one_ne_zero⟩
    exact @Measure.IsHaarMeasure.mk _ _ _ _ _ ⟨fun K _ => measure_lt_top _ _⟩ inferInstance inferInstance
  · exact ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, trivial⟩,
      fun a b hab => absurd (Subtype.ext (Subsingleton.elim _ _)) hab⟩

theorem flat_one (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ A L : HSp D} (dV : HypDec V V₀ 1) (o : OrthDec V₀ A L) (ζ)
    (dW : HypDec W W₀ 1) (μS 𝓕S μT 𝓕T) (Ψ : WO V W → ℂ) :
    flat ψ dV o ζ dW μS 𝓕S μT 𝓕T (Measure.dirac 1) Ψ = evalZero ψ dV o ζ dW μS 𝓕S μT 𝓕T Ψ := by
  haveI : Unique (UX D 1) := ⟨⟨1⟩, UX_one⟩
  haveI : MeasurableSingletonClass (UX D 1) := ⟨fun x => by
    rw [Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty x)]; exact MeasurableSet.univ⟩
  funext w
  rw [flat, flatAt, integral_dirac, flatFun, psiUni, evalZero]
  simp [upSum_one, psiE_zero]

theorem fjKer_one (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ)
    (om : Om V₀ W₀) (Ξ) (h₀ : GA D A) (h : GA D W₀) :
    fjKer ψ dW o ζ om Ξ h₀ 1 h = thetaKO om (o.emb (h₀, 1)) h Ξ := by
  rw [fjKer, opA, jacT_one, id, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem mixT_nB_nC {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (b : Mx D ρ T₀.rank) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (fun w => f (mt T (d.nB b * d.nC c)⁻¹ ⬝ w)) y =
      jacT ψ d S y (d.nB b * d.nC c) (d.mixT S ψ μ 𝓕 f y) := by
  refine mixT_comp d _ (-b) y hμ hf ?_ ?_ ?_ <;> rw [_root_.mul_inv_rev, d.nB_inv, d.nC_inv, mt_mul]
  · rw [Matrix.mul_assoc, d.nB_jX, d.nC_jX]
  · rw [Matrix.mul_assoc, d.nB_j0, Matrix.mul_add, d.nC_j0, cancel₂ (d.nC_jX _)]
  · rw [← Matrix.mul_assoc, d.pY_nC, d.pY_nB]

end GlobalTheory.MixPer.Check

end
end

