import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField
open GlobalTheory.Size (l2O)
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))

structure IsBoundedCommutant (T : Module.End ℂ (WO V W → ℂ)) : Prop where
  pres : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (T f)
  bdd : ∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ V W f → l2O μ 𝓕 (T f) ≤ C * l2O μ 𝓕 f
  comm : ∀ w f, IsThetaFunO ψ V W f → T (heisO ψ V W w f) = heisO ψ V W w (T f)

variable {V W}

def L2DenseIn (M : Submodule ℂ (WO V W → ℂ)) (P : (WO V W → ℂ) → Prop) : Prop :=
  ∀ f, P f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g ∈ M, l2O μ 𝓕 (f - g) < ε

variable (V W)

def IsVac (θ : InfFam D) (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (sW τ)) f

def finSpan (f : WO V W → ℂ) : Submodule ℂ (WO V W → ℂ) :=
  Submodule.span ℂ {g | ∃ w : WO V W, w.map (infPart D) = 0 ∧ g = heisO ψ V W w f}

def CommutantScalar : Prop :=
  ∀ T : Module.End ℂ (WO V W → ℂ), IsBoundedCommutant ψ V W μ 𝓕 T →
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → T f = c • f

def StableDense : Prop :=
  ∀ M : Submodule ℂ (WO V W → ℂ), (∀ f ∈ M, IsThetaFunO ψ V W f) → M ≠ ⊥ →
    (∀ w, ∀ f ∈ M, heisO ψ V W w f ∈ M) → L2DenseIn μ 𝓕 M (IsThetaFunO ψ V W)

def VacuumDense : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) → (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) →
      ∀ f, IsVac ψ V W θ sV sW f → f ≠ 0 → L2DenseIn μ 𝓕 (finSpan ψ V W f) (IsVac ψ V W θ sV sW)

def VacuumDenseModel : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ),
    GlobalTheory.Chain.IsVacVec ψ θ M M' f → L2DenseIn μ 𝓕 (finSpan ψ V W f) (GlobalTheory.Chain.IsVacVec ψ θ M M')

end Defs

def HeisSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      CommutantScalar ψ V W μ 𝓕 ∧ StableDense ψ V W μ 𝓕 ∧ VacuumDense ψ V W μ 𝓕

section Basic₂

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {θ : InfFam D}

theorem VacuumDense.model (h : VacuumDense ψ V W μ 𝓕) : VacuumDenseModel ψ V W μ 𝓕 :=
  fun θ hθ _ _ M M' f hf g hg =>
    h θ hθ (cart M) (cart M') (GlobalTheory.Chain.VacVec.cart_isCartanInv M) (GlobalTheory.Chain.VacVec.cart_isCartanInv M') f
      ⟨hf.theta, hf.vac⟩ hf.ne g ⟨hg.theta, hg.vac⟩

theorem exists_isVac_ne_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) (hW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) :
    ∃ f, IsVac ψ V W θ sV sW f ∧ f ≠ 0 := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ V W _ _ hV hW _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame _) (GlobalTheory.PlaceModel.isSelfDualC_latFrame _)
  have h := hf 1
  simp only [one_mul] at h
  exact ⟨f, ⟨h.1, h.2.2⟩, f0⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hermAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  ((gramAt D V τ)⁻¹ * wᴴ * gramAt D W τ * z).trace

def symplAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hermAt V W τ z w).re

open Classical in

def commScalar (V W : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  if τ = τ' then -(2 * Real.pi * Complex.I) * (symplAt V W τ z w : ℂ) else 0

def Cocompact (V W : HSp D) : Prop := CompactSpace (WO V W ⧸ (ratL W V : AddSubgroup (WO V W)))

def SquareIntegrable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ f, IsThetaFunO ψ V W f →
    (∀ γ ∈ ratL W V, ∀ x : WO V W, ‖f (γ + x)‖ = ‖f x‖) ∧
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      MemLp f 2 (μ.restrict 𝓕)

def HeisUnitary (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  (∀ (u v : WO V W) (f : WO V W → ℂ),
    heisO ψ V W u (heisO ψ V W v f) = ψ (symplOH V W u v) • heisO ψ V W (u + v) f) ∧
  (∀ (u : WO V W) (f : WO V W → ℂ), heisO ψ V W (-u) (heisO ψ V W u f) = f) ∧
  (∀ u f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (heisO ψ V W u f)) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
    ∀ u f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f') ∧
  ∀ γ ∈ ratL W V, ∀ f, IsThetaFunO ψ V W f → heisO ψ V W γ f 0 = f 0

def DerSkew (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ f, IsThetaFunO ψ V W f → ∀ x, HasDerivAt (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) f x)
      (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f x) 0) ∧
    (∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f)) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
        ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) f' =
          -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f')

def DerComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ s t : ℝ, ψ (symplO V W (lineAt θ τ z s) (lineAt θ τ' w t)) =
      Complex.exp (s * t * commScalar V W τ τ' z w)) ∧
    ∀ f, IsThetaFunO ψ V W f →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w f) -
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
          commScalar V W τ τ' z w • f

def FinRealComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ u : WO V W, u.map (infPart D) = 0 →
    (∀ v : WO V W, v.map (finPart D) = 0 → ∀ f : WO V W → ℂ,
      heisO ψ V W u (heisO ψ V W v f) = heisO ψ V W v (heisO ψ V W u f)) ∧
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      heisO ψ V W u (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (heisO ψ V W u f)

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ V W : HSp D, Cocompact V W ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      SquareIntegrable ψ V W ∧ HeisUnitary ψ V W ∧
        ∀ θ : InfFam D, IsInfFam θ → DerSkew ψ θ V W ∧ DerComm ψ θ V W ∧ FinRealComm ψ θ V W

example (D : D7) (m n : ℕ) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n))) (𝓕 : Set (WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n)))
    (f : WO (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n) → ℂ), IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL (GlobalTheory.Size.posSp D n) (GlobalTheory.Size.posSp D m)) 𝓕 μ ∧ IsThetaFunO ψ _ _ f ∧
      ipO μ 𝓕 f f ≠ 0 := by
  obtain ⟨ψ, θ, μ, 𝓕, U, f, h1, h2, h3, -, h5, h6, -⟩ := GlobalTheory.Size.exists_theta_posSp D m n
  exact ⟨ψ, θ, μ, 𝓕, f, h1, h2, h3.1, h3.2.1, h5.1, h6⟩

example (D : D7) (m n : ℕ) (τ : D.what₂.Tau) (z : Matrix (Fin (GlobalTheory.Size.posSp D n).rank) (Fin (GlobalTheory.Size.posSp D m).rank) ℂ)
    (hz : (zᴴ * z).trace.im = 0) :
    symplAt (GlobalTheory.Size.posSp D m) (GlobalTheory.Size.posSp D n) τ (Complex.I • z) z =
      -2 * (tauE D τ D.host.xi0).im * (zᴴ * z).trace.re := by
  simp only [symplAt, hermAt, GlobalTheory.Size.gramAt_posSp, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hz]
  ring

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open Formalism.UG (cT)
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

section Class

variable {G : Type} [Group G]

def ratClass (Γ : Subgroup G) (γ : G) : Set G := {δ | ∃ g ∈ Γ, δ = g⁻¹ * γ * g}

def classKernel (Γ : Subgroup G) (γ : G) (f : G → ℂ) (x : G) : ℂ := ∑' δ : ratClass Γ γ, f (x⁻¹ * δ * x)

def HasClassInt [MeasurableSpace G] (Γ : Subgroup G) (μ : Measure G) (𝓕 : Set G) (γ : G) (f : G → ℂ) (c : ℂ) : Prop :=
  (∀ x, Summable fun δ : ratClass Γ γ => f (x⁻¹ * δ * x)) ∧ IntegrableOn (classKernel Γ γ f) 𝓕 μ ∧
    ∫ x in 𝓕, classKernel Γ γ f x ∂μ = c

theorem classKernel_mul {Γ : Subgroup G} (γ : G) (f : G → ℂ) {g : G} (hg : g ∈ Γ) (x : G) :
    classKernel Γ γ f (g * x) = classKernel Γ γ f x := by
  have key : ∀ g ∈ Γ, ∀ δ ∈ ratClass Γ γ, g⁻¹ * δ * g ∈ ratClass Γ γ := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨a * g, mul_mem ha hg, by group⟩
  let e : ratClass Γ γ ≃ ratClass Γ γ :=
    { toFun := fun δ => ⟨g⁻¹ * δ * g, key g hg _ δ.2⟩
      invFun := fun δ => ⟨g⁻¹⁻¹ * δ * g⁻¹, key _ (inv_mem hg) _ δ.2⟩
      left_inv := fun δ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun δ => Subtype.ext (by simp [mul_assoc]) }
  rw [classKernel, classKernel, ← e.tsum_eq fun δ => f (x⁻¹ * δ * x)]
  exact tsum_congr fun δ => congrArg f (by simp [e, mul_assoc])

end Class

section TypeOf

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J γ : Matrix (Fin n) (Fin n) E)

def IsNonFieldAniso : Prop :=
  IsRegSS γ ∧ ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
    Nonempty (plusAlg σ J γ ≃ₐ[F] ∀ i, K i) ∧ 2 ≤ k ∧ ∀ i, IsField (K i ⊗[F] E)

variable {σ J γ}

def factorIdem {k : ℕ} {K : Fin k → Type} [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : Matrix (Fin n) (Fin n) E :=
  ((e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ)

def IsOrthSplit (σ : E →ₐ[F] E) (J γ ε : Matrix (Fin n) (Fin n) E) : Prop :=
  ε * ε = ε ∧ cT (σ : E →+* E) ε * J = J * ε ∧ cT (σ : E →+* E) (1 - ε) * J * ε = 0 ∧
    (∀ l ∈ genAlg γ, l * ε = ε * l) ∧ 0 < ε.rank ∧ ε.rank < n

end TypeOf

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

def LocalClause (T : TypeDataG V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (γ : GRat D.sp.cm.sig V.gram) : Prop :=
  ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra D.host.F (K i)]
    (e : plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, K i) (i : Fin k),
    IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (factorIdem e i) ∧
    (factorIdem e i).rank = Module.finrank D.host.E (D.host.E ⊗[D.host.F] K i) ∧
    ∀ v : T.S, NoFixed (T.τ v) (radical (ResF v.1) V.rank (factorIdem e i).rank) →
      ∀ dt : Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))), dt.IsHaarMeasure →
        HasOrbInt (μf v) (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) dt (ff v) 0

def ProductClause (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (μ : Measure (GA D V)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (γ : GA D V) : Prop :=
  ∀ (dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w γ)))
    (dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v γ))) (dt : Measure (cent γ)),
    IsCentProd (frameLat V) γ dta dtf dt →
    ∀ 𝓣 : Set (cent γ), IsFundamentalDomain ((GQ V).subgroupOf (cent γ)) 𝓣 dt →
      dt 𝓣 < ∞ ∧
      ∃ (oa : InfinitePlace D.host.F → ℂ) (ob : HeightOneSpectrum (𝓞 D.host.F) → ℂ),
        (∀ w, HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w γ) (dta w) (fa w) (oa w)) ∧
        (∀ v, HasOrbInt (μf v) (proj D.sp.cm.sig V.gram v γ) (dtf v) (ff v) (ob v)) ∧
        (∀ᶠ v in cofinite, ob v = 1) ∧
        HasOrbInt μ γ dt (tensor D.sp.cm.sig V.gram fa ff) ((∏ w, oa w) * ∏ᶠ v, ob v) ∧
        ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ →
          HasClassInt (GQ V) μ 𝓕 γ (tensor D.sp.cm.sig V.gram fa ff) (dt.real 𝓣 * ((∏ w, oa w) * ∏ᶠ v, ob v))

def ZeroClause (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ : GA D V) : Prop :=
  ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ → HasClassInt (GQ V) μ 𝓕 γ f 0

def NonFieldTypeVanishing : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank →
  ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V),
    HypH (k := fun v : T.S => ResF v.1) T.τ →
  ∀ (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ →
  ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestArchG M μa fa → IsTestFin T U μf ff →
  ∀ γ : GRat D.sp.cm.sig V.gram, IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 →
    LocalClause T μf ff γ ∧
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) ∧
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ)

theorem NonFieldTypeVanishing.zero (h : NonFieldTypeVanishing) (hr : Odd V.rank) {S : D.what₂.Tau → SPar}
    {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) {f : GA D V → ℂ}
    (hf : IsTestFnG M T U μa μf f) {γ : GRat D.sp.cm.sig V.gram}
    (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
  obtain ⟨fa, ff, ha, hb, rfl⟩ := hf
  exact (h D V hr S M T U hH μa μf μ hμ fa ff ha hb γ hγ).2.2

end Record

example {G : Type} [CommGroup G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (x : G) : classKernel Γ γ f x = f γ := by
  have e : ratClass Γ γ = {γ} := Set.ext fun δ =>
    ⟨fun ⟨g, _, h⟩ => by simp [h], fun h => ⟨1, one_mem _, by simpa using h⟩⟩
  rw [classKernel, e, tsum_singleton γ fun δ => f (x⁻¹ * δ * x)]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KernelBound {D : D7} (V W : HSp D) (A d : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω →
        ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
          ∀ f ∈ thetaLevel ψ V W U, ∀ (g : GA D V) (h : GA D W),
            ‖thetaKO ω g h f‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f * ENNReal.ofReal ((height V g * height W h) ^ A)

def ThetaGrowth (D : D7) : Prop :=
  ∀ m n : ℕ, ∃ A d : ℕ, ∀ V W : HSp D, V.rank = m → W.rank = n → KernelBound V W A d

def ThetaGrowthUnif : Prop :=
  ∀ r N : ℕ, ∃ A d : ℕ, ∀ (D : D7) (V W : HSp D), Module.finrank ℚ D.host.F = r → V.rank * W.rank = N →
    KernelBound V W A d

theorem ThetaGrowthUnif.thetaGrowth (H : ThetaGrowthUnif) (D : D7) : ThetaGrowth D := fun m n =>
  (H _ (m * n)).imp fun _ h => h.imp fun _ h V W hV hW => h D V W rfl (by rw [hV, hW])

theorem KernelBound.real {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d)
    (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω →
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
        ∀ f ∈ thetaLevel ψ V W U, sobO ψ θ μ 𝓕 d f ≠ ∞ ∧ ∀ (g : GA D V) (h : GA D W),
          ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := by
  obtain ⟨C, hC⟩ := H ψ θ hθ U hU
  refine ⟨C, C.2, fun χS χT ω hω μ 𝓕 hμ f hf => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf.1 d
  refine ⟨hs, fun g h => ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)
    (hC χS χT ω hω μ 𝓕 hμ f hf g h)
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (pow_nonneg (mul_pos (height_pos V g) (height_pos W h)).le A)] at this

example {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ∃ C : ℝ, ∀ g h, ‖thetaKO ω g h f‖ ≤ C * (height V g * height W h) ^ A := by
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := H.real ψ hθ hU
  exact ⟨_, (hC χS χT ω hω μ 𝓕 hμ f hl).2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain
open GlobalTheory.Ker (ipO)

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def creOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') l g

def annOp (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (l : FVar D W.rank V.rank) (g : WO V W → ℂ) : WO V W → ℂ :=
  (-(fockScale D l.1 : ℂ)⁻¹) •
    annih (heisO ψ V W) θ l.1 (cplxO (cart M l.1) (cart M' l.1)) (unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2) g

def multiFact {ι : Type} (α : ι →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial

open Classical in

def FockLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : Prop :=
  (∀ P : PolF D W.rank V.rank, IsThetaFunO ψ V W (ptOf ψ θ M M' f P)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    creOp ψ θ M M' l (creOp ψ θ M M' l' g) = creOp ψ θ M M' l' (creOp ψ θ M M' l g)) ∧
  (∀ (l l' : FVar D W.rank V.rank) (g : WO V W → ℂ), IsThetaFunO ψ V W g →
    annOp ψ θ M M' l (creOp ψ θ M M' l' g) - creOp ψ θ M M' l' (annOp ψ θ M M' l g) = if l = l' then g else 0) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ α β : FVar D W.rank V.rank →₀ ℕ,
      ipO μ 𝓕 (ptOf ψ θ M M' f (MvPolynomial.monomial α 1)) (ptOf ψ θ M M' f (MvPolynomial.monomial β 1)) =
        if α = β then (multiFact α : ℂ) * ipO μ 𝓕 f f else 0) ∧
  Function.Injective (ptOf ψ θ M M' f)

def VacuumFock (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ f : WO V W → ℂ, IsVacVec ψ θ M M' f → FockLaws ψ θ M M' f

theorem ptOf_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (f : WO V W → ℂ) : ptOf ψ θ M M' f 1 = f := by
  have h : (1 : PolF D W.rank V.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
  unfold ptOf pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

example : multiFact (Finsupp.single () 3) = 6 := by
  rw [multiFact, Finsupp.prod_single_index (by simp)]; rfl

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors

end
end

