import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in

def ker (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (v : GA E a) : ℂ :=
  if GeneralLinearGroup.map (pFin E) v ∈ U then β (toL (GeneralLinearGroup.map (pInf E) v).val) else 0

def tst (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (y : GA E a) : ℂ := ker U β y⁻¹

structure IsTest (β : Lie E a → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ β
  compact : HasCompactSupport β
  support : tsupport β ⊆ invSet E a

def ConjInv (β : Lie E a → ℂ) : Prop :=
  ∀ (k : Kinf E a) (x : Lie E a), β (toL (k.1 * Matrix.of x * star k.1)) = β x

def dTest (X : Lie E a) (β : Lie E a → ℂ) (w : Lie E a) : ℂ :=
  fderiv ℝ β w (toL (Matrix.of w * Matrix.of X))

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    sigR R' σ (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

def hermMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : HermR R' σ n :=
  ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (Algebra.TensorProduct.map f (AlgHom.id F E)), by
    intro a b
    have h : sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = (S : Matrix _ _ _) a b := S.2 a b
    simp only [Matrix.map_apply]
    rw [sigR_map, h]⟩

theorem hermMap_sub {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR R σ n) :
    hermMap f σ (S - T) = hermMap f σ S - hermMap f σ T := by
  apply Subtype.ext
  funext a b
  simp [hermMap]

theorem hermMap_hermOf {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) :
    hermMap f σ (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT) = HeckeCharacterZeroLocus.SiegelWeilU.hermOf R' σ T hT := by
  apply Subtype.ext
  funext a b
  simp [hermMap, HeckeCharacterZeroLocus.SiegelWeilU.hermOf, HeckeCharacterZeroLocus.SiegelWeilU.inclR]

theorem sigR_hR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J y x) = hR R σ J x y := by
  have h2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h3 : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [sigR, JR, inclR, hJ j i]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, h2, h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermMap_hR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (hR R σ J x y) =
      hR R' σ J (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (x i))
        (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (y i)) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_map]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [JR, inclR]

end Alg

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

def gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, fun a c => sigR_hR R σ (sig_invol hCM) hJ.1 (X a) (X c)⟩

theorem hermMap_gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    hermMap f σ (gramH hCM hJ R X) =
      gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  apply Subtype.ext
  funext a c
  exact hermMap_hR f σ J (X a) (X c)

theorem isUnit_hermOf_det (R : Type) [CommRing R] [Algebra F R] [Nontrivial (R ⊗[F] E)] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hd : T.det ≠ 0) :
    IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
  have h : (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
    ((inclR R).map_det T).symm
  rw [h]
  exact (IsUnit.mk0 _ hd).map (inclR R)

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxFN {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxFN A).indicator (fun _ => (1 : ℂ)) (projFin X)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermMap (fstA F) σ S

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermMap (sndA F) σ S

def hermV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (S : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermMap (evalV F v) σ S

def latH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Set (HermR (Fv F v) σ n) :=
  {S | (∀ i, algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i i) ∈ v.adicCompletionIntegers F) ∧
    ∀ i j, i < j → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}

def intH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def boxH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)) : Set (HermR (Af F) σ n) :=
  {y | (∀ v ∈ S, hermV σ v y ∈ U v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def testH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : HermR (Ainf F) σ n → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (y : HermR (AF F) σ n) : ℂ :=
  (ρ (hermInf σ y) : ℂ) * (boxH σ b n S U).indicator (fun _ => (1 : ℂ)) (hermFin σ y)

def fouH (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (db : Measure (HermR (AF F) σ n))
    (τ : HermR (AF F) σ n → ℂ) (b : HermR (AF F) σ n) : ℂ :=
  ∫ y, τ y * ψ (pairHerm (AF F) σ n y b) ∂db

def chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (y : HermR (AF F) σ n) : ℂ :=
  ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))

def coefSN {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ y, (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetOfInducedFiltrationStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_of_induced_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := by
  first | exact @GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | exact GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration | (intros; apply GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace GlobalTheory.CompanionTheory.JacTheta

theorem nonempty_jac_comp_thetaW : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  intro k _ _ _ _ h N d hd hd' V _ _ π
  exact ⟨GlobalTheory.CompanionTheory.JmThetaInv.jacCompThetaW d hd hd' π⟩

end GlobalTheory.CompanionTheory.JacTheta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHoldsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jm_theta_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.JmTheta k := by
  first | exact @GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | exact GlobalTheory.CompanionTheory.JmThetaInv.jmTheta | (intros; apply GlobalTheory.CompanionTheory.JmThetaInv.jmTheta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TransDeriv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem descend_eq_sec {X : Type} {f : G → X} (h : LeftInv Γ f) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) :
    descend Γ f q = f (sec Γ q) := by
  conv_lhs => rw [← mk_sec q]
  exact h.descend_mk _

theorem sec_mul_eq {X : Type} {f : G → X} (h : LeftInv Γ f) (g : G) :
    (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => f (sec Γ q * g)) = descend Γ f ∘ rmul Γ g := by
  funext q
  have e : rmul Γ g q = mk Γ (sec Γ q * g) := by
    conv_lhs => rw [← mk_sec q]
    rfl
  rw [Function.comp_apply, e, h.descend_mk]

variable [μ.IsMulLeftInvariant]

theorem inner_toL2_eq_integral {f : G → ℂ} (hf : MemL2Quotient Γ μ f) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    ⟪u, hf.toL2⟫_ℂ = ∫ q : GlobalTheory.AutomorphicL2Unitary.Quot Γ, conj (u q) * f (sec Γ q) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL2] with q e
  rw [e, descend_eq_sec hf.1]
  simp [mul_comm]

theorem sub_eq_integral {φ ψ : G → ℂ} {c : ℝ → G} (hψ : Continuous ψ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (x : G) (t : ℝ) :
    φ (x * c t) - φ x = ∫ s in (0 : ℝ)..t, ψ (x * c s) := by
  have hs : ∀ s, HasDerivAt (fun r => φ (x * c r)) (ψ (x * c s)) s := fun s => by
    have h2 : HasDerivAt (fun t => φ (x * c s * c t)) (ψ (x * c s)) (s - s) := by simpa using hd (x * c s)
    have h3 := h2.comp_sub_const s s
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have : c r = c s * c (r - s) := by rw [← hadd]; congr 1; ring
    simp only [this, mul_assoc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hs s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [h0]

theorem integrable_pair [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] {ψ : G → ℂ}
    (hψ : MemL2Quotient Γ μ ψ) (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  have hsec := (measurableEmbedding_sec (Γ := Γ)).measurable
  have hm : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => ψ (sec Γ p.2 * c p.1)) :=
    hψc.measurable.comp ((hsec.comp measurable_snd).mul (hc.measurable.comp measurable_fst))
  have hu : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u p.2)) :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) :=
    hu.mul hm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF.enorm.aemeasurable]
  set C : ENNReal := eLpNorm u 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) with hC
  have hb : ∀ s, ∫⁻ q, ‖Function.uncurry (fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) (s, q)‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤ C := fun s => by
    have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (q := 2) (r := 1)
      (Lp.aestronglyMeasurable u) (((hψ.mul_right (c s)).2).1) (fun a b => conj a * b) 1
      (Filter.Eventually.of_forall fun q => by simp)
    have h2 : eLpNorm (descend Γ fun x => ψ (x * c s)) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) = eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
      have e : descend Γ (fun x => ψ (x * c s)) = descend Γ ψ ∘ rmul Γ (c s) := by
        funext q
        rw [descend_eq_sec (hψ.1.mul_right (c s)), ← sec_mul_eq hψ.1]
      rw [e]
      exact eLpNorm_comp_measurePreserving hψ.2.1 (measurePreserving_rmul (c s))
    rw [eLpNorm_one_eq_lintegral_enorm, h2] at h1
    simp only [ENNReal.coe_one, one_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun q => ?_
    simp only [Function.uncurry, descend_eq_sec (hψ.1.mul_right (c s))]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (Lp.memLp u).2 hψ.2.2) ?_
  simp [Set.uIoc, Real.volume_Ioc]

variable [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem R_sub_eq_integral {φ ψ : G → ℂ} (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (t : ℝ) :
    R Γ μ (c t) hφ.toL2 - hφ.toL2 = ∫ s in (0 : ℝ)..t, R Γ μ (c s) hψ.toL2 := by
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  refine ext_inner_left ℂ fun u => ?_
  have e1 := (innerSL ℂ u).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply] at e1
  rw [← e1, inner_sub_right]
  simp only [right_translate_toL2, inner_toL2_eq_integral]
  have hi : ∀ {f : G → ℂ} (hf : MemL2Quotient Γ μ f),
      Integrable (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u q) * f (sec Γ q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := fun {f} hf => by
    have h := (Lp.memLp u).star.integrable_mul hf.2
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [descend_eq_sec hf.1]
  rw [← integral_sub (hi (hφ.mul_right (c t))) (hi hφ), intervalIntegral.intervalIntegral_eq_integral_uIoc,
    integral_integral_swap (integrable_pair hψ hψc hc u t), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [integral_const_mul]
  rw [← mul_sub, sub_eq_integral hψc hc h0 hadd hd, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [mul_smul_comm]

theorem hasDerivAt_R : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c _ hψc hc h0 hadd hd t
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  have e : (fun s => R Γ μ (c s) hφ.toL2) = fun s => hφ.toL2 + ∫ r in (0 : ℝ)..s, R Γ μ (c r) hψ.toL2 := by
    funext s
    rw [← R_sub_eq_integral hφ hψ hψc hc h0 hadd hd s]
    abel
  rw [e]
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

end GlobalTheory.CompanionTheory.TransDeriv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbLeviProjMemKm
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.KmIwahori

open GlobalTheory.CompanionTheory.HeckeJacquet (mem_Km_iff val_unif_lt_one)
open GlobalTheory.LocGL.IwahoriFactor (one_same one_ne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) {M : Matrix (Fin N) (Fin N) k}
    (h : ∀ i j, valuation k (M i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (((Zls.unifU k : kˣ) : k) ^ m)) :
    ∃ g ∈ Zls.Km k N m, g.val = M := by
  have hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  obtain ⟨g, -, hg⟩ := GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M)
    fun i j => by
      rw [Matrix.sub_apply]
      exact (h i j).trans_lt hlt
  exact ⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩

variable {α : Type} {μ : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (μ a)]
  [∀ a, DecidableEq (μ a)]

theorem exists_mul_mem_parab {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ c ∈ Zls.Km k N m ⊓ unipRadLower k e, x * c ∈ parab k e := by
  have hx' := (mem_Km_iff N hm x).1 hx
  have hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l := fun a =>
    exists_mem_Km hm fun i l => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) *
      c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem leviEmb_leviProj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) (p : parab k e)
    (hp : (p : GL (Fin N) k) ∈ Zls.Km k N m) :
    leviEmb k e (leviProj k e p) ∈ Zls.Km k N m := by
  refine (mem_Km_iff N hm _).2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := (mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)
    rwa [leviEmb_apply_same, leviProj_apply]
  · rw [leviEmb_apply_ne k e _ h, one_ne e h]
    simp

theorem exists_factor {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ a ∈ Zls.Km k N m ⊓ unipRadLower k e, ∃ b ∈ Zls.Km k N m ⊓ (leviEmb k e).range,
      ∃ c ∈ Zls.Km k N m ⊓ unipRad k e, x = a * b * c := by
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab hm e (inv_mem hx)
  have hq : (x⁻¹ * c)⁻¹ ∈ parab k e := inv_mem hp
  have hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m := inv_mem (mul_mem (inv_mem hx) hc.1)
  obtain ⟨u, hu, hqu⟩ := exists_levi_mul_unip k e ⟨_, hq⟩
  have hd := leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK
  refine ⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩
  · have : u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hqu.symm
    show u ∈ Zls.Km k N m
    rw [this]
    exact mul_mem (inv_mem hd) hqK
  · rw [mul_assoc, ← hqu]
    group

theorem c0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    PositivityTheory.Lbc.C0 k := by
  intro k _ _ _ _ N m h d hd hm
  exact ⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m,
    fun x hx => exists_factor hm (stdBlocks d hd) hx⟩

end GlobalTheory.CompanionTheory.KmIwahori

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicFrameBlockZeroStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_frame_block_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ g ∈ minPar σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w g) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero | exact GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.minPar_frame_block_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuousStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_coefficient_continuous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.continuous_coef | exact GlobalTheory.CompanionTheory.MirPair.continuous_coef | (intros; apply GlobalTheory.CompanionTheory.MirPair.continuous_coef <;> assumption)
end

