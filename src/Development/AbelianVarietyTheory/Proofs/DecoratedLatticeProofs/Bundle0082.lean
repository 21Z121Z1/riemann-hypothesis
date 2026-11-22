import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.Bundle0028
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEqStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ), IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  first | exact @GlobalTheory.ParHeckeCard.card_isReps_inv | exact GlobalTheory.ParHeckeCard.card_isReps_inv | (intros; apply GlobalTheory.ParHeckeCard.card_isReps_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassLatticeSelfDual
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.ClassLatticeSelfDual

section General

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

omit [NumberField F] [DecidableEq n] [Fintype n] in

theorem mem_span_of_mem_latS (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] (S : Subring (E ⊗[F] R))
    (L : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : (fun i => inclE (F := F) R (x i)) ∈ latS (F := F) R S L) :
    x ∈ Submodule.span E (L : Set (n → E)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →ₗ[F] F, φ 1 = 1 := Module.Projective.exists_dual_eq_one F one_ne_zero
  let π : E ⊗[F] R →ₗ[E] E :=
    (TensorProduct.AlgebraTensorModule.rid F E E).toLinearMap ∘ₗ (φ.baseChange E)
  have hπ : ∀ (s : E ⊗[F] R) (a : E), π (s * inclE (F := F) R a) = π s * a := by
    intro s a
    have : s * inclE (F := F) R a = a • s := by
      rw [mul_comm, Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hπ1 : π 1 = 1 := by
    simp [π, Algebra.TensorProduct.one_def, hφ]
  have key : ∀ u ∈ latS (F := F) R S L, ∀ s : E ⊗[F] R,
      (fun i => π (s * u i)) ∈ Submodule.span E (L : Set (n → E)) := by
    intro u hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      intro s
      have : (fun i => π (s * inclE (F := F) R (y i))) = π s • y := by
        funext i; rw [hπ]; rfl
      exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span hy)
    | zero =>
      intro s
      have : (fun i => π (s * (0 : n → E ⊗[F] R) i)) = 0 := by funext i; simp
      exact this ▸ zero_mem _
    | add u u' _ _ h h' =>
      intro s
      have : (fun i => π (s * (u + u') i)) = (fun i => π (s * u i)) + fun i => π (s * u' i) := by
        funext i; simp [mul_add]
      exact this ▸ add_mem (h s) (h' s)
    | smul r u _ h =>
      intro s
      have : (fun i => π (s * (r • u) i)) = fun i => π ((s * (r : E ⊗[F] R)) * u i) := by
        funext i; rw [mul_assoc]; rfl
      exact this ▸ h _
  have h := key _ hx 1
  have e : (fun i => π (1 * inclE (F := F) R (x i))) = x := by
    funext i; rw [hπ, hπ1, one_mul]
  rwa [e] at h

theorem eq_globLat (Λ L : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (hL : Module.Finite (𝓞 E) L)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ x : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (g⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    L = CS.globLat g Λ := by
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, hp.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (0 : FiniteAdeleRing (𝓞 F) F) v = (1 : FiniteAdeleRing (𝓞 F) F) v := by rw [h]
    exact (zero_ne_one : (0 : v.adicCompletion F) ≠ 1) h1
  have hG := csGlob_lattice (F := F) Λ hfin hspan g
  have hLs : Submodule.span E (L : Set (n → E)) = ⊤ := by
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact mem_span_of_mem_latS (F := F) _ _ L x ((h _).2 hx)
  ext x
  conv_lhs => rw [← global_lattice_one_holds F E n L hL hLs]
  refine Iff.trans ?_ (h _)
  show ((1⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ _
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

end General

theorem classLattice_selfDual : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (c : (D.fm u).clsP), Submodule.IsLattice D.host.E (K.lat c) ∧ ∀ y, y ∈ K.lat c ↔ ∀ x ∈ K.lat c, Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro D u K c
  have e := eq_globLat (F := D.host.F) K.lev.Lb (K.lat c) K.lev.Lb_fin K.lev.Lb_span (K.lat_fin c) (K.y c).1 (K.y_lat c)
  have hdual : ∀ x, x ∈ K.lev.Lb ↔ ∀ y ∈ K.lev.Lb,
      Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    refine ⟨fun hx => K.lev.Lb_int x hx, fun hx => ?_⟩
    have := K.lev.Lb_dual x hx
    rwa [Nat.cast_one, one_smul] at this
  rw [e]
  exact ⟨Formalism.UG.P.csGlob_lattice (F := D.host.F) _ K.lev.Lb_fin K.lev.Lb_span _,
    fun y => GlobalTheory.PointLattice.globLat_selfDual (sigD D) (gramP D) _ hdual K.lev.Lb_fin K.lev.Lb_span _ (K.y c).2 y⟩

end GlobalTheory.ClassLatticeSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPartIso

section Swap

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (φ : A →+* B) (h : Continuous φ) : Continuous (bc (n := Fin n) φ) :=
  Continuous.units_map _ (continuous_id.matrix_map h)

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  have h2 := congrArg (fun M => M.map φ) hg'
  simp only [Matrix.map_mul, hJ] at h2
  have e1 : cT σ' (g.1.map φ) = (cT σ g.1).map φ := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, h]
  change cT σ' (g.1.map φ) * J' * g.1.map φ = J'
  rw [e1]; exact h2

def ujEquiv {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (σ : A →+* A) (σ' : B →+* B) (φ : A ≃+* B) (hc : Continuous φ) (hc' : Continuous φ.symm)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') : UJ σ J ≃ₜ* UJ σ' J' where
  toFun g := ⟨bc φ.toRingHom g.1, bc_mem _ _ φ.toRingHom h _ _ hJ g.2⟩
  invFun g := ⟨bc φ.symm.toRingHom g.1, bc_mem _ _ φ.symm.toRingHom (fun x => φ.injective (by
      change φ (σ (φ.symm x)) = φ (φ.symm (σ' x))
      rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])) _ _
      (hJ ▸ Matrix.ext fun _ _ => φ.symm_apply_apply _) g.2⟩
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.symm_apply_apply _))
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.apply_symm_apply _))
  map_mul' g h := Subtype.ext (map_mul (bc φ.toRingHom) g.1 h.1)
  continuous_toFun := ((continuous_bc φ.toRingHom hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_bc φ.symm.toRingHom hc').comp continuous_subtype_val).subtype_mk _

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

def swapR : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem continuous_swapR :
    @Continuous _ _ _ (tensTopL (F := F) (E := E) R) (swapR (F := F) (E := E) R) ∧
    @Continuous _ _ (tensTopL (F := F) (E := E) R) _ (swapR (F := F) (E := E) R).symm := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) R
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  haveI := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let L : R ⊗[F] E ≃ₗ[R] E ⊗[F] R :=
    { (swapR (F := F) (E := E) R).toAddEquiv with
      map_smul' := fun c y => by
        change swapR (F := F) (E := E) R (c • y) = c • swapR (F := F) (E := E) R y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  exact ⟨IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [TopologicalSpace R] in
theorem swapR_sig (x : R ⊗[F] E) :
    Formalism.UG.sigR σ R (swapR R x) = swapR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def swapU : letI := tensTopL (F := F) (E := E) R; HA R σ J ≃ₜ* UPts σ J R :=
  letI := tensTopL (F := F) (E := E) R
  ujEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapR R) (continuous_swapR R).1 (continuous_swapR R).2
    (swapR_sig R σ) (JR R J) (J.map (inclE (F := F) R)) (Matrix.ext fun _ _ => rfl)

end Swap

section Fin

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def finEquiv : finPts σ J ≃ₜ* GFin σ J where
  toFun g := projFin σ J g.1
  invFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  left_inv g := Subtype.ext (ext_inf_fin σ J ((projInf_ofFin σ J _).trans (mem_finPts.1 g.2).symm)
    (projFin_ofFin σ J _))
  right_inv y := projFin_ofFin σ J y
  map_mul' g h := map_mul (projFin σ J) g.1 h.1
  continuous_toFun := (continuous_projFin σ J).comp continuous_subtype_val
  continuous_invFun := (continuous_ofFin σ J).subtype_mk _

end Fin

theorem exists_finIso : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); ∃ e : ↥(GfC V) ≃ₜ* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ∀ g, (e g).1.1 = finM V hn g.1 := by
  intro D V n hn
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  exact ⟨(finEquiv D.sp.cm.sig V.gram).trans
    (swapU (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.sp.cm.sig V.gram), fun g => rfl⟩

end GlobalTheory.FinPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralThetaEtaTwelfthPowerConjugatesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_thetaEta_twelfth_power_conjugates : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  first | exact @GlobalTheory.IntegralXCore.exists_integral_theta_ratio | exact GlobalTheory.IntegralXCore.exists_integral_theta_ratio | (intros; apply GlobalTheory.IntegralXCore.exists_integral_theta_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2,
      GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsQuotientIntegrableFoldUnimodular
section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Tw
open scoped ENNReal

namespace GlobalTheory.EvalAbs

theorem lintegral_eq_of_integral {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m₁ : Measure α} {m₂ : Measure β} {a : α → γ} {b : β → γ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ f : γ → ℂ, Measurable f → (Integrable (fun x => f (a x)) m₁ ↔ Integrable (fun y => f (b y)) m₂) ∧
      (Integrable (fun y => f (b y)) m₂ → ∫ x, f (a x) ∂m₁ = ∫ y, f (b y) ∂m₂))
    (F : γ → ℝ≥0∞) (hF : Measurable F) : ∫⁻ x, F (a x) ∂m₁ = ∫⁻ y, F (b y) ∂m₂ := by
  have e : m₁.map a = m₂.map b := by
    ext A hA
    rw [Measure.map_apply ha hA, Measure.map_apply hb hA]
    obtain ⟨h1, h2⟩ := h (A.indicator fun _ => 1) (measurable_const.indicator hA)
    have e1 : (fun x => A.indicator (fun _ => (1 : ℂ)) (a x)) = (a ⁻¹' A).indicator fun _ => 1 := rfl
    have e2 : (fun x => A.indicator (fun _ => (1 : ℂ)) (b x)) = (b ⁻¹' A).indicator fun _ => 1 := rfl
    rw [e1, e2, integrable_indicator_iff (ha hA), integrable_indicator_iff (hb hA), integrableOn_const_iff,
      integrableOn_const_iff] at h1
    rw [e1, e2, integrable_indicator_iff (hb hA), integrableOn_const_iff, integral_indicator (ha hA),
      integral_indicator (hb hA)] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter, Complex.real_smul, mul_one, Complex.ofReal_inj] at h1 h2
    by_cases hf : m₂ (b ⁻¹' A) < ∞
    · exact (ENNReal.toReal_eq_toReal_iff' (h1.2 hf).ne hf.ne).1 (h2 hf)
    · rw [not_lt_top_iff.1 hf, not_lt_top_iff.1 (fun h' => hf (h1.1 h'))]
  rw [← lintegral_map hF ha, e, lintegral_map hF hb]

theorem setLIntegral_mul_right {R : Type} [Group R] [MeasurableSpace R] [MeasurableMul R] {μ : Measure R}
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup R} [Countable Γ] {𝓡 : Set R}
    (h : IsFundamentalDomain Γ 𝓡 μ) (q : R → ℝ≥0∞) (hq : ∀ γ ∈ Γ, ∀ r, q (γ * r) = q r) (m : R) :
    ∫⁻ r in 𝓡, q (r * m) ∂μ = ∫⁻ r in 𝓡, q r ∂μ := by
  have hp : MeasurePreserving (· * m) μ μ := measurePreserving_mul_right μ m
  have h2 : IsFundamentalDomain Γ ((· * m) ⁻¹' 𝓡) μ :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h.setLIntegral_eq h2 (fun r => q (r * m)) fun γ r => by
    rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hq _ γ.2 _]
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight m).measurableEmbedding q 𝓡

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {R Γ : Subgroup G} {μR : Measure R} [μR.IsHaarMeasure] [μR.IsInvInvariant] {𝓡 : Set R} {𝓑 : Set G}

theorem exists_quotientIntegrable_of_le_mean (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ) {K : G → ℝ≥0∞}
    (hK : Measurable K) (hKΓ : ∀ γ ∈ Γ, ∀ g, K (γ * g) = K g) (hfin : ∫⁻ g in 𝓑, K g ∂μ < ∞) {f : G → ℂ}
    (hf : Measurable f) (hfR : ∀ r ∈ R, ∀ g, f (r * g) = f g) (hle : ∀ h, ‖f h‖ₑ ≤ ∫⁻ r in 𝓡, K (r * h) ∂μR) :
    ∃ z, IsQuotIntL1 μR μ f z := by
  refine ⟨_, (isQuotIntL1_iff hR hf).2 ⟨hfR, ⟨(measurable_comp_out hf hfR).aestronglyMeasurable, ?_⟩, rfl⟩⟩
  obtain ⟨S, hSm, hS⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable hSm
  have e : ∀ h : G, ∫⁻ r in 𝓡, K (r * h) ∂μR = ∫⁻ r : R, S.indicator K (r * h) ∂μR := fun h => by
    have hfd : IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR :=
      IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓR hS h)
    rw [h𝓡.setLIntegral_eq hfd (fun r : R => K (r * h)) fun γ r => by
      change K ((((γ : R) : G) * r) * h) = _
      rw [mul_assoc]; exact hKΓ _ γ.2 _, ← lintegral_indicator (hSh h)]
    rfl
  calc ∫⁻ c, ‖f (Quotient.out c)‖ₑ ∂quotMeas R μ μR
      ≤ ∫⁻ c, ∫⁻ r : R, S.indicator K (r * Quotient.out c) ∂μR ∂quotMeas R μ μR :=
        lintegral_mono fun c => (hle _).trans (e _).le
    _ = ∫⁻ g, S.indicator K g ∂μ := (isQuotMeasure_quotMeas hR _ (hK.indicator hSm)).symm
    _ = ∫⁻ g in 𝓑, K g ∂μ := by
        rw [lintegral_indicator hSm]
        exact hSfd.setLIntegral_eq h𝓑 K fun γ x => hKΓ _ γ.2 x
    _ < ∞ := hfin

theorem exists_quotientIntegrable_fold_unimodular (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ)
    {U : Type} [Group U] [MeasurableSpace U] [MeasurableMul U] [MeasurableInv U] {ν : Measure U} [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (j : U →* G) (hj : Measurable j) (hjR : ∀ u, j u ∈ R)
    {q : G → G → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (hqΓ : ∀ γ ∈ Γ, ∀ g, ∀ r ∈ R, q (γ * g) (γ * r) = q g r)
    (hqR : ∀ r ∈ R, ∃ v, ∀ g u, q g (r * j u) = q g (j (v * u)))
    (hfin : ∫⁻ g in 𝓑, ∫⁻ u, q g (j u) ∂ν ∂μ < ∞) {P : G → ℂ} (hP : Measurable P)
    (hPR : ∀ r ∈ R, ∃ v, ∀ g u, P (j u * (r * g)) = P (j (u * v) * g))
    (hle : ∀ h, ‖P h‖ₑ ≤ ∫⁻ r in 𝓡, q (r * h) r ∂μR) :
    ∃ z, IsQuotIntL1 μR μ (fun h => ((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)) z := by
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  have : ν.IsMulRightInvariant := by rw [← Measure.inv_eq_self ν]; infer_instance
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hU : ∀ r ∈ R, ∀ g, ∫⁻ u, q g (r * j u) ∂ν = ∫⁻ u, q g (j u) ∂ν := fun r hr g => by
    obtain ⟨v, hv⟩ := hqR r hr
    simp only [hv]
    exact lintegral_mul_left_eq_self (fun u => q g (j u)) v
  refine exists_quotientIntegrable_of_le_mean hΓR hR h𝓡 h𝓑 (K := fun g => ∫⁻ u, q g (j u) ∂ν) ?_ (fun γ hγ g => ?_) hfin ?_
    (fun r hr g => ?_) fun h => ?_
  · exact (hq.comp (measurable_fst.prodMk (hj.comp measurable_snd))).lintegral_prod_right'
  · rw [← hU γ⁻¹ (inv_mem (hΓR hγ)) g]
    refine lintegral_congr fun u => ?_
    rw [← hqΓ γ hγ g _ (mul_mem (inv_mem (hΓR hγ)) (hjR u)), mul_inv_cancel_left]
  · refine Complex.measurable_ofReal.comp (StronglyMeasurable.measurable ?_)
    exact (hP.comp ((hj.comp measurable_snd).mul measurable_fst)).norm.stronglyMeasurable.integral_prod_right'
  · obtain ⟨v, hv⟩ := hPR r hr
    simp only [hv]
    rw [integral_mul_right_eq_self (fun u => ‖P (j u * g)‖) v]
  · have hm : Measurable fun p : U × R => q (p.2 * h) (p.2 * j p.1⁻¹) :=
      hq.comp (((measurable_subtype_coe.comp measurable_snd).mul_const h).prodMk
        ((measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst.inv)))
    calc ‖((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)‖ₑ = ‖∫ u, ‖P (j u * h)‖ ∂ν‖ₑ := by
          simp only [enorm, Complex.nnnorm_real]
      _ ≤ ∫⁻ u, ‖‖P (j u * h)‖‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ∫⁻ r in 𝓡, q (r * h) (r * j u⁻¹) ∂μR ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [enorm_norm]
          refine (hle _).trans (le_of_eq ?_)
          rw [← setLIntegral_mul_right h𝓡 (fun r : R => q (r * h) (r * j u⁻¹)) (fun γ hγ r => by
            simp only [Subgroup.coe_mul, mul_assoc]
            exact hqΓ _ hγ _ _ (mul_mem r.2 (hjR _))) ⟨j u, hjR u⟩]
          simp only [Subgroup.coe_mul, mul_assoc, map_inv, mul_inv_cancel, mul_one]
      _ = ∫⁻ r in 𝓡, ∫⁻ u, q (r * h) (r * j u⁻¹) ∂ν ∂μR := lintegral_lintegral_swap hm.aemeasurable
      _ = _ := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_inv_eq_self (μ := ν) fun u => q (r * h) (r * j u), hU r r.2]

end

end GlobalTheory.EvalAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  first | exact @GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | exact GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | (intros; apply GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp <;> assumption)
end

