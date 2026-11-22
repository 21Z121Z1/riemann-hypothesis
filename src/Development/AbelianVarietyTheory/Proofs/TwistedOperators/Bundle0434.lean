import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocally
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_secGen_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  intro E _ _ _ H Dw l Xo c T _ _ x hx q
  have hS := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F T) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F T)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj T xF h2 q hp
  refine ⟨g, hg, ?_⟩
  let lam : T →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F T (Localization.Away g)
  obtain ⟨ψ, hψ⟩ := hT (Localization.Away g) lam (IsLocalization.Away.algebraMap_isUnit g)
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R _ ψ y₀
  have hzx : z.x = spMap (algebraMap T (Localization.Away g)) ≫ x := by
    rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, Category.assoc, h1]
    rfl
  have key : ∀ x' : Sp (Localization.Away g) ⟶ Xo.X, z.x = x' → ∃ s : LB.Sec (PPx x'), SecGen x' s := by
    rintro _ rfl
    exact ⟨z.s, z.gen⟩
  exact key _ hzx

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.EtaleTraceGeom

open TensorProduct

theorem exists_eq_eval {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K) : ∃ p : P, ∀ z : P → K, θ z = z p := by
  first
  | exact @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | (apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval ..)

theorem trace_pi_self {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P] (z : P → K) :
    Algebra.trace K (P → K) z = ∑ p, z p := by
  let b := Pi.basisFun K P
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]

theorem exists_trace_eq_finsum : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B →
    Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
      φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  intro R B _ _ _ hfin het b
  classical
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  have : Module.Flat R B := inferInstance
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R B
  refine ⟨LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f), fun Ω _ _ φ => ?_⟩
  letI := φ.toAlgebra
  have hφ : algebraMap R Ω = φ := rfl

  have step1 : φ (LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f)) =
      Algebra.trace Ω (Ω ⊗[R] B) (1 ⊗ₜ b) := by
    rw [← hφ, ← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hfg,
      LinearMap.baseChange_id, LinearMap.comp_id, Algebra.trace_apply, Algebra.baseChange_lmul]
  rw [step1]
  set e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] B) with he
  haveI : Module.Finite Ω (PrimeSpectrum (Ω ⊗[R] B) → Ω) := Module.Finite.equiv e.toLinearEquiv
  haveI : IsArtinianRing (Ω ⊗[R] B) := isArtinian_of_tower Ω inferInstance
  haveI : Finite (PrimeSpectrum (Ω ⊗[R] B)) := inferInstance
  haveI : Fintype (PrimeSpectrum (Ω ⊗[R] B)) := Fintype.ofFinite _
  rw [← Algebra.trace_eq_of_algEquiv e, trace_pi_self]
  let S := {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}
  let G : PrimeSpectrum (Ω ⊗[R] B) → (B →ₐ[R] Ω) := fun p =>
    (((Pi.evalAlgHom Ω (fun _ => Ω) p).comp (e : Ω ⊗[R] B →ₐ[Ω] _)).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let F : PrimeSpectrum (Ω ⊗[R] B) → S := fun p =>
    ⟨(G p).toRingHom, RingHom.ext fun r => (G p).commutes r⟩
  have hF : ∀ p y, (F p).1 y = e (1 ⊗ₜ y) p := fun p y => rfl
  have hinj : Function.Injective F := by
    intro p q h
    have h' : ∀ y : B, e (1 ⊗ₜ y) p = e (1 ⊗ₜ y) q := fun y => by
      rw [← hF, ← hF, h]
    have h'' : ∀ x, e x p = e x q := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a y =>
        rw [show a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y : Ω ⊗[R] B) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, Pi.smul_apply,
          Pi.smul_apply, h' y]
      | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
    have := h'' (e.symm (Pi.single p 1))
    rw [e.apply_symm_apply, Pi.single_eq_same] at this
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero this
  have hsurj : Function.Surjective F := by
    rintro ⟨χ, hχ⟩
    let χ' : B →ₐ[R] Ω := { χ with commutes' := fun r => RingHom.congr_fun hχ r }
    let ψ : Ω ⊗[R] B →ₐ[Ω] Ω := AlgHom.liftEquiv R Ω B Ω χ'
    obtain ⟨p, hp⟩ := exists_eq_eval (ψ.comp e.symm.toAlgHom)
    refine ⟨p, Subtype.ext (RingHom.ext fun y => ?_)⟩
    rw [hF, ← hp (e (1 ⊗ₜ y))]
    simp [ψ, χ']
  rw [← finsum_comp_equiv (Equiv.ofBijective F ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.EtaleTraceGeom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceTensor.GenPair

theorem exists_pairing {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (G : BoundedContinuousFunction Z ℂ) :
    ∃ L : BoundedContinuousFunction Z ℂ →L[ℂ] ℂ, ∀ F, L F = ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν := by
  have hint : ∀ F : BoundedContinuousFunction Z ℂ, MeasureTheory.Integrable (fun w => F w * (starRingEnd ℂ) (G w)) ν :=
    fun F => (F * star G).integrable ν
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ∫ w, F w * (starRingEnd ℂ) (G w) ∂ν
      map_add' := fun F F' => by
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint F) (hint F')
      map_smul' := fun c F => by
        simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ } ((ν Set.univ).toReal * ‖G‖) fun F => ?_, fun F => rfl⟩
  have hb : ∀ w, ‖F w * (starRingEnd ℂ) (G w)‖ ≤ ‖F‖ * ‖G‖ := fun w => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (F.norm_coe_le_norm w) (G.norm_coe_le_norm w) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc _ ≤ ‖F‖ * ‖G‖ * (ν Set.univ).toReal := by simpa [Measure.real] using this
    _ = _ := by ring

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.DefLift GlobalTheory.DefLift.Gen

theorem blk_sub_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (Y : O → Matrix (Fin m) (Fin m) ℂ)
    (X : O → Matrix (Fin n) (Fin n) ℂ) (τ' : O) (u : Matrix (Fin m) (Fin n) ℂ) :
    (GlobalTheory.RealWeil.blk Y (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) X) *ᵥ
                 vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext p
  obtain ⟨⟨i, j⟩, τ⟩ := p
  have key : ∀ (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ)
      (v : (Fin m × Fin n) × O → ℂ), (GlobalTheory.RealWeil.blk b a *ᵥ v) ((i, j), τ) = (b τ * cpt v τ * a τ) i j :=
    fun b a v => by rw [← cpt_blk]; rfl
  have hc : cpt (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) τ = (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) τ := rfl
  rw [Matrix.sub_mulVec, Pi.sub_apply, key, key, hc]
  show _ = (Pi.single τ' (Y τ' * u - u * X τ') : O → Matrix (Fin m) (Fin n) ℂ) τ i j
  by_cases h : τ = τ'
  · subst h
    simp
  · simp [h]

open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem oneP_zero (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : oneP θ V τ X 0 = 1 := by
  have h := GlobalTheory.Mem.Lift.oneP_add hθ hX 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel]
  exact GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX

theorem hasDerivAt_mM (hθ : IsInfFam θ) {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hX : X ∈ lieAt S τ) {Y : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hY : Y ∈ lieAt T τ) (k l : GlobalTheory.RealWeil.Ix S T) :
    HasDerivAt (fun t : ℝ => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t) k l)
      ((GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X) :
        Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) k l) 0 := by
  obtain ⟨⟨i, j⟩, τ₁⟩ := k
  obtain ⟨⟨i', j'⟩, τ₂⟩ := l
  have hS : ∀ t : ℝ, (oneP θ S τ X t)⁻¹ = oneP θ S τ X (-t) := GlobalTheory.PlaceTensor.GenPair.oneP_inv hθ hX
  simp only [mM_apply, hS, GlobalTheory.RealWeil.blk, Matrix.sub_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h : τ₁ = τ₂
  · subst h
    simp only [if_true]
    have hb := hasDerivAt_comp hθ hY τ₁ i i'
    have ha0 := hasDerivAt_comp hθ hX τ₁ j' j
    have ha : HasDerivAt (fun t : ℝ => Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X t)) j' j)
        ((Pi.single τ X : D.what₂.Tau → _) τ₁ j' j) (-0) := by rw [neg_zero]; exact ha0
    have hT0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt T (oneP θ T τ Y 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]; exact compAt_fin (one_mem _) τ₁
    have hS0 : Formalism.IndefR.Datum.compAt θ τ₁ (Formalism.L2.Theta.mt S (oneP θ S τ X 0)) = 1 := by
      rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX]; exact compAt_fin (one_mem _) τ₁
    refine (hb.mul (ha.scomp 0 (hasDerivAt_neg 0))).congr_deriv ?_
    simp only [Function.comp_apply, neg_zero, hT0, hS0, Matrix.one_apply]
    split_ifs <;> simp <;> ring
  · simp only [h, if_false, sub_zero]
    exact hasDerivAt_const _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  intro D ψ θ S T χS χT om hW hθ τ X hX Y hY
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hweak : GlobalTheory.Ker.IsWeak ψ S T om := GlobalTheory.Ker.isWeak_of_datum hW
  have hcont : OmCont ψ S T om := hW.om_cont
  have hγc : Continuous fun t : ℝ => (oneP θ S τ X t, oneP θ T τ Y t) :=
    (GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hγa : ∀ s t : ℝ, (oneP θ S τ X (s + t), oneP θ T τ Y (s + t)) =
      (oneP θ S τ X s, oneP θ T τ Y s) * (oneP θ S τ X t, oneP θ T τ Y t) := fun s t => by
    rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY]; rfl
  have hγm : ∀ t : ℝ, oneP θ S τ X t ∈ GinfC S ∧ oneP θ T τ Y t ∈ GinfC T := fun t =>
    ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩
  obtain ⟨lam, hlam⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ hσ ψ hψ S T om hweak hcont
    (fun t => (oneP θ S τ X t, oneP θ T τ Y t)) hγc hγa hγm _
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  have h0 : mM θ S T (oneP θ S τ X 0, oneP θ T τ Y 0) = 1 := by
    rw [GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hX, GlobalTheory.PlaceTensor.GenPair.oneP_zero hθ hY]
    exact (mM θ S T).map_one
  have hlie := GlobalTheory.Mem.Lift.GenZero.lie_of_path (HM S T)
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X))
    (fun t => mM θ S T (oneP θ S τ X t, oneP θ T τ Y t)) h0 (fun t => mM_unitary hθ _)
    (fun k l => GlobalTheory.PlaceTensor.GenPair.hasDerivAt_mM hθ hX hY k l)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.DefLift.Gen.exists_extension hσ hψ
    (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    ⟨GlobalTheory.RealWeil.toB hψ f hf, GlobalTheory.RealWeil.coe_toB hψ f hf⟩
  obtain ⟨hnt, hGF⟩ := hGn F hf
  have hAt : IsThetaFunO ψ S T ((nOp (rhoV hψ σ S T) (HM S T)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
      + lam • F).1 : WO S T → ℂ) := by
    rw [← GlobalTheory.DefLift.Gen.coe_add_smul]
    exact GlobalTheory.OrientedHeis.theta_add hnt (GlobalTheory.OrientedHeis.theta_smul lam hf)
  have hcomm : ∀ (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u F.1) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ'
        ((Pi.single τ Y : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) τ' * u -
          u * (Pi.single τ X : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) τ') F.1 := by
    intro τ' u
    have hdt := GlobalTheory.DefLift.Gen.theta_dH hσ hψ F hf
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    have e2 := (hGn _ hdt).2
    have e4 := nOp_add_comm HM_herm HM_det hlie (isHeis_rhoB hσ hψ) lam
      (GlobalTheory.RealWeil.sm_of_theta hσ hψ F hf) (GlobalTheory.RealWeil.sm_of_theta hσ hψ _ hnt)
      (vecL (Pi.single τ' u : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ))
    rw [← GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' u, e2, hGF, ← GlobalTheory.DefLift.Gen.coe_dH hσ hψ _ hAt τ' u, e4,
      GlobalTheory.PlaceTensor.GenPair.blk_sub_vecL, GlobalTheory.DefLift.Gen.coe_add_sub]
    exact GlobalTheory.DefLift.Gen.coe_dH hσ hψ F hf τ' _
  obtain ⟨u, hu1, hu2⟩ := hlam F hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGF]; exact hAt
  · intro v
    rw [hcomm, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' h v
    have hc := hcomm τ' v
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_mul, Matrix.mul_zero, sub_zero,
      GlobalTheory.DefLift.Gen.dRho_zero hσ hψ F hf] at hc
    exact sub_eq_zero.mp hc
  · intro w
    have h2 : HasDerivAt (fun t => ev _ _ w (u t)) (ev _ _ w (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F)) 0 :=
      ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [ev_apply, hu1] at h2
    rw [hGF]; exact h2
  · intro μ 𝓕 hμ g hg
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
      rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨L, hL⟩ := GlobalTheory.PlaceTensor.GenPair.exists_pairing (μ.restrict 𝓕) (GlobalTheory.RealWeil.toB hψ g hg).1
    have h2 : HasDerivAt (fun t => L (u t).1) (L (nOp (rhoV hψ σ S T) (HM S T)
        (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) - GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ X)) F
        + lam • F).1) 0 :=
      ((L.comp (BB ψ S T).subtypeL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hu2
    simp only [hL, hu1, GlobalTheory.RealWeil.coe_toB] at h2
    rw [hGF]; exact h2

end GlobalTheory.PlaceTensor.GenPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

open GlobalTheory.Spread

theorem fibre_transition {G X : Scheme.{0}} (p : G ⟶ X) {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) (x : Sp K ⟶ X)
    (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom) :
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ π =
      bcMap (pullback.snd p x) M.val ≫ (pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, h₁, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, bcMap_fst_assoc]
  · rw [Category.assoc, h₂, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, bcMap_snd]

theorem exists_descend_fibre {G X : Scheme.{0}} (p : G ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation p] {K L : Type} [Field K] [Field L] [Algebra K L] (x x' : Sp K ⟶ X)
    (g : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K L) ≫ x'))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ s : Finset L, ∀ M : IntermediateField K L, (s : Set L) ⊆ M →
      ∃ f : pullback p (spMap (algebraMap K M) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x'),
        f ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        ∀ (π : pullback p (spMap (algebraMap K L) ≫ x) ⟶ pullback p (spMap (algebraMap K M) ≫ x))
          (π' : pullback p (spMap (algebraMap K L) ≫ x') ⟶ pullback p (spMap (algebraMap K M) ≫ x')),
          π ≫ pullback.fst _ _ = pullback.fst _ _ →
          π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          π' ≫ pullback.fst _ _ = pullback.fst _ _ →
          π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap M.val.toRingHom →
          g ≫ π' = π ≫ f := by
  let A : Over (Sp K) := Over.mk (pullback.snd p x)
  let B : Over (Sp K) := Over.mk (pullback.snd p x')
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (pullback.snd p x))
  have : QuasiSeparated A.hom := inferInstanceAs (QuasiSeparated (pullback.snd p x))
  have : LocallyOfFinitePresentation B.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd p x'))
  let g₀ : pullback (pullback.snd p x) (spMap (algebraMap K L)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K L)) :=
    (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom ≫ g ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K L))).inv
  have hg₀ : g₀ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    simp only [g₀, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hg, pullbackLeftPullbackSndIso_hom_snd]
  obtain ⟨s, hs⟩ := HomPairDescent.exists_descend (Ω := L) A B (Over.homMk g₀ hg₀)
  refine ⟨s, fun M hM => ?_⟩
  obtain ⟨f, hf⟩ := hs M hM
  let f₀ : pullback (pullback.snd p x) (spMap (algebraMap K M)) ⟶
      pullback (pullback.snd p x') (spMap (algebraMap K M)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hf₁ : bcMap (pullback.snd p x) M.val ≫ f₀ = g₀ ≫ bcMap (pullback.snd p x') M.val := hf
  refine ⟨(pullbackLeftPullbackSndIso p x (spMap (algebraMap K M))).inv ≫ f₀ ≫
      (pullbackLeftPullbackSndIso p x' (spMap (algebraMap K M))).hom, ?_, fun π π' h₁ h₂ h₃ h₄ => ?_⟩
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, hf₀, pullbackLeftPullbackSndIso_hom_snd]
  · have e := fibre_transition p M x π h₁ h₂
    have e' := fibre_transition p M x' π' h₃ h₄
    rw [← cancel_epi (pullbackLeftPullbackSndIso p x (spMap (algebraMap K L))).hom, reassoc_of% e,
      Iso.hom_inv_id_assoc, reassoc_of% hf₁, ← e']
    simp only [g₀, Category.assoc, Iso.inv_hom_id_assoc]

theorem pair_defined_over_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  classical
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' g g' hφ hw hw' _ _
  let _ : Algebra K L := φ.toAlgebra
  have hint : Algebra.IsIntegral K L := ⟨hφ⟩
  subst hw hw'
  have hA := ObjDim.isAbelianScheme Xo.univ
  have := hA.proper
  have := hA.smooth
  obtain ⟨s, hs⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x x' g.left (Over.w g)
  obtain ⟨t, ht⟩ := exists_descend_fibre Xo.univ.t.G.hom (L := L) x' x g'.left (Over.w g')
  let M : IntermediateField K L := IntermediateField.adjoin K ((s ∪ t : Finset L) : Set L)
  have hM : ((s ∪ t : Finset L) : Set L) ⊆ M := IntermediateField.subset_adjoin _ _
  obtain ⟨f, hf, hf'⟩ := hs M ((Finset.coe_subset.2 Finset.subset_union_left).trans hM)
  obtain ⟨r, hr, hr'⟩ := ht M ((Finset.coe_subset.2 Finset.subset_union_right).trans hM)
  have hfin : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨M, inferInstance, algebraMap K M, M.val.toRingHom, RingHom.ext fun _ => rfl,
    RingHom.finite_algebraMap.2 hfin, ?_⟩
  rintro v v' rfl rfl
  have e : ∀ y : Sp K ⟶ Xo.X, spMap φ ≫ y = spMap M.val.toRingHom ≫ spMap (algebraMap K M) ≫ y := fun y => by
    rw [← Category.assoc, spMap_algHom_comp]
  exact ⟨Over.homMk f hf, Over.homMk r hr, ⟨e x, e x', hf'⟩, ⟨e x', e x, hr'⟩⟩

end GlobalTheory.HkIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.RationalIsometry
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_congr (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {r : ℕ} {J J' : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (Jᵀ a b) = Jᵀ b a) (hG' : ∀ a b, cc (J'ᵀ a b) = J'ᵀ b a)
    (hd : J.det ≠ 0) (hd' : J'.det ≠ 0) {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Jᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm J'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map τ) p q ∧ Formalism.UG.HasSignature (J'.map τ) p q) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ ∀ x y, herm Jᵀ (P *ᵥ x) (P *ᵥ y) = herm J'ᵀ x y := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := fun z =>
    (FractionalIdeal.mem_one_iff _).trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨P, hP0, hP⟩ := congr_of_modular (G := Jᵀ) (G' := J'ᵀ) (L := L) (L' := L') (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hz
      exact (FractionalIdeal.mem_one_iff _).2 ⟨IsCMField.ringOfIntegersComplexConj E a, rfl⟩)
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [hone] using hsd) (by simpa only [hone] using hsd')
    (fun τ => by
      obtain ⟨p, q, h, h'⟩ := hs τ
      obtain ⟨f⟩ : Nonempty (Fin r ≃ Fin p ⊕ Fin q) := ⟨h.choose⟩
      obtain ⟨A, hA, e⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h f
      obtain ⟨A', hA', e'⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h' f
      refine GlobalTheory.Published.Landherr.congr_of_gram_eq τ hA hA' ?_
      rw [GlobalTheory.Published.gram_eq, GlobalTheory.Published.gram_eq]
      exact e.trans e'.symm)
  exact ⟨P, hP0, fun x y => by rw [herm_mulVec, ← hP]⟩

theorem gram_herm (W : HSpace E) (a b : Fin W.rank) : cc (W.gramᵀ a b) = W.gramᵀ b a :=
  W.herm.eq (W.frame b) (W.frame a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W Y : HSpace E) (hW : W.SigOK) (hY : Y.SigOK)
    (hr : W.rank = Y.rank) (hs : ∀ τ, W.sig τ = Y.sig τ) :
    ∃ φ : W.V ≃ₗ[E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap := by
  obtain @⟨V, i1, i2, i3, i4, i5, hT, hh, hn, r, hrk, fr, sg, L, hL, hu⟩ := Y
  change W.rank = r at hr
  subst hr
  let Y : HSpace E := ⟨V, hT, hh, hn, W.rank, hrk, fr, sg, L, hL, hu⟩
  obtain ⟨P, hP0, hP⟩ := exists_congr hc (r := W.rank) (J := Y.gram) (J' := W.gram) (gram_herm Y) (gram_herm W)
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit Y).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
    (isLattice_coordLat Y Y.L0 Y.standardTuple_isLattice) (isLattice_coordLat W W.L0 W.standardTuple_isLattice)
    (selfDual_coordLat Y Y.L0 Y.baseLattice_isUnimodular) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    (fun τ => ⟨_, _, hY τ, by have := hW τ; rwa [hs τ] at this⟩)
  refine ⟨(W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    Y.frame.equivFun.symm, fun x y => ?_⟩
  change Y.hT (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun x))
    (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun y)) = _
  rw [← herm_coord, ← herm_coord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hP _ _

end

theorem rationalSt (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W Y hW hY hr hs => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W Y hW hY hr hs

end GlobalTheory.RationalIsometry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  first | exact @GlobalTheory.ResNormFourier.resNorm_fourier | exact GlobalTheory.ResNormFourier.resNorm_fourier | (intros; apply GlobalTheory.ResNormFourier.resNorm_fourier <;> assumption)
end

