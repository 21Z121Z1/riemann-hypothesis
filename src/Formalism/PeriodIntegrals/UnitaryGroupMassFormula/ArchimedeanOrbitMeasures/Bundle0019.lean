import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0004

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstFin
section
noncomputable section

namespace PI.AprimeInfW

theorem properOrb_of_compact (hH : MassDataMassesW.HinfCompact) : ProperOrb :=
  properOrb_of_one (properOne_of wittInf_holds hH) invNbhd_holds

theorem pushCont_of_compact (hH : MassDataMassesW.HinfCompact) : PushCont :=
  pushCont_of frame_independent_at_infinity (properOrb_of_compact hH)

theorem pushLFin_of_compact (hH : MassDataMassesW.HinfCompact) : PushLFin :=
  pushLFin_of_proper (properOrb_of_compact hH)

theorem constTest_of_polar_compact (hP : PolarLoc) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar hP (pushCont_of_compact hH)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure V) (χ : V → V → ℂ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  haveI := h.1
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  have hm : μ.map e = μ.map em := rfl
  refine ⟨ea.isAddHaarMeasure_map μ e.continuous e.symm.continuous, fun Φ hc hs hI z => ?_⟩
  rw [hm] at hI ⊢
  have hT : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map em) = ∫ x, Φ (e x) * χ x (e.symm y) ∂μ := by
    intro y
    rw [integral_map_equiv]
    simp [em]
  simp only [hT] at hI ⊢
  rw [integrable_map_equiv] at hI
  rw [integral_map_equiv]
  simp only [em, Function.comp_def, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply] at hI ⊢
  rw [h.2 (fun x => Φ (e x)) (hc.comp e.continuous) (hs.comp_homeomorph e) hI (e.symm z)]
  show Φ (e (-e.symm z)) = Φ (-z)
  rw [show e (-e.symm z) = -z from by
    have := ea.map_neg (e.symm z)
    change e (-e.symm z) = -e (e.symm z) at this
    rw [this, e.apply_symm_apply]]

section Beta

variable {D : D7} (X : HidaSetting D)

theorem tupCoord_symm_add (x y : EuclideanSpace ℝ (KapI X)) :
    (tupCoord X).symm (x + y) = (tupCoord X).symm x + (tupCoord X).symm y := by
  apply (tupCoord X).injective
  rw [tupCoord_add]
  simp

theorem betaI_add_left (x x' y : EuclideanSpace ℝ (KapI X)) : betaI X (x + x') y = betaI X x y + betaI X x' y := by
  simp only [betaI, tupCoord_symm_add, BR_add_leftP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y)) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x') ((tupCoord X).symm y) w from rfl,
    map_add, Complex.add_re]

theorem betaI_add_right (x y y' : EuclideanSpace ℝ (KapI X)) : betaI X x (y + y') = betaI X x y + betaI X x y' := by
  simp only [betaI, tupCoord_symm_add, BR_add_rightP]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y')) w =
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y) w +
      BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y') w from rfl,
    map_add, Complex.add_re]

theorem continuous_betaI_left (y : EuclideanSpace ℝ (KapI X)) : Continuous fun x => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)))

theorem continuous_betaI_right (x : EuclideanSpace ℝ (KapI X)) : Continuous fun y => betaI X x y :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp
      ((continuous_apply w).comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous)))

theorem betaI_smul_left (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X (r • x) y = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun x => betaI X x y) fun a b => betaI_add_left X a b y)
    (continuous_betaI_left X y) r x

theorem betaI_smul_right (r : ℝ) (x y : EuclideanSpace ℝ (KapI X)) : betaI X x (r • y) = r * betaI X x y :=
  map_real_smul (AddMonoidHom.mk' (fun y => betaI X x y) fun a b => betaI_add_right X x a b)
    (continuous_betaI_right X x) r y

def betaL : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (betaI X) (betaI_add_left X) (fun r x y => betaI_smul_left X r x y) (betaI_add_right X)
    (fun r x y => betaI_smul_right X r x y)

open Classical in
theorem betaI_expand (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ i, ∑ j, x i * matI X i j * y j := by
  have h : betaI X x y = betaL X x y := rfl
  rw [h]
  conv_lhs => rw [← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr x, ← (EuclideanSpace.basisFun (KapI X) ℝ).sum_repr y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [betaL, LinearMap.mk₂_apply, matI]
  ring

end Beta

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Lie

variable {V : Type} [Fintype V] {n : ℕ}

def lieK (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i hi j hj, (hB v).2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i hi j hj, smul_zero]

def entL (V : Type) [Fintype V] (n : ℕ) :
    (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ (V × Fin n × Fin n) :=
  ({ toFun := fun M p => M p.1 p.2.1 p.2.2
     invFun := fun f v i j => f (v, i, j)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (V → Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] (V × Fin n × Fin n → ℂ)).trans
    ((EuclideanSpace.equiv (V × Fin n × Fin n) ℂ).toLinearEquiv.restrictScalars ℝ).symm

theorem entL_apply (M : V → Matrix (Fin n) (Fin n) ℂ) (p : V × Fin n × Fin n) :
    (EuclideanSpace.equiv (V × Fin n × Fin n) ℂ) (entL V n M) p = M p.1 p.2.1 p.2.2 := by
  simp [entL] <;> rfl

theorem norm_entL_sq (M : V → Matrix (Fin n) (Fin n) ℂ) :
    ‖entL V n M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := entL_apply M (v, i, j)
  simp only [EuclideanSpace.equiv] at this
  rw [← this]
  rfl

theorem exists_lieCompl (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) →
          ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieK ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieK ε S := by
    intro x
    obtain ⟨M, hM, hMe⟩ := (b.repr.symm x).2
    have : L x = M := by
      apply (entL V n).injective
      rw [hLe]; exact hMe.symm
    rw [this]; exact hM
  refine ⟨Fin (Module.finrank ℝ K'), inferInstance, L, fun x v => hLK x v, fun x => ?_, fun M hM => ?_⟩
  · rw [← norm_entL_sq, hLe]
    exact congrArg (· ^ 2) (b.repr.symm.norm_map x)
  · have hM' : entL V n M ∈ K' := ⟨M, hM, rfl⟩
    refine ⟨b.repr ⟨entL V n M, hM'⟩, ?_⟩
    apply (entL V n).injective
    rw [hLe, LinearIsometryEquiv.symm_apply_apply]

end Lie

def StdConjEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I,
    ∃ (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S

theorem stdDataEx_of (h : StdConjEx) : StdDataEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨c, S, hc⟩ := h X u' ψ hT μinf νinf fibInf hP hb
  obtain ⟨ι, hι, L, h1, h2, h3⟩ := exists_lieCompl X.B.I.ε S
  exact ⟨c, S, ι, hι, L, hc, ⟨h1, h2, h3⟩⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
section
noncomputable section

namespace PI.AprimeInfW

theorem fibOrbAt_of (hU : UnitsOpenTens) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) : FibOrbAt := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  obtain ⟨Ω₁, hΩ₁, hn, hu⟩ := nearFacts_of hU X u' ψ hT μinf νinf fibInf hP Ω a hCh
  exact ⟨Ω₁, hΩ₁, hn, fun T hT1 => fib_near rmulFacts_holds hF hC X u' ψ hT μinf νinf fibInf hP T (a T)
    (hu T hT1).1 (hCh.2.2.2 T (hΩ₁ hT1)) (hu T hT1).2⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpParts
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Matrix Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
theorem continuous_matExp (n : ℕ) : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  open scoped Norms.Operator in NormedSpace.exp_continuous

theorem continuous_expU {n : ℕ} (ε : Fin n → Bool) {Y : Type} [TopologicalSpace Y]
    (f : Y → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (hL : ∀ y, (f y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * f y = 0) : Continuous (fun y => expU ε (f y)) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : (Units.val ∘ Subtype.val ∘ fun y => expU ε (f y)) = fun y => NormedSpace.exp (f y) :=
      funext fun y => expU_val ε _ (hL y)
    rw [e]
    exact (continuous_matExp n).comp hf
  · have e : (fun x => ((((Subtype.val ∘ fun y => expU ε (f y)) x)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = fun y => NormedSpace.exp (-f y) := by
      funext y
      apply Units.inv_eq_of_mul_eq_one_right
      show (((expU ε (f y) : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        NormedSpace.exp (-f y) = 1
      rw [expU_val ε _ (hL y), ← Matrix.exp_add_of_commute (f y) (-f y) (Commute.neg_right (Commute.refl (f y))), add_neg_cancel,
        NormedSpace.exp_zero]
    rw [e]
    exact (continuous_matExp n).comp hf.neg

theorem continuous_kap0_of_lieCompl {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (hL : LieCompl X S L) : Continuous (kap0 X hb c L) := by
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hg : Continuous (fun x => ((fun v => expU (X.B.I.ε v) (L x v)) : X.B.I.Ginf)) :=
    continuous_pi fun v => continuous_expU _ (fun x => L x v) ((continuous_apply v).comp hLc)
      (fun x => (hL.1 x v).1)
  exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul hg).mul continuous_const)

def chiOf {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf) {η : Type}
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (y : EuclideanSpace ℝ η) : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L₁ y v)) * c⁻¹)

def BlockLie {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {η : Type}
    [Fintype η]
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) :
    Prop :=
  (∀ y v, (L₁ y v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * L₁ y v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → L₁ y v i j = 0) ∧
  (∀ y, ∑ v, ∑ i, ∑ j, ‖L₁ y v i j‖ ^ 2 = ‖y‖ ^ 2) ∧
  ∀ M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
    (∀ v, (M v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) + Formalism.REAL.Jm (X.B.I.ε v) * M v = 0 ∧
      ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ y, L₁ y = M

def BlockEx : Prop := ∀ {D : D7} (X : HidaSetting D) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)),
    ∃ (η : Type) (_ : Fintype η)
      (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
      BlockLie X S L₁

def StdCtx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (c : X.B.I.Ginf) (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) : Prop :=
  (∃ ψ : AddChar (AF X.B.I.F) ℂ, ∃ hT μinf νinf fibInf, PushHyp X u' ψ hT μinf νinf fibInf) ∧
    StdConj X hb u' c S ∧ LieCompl X S L ∧ BlockLie X S L₁

def ChiStab : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')

def GrpDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        X.measG.μGinf ((fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

def GrpHaarH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∀ hS : ∀ y, chiOf X hb c L₁ y ∈
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'),
    ∃ (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) (r : ℝ)
      (e : EuclideanSpace ℝ η → ℝ),
      ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧
      (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) ∧
      ∀ s, 0 < s → s ≤ r → ν ((fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s) =
        ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)

def GrpInj : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧
      (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r,
        (kap0 X hb c L a)⁻¹ * kap0 X hb c L b ∈
          MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
      Set.InjOn (chiOf X hb c L₁) (ball 0 r)

theorem grpPiecesStd_of (h0 : BlockEx) (hS : ChiStab) (hD : GrpDens) (hH : GrpHaarH) (hI : GrpInj) :
    GrpPiecesStd := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  obtain ⟨η, hη, L₁, hB⟩ := h0 X S
  have ctx : StdCtx X u' hb c S L L₁ := ⟨⟨ψ, hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩
  have hst := hS X u' hb c S L L₁ ctx
  obtain ⟨r1, hr1, d, hdc, hd0, hdens⟩ := hD X u' hb c S L L₁ ctx
  obtain ⟨ν, r2, e, hL', hSF, h0', hf, hr2, hec, he0, hvol, hνd⟩ := hH X u' hb c S L L₁ ctx hst
  obtain ⟨r3, hr3, hinj, hχi⟩ := hI X u' hb c S L L₁ ctx
  have hr : 0 < min r1 (min r2 r3) := lt_min hr1 (lt_min hr2 hr3)
  have h1 : min r1 (min r2 r3) ≤ r1 := min_le_left _ _
  have h2 : min r1 (min r2 r3) ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min r1 (min r2 r3) ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  have hχc : Continuous (fun y => (⟨chiOf X hb c L₁ y, hst y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) := by
    apply Continuous.subtype_mk
    have hLc : Continuous L₁ := L₁.continuous_of_finiteDimensional
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_expU _ (fun y => L₁ y v) ((continuous_apply v).comp hLc) (fun y => (hB.1 y v).1))).mul
        continuous_const)
  have hgpos : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := Finset.prod_pos fun v _ => (hP.2.2.2.1 v).2
  have hdet1 : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).det = 1 := by
    simp [ContinuousLinearMap.det]
  refine ⟨η, hη, fun y => ⟨chiOf X hb c L₁ y, hst y⟩, min r1 (min r2 r3),
    fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2, ball 0 (min r1 (min r2 r3)), d, id,
    fun _ => ContinuousLinearMap.id ℝ _, e, ν, hL', hSF, h0', hf, hr,
    (continuous_kap0_of_lieCompl X hb c S L hL).continuousOn, hχc.continuousOn, ?_, ?_, ?_, ?_, Set.injOn_id _, ?_, ?_, ?_,
    continuousAt_id, ?_, hdc, hec, he0, ?_, ?_⟩
  · intro a ha b hb' hab
    exact hχi (ball_subset_ball h3 ha) (ball_subset_ball h3 hb') (congrArg Subtype.val hab)
  · intro a ha b hb' hm
    exact hinj a (ball_subset_ball h3 ha) b (ball_subset_ball h3 hb') hm
  · intro A hA hAm
    exact hdens A (hA.trans (ball_subset_ball h1)) hAm
  · intro p _
    exact hasFDerivWithinAt_id p _
  · rw [Set.image_id]
  · intro p _
    rfl
  · intro s hs hsr
    exact hνd s hs (hsr.trans h2)
  · simp only [hdet1]
    exact continuousAt_const
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0]
    exact hgpos
  · simp only [hdet1, abs_one, one_mul, id]
    rw [hd0, gVal, ← hvol]
    ring

set_option backward.isDefEq.respectTransparency false in

theorem exp_mul_of_mul_eq_zero {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℂ) (hMP : M * P = 0) :
    NormedSpace.exp M * P = P := by
  open scoped Norms.Operator in
  have hs : Summable (fun k : ℕ => ((k.factorial : ℚ)⁻¹) • M ^ k) := NormedSpace.expSeries_summable' (𝕂 := ℚ) M
  rw [NormedSpace.exp_eq_tsum_rat, ← hs.tsum_mul_right P, tsum_eq_single 0]
  · simp
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [smul_mul_assoc, pow_succ, Matrix.mul_assoc, hMP, Matrix.mul_zero, smul_zero]

theorem exp_block_col {n : ℕ} (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) (i : Fin n) (hi : i ∉ S) (j : Fin n) :
    NormedSpace.exp M j i = if j = i then 1 else 0 := by
  have hMP : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0 := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b ∈ S
    · simp [hb]
    · simp [hb, hM a b (Or.inr hb)]
  have h := congrFun (congrFun (exp_mul_of_mul_eq_zero M _ hMP) j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply] at h
  simp only [hi, if_false, mul_one] at h
  rw [h]
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]

theorem chiStab' : ChiStab := by
  intro D X u' hb c S ι η _ _ L L₁ ctx y
  unfold chiOf
  refine (ctx.2.1.2 _).2 fun v i hi j => ?_
  show (((expU (X.B.I.ε v) (L₁ y v) : Formalism.REAL.UJ (X.B.I.ε v)) :
    (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) j i = _
  rw [expU_val _ _ (ctx.2.2.2.1 y v).1]
  exact exp_block_col (S v) _ (ctx.2.2.2.1 y v).2 i hi j

end PI.AprimeInfW
end
end

