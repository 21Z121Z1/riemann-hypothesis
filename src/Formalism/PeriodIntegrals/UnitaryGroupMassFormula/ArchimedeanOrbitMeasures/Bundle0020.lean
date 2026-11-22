import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0019
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0017

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockEx
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

section Block

variable {V : Type} [Fintype V] {n : ℕ}

def lieB (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) : Submodule ℝ (V → Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
    ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0}
  zero_mem' := by intro v; simp
  add_mem' := by
    intro A B hA hB v
    refine ⟨?_, fun i j hij => ?_⟩
    · have e : (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) =
          ((A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * A v) +
            ((B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * B v) := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
      show (A v + B v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (A v + B v) = 0
      rw [e, (hA v).1, (hB v).1, add_zero]
    · show A v i j + B v i j = 0
      rw [(hA v).2 i j hij, (hB v).2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA v
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * (c • A v) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hA v).1,
        smul_zero]
    · show c • A v i j = 0
      rw [(hA v).2 i j hij, smul_zero]

theorem exists_lieBlock (ε : V → Fin n → Bool) (S : V → Finset (Fin n)) :
    ∃ (η : Type) (_ : Fintype η) (L : EuclideanSpace ℝ η →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)),
      (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧
        ∀ i j, (i ∉ S v ∨ j ∉ S v) → L x v i j = 0) ∧
      (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) ∧
      ∀ M : V → Matrix (Fin n) (Fin n) ℂ,
        (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
          ∀ i j, (i ∉ S v ∨ j ∉ S v) → M v i j = 0) → ∃ x, L x = M := by
  set K' : Submodule ℝ (EuclideanSpace ℂ (V × Fin n × Fin n)) := (lieB ε S).map (entL V n).toLinearMap with hK'
  let b := stdOrthonormalBasis ℝ K'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ K')) →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    (entL V n).symm.toLinearMap ∘ₗ K'.subtype ∘ₗ b.repr.symm.toLinearEquiv.toLinearMap
  have hLe : ∀ x, entL V n (L x) = (b.repr.symm x : EuclideanSpace ℂ (V × Fin n × Fin n)) := by
    intro x; simp [L]
  have hLK : ∀ x, L x ∈ lieB ε S := by
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

end Block

theorem blockEx_holds : BlockEx := by
  intro D X S
  obtain ⟨η, hη, L, h1, h2, h3⟩ := exists_lieBlock X.B.I.ε S
  exact ⟨η, hη, L, h1, h2, h3⟩

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuF
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x

open Classical in

def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)

open Classical in

def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

open Classical in
theorem densMu_of (hS : BetaSym) (hN : MatND) : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by rw [det_Alin]; exact isUnit_iff_ne_zero.2 (hN X)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, hS]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpTop
section
namespace PI.AprimeInfW

theorem expProdU_of_G (h : CayDensG) : ExpProdU := expProdU_of_cayProdU (cayProdU_of_G h)

theorem expProdU_of_hua (h1 : CayDensEx) (h2 : CayValId) : ExpProdU := expProdU_of_G (cayDensG_of h1 h2)

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibNear
section
namespace PI.AprimeInfW

theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FixIffSpan
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : Fin X.B.I.n → ℂ :=
  (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (tupH (frameOf X u') b i)

def StabInfV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Ginf), X.toInf hb x ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔
      ∀ v b, uMat (x v) *ᵥ wV X u' v b = wV X u' v b

def WittBlock : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : NumberField.InfinitePlace X.B.I.F,
    ∃ (S : Finset (Fin X.B.I.n)) (c : Formalism.REAL.UJ (X.B.I.ε v)),
      (S.card = D.R.k ∧ ∀ i ∈ S, X.B.I.ε v i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ wV X u' v b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin X.B.I.n → ℂ)) '' (↑S)ᶜ)

theorem fix_iff_span {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (u : ι → Fin n → ℂ) (S : Finset (Fin n))
    (hspan : Submodule.span ℂ (Set.range u) =
      Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)) :
    (∀ b, A *ᵥ u b = u b) ↔ ∀ i ∉ S, ∀ j, A j i = if j = i then 1 else 0 := by
  classical
  have hker : ∀ x, A *ᵥ x = x ↔ x ∈ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    intro x
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have e1 : (∀ b, A *ᵥ u b = u b) ↔ Submodule.span ℂ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    rw [Submodule.span_le]
    constructor
    · rintro h _ ⟨b, rfl⟩; exact (hker _).1 (h b)
    · intro h b; exact (hker _).2 (h ⟨b, rfl⟩)
  rw [e1, hspan, Submodule.span_le]
  constructor
  · intro h i hi j
    have h1 := (hker _).2 (h ⟨i, hi, rfl⟩)
    rw [Matrix.mulVec_single_one] at h1
    have := congrFun h1 j
    simp only [Matrix.col_apply, Pi.single_apply] at this
    exact this
  · rintro h _ ⟨i, hi, rfl⟩
    refine (hker _).1 ?_
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply, Pi.single_apply]
    exact h i hi j

theorem stdConjEx_of (h1 : StabInfV) (h2 : WittBlock) : StdConjEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  have h2' := h2 X u' ψ hT μinf νinf fibInf hP
  choose S c hS hspan using h2'
  refine ⟨c, S, fun v => hS v, fun g => ?_⟩
  rw [h1 X u' hb (c * g * c⁻¹)]
  refine forall_congr' fun v => ?_
  refine Iff.trans ?_ (fix_iff_span (uMat (g v)) (fun b => uMat (c v)⁻¹ *ᵥ wV X u' v b) (S v) (hspan v))
  refine forall_congr' fun b => ?_
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * uMat (g v) * uMat (c v)⁻¹ := by
    simp [uMat]
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  have hci' : uMat (c v) * uMat (c v)⁻¹ = 1 := by simp [uMat]
  rw [hm]
  constructor
  · intro h
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) h
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [Matrix.mulVec_mulVec]
    exact h'
  · intro h
    calc (uMat (c v) * uMat (g v) * uMat (c v)⁻¹) *ᵥ wV X u' v b
        = uMat (c v) *ᵥ (uMat (g v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = uMat (c v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b) := by rw [h]
      _ = wV X u' v b := by rw [Matrix.mulVec_mulVec, hci', Matrix.one_mulVec]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix NNReal

theorem injOn_nhds_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hinj : Function.Injective f') : ∃ s ∈ 𝓝 a, InjOn f s := by
  obtain ⟨K, hK, hanti⟩ := (f' : E →ₗ[ℝ] F).injective_iff_antilipschitz.mp hinj
  have hc : (0 : ℝ≥0) < (2 * K)⁻¹ := by
    apply inv_pos.2
    exact mul_pos (by norm_num) hK
  obtain ⟨s, hs, hap⟩ := hf.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (Or.inr hc)
  refine ⟨s, hs, fun x hx y hy hxy => ?_⟩
  have h1 : ‖f x - f y - f' (x - y)‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖ := hap x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 : dist x y ≤ K * dist (f' x) (f' y) := hanti.le_mul_dist x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h2
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h3 : ‖x - y‖ ≤ ‖x - y‖ / 2 := by
    calc ‖x - y‖ ≤ K * ‖f' (x - y)‖ := h2
      _ ≤ K * (((2 * K)⁻¹ : ℝ≥0) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 hK'.le
      _ = ‖x - y‖ / 2 := by
        push_cast
        field_simp
  have : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

set_option backward.isDefEq.respectTransparency false in

theorem exp_mul_injOn {ι V : Type} [Fintype ι] [Fintype V] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)) (P : V → Matrix (Fin n) (Fin n) ℂ)
    (hker : ∀ x, (∀ v, L x v * P v = 0) → x = 0) :
    ∃ r : ℝ, 0 < r ∧ InjOn (fun x => fun v => NormedSpace.exp (L x v) * P v) (ball 0 r) := by
  open scoped Matrix.Norms.Operator in
  let Lc : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) := L.toContinuousLinearMap
  let R : V → (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    fun v => (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip (P v)
  let f' : EuclideanSpace ℝ ι →L[ℝ] (V → Matrix (Fin n) (Fin n) ℂ) :=
    ContinuousLinearMap.pi fun v => (R v).comp ((ContinuousLinearMap.proj v).comp Lc)
  have hf' : ∀ x v, f' x v = L x v * P v := fun x v => rfl
  have hd : HasStrictFDerivAt (fun x => fun v => NormedSpace.exp (L x v) * P v) f' 0 := by
    rw [hasStrictFDerivAt_pi]
    intro v
    have h0 : HasStrictFDerivAt (fun x : EuclideanSpace ℝ ι => L x v)
        ((ContinuousLinearMap.proj v).comp Lc) 0 :=
      ((ContinuousLinearMap.proj v).comp Lc).hasStrictFDerivAt
    have he : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L 0 v) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    have h2 := (R v).hasStrictFDerivAt.comp 0 (he.comp 0 h0)
    convert h2 using 1
    · funext x
      rfl
    · exact ContinuousLinearMap.ext fun x => rfl
  have hinj : Function.Injective f' := by
    intro x y hxy
    have : x - y = 0 := hker (x - y) fun v => by
      have := congrFun (congrArg (fun g => g) (show f' (x - y) = 0 by rw [map_sub, hxy, sub_self])) v
      rwa [hf'] at this
    exact sub_eq_zero.1 this
  obtain ⟨s, hs, hsi⟩ := injOn_nhds_of_strict hd hinj
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  exact ⟨r, hr, hsi.mono hrs⟩

theorem toInf_injective {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    Function.Injective (X.toInf hb) := by
  intro s t h
  have e := PI.AprimeInfU.eq_of_ofHA X hb ((s, 1) : X.B.I.GA) ((t, 1) : X.B.I.GA)
    (PI.AprimeInfU.ofHAInf_congr X _ _ h)
    (PI.AprimeInfU.ofHAFin_congr X _ _ (by rw [PI.AprimeInfU.toHA_fin_one X hb s, PI.AprimeInfU.toHA_fin_one X hb t]))
  exact congrArg Prod.fst e

def toInfHom {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) :
    X.B.I.Ginf →* HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :=
  MonoidHom.mk' (X.toInf hb) (PI.AprimeInfU.toInf_mul X hb)

theorem lie_zero_of_cols {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hL : Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0) (hB : ∀ i ∈ S, ∀ j ∈ S, M i j = 0)
    (hC : M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) = 0) : M = 0 := by
  have hcol : ∀ r s, s ∉ S → M r s = 0 := by
    intro r s hs
    have := congrFun (congrFun hC r) s
    rw [Matrix.mul_diagonal] at this
    simpa [hs] using this
  ext r s
  by_cases hs : s ∈ S
  · by_cases hr : r ∈ S
    · exact hB r hr s hs
    · have h := congrFun (congrFun hL s) r
      simp only [Formalism.REAL.Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.conjTranspose_apply, Matrix.zero_apply, hcol s r hr, mul_zero, add_zero] at h
      have hd : (if ε r = true then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have := (mul_eq_zero.1 h).resolve_right hd
      simpa using this
  · exact hcol r s hs

theorem grpInj_holds : GrpInj := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  have hc := ctx.2.1
  have hL := ctx.2.2.1
  have hB := ctx.2.2.2
  set P : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ :=
    fun v => Matrix.diagonal (fun k => if k ∈ S v then (0 : ℂ) else 1) with hP
  have hnorm : ∀ {κ' : Type} [Fintype κ'] (x : EuclideanSpace ℝ κ')
      (M : NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ),
      M = 0 → ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 = ‖x‖ ^ 2 → x = 0 := by
    intro κ' _ x M hM h
    subst hM
    simp only [Pi.zero_apply, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h.symm)
  obtain ⟨r1, hr1, hi1⟩ := exp_mul_injOn L P fun x hx => by
    refine hnorm x (L x) (funext fun v => lie_zero_of_cols (X.B.I.ε v) (S v) _ (hL.1 x v).1 (hL.1 x v).2 (hx v))
      (hL.2.1 x)
  obtain ⟨r2, hr2, hi2⟩ := exp_mul_injOn L₁ (fun _ => 1) fun x hx => by
    refine hnorm x (L₁ x) (funext fun v => by simpa using hx v) (hB.2.1 x)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun a ha b hb' hm => ?_, fun y hy y' hy' he => ?_⟩
  ·
    have e1 : (kap0 X hb c L a)⁻¹ * kap0 X hb c L b =
        X.toInf hb (c * ((fun v => expU (X.B.I.ε v) (L a v))⁻¹ * (fun v => expU (X.B.I.ε v) (L b v))) * c⁻¹) := by
      unfold kap0
      change (toInfHom X hb _)⁻¹ * toInfHom X hb _ = toInfHom X hb _
      rw [← map_inv, ← map_mul]
      congr 1
      group
    rw [e1] at hm
    have hstd := (hc.2 _).1 hm
    apply hi1 (ball_subset_ball (min_le_left _ _) ha) (ball_subset_ball (min_le_left _ _) hb')
    funext v
    have hv := hstd v
    set u := expU (X.B.I.ε v) (L a v) with hu
    set w := expU (X.B.I.ε v) (L b v) with hw
    have hcol : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v = P v := by
      ext j i
      simp only [hP, Matrix.mul_diagonal, Matrix.diagonal_apply]
      by_cases hi : i ∈ S v
      · by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji, hi]
      · have := hv i hi j
        simp only [Pi.mul_apply, Pi.inv_apply] at this
        rw [this]
        by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [hji]
    have ea : NormedSpace.exp (L a v) = (((u : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 a v).1).symm
    have eb : NormedSpace.exp (L b v) = (((w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := (expU_val _ _ (hL.1 b v).1).symm
    show NormedSpace.exp (L a v) * P v = NormedSpace.exp (L b v) * P v
    rw [ea, eb]
    set U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (u : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hU
    set W : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := (w : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) with hW
    have e4 : (((u⁻¹ * w : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) =
        ((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := rfl
    rw [e4] at hcol
    calc (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v
        = (U : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          (((U⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
            (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v) := by rw [hcol]
      _ = (W : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) * P v := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  ·
    have e2 := toInf_injective X hb he
    have e3 : ((fun v => expU (X.B.I.ε v) (L₁ y v)) : X.B.I.Ginf) = fun v => expU (X.B.I.ε v) (L₁ y' v) := by
      simpa using e2
    apply hi2 (ball_subset_ball (min_le_right _ _) hy) (ball_subset_ball (min_le_right _ _) hy')
    funext v
    have := congrArg (fun g : X.B.I.Ginf => (((g v : Formalism.REAL.UJ (X.B.I.ε v)) :
      (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) e3
    rw [expU_val _ _ (hB.1 y v).1, expU_val _ _ (hB.1 y' v).1] at this
    show NormedSpace.exp (L₁ y v) * 1 = NormedSpace.exp (L₁ y' v) * 1
    rw [this]

end PI.AprimeInfW
end
end

