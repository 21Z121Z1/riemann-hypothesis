import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayValId
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0002

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExEnd
section
namespace PI.AprimeInfW

theorem expProdU_holds : ExpProdU := expProdU_of_hua cayDensEx_holds cayValId_holds

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfWitt
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def WittLin : Prop := ∀ {n m k : ℕ}, n = m + k → ∀ (ε : Fin n → Bool) (w : Fin m → Fin n → ℂ),
    LinearIndependent ℂ w →
    (∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, star (w b) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ z)).re) →
    ∃ (S : Finset (Fin n)) (c : Formalism.REAL.UJ ε), (S.card = k ∧ ∀ i ∈ S, ε i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ w b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)

def DimNK : Prop := ∀ {D : D7} (X : HidaSetting D), X.B.I.n = (D.R.rS + 1 + D.R.rS) + D.R.k

def LinIndW : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, LinearIndependent ℂ (wV X u' v)

def PerpPosV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : InfinitePlace X.B.I.F, ∀ z : Fin X.B.I.n → ℂ, z ≠ 0 →
      (∀ b, star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z) = 0) →
      0 < (star z ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)).re

theorem dimNK_holds : DimNK := by
  intro D X
  rw [X.n_eq]
  have h1 := D.R.rS_two
  have h2 := D.R.r_eq
  omega

theorem gram_wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (b b' : Fin (D.R.rS + 1 + D.R.rS)) :
    star (wV X u' v b) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ wV X u' v b') =
      X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) b b') := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hJ : ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
    rw [← X.B.I.P_spec v]
    have e1 : ((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, Matrix.conjTranspose_one]
    calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
        = (((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ) * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X.B.I.J.map (X.B.I.φ v) := by
          rw [e1, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
  unfold wV
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hJ]
  have hσφ : ∀ a, X.B.I.φ v (X.B.I.cm.sig a) = star (X.B.I.φ v a) := fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, gramE, hE, Formalism.UG.hform, map_sum, map_mul, Pi.star_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) (tupH (frameOf X u') b i) = X.B.I.cm.sig (tupH (frameOf X u') b i) from rfl,
    hσφ]
  ring

theorem linIndW_holds : LinIndW := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  set G : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (X.B.I.φ v) with hG
  have hGd : G.det ≠ 0 := by
    have e : G.det = X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det :=
      (RingHom.map_det (X.B.I.φ v) _).symm
    rw [e]
    exact (map_ne_zero _).2 hd
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hGg : G *ᵥ g = 0 := by
    funext b'
    have h0 := congrArg (fun z => star (wV X u' v b') ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ z)) hg
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul,
      Matrix.mulVec_zero, dotProduct_zero] at h0
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gram_wV]
    simp only [hG, Matrix.map_apply]
    ring
  exact fun b => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGd hGg) b

theorem wittBlock_of (h0 : DimNK) (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) : WittBlock := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  exact h3 (h0 X) (X.B.I.ε v) (wV X u' v) (h1 X u' ψ hT μinf νinf fibInf hP v)
    (h2 X u' ψ hT μinf νinf fibInf hP v)

theorem goodChartEx_of_witt (h1 : LinIndW) (h2 : PerpPosV) (h3 : WittLin) (hG : GrpStd) (hT : TupStd) :
    GoodChartEx :=
  goodChartEx_of_std (stdDataEx_of (stdConjEx_of_witt (wittBlock_of dimNK_holds h1 h2 h3))) hG hT

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem no_kernel {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (χ : W → W → ℂ) (hμ : SelfDual μ χ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hT : ST.TestExP μ χ) (t : W) (ht0 : t ≠ 0)
    (ht : ∀ y, χ t y = 1) : False := by
  haveI := hμ.1
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := hT

  have htr : ∀ y, ∫ x, Φ (x - t) * χ x y ∂μ = ∫ x, Φ x * χ x y ∂μ := by
    intro y
    have := integral_sub_right_eq_self (μ := μ) (fun x => Φ x * χ (x + t) y) t
    simp only [sub_add_cancel] at this
    rw [this]
    congr 1; funext x
    rw [hadd, ht, mul_one]
  have hc' : Continuous fun x => Φ (x - t) := hc.comp (continuous_id.sub continuous_const)
  have hs' : HasCompactSupport fun x => Φ (x - t) := hs.comp_homeomorph (Homeomorph.subRight t)
  have hper : ∀ w, Φ (w - t) = Φ w := by
    intro w
    have h1 := hμ.2 (fun x => Φ (x - t)) hc' hs' (by simp only [htr]; exact hI) (-w)
    have h2 := hμ.2 Φ hc hs hI (-w)
    simp only [htr, neg_neg] at h1 h2
    rw [← h1, h2]
  have hpern : ∀ n : ℕ, ∀ w, Φ (w - n • t) = Φ w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [succ_nsmul, ← sub_sub, hper, ih]
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  apply hz
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖-z‖) / ‖t‖)
  rw [← hpern n (-z)]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have h1 : ‖(n : ℝ) • t‖ ≤ ‖-z - n • t‖ + ‖-z‖ := by
    have := norm_sub_le (-z) (-z - n • t)
    simp only [sub_sub_cancel] at this
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this ⊢
    linarith [norm_sub_rev (-z) (-z - (n : ℝ) • t)]
  rw [norm_smul, Real.norm_natCast] at h1
  have h2 : (R + ‖-z‖) < n * ‖t‖ := by rwa [div_lt_iff₀ htpos] at hn
  linarith

open Classical in

def MatNDH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (matI X).det ≠ 0

theorem matNDH_holds : MatNDH := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP hdet0
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  let t : EuclideanSpace ℝ (KapI X) := (EuclideanSpace.equiv (KapI X) ℝ).symm v
  have ht0 : t ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (EuclideanSpace.equiv (KapI X) ℝ) h
    simpa [t] using this
  have hAt : Alin X t = 0 := by
    simp [Alin, t, Matrix.toLin'_apply]
    exact hv
  have hβ : ∀ y, betaI X t y = 0 := by
    intro y
    rw [betaSym_holds, ← inner_Alin, hAt, inner_zero_right]
  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  haveI := hμ'.1
  have hadd : ∀ x x' y : EuclideanSpace ℝ (KapI X), (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) (x + x') y = (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x y * (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x' y := by
    intro x x' y
    simp only [tupCoord_symm_add, BR_add_leftP, psiInf_addP]
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) :=
    { addL := hadd
      addR := fun x y y' => by simp only [tupCoord_symm_add, BR_add_rightP, psiInf_addP]
      norm1 := fun x y => norm_psiInfP ψ hS _
      contL := fun y => hpc.comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)
      contR := fun x => hpc.comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous) }
  have hTest := ST.testEx_bichar (μinf.map (tupCoord X)) hB
  refine no_kernel (μinf.map (tupCoord X)) _ hμ' hadd hTest t ht0 fun y => ?_
  rw [psiInf_eq ψ hS]
  beta_reduce
  have : (∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
      (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm t) ((tupCoord X).symm y) w)).re) = 0 := hβ y
  simp only [this]
  simp

open Classical in
theorem densMu_holds : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by
    rw [det_Alin]; exact isUnit_iff_ne_zero.2 (matNDH_holds X u' ψ hT μinf νinf fibInf hP)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, betaSym_holds]
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

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceCh
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def InCompl {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, M i j = 0

def InBlock {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 ∧ ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0

def frob {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

def PlaceChartV : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)), (∀ i ∈ S, ε i = true) →
    Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∃ (α β : Type) (_ : Fintype α) (_ : Fintype β)
      (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (P₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ α)
      (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ β)
      (r : ℝ) (D : EuclideanSpace ℝ α × EuclideanSpace ℝ β → ℝ),
      (∀ z, P₀ (L₀ z) = z) ∧ (∀ M, InCompl ε S M → L₀ (P₀ M) = M) ∧ (∀ z, InCompl ε S (L₀ z)) ∧
      (∀ z, frob (L₀ z) = ‖z‖ ^ 2) ∧
      (∀ z, P₁ (L₁ z) = z) ∧ (∀ M, InBlock ε S M → L₁ (P₁ M) = M) ∧ (∀ z, InBlock ε S (L₁ z)) ∧
      (∀ z, frob (L₁ z) = ‖z‖ ^ 2) ∧
      0 < r ∧ ContinuousAt D 0 ∧ D 0 = Formalism.MainNotions.S.Gauge.gaugeU ε ∧ Measurable D ∧ (∀ z, 0 ≤ D z) ∧
      Continuous (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β => expU ε (L₀ z.1) * expU ε (L₁ z.2)) ∧
      Set.InjOn (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β => expU ε (L₀ z.1) * expU ε (L₁ z.2)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ α × EuclideanSpace ℝ β) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β => expU ε (L₀ z.1) * expU ε (L₁ z.2)) '' A) =
          ∫⁻ z in A, ENNReal.ofReal (D z)

theorem coord_facts {ι V : Type} [Fintype ι] [Fintype V] {n : ℕ} {α : V → Type} [∀ v, Fintype (α v)]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ)) (Q : V → Matrix (Fin n) (Fin n) ℂ → Prop)
    (L₀ : ∀ v, EuclideanSpace ℝ (α v) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (P₀ : ∀ v, Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (α v))
    (h1 : ∀ v z, P₀ v (L₀ v z) = z) (h2 : ∀ v M, Q v M → L₀ v (P₀ v M) = M) (h3 : ∀ v z, Q v (L₀ v z))
    (h4 : ∀ v z, frob (L₀ v z) = ‖z‖ ^ 2) (hLQ : ∀ x v, Q v (L x v))
    (hLn : ∀ x, ∑ v, frob (L x v) = ‖x‖ ^ 2) (hLs : ∀ M : V → Matrix (Fin n) (Fin n) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    let Tx : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v)) :=
      LinearMap.pi fun v => (P₀ v).comp ((LinearMap.proj v).comp L)
    Function.Bijective Tx ∧ (∀ x, ∑ v, ‖Tx x v‖ ^ 2 = ‖x‖ ^ 2) := by
  intro Tx
  have hTx : ∀ x v, Tx x v = P₀ v (L x v) := fun x v => rfl
  have hn : ∀ x, ∑ v, ‖Tx x v‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← hLn x]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hTx, ← h4 v, h2 v _ (hLQ x v)]
  refine ⟨⟨fun x y hxy => ?_, fun z => ?_⟩, hn⟩
  · have h0 : Tx (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hn (x - y)
    rw [h0] at this
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at this
    have h00 : ‖x - y‖ = 0 := by
      have := this.symm
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact sub_eq_zero.1 (norm_eq_zero.1 h00)
  · obtain ⟨x, hx⟩ := hLs (fun v => L₀ v (z v)) fun v => h3 v (z v)
    refine ⟨x, funext fun v => ?_⟩
    rw [hTx, hx, h1]

theorem placeCharts_of (h : PlaceChartV) : PlaceCharts := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  obtain ⟨⟨ψ, hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩ := ctx
  have hSε : ∀ v, ∀ i ∈ S v, X.B.I.ε v i = true := fun v => (hc.1 v).2
  have hgd : ∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := hP.2.2.2.1
  choose α β hα hβ L0 P0 L1 P1 r Dv h1 h2 h3 h4 h5 h6 h7 h8 hr hDc hD0 hDm hDnn hΦc hΦi hdens using
    fun v => h X.B.I.n (X.B.I.ε v) (S v) (hSε v) (hgd v)
  letI : ∀ v, Fintype (α v) := hα
  letI : ∀ v, Fintype (β v) := hβ
  obtain ⟨hTxb, hTxn⟩ := coord_facts L (fun v M => InCompl (X.B.I.ε v) (S v) M) L0 P0 h1 h2 h3 h4
    (fun x v => hL.1 x v) (fun x => hL.2.1 x) (fun M hM => hL.2.2 M hM)
  obtain ⟨hTyb, hTyn⟩ := coord_facts L₁ (fun v M => InBlock (X.B.I.ε v) (S v) M) L1 P1 h5 h6 h7 h8
    (fun x v => hB.1 x v) (fun x => hB.2.1 x) (fun M hM => hB.2.2 M hM)
  set Tx : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v)) :=
    LinearMap.pi fun v => (P0 v).comp ((LinearMap.proj v).comp L) with hTxd
  set Ty : EuclideanSpace ℝ η →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (β v)) :=
    LinearMap.pi fun v => (P1 v).comp ((LinearMap.proj v).comp L₁) with hTyd
  have hTxm := PI.AprimeInfG.measurePreserving_of_normSq Tx hTxb hTxn
  have hTym := PI.AprimeInfG.measurePreserving_of_normSq Ty hTyb hTyn
  let Txe : EuclideanSpace ℝ ι ≃ᵐ (∀ v, EuclideanSpace ℝ (α v)) :=
    (LinearEquiv.ofBijective Tx hTxb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let Tye : EuclideanSpace ℝ η ≃ᵐ (∀ v, EuclideanSpace ℝ (β v)) :=
    (LinearEquiv.ofBijective Ty hTyb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ (∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)) :=
    (Txe.prodCongr Tye).trans
      (PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (α v)) (fun v => EuclideanSpace ℝ (β v))).symm
  have hTfun : ∀ p, T p = fun v => (Tx p.1 v, Ty p.2 v) := fun p => rfl
  have hTmp : MeasurePreserving T volume (Measure.pi fun _ => volume) := by
    have hprod := hTxm.prod hTym
    have hpe := (PI.AprimeInfG.measurePreserving_piProdEquiv (fun v => EuclideanSpace ℝ (α v))
      (fun v => EuclideanSpace ℝ (β v)) (fun _ => volume) (fun _ => volume)).symm
    exact hpe.comp hprod
  have hTc : Continuous T := by
    rw [show (T : _ → _) = fun p => fun v => (Tx p.1 v, Ty p.2 v) from funext hTfun]
    exact continuous_pi fun v =>
      ((continuous_apply v).comp (Tx.continuous_of_finiteDimensional.comp continuous_fst)).prodMk
        ((continuous_apply v).comp (Ty.continuous_of_finiteDimensional.comp continuous_snd))
  have hT0 : T 0 = 0 := by
    rw [hTfun]
    funext v
    simp
  set rr := (insert 1 (Finset.univ.image r)).min' ⟨1, Finset.mem_insert_self _ _⟩ with hrr
  have hrr0 : 0 < rr := by
    have hm := Finset.min'_mem (insert 1 (Finset.univ.image r)) ⟨1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hm with e | e
    · rw [hrr, e]; norm_num
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 e
      rw [hrr, ← hv]; exact hr v
  have hrrv : ∀ v, rr ≤ r v := fun v =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ v)))
  have hle : ∀ {γ : NumberField.InfinitePlace X.B.I.F → Type} [∀ v, Fintype (γ v)] {κ' : Type} [Fintype κ']
      (M : EuclideanSpace ℝ κ' →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (γ v))),
      (∀ x, ∑ v, ‖M x v‖ ^ 2 = ‖x‖ ^ 2) → ∀ x v, ‖M x v‖ ≤ ‖x‖ := by
    intro γ _ κ' _ M hM x v
    have : ‖M x v‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← hM x]
      exact Finset.single_le_sum (f := fun v => ‖M x v‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ v)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  refine ⟨α, β, hα, hβ, fun v z => expU (X.B.I.ε v) (L0 v z.1) * expU (X.B.I.ε v) (L1 v z.2), Dv,
    fun v => ball 0 (r v), T, rr, fun v => measurableSet_ball, hΦc, hΦi, hDm, hDnn, hdens, hTmp, hTc, hrr0,
    ?_, ?_, ?_, ?_⟩
  · intro p hp v _
    rw [hTfun]
    show (Tx p.1 v, Ty p.2 v) ∈ ball (0 : EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)) (r v)
    rw [mem_ball_zero_iff, Prod.norm_def]
    have hp' : ‖p‖ < rr := mem_ball_zero_iff.1 hp
    rw [Prod.norm_def] at hp'
    refine max_lt ?_ ?_
    · exact ((hle Tx hTxn p.1 v).trans_lt ((le_max_left _ _).trans_lt hp')).trans_le (hrrv v)
    · exact ((hle Ty hTyn p.2 v).trans_lt ((le_max_right _ _).trans_lt hp')).trans_le (hrrv v)
  · intro p _
    funext v
    rw [hTfun]
    show expU (X.B.I.ε v) (L p.1 v) * expU (X.B.I.ε v) (L₁ p.2 v) =
      expU (X.B.I.ε v) (L0 v (P0 v (L p.1 v))) * expU (X.B.I.ε v) (L1 v (P1 v (L₁ p.2 v)))
    rw [h2 v _ (hL.1 p.1 v), h6 v _ (hB.1 p.2 v)]
  · rw [hT0]
    refine tendsto_finsetProd _ fun v _ => ?_
    have hv : ContinuousAt (fun z : (∀ w, EuclideanSpace ℝ (α w) × EuclideanSpace ℝ (β w)) => z v) 0 :=
      (continuous_apply v).continuousAt
    have hd : ContinuousAt (Dv v) ((0 : ∀ w, EuclideanSpace ℝ (α w) × EuclideanSpace ℝ (β w)) v) := hDc v
    have hdv := ContinuousAt.comp (f := fun z : (∀ w, EuclideanSpace ℝ (α w) × EuclideanSpace ℝ (β w)) => z v) hd hv
    exact hdv
  · rw [hT0]
    simp only [Pi.zero_apply]
    rw [Finset.prod_congr rfl fun v _ => hD0 v]
    rfl

end PI.AprimeInfW
end
end

