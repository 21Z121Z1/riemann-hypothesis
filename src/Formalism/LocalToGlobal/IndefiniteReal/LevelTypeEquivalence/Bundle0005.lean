import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.HfinExistsMat
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ga_facts (V : HSp D) :
    IsTopologicalGroup (GA D V) ∧ T2Space (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
      SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram

theorem ae_facts : IsTopologicalRing (AE D) ∧ T2Space (AE D) ∧ LocallyCompactSpace (AE D) ∧
    SecondCountableTopology (AE D) ∧ BorelSpace (AE D) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.tens_facts (AF D.host.F) D.sp.cm.deg2

theorem gQDiscrete_holds : GQDiscrete D := fun V => G5.hfin_disc D.sp.cm.sig V.gram

theorem gQ_countable (V : HSp D) : Countable (GQ V) := G5.hfin_countable D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) := by
  obtain ⟨h1, -, -, -, h5⟩ := ga_facts D V
  infer_instance

theorem measurableMul₂_GA (V : HSp D) : MeasurableMul₂ (GA D V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  infer_instance

theorem gfC_secondCountable (V : HSp D) : SecondCountableTopology (GfC V) := by
  obtain ⟨-, -, -, h4, -⟩ := ga_facts D V
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem fundDomExists_holds : FundDomExists D := fun V => by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  have := gQDiscrete_holds D V
  exact G5.fdom_exists_all (GQ V)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GrowthNorm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infMat_eq (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) (i j : Fin V.rank) :
    infMat D.sp.cm.sig V.gram (θ τ) g i j = θ τ (infPart D (mt V g i j)) := rfl

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsParI
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsParI (T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (m : GA D T) : Prop :=
  (∃ a : Matrix (Fin r) (Fin r) (AE D),
      HMul.hMul (Formalism.L2.Theta.mt T m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a) ∧
    ∀ x : Fin T.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram).mulVec x = 0 →
      ∃ b : Fin r → AE D, (Formalism.L2.Theta.mt T m).mulVec (fun i => incA D (x i)) - (fun i => incA D (x i)) =
        (C.map (incA D)).mulVec b

def ParabM (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ m : GA D T, IsParI T C m → ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f →
          ellI S T C μ 𝓕 (om (1, m) f) = c * ellI S T C μ 𝓕 f

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Red (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellI S T C μ 𝓕 (heisO ψ S T w f)

def IsPerpA (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (w : WO S T) : Prop :=
  ∀ a : Mx D r S.rank, symplO S T (embI S T C a) w = 0

def EllIndep (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 𝓕' : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → IsAddFundamentalDomain (ratMx D r S.rank) 𝓕' μ →
      ∀ f, IsThetaFunO ψ S T f → ellI S T C μ 𝓕 f = ellI S T C μ 𝓕' f

def RedZero (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ),
    Red ψ S T C μ 𝓕 f 0 = ellI S T C μ 𝓕 f

def RedLeft (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a w,
        Red ψ S T C μ 𝓕 f (embI S T C a + w) = ψ (-(symplOH S T (embI S T C a) w)) * Red ψ S T C μ 𝓕 f w

def RedPerp (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (w₀ : WO S T), IsPerpA S T C w₀ →
    ∀ f : WO S T → ℂ, Red ψ S T C μ 𝓕 (heisO ψ S T w₀ f) = heisO ψ S T w₀ (Red ψ S T C μ 𝓕 f)

def RedTheta (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        (∀ x, IsPerpI S T C x → ∀ w,
          Red ψ S T C μ 𝓕 f (ratW T S x + w) = ψ (-(symplOH S T (ratW T S x) w)) * Red ψ S T C μ 𝓕 f w) ∧
        (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, IsPerpA S T C u →
          u.map (infPart D) = 0 → heisO ψ S T u (Red ψ S T C μ 𝓕 f) = Red ψ S T C μ 𝓕 f) ∧
        Continuous (Red ψ S T C μ 𝓕 f)

def RedInv (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ C' : Matrix (Fin T.rank) (Fin r) D.host.E,
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        Summable (fun b : Matrix (Fin r) (Fin S.rank) D.host.E =>
          ‖Red ψ S T C μ 𝓕 (heisO ψ S T (ratW T S (C' * b)) f) 0‖) ∧
        ((μ 𝓕).toReal : ℂ) * f 0 =
          ∑' b : Matrix (Fin r) (Fin S.rank) D.host.E, Red ψ S T C μ 𝓕 (heisO ψ S T (ratW T S (C' * b)) f) 0

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SymplOHSmulRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem eInf_mul_eFin : eInf D * eFin D = 0 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (mul_zero _) (zero_mul _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem eInf_add_eFin : eInf D + eFin D = 1 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (add_zero _) (zero_add _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by

  unfold cA sigR
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  · intro x y hx hy
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem hO_smul_right (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc]

theorem hO_smul_left (c : AF D.host.F) (x y : WO S T) : hO S T (c • x) y = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, mul_smul_comm, smul_mul_assoc]

theorem symplOH_smul_right (c : AF D.host.F) (x y : WO S T) : symplOH S T x (c • y) = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_right, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_smul_left (c : AF D.host.F) (x y : WO S T) : symplOH S T (c • x) y = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_left, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_snd (x y : WO S T) (hy : eInf D • y = y) : (symplOH S T x y).2 = 0 := by

  rw [← hy, symplOH_smul_right]
  simp only [eInf, pairA]
  first
  | exact zero_mul _
  | simp

theorem symplOH_fin_real (u y : WO S T) (hu : eFin D • u = u) (hy : eInf D • y = y) : symplOH S T u y = 0 := by

  rw [← hu, ← hy, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, mul_comm (eFin D) (eInf D), eInf_mul_eFin,
    zero_mul]

theorem symplOH_real_fin (y u : WO S T) (hy : eInf D • y = y) (hu : eFin D • u = u) : symplOH S T y u = 0 := by

  rw [← hy, ← hu, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, eInf_mul_eFin, zero_mul]

theorem wo_real_iff (w : WO S T) : w.map (finPart D) = 0 ↔ eInf D • w = w := by
  constructor
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem wo_fin_iff (w : WO S T) : w.map (infPart D) = 0 ↔ eFin D • w = w := by
  constructor
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem eFin_smul_sub (w : WO S T) : w - eInf D • w = eFin D • w := by

  rw [eq_sub_of_add_eq' (eInf_add_eFin (D := D)), sub_smul, one_smul]

end Formalism.IndefR.Eqv

end
end

