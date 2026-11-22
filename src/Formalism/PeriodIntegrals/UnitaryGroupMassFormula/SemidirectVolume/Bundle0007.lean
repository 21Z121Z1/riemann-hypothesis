import Mathlib
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModVec

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ConjInvOfExists
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def ModOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∃ μ : Measure (FrameUnipotentSubgroup (AF F) σ J P), μ.IsHaarMeasure ∧
      ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
        ∫⁻ n, f (h * (n : HA (AF F) σ J) * h⁻¹) ∂μ = ∫⁻ n, f (n : HA (AF F) σ J) ∂μ

theorem conjInv_of_exists {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

theorem conjStep_of (hM : ModOne) : ConjStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  have hX := Lc.locally_compact_adelic_unitary F E σ hCM M J hJ
  obtain ⟨-, cN, -⟩ := closed_subgroup_holds F E σ hCM M J hJ r P T hr hP
  obtain ⟨hcnt, hdisc⟩ := discrete_adelic_unitary F E σ hCM M J hJ
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (AF F) σ J) (HFinIn (AF F) σ J) _ hX cN
    hcnt hdisc
  exact conjInv_of_exists _ _ lN (hM F E σ hCM M J hJ r P T hr hP)

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianDatumFormEq
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def dat0 : PG.Dat (A ⊗[F] E) (Fin M) 0 where
  σA := sigR A σ
  JA := JR A J
  e := Fin.elim0
  f := Fin.elim0
  z := 0
  tz := 0

def Bf (u v : Fin M → A ⊗[F] E) : A := Algebra.trace A (A ⊗[F] E) (hR A σ J u v)

theorem sigR_algebraMap (c : A) :
    sigR A σ (algebraMap A (A ⊗[F] E) c) = algebraMap A (A ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem trace_algebraMap_mul (c : A) (y : A ⊗[F] E) :
    Algebra.trace A (A ⊗[F] E) (algebraMap A (A ⊗[F] E) c * y) =
      c * Algebra.trace A (A ⊗[F] E) y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem Bf_smul_left (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J (c • u) v = c * Bf σ J u v := by
  have h : hR A σ J (c • u) v = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_smul_right (c : A) (u v : Fin M → A ⊗[F] E) : Bf σ J u (c • v) = c * Bf σ J u v := by
  have h : hR A σ J u (c • v) = algebraMap A (A ⊗[F] E) c * hR A σ J u v := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold Bf
  rw [h, trace_algebraMap_mul]

theorem Bf_sum_left {k : ℕ} (x : Fin k → Fin M → A ⊗[F] E) (v : Fin M → A ⊗[F] E) :
    Bf σ J (∑ a, x a) v = ∑ a, Bf σ J (x a) v := by
  have h : hR A σ J (∑ a, x a) v = ∑ a, hR A σ J (x a) v := by
    simp only [hR, Formalism.UG.hform, Finset.sum_apply, _root_.map_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf
  rw [h, _root_.map_sum]

theorem Bf_sum_right {k : ℕ} (u : Fin M → A ⊗[F] E) (y : Fin k → Fin M → A ⊗[F] E) :
    Bf σ J u (∑ a, y a) = ∑ a, Bf σ J u (y a) := by
  have h : hR A σ J u (∑ a, y a) = ∑ a, hR A σ J u (y a) := by
    simp only [hR, Formalism.UG.hform, Finset.sum_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  unfold Bf
  rw [h, _root_.map_sum]

theorem Bf_expand {k : ℕ} (b : Fin k → Fin M → A ⊗[F] E) (x y : Fin k → A) :
    Bf σ J (∑ a, x a • b a) (∑ c, y c • b c) = ∑ a, ∑ c, x a * (Bf σ J (b a) (b c) * y c) := by
  rw [Bf_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Bf_smul_right]
  ring

theorem Bf_lin (g : HA A σ J) (u v : Fin M → A ⊗[F] E) :
    Bf σ J (lin A σ J g u) (lin A σ J g v) = Bf σ J u v := by
  have hf : ∀ x y : Fin M → A ⊗[F] E, hR A σ J x y =
      dotProduct (Matrix.vecMul (fun i => sigR A σ (x i)) (JR A J)) y := by
    intro x y
    simp only [hR, Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    exact Finset.sum_comm
  have hs : ∀ (P : Matrix (Fin M) (Fin M) (A ⊗[F] E)) (x : Fin M → A ⊗[F] E),
      (fun i => sigR A σ (P.mulVec x i)) =
        Matrix.vecMul (fun i => sigR A σ (x i)) (Formalism.UG.cT (sigR A σ) P) := by
    intro P x
    funext j
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, _root_.map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hg : (HA.mat A σ J g) ∈ HR A σ J := (show ↥(HR A σ J) from g).2
  have hg' : Formalism.UG.cT (sigR A σ) ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) * JR A J *
      ((HA.mat A σ J g : GL (Fin M) (A ⊗[F] E)) : Matrix _ _ _) = JR A J := hg
  unfold Bf lin
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hf, hf, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']

end Alg

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop
section
noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def sigRLin : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) σ.toLinearMap

theorem sigRLin_eq (x : R ⊗[F] E) : sigRLin R σ x = sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigRLin, sigR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_sigR : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (sigRLin R σ) := IsModuleTopology.continuous_of_linearMap _
  have he : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = sigRLin R σ :=
    funext fun x => (sigRLin_eq R σ x).symm
  rw [he]
  exact hc

theorem continuous_hR {X : Type} [TopologicalSpace X] {u v : X → Fin M → R ⊗[F] E}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => hR R σ J (u x) (v x) := by
  unfold hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_sigR R σ).comp ((continuous_apply i).comp hu)).mul continuous_const).mul
    ((continuous_apply j).comp hv)

theorem continuous_linMap {X : Type} [TopologicalSpace X]
    (f : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E)) {v : X → Fin M → R ⊗[F] E}
    (hv : Continuous v) : Continuous fun x => f (v x) := by
  have key : (fun x => f (v x)) =
      fun x => ∑ j, v x j • f (fun k => if j = k then (1 : R ⊗[F] E) else 0) := by
    funext x
    conv_lhs => rw [pi_eq_sum_univ (v x)]
    rw [map_sum]
    simp only [map_smul]
  rw [key]
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp hv).smul continuous_const

theorem continuous_linear_action {X : Type} [TopologicalSpace X] {g : X → HA R σ J}
    {v : X → Fin M → R ⊗[F] E} (hg : Continuous g) (hv : Continuous v) :
    Continuous fun x => lin R σ J (g x) (v x) := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  unfold lin
  simp only [Matrix.mulVecLin_apply]
  exact (hm.comp hg).matrix_mulVec hv

theorem continuous_L_apply {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => (datR R σ J P T).L (w x) (s x) v := by
  set D := datR R σ J P T with hD
  have key : (fun x => D.L (w x) (s x) v) = fun x =>
      v + ∑ b, D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) - ∑ a, D.hL (w x a) (D.pW v) • D.e a := by
    funext x
    simp only [PI.VolSemiDirect.W.PG.Dat.L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
  rw [key]
  have hh : ∀ (c : Fin M → R ⊗[F] E), Continuous fun u : Fin M → R ⊗[F] E => D.hL u c := by
    intro c
    first
      | exact continuous_hR R σ J (u := fun u => u) (v := fun _ => c) continuous_id continuous_const
      | exact continuous_hR R σ J (u := fun _ => c) (v := fun u => u) continuous_const continuous_id
  have hA : ∀ b : Fin r, Continuous fun x => w x b + ∑ a, s x a b • D.e a := by
    intro b
    have h1 : Continuous fun x => w x b := (continuous_apply b).comp hw
    have h2 : ∀ a : Fin r, Continuous fun x => s x a b • D.e a := by
      intro a
      have h3 : Continuous fun x => s x a b := (continuous_apply b).comp ((continuous_apply a).comp hs)
      exact h3.smul continuous_const
    exact h1.add (continuous_finset_sum _ fun a _ => h2 a)
  have hB : ∀ b : Fin r, Continuous fun x => D.hL (D.e b) v • (w x b + ∑ a, s x a b • D.e a) := by
    intro b
    exact (continuous_const (y := D.hL (D.e b) v)).smul (hA b)
  have hC : ∀ a : Fin r, Continuous fun x => D.hL (w x a) (D.pW v) • D.e a := by
    intro a
    have h4 : Continuous fun x => D.hL (w x a) (D.pW v) := (hh (D.pW v)).comp ((continuous_apply a).comp hw)
    exact h4.smul continuous_const
  exact (continuous_const.add (continuous_finset_sum _ fun b _ => hB b)).sub
    (continuous_finset_sum _ fun a _ => hC a)

theorem continuous_toMatrix'_L {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) :
    Continuous fun x => LinearMap.toMatrix' ((datR R σ J P T).L (w x) (s x)) := by
  refine continuous_matrix fun i j => ?_
  first
    | exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _)
    | (simp only [LinearMap.toMatrix'_apply]
       exact (continuous_apply i).comp (continuous_L_apply R σ J P T hw hs _))

end Cont

section HAcont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem mat_inv_eq (hJ : IsHermND σ J) (g : HA R σ J) :
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J⁻¹).map (inclR (F := F) R) *
        Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J := by
  obtain ⟨_, hdet⟩ := hJ
  set A : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hA
  set B : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) with hB
  set Ji : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (J⁻¹).map (inclR (F := F) R) with hJi
  have hmem : Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A = JR (F := F) R J := g.2
  have hAB : A * B = 1 := by
    have e : (HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) = (HA.mat R σ J g)⁻¹ := by
      first
        | rfl
        | exact Subgroup.coe_inv _
    rw [hA, hB, e]
    exact Units.mul_inv _
  have hJJ : Ji * JR (F := F) R J = 1 := by
    rw [hJi]
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hdet)]
    simp
  calc B = (Ji * JR (F := F) R J) * B := by rw [hJJ, Matrix.one_mul]
    _ = Ji * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * A) * B := by rw [hmem]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J * (A * B) := by simp only [Matrix.mul_assoc]
    _ = Ji * Formalism.UG.cT (sigR R σ) A * JR (F := F) R J := by rw [hAB, Matrix.mul_one]

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]

theorem continuous_into_HA (hJ : IsHermND σ J) {X : Type} [TopologicalSpace X] {f : X → HA R σ J}
    (hf : Continuous fun x => ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E))) : Continuous f := by
  have hcT : Continuous fun x => Formalism.UG.cT (sigR R σ)
      ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_sigR R σ).comp (hf.matrix_elem j i)
  have hI : Continuous fun x =>
      ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    have e : (fun x =>
        ((HA.mat R σ J (f x)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) =
        fun x => (J⁻¹).map (inclR (F := F) R) *
          Formalism.UG.cT (sigR R σ) ((HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :
            Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J :=
      funext fun x => mat_inv_eq hJ (f x)
    rw [e]
    exact (continuous_const.matrix_mul hcT).matrix_mul continuous_const
  have hGL : Continuous fun x => (HA.mat R σ J (f x) : GL (Fin M) (R ⊗[F] E)) :=
    Units.continuous_iff.2 ⟨hf, hI⟩
  first
    | exact continuous_induced_rng.2 hGL
    | exact hGL.subtype_mk fun x => (f x).2

end HAcont

section Raw

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_phiW_raw :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun b : Fin r =>
      (datR R σ J P T).pW (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun b => ?_
  exact continuous_linMap R _
    (continuous_linear_action R σ J (v := fun _ => ratV (F := F) R (P.f b)) continuous_subtype_val continuous_const)

theorem continuous_phiS_raw :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun a b : Fin r =>
      hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact continuous_hR R σ J (u := fun _ => ratV (F := F) R (P.f a))
    (v := fun n : FrameUnipotentSubgroup R σ J P => lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) continuous_const
    (continuous_linear_action R σ J continuous_subtype_val continuous_const)

theorem continuous_gram_shift {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b - κ * hR R σ J (w x a) (w x b) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).sub
    (continuous_const.mul (continuous_hR R σ J ((continuous_apply a).comp hw) ((continuous_apply b).comp hw)))

theorem continuous_gram_add {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b + κ * hR R σ J (w x a) (w x b) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).add
    (continuous_const.mul (continuous_hR R σ J ((continuous_apply a).comp hw) ((continuous_apply b).comp hw)))

end Raw

end PI.VolSemiDirect.W.Md
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjContAll
section
namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

theorem representation_continuous : PiCont := by
  intro F E _ _ _ _ _ σ M J r P T hσσ hJ hP
  have := (Lc.tensor_adele_topology_holds F E).1
  exact continuous_piG hσσ hJ hP

end PI.VolSemiDirect.W
end

