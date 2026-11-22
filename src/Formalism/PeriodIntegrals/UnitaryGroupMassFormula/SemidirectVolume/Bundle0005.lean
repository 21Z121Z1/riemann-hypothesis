import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeQuotientHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianIsotropicProjComplement

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
section
namespace PI.VolSemiDirect.W.Lc

theorem tensor_adele_topology_holds : TensTop := tensTop_of PI.VolStabSW.TopoAF.afTop_holds

theorem locally_compact_adelic_unitary : LcscHA := lcscHA_of tensor_adele_topology_holds

end PI.VolSemiDirect.W.Lc
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.MapPhiOfModM
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def phi (X : GL (Fin k) A) : (Fin k → A) ≃ₜ+ (Fin k → A) where
  toFun v := (X : Matrix (Fin k) (Fin k) A).mulVec v
  invFun v := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem phi_apply (X : GL (Fin k) A) (v : Fin k → A) :
    phi X v = (X : Matrix (Fin k) (Fin k) A).mulVec v := rfl

def modM (X : GL (Fin k) A) : ℝ≥0 := addEquivAddHaarChar (phi X)

theorem phi_mul (X Y : GL (Fin k) A) : phi (X * Y) = (phi Y).trans (phi X) := by
  apply ContinuousAddEquiv.ext
  intro v
  simp only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem modM_mul (X Y : GL (Fin k) A) : modM (X * Y) = modM X * modM Y := by
  simp only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]

theorem modM_one : modM (1 : GL (Fin k) A) = 1 := by
  have h : phi (1 : GL (Fin k) A) = ContinuousAddEquiv.refl _ := by
    apply ContinuousAddEquiv.ext
    intro v
    simp [phi_apply]
  simp only [modM, h, addEquivAddHaarChar_refl]

theorem modM_inv (X : GL (Fin k) A) : modM X⁻¹ = (modM X)⁻¹ := by
  have h : modM X⁻¹ * modM X = 1 := by rw [← modM_mul, inv_mul_cancel, modM_one]
  exact eq_inv_of_mul_eq_one_left h

theorem map_phi_of_modM (X : GL (Fin k) A) (hX : modM X = 1) (μ : Measure (Fin k → A))
    [μ.IsAddHaarMeasure] : μ.map (phi X) = μ := by
  have h := addEquivAddHaarChar_smul_map μ (phi X)
  rwa [show addEquivAddHaarChar (phi X) = modM X from rfl, hX, one_smul] at h

theorem modM_of_map (X : GL (Fin k) A) (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure]
    (h : μ.map (phi X) = μ) : modM X = 1 := by
  have h1 := addEquivAddHaarChar_smul_map μ (phi X)
  rw [h] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : Fin k → A)
  have hpos : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hKn).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure (Fin k → A) => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modM X : ℝ≥0) : ENNReal) = 1 := by
    have h4 : (modM X : ENNReal) * μ K / μ K = 1 * μ K / μ K := by rw [one_mul]; exact congrArg (· / μ K) h2
    rwa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.mul_div_cancel_right hpos hfin] at h4
  exact_mod_cast h3

end Gen

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProdHaar
section
noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

theorem product_haar_measure_holds : ProdHaarG := by
  intro X _ _ _ _ K N H hS hK hN hH hC μN hμN μH hμH
  obtain ⟨hnorm, e, he⟩ := hS
  obtain ⟨_, _, _, _⟩ := hK
  obtain ⟨_, _, _, _⟩ := hN
  obtain ⟨_, _, _, _⟩ := hH
  have hem : Measurable e := e.continuous.measurable
  have hPF : ProdF K N H ((μN.prod μH).map e) μN μH := by
    intro f hf
    have h1 : Measurable (fun k : K => f (k : X)) := hf.comp measurable_subtype_coe
    rw [lintegral_map h1 hem, lintegral_prod (fun p => f ((e p : K) : X)) (h1.comp hem).aemeasurable]
    simp only [he]
  refine ⟨(μN.prod μH).map e, ?_, hPF⟩
  have hLI : (Measure.map e (μN.prod μH)).IsMulLeftInvariant := by
    constructor
    intro k
    set p0 := e.symm k with hp0
    have hk : (k : X) = (p0.1 : X) * (p0.2 : X) := by
      rw [← he, hp0, Homeomorph.apply_symm_apply]
    let T : N × H → N × H := fun p => e.symm (k * e p)
    have hTc : Continuous T := e.symm.continuous.comp (continuous_const.mul e.continuous)
    have hTm : Measurable T := hTc.measurable
    let A : N → N := fun m => ⟨(p0.1 : X) * ((p0.2 : X) * (m : X) * (p0.2 : X)⁻¹),
      N.mul_mem p0.1.2 (hnorm _ p0.2.2 _ m.2)⟩
    let C : N → N := fun m => ⟨(p0.2 : X) * (m : X) * (p0.2 : X)⁻¹, hnorm _ p0.2.2 _ m.2⟩
    have hT : ∀ p : N × H, T p = (A p.1, p0.2 * p.2) := by
      intro p
      apply e.injective
      simp only [T, Homeomorph.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_mul, he, he, hk]
      simp only [A, Subgroup.coe_mul]
      group
    have hTAB : T = Prod.map A (fun h => p0.2 * h) := funext fun p => hT p
    have hAm : Measurable A := by
      have hA1 : A = fun m => (T (m, 1)).1 := funext fun m => by rw [hT]
      rw [hA1]
      first
        | exact (continuous_fst.comp (hTc.comp (continuous_id.prodMk continuous_const))).measurable
        | exact (continuous_fst.comp (hTc.comp (continuous_id.prod_mk continuous_const))).measurable
    have hCA : C = fun m => p0.1⁻¹ * A m := funext fun m => Subtype.ext (by
      simp only [A, C, Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    have hCm : Measurable C := by
      rw [hCA]
      exact (measurable_const_mul _).comp hAm
    have hCinv : Measure.map C μN = μN := by
      ext S hS
      rw [Measure.map_apply hCm hS]
      obtain ⟨B, hB, rfl⟩ := hS
      have key := hC μN hμN (p0.2 : X) p0.2.2 (B.indicator 1) (measurable_one.indicator hB)
      have e1 : ∫⁻ n, B.indicator 1 ((p0.2 : X) * (n : X) * (p0.2 : X)⁻¹) ∂μN =
          μN (C ⁻¹' (Subtype.val ⁻¹' B)) := by
        rw [← lintegral_indicator_one (hCm (measurable_subtype_coe hB))]
        first
          | rfl
          | (congr 1; funext n; simp [Set.indicator_apply, C])
      have e2 : ∫⁻ n, B.indicator 1 (n : X) ∂μN = μN (Subtype.val ⁻¹' B) := by
        rw [← lintegral_indicator_one (measurable_subtype_coe hB)]
        first
          | rfl
          | (congr 1; funext n; simp [Set.indicator_apply])
      rw [← e1, key, e2]
    have hA : Measure.map A μN = μN := by
      have hAC : A = (fun m => p0.1 * m) ∘ C :=
        funext fun m => Subtype.ext (by simp only [A, C, Function.comp_apply, Subgroup.coe_mul])
      rw [hAC, ← Measure.map_map (measurable_const_mul _) hCm, hCinv, map_mul_left_eq_self]
    have hB : Measure.map (fun h : H => p0.2 * h) μH = μH := map_mul_left_eq_self μH p0.2
    calc Measure.map (k * ·) (Measure.map e (μN.prod μH))
        = Measure.map ((k * ·) ∘ e) (μN.prod μH) := by
          rw [Measure.map_map (measurable_const_mul k) hem]
      _ = Measure.map (e ∘ T) (μN.prod μH) := by
          congr 1
          funext p
          simp [T]
      _ = Measure.map e (Measure.map T (μN.prod μH)) := by rw [Measure.map_map hem hTm]
      _ = Measure.map e (μN.prod μH) := by
          rw [hTAB, ← Measure.map_prod_map _ _ hAm (measurable_const_mul _), hA, hB]
  have hFC : IsFiniteMeasureOnCompacts (Measure.map e (μN.prod μH)) := by
    constructor
    intro C hCc
    rw [Measure.map_apply hem hCc.measurableSet]
    exact (e.isCompact_preimage.mpr hCc).measure_lt_top
  have hOP : (Measure.map e (μN.prod μH)).IsOpenPosMeasure := by
    constructor
    intro U hU hne
    rw [Measure.map_apply hem hU.measurableSet]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  exact ⟨⟩

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

def datR : PG.Dat (R ⊗[F] E) (Fin M) r where
  σA := sigR R σ
  JA := JR R J
  e a := ratV (F := F) R (P.e a)
  f a := ratV (F := F) R (P.f a)
  z := ratV (F := F) R P.z
  tz := inclR (F := F) R ((algebraMap F E (-T))⁻¹)

theorem datR_h (x y : Fin M → R ⊗[F] E) : (datR R σ J P T).h x y = hR R σ J x y := rfl

theorem sigR_inclR (x : E) : sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id F R) σ (Algebra.TensorProduct.includeRight x) =
    Algebra.TensorProduct.includeRight (σ x)
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem hR_ratV (x y : Fin M → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR (F := F) R (hE σ J x y) := by
  unfold hR hE Formalism.UG.hform JR ratV
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, sigR_inclR, Matrix.map_apply]
  rfl

variable {R σ J P T}

theorem datR_hyp (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) :
    (datR R σ J P T).Hyp := by
  have hT : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr ((map_ne_zero _).mpr hP.2.2.2.2.2.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show sigR R σ (sigR R σ x) = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show Algebra.TensorProduct.map (AlgHom.id F R) σ
          (Algebra.TensorProduct.map (AlgHom.id F R) σ (a ⊗ₜ b)) = a ⊗ₜ b
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.id_apply, hσσ]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · intro i j
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR, hJ.1]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
    rw [hR_ratV, hP.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
    rw [hR_ratV, hP.2.1 a b, map_zero]
  · intro a b
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
    rw [hR_ratV, hP.2.2.1 a b]
    split_ifs <;> simp
  · intro a
    show hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.1 a, map_zero]
  · intro a
    show hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
    rw [hR_ratV, hP.2.2.2.2.1 a, map_zero]
  · show inclR (F := F) R ((algebraMap F E (-T))⁻¹) * hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hR_ratV, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ hT, map_one]

theorem stabilizer_fixes_normal_vector {g : HA R σ J} (hg : g ∈ S0 R σ J P) :
    lin R σ J g (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  have h := congrFun (MulAction.mem_stabilizer_iff.mp hg) (Fin.last r)
  change (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
      (fun i => inclR R (F0 P (Fin.last r) i)) = fun i => inclR R (F0 P (Fin.last r) i) at h
  simp only [F0, Fin.snoc_last] at h
  exact h

theorem stabilizer_fixes_frame_and_normal {g : HA R σ J} (hg : g ∈ S0 R σ J P) :
    (datR R σ J P T).FixEZ (lin R σ J g) := by
  exact ⟨fun a => stabilizer_fixes_frame_vector R σ J P hg a, stabilizer_fixes_normal_vector hg⟩

private theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σA : A →+* A)
    (JA : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σA JA x y = dotProduct (fun i => σA (x i)) (Matrix.mulVec JA y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_eq_hform_cT_mul_mul {A : Type} [CommRing A] {n : Type} [Fintype n] (σA : A →+* A)
    (JA Mx : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) =
      Formalism.UG.hform σA (Formalism.UG.cT σA Mx * JA * Mx) x y := by
  have h1 : (fun i => σA (Matrix.mulVec Mx x i)) =
      Matrix.mulVec (Mx.map σA) (fun i => σA (x i)) := by
    funext i
    exact RingHom.map_mulVec σA Mx x i
  calc Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y)
      = dotProduct (Matrix.mulVec (Mx.map σA) (fun i => σA (x i)))
          (Matrix.mulVec JA (Matrix.mulVec Mx y)) := by
        rw [hform_eq_dotProduct_mulVec, h1]
    _ = dotProduct (fun i => σA (x i))
          (Matrix.mulVec (Mx.map σA).transpose (Matrix.mulVec JA (Matrix.mulVec Mx y))) := by
        symm
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct (fun i => σA (x i)) (Matrix.mulVec (Formalism.UG.cT σA Mx * JA * Mx) y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        rfl
    _ = Formalism.UG.hform σA (Formalism.UG.cT σA Mx * JA * Mx) x y := (hform_eq_dotProduct_mulVec _ _ _ _).symm

private theorem hform_single_single_semidirect_volume {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σA : A →+* A) (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σA N (Pi.single i 1) (Pi.single j 1) = N i j := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp

theorem uni_lin (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  intro x y
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
    g.2
  show Formalism.UG.hform (sigR R σ) (JR R J)
      (Matrix.mulVec ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) x)
      (Matrix.mulVec ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) y) =
    Formalism.UG.hform (sigR R σ) (JR R J) x y
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hg]

theorem uj_of_uni {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σA : A →+* A)
    (JA : Matrix n n A) (Mx : Matrix n n A)
    (h : ∀ x y, Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) = Formalism.UG.hform σA JA x y) :
    Formalism.UG.cT σA Mx * JA * Mx = JA := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hform_single_single_semidirect_volume, hform_single_single_semidirect_volume] at h1
  exact h1

def piMat (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  LinearMap.toMatrix' ((datR R σ J P T).Pi (lin R σ J g))

theorem piMat_mulVec (g : HA R σ J) (v : Fin M → R ⊗[F] E) :
    Matrix.mulVec (piMat (P := P) (T := T) g) v = (datR R σ J P T).Pi (lin R σ J g) v := by
  exact LinearMap.toMatrix'_mulVec _ v

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem Pi_lin_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    (datR R σ J P T).Pi (lin R σ J (g * g')) =
      (datR R σ J P T).Pi (lin R σ J g) ∘ₗ (datR R σ J P T).Pi (lin R σ J g') := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  have hl : lin R σ J (g * g') = lin R σ J g ∘ₗ lin R σ J g' := by
    unfold lin
    rw [← Matrix.mulVecLin_mul]
    rfl
  refine LinearMap.ext (fun v => ?_)
  rw [hl, LinearMap.comp_apply]
  exact (PG.Dat.Pi_comp H (fun a => stabilizer_fixes_frame_vector R σ J P hg a) (stabilizer_fixes_frame_and_normal hg') (uni_lin g') v).symm

theorem Pi_lin_one :
    (datR R σ J P T).Pi (lin R σ J 1) = LinearMap.id := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  have hl : lin R σ J (1 : HA R σ J) = LinearMap.id := by
    unfold lin
    rw [show ((HA.mat R σ J 1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1
      from rfl, Matrix.mulVecLin_one]
  rw [hl]
  exact LinearMap.ext (fun v => PG.Dat.Pi_id H v)

def piU (g : HA R σ J) (hg : g ∈ S0 R σ J P) : GL (Fin M) (R ⊗[F] E) where
  val := piMat (P := P) (T := T) g
  inv := piMat (P := P) (T := T) g⁻¹
  val_inv := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP hg ((S0 R σ J P).inv_mem hg), mul_inv_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
  inv_val := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP ((S0 R σ J P).inv_mem hg) hg, inv_mul_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]

theorem piU_mem (g : HA R σ J) (hg : g ∈ S0 R σ J P) : piU hσσ hJ hP g hg ∈ HR R σ J := by
  have H := datR_hyp (R := R) (T := T) hσσ hJ hP
  show Formalism.UG.cT (sigR R σ) (piMat (P := P) (T := T) g) * JR R J * piMat (P := P) (T := T) g = JR R J
  apply uj_of_uni
  intro x y
  rw [piMat_mulVec, piMat_mulVec]
  exact PG.Dat.Pi_uni H (stabilizer_fixes_frame_and_normal hg) (uni_lin g) x y

def piG (g : HA R σ J) (hg : g ∈ S0 R σ J P) : HA R σ J := ⟨piU hσσ hJ hP g hg, piU_mem hσσ hJ hP g hg⟩

theorem lin_piG (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    lin R σ J (piG hσσ hJ hP g hg) = (datR R σ J P T).Pi (lin R σ J g) := by
  exact LinearMap.ext (fun v => piMat_mulVec (P := P) (T := T) g v)

end R

end PI.VolSemiDirect.W
end
end

