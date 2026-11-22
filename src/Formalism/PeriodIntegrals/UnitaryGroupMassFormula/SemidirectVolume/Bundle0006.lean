import Mathlib
import Formalism.PeriodIntegrals.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeQuotientHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Assemble
section
namespace PI.VolSemiDirect.W

theorem volume_unipotent_of_adelic (hLC : LcscHA) (hD : DiscHA) (hCl : ClosedStep) (hSe : SemiStep)
    (hCo : ConjStep) : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  volume_unipotent_of_steps subgroup_locally_compact_holds fundamental_domain_exists product_haar_measure_holds volume_quotient_holds hLC hD hCl hSe hCo

end PI.VolSemiDirect.W
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.DiscAll
section
noncomputable section

namespace PI.VolSemiDirect.W

theorem closed_subgroup_holds : ClosedStep := closedStep_of Lc.tensor_adele_topology_holds

theorem discrete_adelic_unitary : DiscHA := discHA_of Lc.tensor_adele_topology_holds

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.NnrealEqOneOfMulSelf
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def trG (X : GL (Fin k) A) : GL (Fin k) A where
  val := (X : Matrix (Fin k) (Fin k) A).transpose
  inv := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

theorem trG_val (X : GL (Fin k) A) :
    ((trG X : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = (X : Matrix (Fin k) (Fin k) A).transpose :=
  rfl

theorem trG_mul (X Y : GL (Fin k) A) : trG (X * Y) = trG Y * trG X := by
  ext1
  simp [trG_val, Matrix.transpose_mul]

theorem trG_one : trG (1 : GL (Fin k) A) = 1 := by
  ext1
  simp [trG_val]

theorem trG_inv (X : GL (Fin k) A) : trG X⁻¹ = (trG X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trG_mul, mul_inv_cancel, trG_one]

theorem modM_transv (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by
  have h := hT A k i j hij c (addHaar : Measure (Fin k → A)) inferInstance
  have e : (phi X : (Fin k → A) → (Fin k → A)) = Matrix.mulVec (Matrix.transvection i j c) := by
    funext v
    rw [phi_apply, hX]
  apply modM_of_map X (addHaar : Measure (Fin k → A))
  rw [e]
  exact h

theorem transvection_transpose (i j : Fin k) (c : A) :
    (Matrix.transvection i j c).transpose = Matrix.transvection j i c := by
  ext a b
  simp [Matrix.transvection, Matrix.transpose_apply, Matrix.one_apply, Matrix.single_apply]
  aesop

theorem modM_tr_of_mem (hT : TransvHaar) (X : GL (Fin k) A)
    (hX : X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})) :
    modM (trG X) = modM X := by
  induction hX using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, hij, hx⟩ | ⟨d, hx⟩
    · rw [modM_transv hT x i j hij c hx, modM_transv hT (trG x) j i hij.symm c
        (by rw [trG_val, hx, transvection_transpose])]
    · have : trG x = x := by
        ext1
        rw [trG_val, hx, Matrix.diagonal_transpose]
      rw [this]
  | one => rw [trG_one]
  | mul x y _ _ hx hy => rw [trG_mul, modM_mul, modM_mul, hx, hy, mul_comm]
  | inv x _ hx => rw [trG_inv, modM_inv, modM_inv, hx]

end Gen

theorem nnreal_eq_one_of_mul_self {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  have h' : (x : ℝ) * x = 1 := by exact_mod_cast h
  have : (x : ℝ) = 1 := by nlinarith [x.coe_nonneg]
  exact_mod_cast this

theorem orthInv_of (h1 : AdeleStableRankOne) (h2 : ElimSR1) (h3 : TransvHaar) : OrthInv := by
  intro F _ _ k G X hG hXG μ hμ
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem h3 Xu (h2 (AF F) (h1 F) k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → AF F) → (Fin k → AF F)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

end PI.VolSemiDirect.W.Cj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjCont
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem toMatrix'_lin (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  unfold Formalism.L2.SG.Sub.lin
  first
    | exact LinearMap.toMatrix'_mulVecLin _
    | exact LinearMap.toMatrix'_toLin' _
    | (ext i j; simp [LinearMap.toMatrix'_apply, Matrix.mulVec, dotProduct, Pi.single_apply])

theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  simp only [piMat, PG.Dat.Pi, map_add, LinearMap.toMatrix'_comp, toMatrix'_lin, Matrix.mul_assoc]

theorem mat_inv (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl

theorem continuous_piMat_inv [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  have hm : Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [piMat_eq, mat_inv]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

theorem continuous_piMat [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  simp only [piMat_eq]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)

theorem continuous_piG [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun s : S0 R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨(continuous_piMat (P := P) (T := T)).comp continuous_subtype_val,
    (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val⟩

end Cont

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep
section
noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField
open scoped TensorProduct

theorem HA_ext {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g g' : HA R σ J}
    (h : ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) : g = g' :=
  Subtype.ext (Units.ext h)

theorem lin_eq_toLin' {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  rw [lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

theorem tupH_alt {E : Type} {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_last]

theorem tupH_e {E : Type} {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0, Fin.append_left, Fin.snoc_castSucc]

theorem tupH_f {E : Type} {M r : ℕ} (P : Frame E M r) (b : Fin r) :
    tupH P (Fin.natAdd (r + 1) b) = P.f b := by
  simp [tupH, Fin.append_right]

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hCM.2.2.2 τ (σ x), hCM.2.2.2 τ x, star_star]

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem fix_f_of_H {g : HA R σ J} (hg : g ∈ Hsub R σ J P) (b : Fin r) :
    lin R σ J g (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  rw [Hsub, mem_stabT] at hg
  have := hg (Fin.natAdd (r + 1) b)
  rwa [tupH_f] at this

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_piG]
  have H := datR_hyp (R := R) hσσ hJ hP
  refine Fin.addCases (fun b0 => ?_) (fun b1 => ?_) b
  · refine Fin.lastCases ?_ (fun a => ?_) b0
    · rw [tupH_alt]; exact PG.Dat.unipotent_proj_fixes_normal H _
    · rw [tupH_e]; exact PG.Dat.Pi_e H _ a
  · rw [tupH_f]; exact PG.Dat.Pi_f H _ b1

theorem mat_one : ((HA.mat R σ J (1 : HA R σ J) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1 := rfl

theorem mat_mul (g g' : HA R σ J) : ((HA.mat R σ J (g * g') : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) * ((HA.mat R σ J g' : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) := rfl

theorem piG_mat (g : HA R σ J) (hg : g ∈ S0 R σ J P) :
    ((HA.mat R σ J (piG hσσ hJ hP g hg) : GL (Fin M) (R ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E)) = piMat (P := P) (T := T) g := rfl

theorem piG_one : piG hσσ hJ hP (1 : HA R σ J) (S0 R σ J P).one_mem = 1 := by
  apply HA_ext
  rw [piG_mat, mat_one hσσ hJ hP, piMat, Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ S0 R σ J P) (hg' : g' ∈ S0 R σ J P) :
    piG hσσ hJ hP (g * g') ((S0 R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  apply HA_ext
  rw [mat_mul hσσ hJ hP, piG_mat, piG_mat, piG_mat, piMat, piMat, piMat, Pi_lin_mul hσσ hJ hP hg hg',
    LinearMap.toMatrix'_comp]

def piHom : S0 R σ J P →* Hsub R σ J P where
  toFun s := ⟨_, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩
  map_one' := Subtype.ext (piG_one hσσ hJ hP)
  map_mul' s s' := Subtype.ext (piG_mul hσσ hJ hP s.2 s'.2)

theorem piHom_coe (s : S0 R σ J P) :
    ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J) = piG hσσ hJ hP s s.2 := rfl

theorem piHom_H (s : S0 R σ J P) (hs : (s : HA R σ J) ∈ Hsub R σ J P) :
    ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J) = s := by
  rw [piHom_coe]
  apply HA_ext
  show piMat (P := P) (T := T) (s : HA R σ J) = _
  have e : (datR R σ J P T).Pi (lin R σ J s) = lin R σ J s := LinearMap.ext fun v =>
    PG.Dat.Pi_of_fix (datR_hyp hσσ hJ hP) (stabilizer_fixes_frame_and_normal s.2) (fix_f_of_H hσσ hJ hP hs)
      (uni_lin _) v
  rw [piMat, e, lin_eq_toLin']

theorem spanR_eq {m : ℕ} (Y : Fin m → Fin M → E) :
    spanR (F := F) R Y Set.univ = Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  rw [spanR, Set.image_univ]

theorem piHom_N (s : S0 R σ J P) (hs : (s : HA R σ J) ∈ FrameUnipotentSubgroup R σ J P) : piHom hσσ hJ hP s = 1 := by
  apply Subtype.ext
  rw [piHom_coe]
  apply HA_ext
  show piMat (P := P) (T := T) (s : HA R σ J) = 1
  have hN := (Subgroup.mem_inf.1 hs).1
  have e : (datR R σ J P T).Pi (lin R σ J s) = LinearMap.id := LinearMap.ext fun v =>
    PG.Dat.Pi_of_N (datR_hyp hσσ hJ hP) (fun w hw => by
      have := hN.2 w hw
      rwa [spanR_eq hσσ hJ hP] at this) v
  rw [piMat, e, LinearMap.toMatrix'_id]

theorem piHom_S (s : S0 R σ J P) :
    (s : HA R σ J) * ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J)⁻¹ ∈ FrameUnipotentSubgroup R σ J P := by
  have hinv : ((piHom hσσ hJ hP s : Hsub R σ J P) : HA R σ J)⁻¹ =
      ((piHom hσσ hJ hP s⁻¹ : Hsub R σ J P) : HA R σ J) := by
    rw [map_inv]; rfl
  rw [hinv, piHom_coe]
  have hS0 : (s : HA R σ J) * piG hσσ hJ hP (s⁻¹ : S0 R σ J P) (s⁻¹ : S0 R σ J P).2 ∈ S0 R σ J P :=
    (S0 R σ J P).mul_mem s.2 (heisenberg_le_stabilizer R σ J P (piG_mem_H hσσ hJ hP _ _))
  rw [FrameUnipotentSubgroup, Subgroup.mem_inf]
  refine ⟨?_, hS0⟩
  show UniC R σ J P.e _ ∧ ∀ v, InXperp R σ J P v → _
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [stabilizer_fixes_frame_vector R σ J P hS0 b, sub_self]
    exact Submodule.zero_mem _
  · rw [lin_mul, lin_piG, spanR_eq hσσ hJ hP]
    have hsi : ((s⁻¹ : S0 R σ J P) : HA R σ J) = (s : HA R σ J)⁻¹ := rfl
    have := PG.Dat.Pi_N_part (datR_hyp hσσ hJ hP) (stabilizer_fixes_frame_and_normal s.2)
      (stabilizer_fixes_frame_and_normal (s⁻¹ : S0 R σ J P).2) (uni_lin _) (fun w => by rw [hsi, lin_lin_inv]) v hv
    exact this

end R

def PiCont : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (r : ℕ) (P : Frame E M r) (T : F)
    (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T),
    Continuous fun s : S0 (AF F) σ J P => piG hσσ hJ hP (s : HA (AF F) σ J) s.2

def PiRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (r : ℕ) (P : Frame E M r) (T : F)
    (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (g : HA (AF F) σ J) (hg : g ∈ S0 (AF F) σ J P),
    g ∈ HFinIn (AF F) σ J → piG hσσ hJ hP g hg ∈ HFinIn (AF F) σ J

theorem projStep_of (hC : PiCont) (hR : PiRat) : ProjStep := by
  intro F E _ _ _ _ _ σ hCM M J hJ r P T hr hP
  have hσσ := sigma_invol hCM
  refine ⟨piHom hσσ hJ hP, ?_, fun s hs => piHom_H hσσ hJ hP s hs,
    fun s hs => piHom_N hσσ hJ hP s hs, fun s => piHom_S hσσ hJ hP s,
    fun s hs => hR F E σ M J r P T hσσ hJ hP s s.2 hs⟩
  exact (hC F E σ M J r P T hσσ hJ hP).subtype_mk _

end PI.VolSemiDirect.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TraceGramNondegenerate
section
noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (z : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = algebraMap F R (Algebra.trace F E z) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r e
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

theorem trace_basis_holds : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _

theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J (c • x) y = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c := σ.commutes c
  rw [map_mul, hc]
  ring

theorem hE_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J x (c • y) = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def trForm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : LinearMap.BilinForm F (Fin M → E) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (hE σ J x y))
    (fun x x' y => by simp only [hE_add_left, map_add])
    (fun c x y => by simp only [hE_smul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [hE_add_right, map_add])
    (fun c x y => by simp only [hE_smul_right, ← Algebra.smul_def, map_smul])

theorem hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]

theorem trace_gram_nondegenerate : TraceGramND := by
  intro F E _ _ _ _ _ σ hCM M J hJ k b
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  have hG : (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))) =
      LinearMap.BilinForm.toMatrix b (trForm σ J) := by
    ext i j
    simp [trForm, LinearMap.BilinForm.toMatrix_apply]
  rw [hG, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro x hx
  have hrow : ∀ j, ∑ i, σ (x i) * J i j = 0 := by
    intro j
    apply (traceForm_nondegenerate F E).1
    intro c
    have h1 := hx (Pi.single j c)
    simp only [trForm, LinearMap.mk₂_apply] at h1
    rw [Algebra.traceForm_apply, ← hE_single]
    exact h1
  have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hrow j
  by_contra hx0
  have hne : (fun i => σ (x i)) ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simpa using this
  exact hJ.2 (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hv⟩)

end PI.VolSemiDirect.W.Cj
end
end

