import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows
open scoped ContDiff

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CutOff

section Row

variable {R : Type} [CommRing R] {k : ℕ}

def eRow (R : Type) [CommRing R] (k : ℕ) : Fin k → R := fun c => if (c : ℕ) + 1 = k then 1 else 0

def lastEnt (r : Fin k → R) : R := ∑ c : Fin k, if (c : ℕ) + 1 = k then r c else 0

def lastRowM (A : Matrix (Fin k) (Fin k) R) : Fin k → R := fun c => ∑ i : Fin k, if (i : ℕ) + 1 = k then A i c else 0

def rowM (r : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i c => if (i : ℕ) + 1 = k then r c else (1 : Matrix (Fin k) (Fin k) R) i c

def rowI (r : Fin k → R) : Fin k → R :=
  fun c => if (c : ℕ) + 1 = k then Ring.inverse (lastEnt r) else -(r c * Ring.inverse (lastEnt r))

theorem rowM_apply_last (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 = k) : rowM r i c = r c := by
  simp [rowM, h]

theorem rowM_apply_ne (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 ≠ k) :
    rowM r i c = (1 : Matrix (Fin k) (Fin k) R) i c := by
  simp [rowM, h]

theorem lastEnt_eq (r : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) : lastEnt r = r l := by
  rw [lastEnt, Finset.sum_eq_single l]
  · simp [hl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · simp

theorem rowM_mul_rowM (r t : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) (i c : Fin k) :
    (rowM r * rowM t) i c = if (i : ℕ) + 1 = k then
      (if (c : ℕ) + 1 = k then r l * t c else r c + r l * t c) else rowM t i c := by
  have hlast : ∀ j : Fin k, (j : ℕ) + 1 = k → j = l := fun j hj => Fin.ext (by omega)
  by_cases hi : (i : ℕ) + 1 = k
  · rw [if_pos hi, Matrix.mul_apply]
    have e : ∀ j, rowM r i j * rowM t j c =
        r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) := fun j => by
      rw [rowM_apply_last r i j hi]
      by_cases hj : j = l
      · subst hj; rw [rowM_apply_last t _ c hl, if_pos rfl]
      · rw [rowM_apply_ne t j c (fun h => hj (hlast j h)), if_neg hj]
    simp only [e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have e2 : ∀ j ∈ Finset.univ.erase l, r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) =
        if j = c then r j else 0 := fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2, if_pos rfl, Finset.sum_ite_eq' ]
    by_cases hc : (c : ℕ) + 1 = k
    · have : c = l := hlast c hc
      subst this
      simp [hc]
    · have : c ≠ l := fun h => hc (h ▸ hl)
      simp [hc, this, add_comm]
  · rw [if_neg hi, Matrix.mul_apply]
    simp only [rowM_apply_ne r i _ hi, Matrix.one_apply]
    simp

variable {r : Fin k → R}

theorem rowM_mul_rowI (h : IsUnit (lastEnt r)) : rowM r * rowM (rowI r) = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, rowI, e, Matrix.one_apply, if_true]
        exact hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, rowI, e, Matrix.one_apply, if_neg hcl]
        linear_combination (- r c) * hu
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

theorem rowI_mul_rowM (h : IsUnit (lastEnt r)) : rowM (rowI r) * rowM r = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    have el : rowI r l = Ring.inverse (r l) := by simp [rowI, hl, e]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, el, Matrix.one_apply, if_true]
        linear_combination hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, el, Matrix.one_apply, if_neg hcl]
        simp only [rowI, if_neg hc, e]
        ring
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

open Classical in

def rowGL (r : Fin k → R) : GL (Fin k) R :=
  if h : IsUnit (lastEnt r) then ⟨rowM r, rowM (rowI r), rowM_mul_rowI h, rowI_mul_rowM h⟩ else 1

theorem rowGL_val (h : IsUnit (lastEnt r)) : (rowGL r).val = rowM r := by
  simp [rowGL, h]

theorem rowGL_inv_val (h : IsUnit (lastEnt r)) : ((rowGL r)⁻¹).val = rowM (rowI r) := by
  simp [rowGL, h]

theorem lastEnt_eRow (hk : 1 ≤ k) : lastEnt (eRow R k) = 1 := by
  rw [lastEnt_eq _ ⟨k - 1, by omega⟩ (by simp; omega)]
  simp [eRow]; omega

theorem rowM_eRow : rowM (eRow R k) = 1 := by
  ext i c
  by_cases hi : (i : ℕ) + 1 = k
  · rw [rowM_apply_last _ _ _ hi, eRow, Matrix.one_apply]
    by_cases hc : (c : ℕ) + 1 = k
    · rw [if_pos hc, if_pos (Fin.ext (by omega))]
    · rw [if_neg hc, if_neg (fun h : i = c => hc (h ▸ hi))]
  · rw [rowM_apply_ne _ _ _ hi]

theorem rowGL_eRow (hk : 1 ≤ k) : rowGL (eRow R k) = 1 := by
  by_cases h : IsUnit (lastEnt (eRow R k))
  · exact Units.ext ((rowGL_val h).trans rowM_eRow)
  · simp [rowGL, h]

theorem lastRow_mul_rowGL_inv (A : GL (Fin k) R) (h : IsUnit (lastEnt r)) (hA : lastRowM A.val = r) :
    Mir (k - 1) (A * (rowGL r)⁻¹) := by
  intro i j hij
  have hi : (i : ℕ) + 1 = k := by have := i.2; have := j.2; omega
  have e1 : ∀ m, A.val i m = rowM r i m := fun m => by
    rw [rowM_apply_last _ _ _ hi, ← hA, lastRowM, Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  have e2 : (A * (rowGL r)⁻¹).val i j = (rowM r * rowM (rowI r)) i j := by
    rw [Units.val_mul, rowGL_inv_val h, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [e1]
  rw [e2, rowM_mul_rowI h]

end Row

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def latS (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)) : AddSubgroup (Af E) where
  carrier := {a | (∀ w, w ∉ S → pLoc E w a ∈ Formalism.UG.Ov E w) ∧ ∀ w ∈ S, pLoc E w a ∈ B w}
  add_mem' := fun {a b} ha hb => ⟨fun w hw => by
      rw [map_add]; exact add_mem (ha.1 w hw) (hb.1 w hw), fun w hw => by
      rw [map_add]; exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
  zero_mem' := ⟨fun w _ => by rw [map_zero]; exact zero_mem _, fun w _ => by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun w hw => by
      rw [map_neg]; exact neg_mem (ha.1 w hw), fun w hw => by
      rw [map_neg]; exact neg_mem (ha.2 w hw)⟩

variable (E k) in

def nuFin : Measure (Fin k → Af E) := Measure.pi fun _ => GroundTheory.Global.finiteAdeleMeasure E

def boxL (L : Set (Af E)) (c : Fin k → Af E) : Set (Fin k → Af E) := {f | ∀ i, f i - c i ∈ L}

variable [IsTotallyComplex E]

variable (E k) in

def nuInf : Measure (Fin k → Cinf E) :=
  (Measure.pi fun _ => GroundTheory.Global.infiniteAdeleMeasure E).map fun y i => (infEq E).symm (y i)

def glue (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) : GA E k :=
  (S.toList.map fun w => fl k w (u w)).prod * infGL E k a

def sOf (S : Finset (Pl E)) (y : Fin k → Ad E) : GA E k :=
  glue S (rowGL fun i => pInf E (y i)) fun w => rowGL fun i => pLoc E w (pFin E (y i))

def etaOf (b : (Fin k → Cinf E) → ℝ) (L : Set (Af E)) (y : Fin k → Ad E) : ℝ :=
  b (fun i => pInf E (y i)) * (boxL L (eRow (Af E) k)).indicator (fun _ => 1) fun i => pFin E (y i)

end Adelic

end GlobalTheory.CompanionTheory.CutOff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTer
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem coef_inv (hF : PFr s Jm Xm Ym) {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm)
    {d d' : Fin r → R} (e : M * Xm = Xm * diagonal d) (e' : M * Ym = Ym * diagonal d') (i : Fin r) :
    d i * s (d' i) = 1 := by
  have h := hF.inv_coef hM e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 := congrFun (congrFun h i) i
  have e3 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [e3, Matrix.diagonal_mul_diagonal] at h2
  simpa [mul_comm] using h2

theorem inv_mul_frame {M Mi : Matrix (Fin n) (Fin n) R} (hMi : Mi * M = 1) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) : Mi * Xm = Xm * diagonal c := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  calc Mi * Xm = Mi * (Xm * (diagonal d * diagonal c)) := by rw [h1, Matrix.mul_one]
    _ = Mi * M * Xm * diagonal c := by
      rw [← Matrix.mul_assoc Xm, ← e]
      simp only [Matrix.mul_assoc]
    _ = Xm * diagonal c := by rw [hMi, Matrix.one_mul]

theorem orth_mulVec {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) {v : Fin n → R}
    (hv : (cT s Xm * Jm) *ᵥ v = 0) : (cT s Xm * Jm) *ᵥ (M *ᵥ v) = 0 := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  have h := pgram_unitary hM (Xm * diagonal c) (1 : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.mul_assoc M, e, Matrix.mul_assoc Xm, h1, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one,
    Formalism.UG.cT_mul] at h
  rw [Matrix.mulVec_mulVec, h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem clause_extend (hF : PFr s Jm Xm Ym) {U : Matrix (Fin n) (Fin n) R} {B : Matrix (Fin r) (Fin r) R}
    (hU : U * Xm = Xm * B) {P : Matrix (Fin n) (Fin n) R}
    (hP : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm))
    (hc : ∀ k, ∃ a : Fin r → R, (U - 1) *ᵥ (fun i => P i k) = Xm *ᵥ a) {w : Fin n → R}
    (hw : (cT s Xm * Jm) *ᵥ w = 0) : ∃ a : Fin r → R, (U - 1) *ᵥ w = Xm *ᵥ a := by
  choose A hA using hc
  have hUP : (U - 1) * P = Xm * (Matrix.of fun j k => A k j) := by
    ext i k
    have := congrFun (hA k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hUX : (U - 1) * Xm = Xm * (B - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hU, Matrix.mul_sub, Matrix.mul_one]
  have hwd : w = P *ᵥ w + Xm *ᵥ ((cT s Ym * Jm) *ᵥ w) := by
    rw [hP, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec w Ym, hw,
      Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
    abel
  refine ⟨(Matrix.of fun j k => A k j) *ᵥ w + (B - 1) *ᵥ ((cT s Ym * Jm) *ᵥ w), ?_⟩
  conv_lhs => rw [hwd]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUP, hUX, Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def orthProj (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    Matrix (Fin n) (Fin n) E :=
  1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)

theorem orth_orthProj (hW : IsWittFrame σ J X Y) : (cT (σ : E →+* E) X * J) * orthProj σ J X Y = 0 := by
  have e1 : cT (σ : E →+* E) X * J * (X * (cT (σ : E →+* E) Y * J)) = 0 := by
    rw [← Matrix.mul_assoc, hW.xx, Matrix.zero_mul]
  have e2 : cT (σ : E →+* E) X * J * (Y * (cT (σ : E →+* E) X * J)) = cT (σ : E →+* E) X * J := by
    rw [← Matrix.mul_assoc, hW.xy, Matrix.one_mul]
  rw [orthProj, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, e1, e2]
  abel

theorem leviMin_normalises_unipMin (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m : GAd σ J) (hm : m ∈ leviMin σ J X Y)
    (u : GAd σ J) (hu : u ∈ unipMin σ J X) : m⁻¹ * u * m ∈ unipMin σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  obtain ⟨B, hB, hB1, eU, hz⟩ := hu
  have hM := unitaryA_matHom m
  set M := (matHom _ σ J m).1 with hMdef
  set U := (matHom _ σ J u).1 with hUdef
  set Mi := (matHom _ σ J m⁻¹).1 with hMidef
  have hMi : Mi * M = 1 := by
    rw [hMidef, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨c, hdc⟩ : ∃ c : Fin r → AF F ⊗[F] E, ∀ i, d i * c i = 1 := ⟨_, coef_inv hF hM e e'⟩
  have eMi := inv_mul_frame hMi hdc e
  have hV : (matHom _ σ J (m⁻¹ * u * m)).1 = Mi * U * M := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  refine ⟨diagonal c * B * diagonal d, ((Matrix.blockTriangular_diagonal _).mul hB).mul
    (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_⟩
  · intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hB1, mul_one, mul_comm]
    exact hdc i
  · rw [hV, Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.mul_assoc Mi, eU, ← Matrix.mul_assoc Mi, eMi]
    simp only [Matrix.mul_assoc]
  · intro z hzz
    have hcol : ∀ k, ∃ a, (U - 1) *ᵥ (fun i => ((orthProj σ J X Y).map (inclR (F := F) (AF F))) i k) =
        adMat F X *ᵥ a := by
      intro k
      refine hz (fun i => orthProj σ J X Y i k) ?_
      funext i
      have := congrFun (congrFun (orth_orthProj hW) i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hv : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) *ᵥ
        (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J =
          (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR, Matrix.map_mul]
        rfl
      rw [e1]
      funext i
      have := congrArg (inclR (F := F) (AF F)) (congrFun hzz i)
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul] using this
    obtain ⟨a, ha⟩ := clause_extend hF eU (by
      unfold JR
      rw [← cT_map_inclR, ← cT_map_inclR, orthProj, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]) hcol
      (orth_mulVec hM hdc e hv)
    refine ⟨diagonal c *ᵥ a, ?_⟩
    have e4 : Mi * U * M - 1 = Mi * (U - 1) * M := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hMi]
    rw [hV, e4, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, eMi,
      Matrix.mulVec_mulVec]

end GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationUnique
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.SW.FibSch

theorem fib_scale_core (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [MeasurableSpace R] [BorelSpace R] (hR : GlobalTheory.CompanionTheory.SW.IsLocR R) (n : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n))
    (m : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) (hm : GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : IsUnit g.det) :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n,
      (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g →
      m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨-, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g
      invFun := fun X => GlobalTheory.CompanionTheory.SW.rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      map_add' := fun X Y => by
        funext b i
        simp only [GlobalTheory.CompanionTheory.SW.rmul, Pi.add_apply, add_mul, Finset.sum_add_distrib] }
  have hc1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ)
      (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h = 1 := by
      rw [← HeckeCharacterZeroLocus.SiegelWeilU.cT_mul, hh, hc1]
    calc HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
          (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h * A * h) * h'
        = (HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h' *
            HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n =>
        HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) h *
          (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let t : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n ≃+ HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n :=
    { toFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, hmem S g⟩
      invFun := fun S => ⟨HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR R σ) g⁻¹ *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
      left_inv := fun S => Subtype.ext (key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (key _ _ _ hg2)
      map_add' := fun S T => Subtype.ext (by
        simp only [AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hec : Continuous e := hrc g
  have hes : Continuous e.symm := hrc g⁻¹
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g⁻¹).subtype_mk _
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hec hes
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨a, ha0, hmu⟩ : ∃ a : ℝ≥0, a ≠ 0 ∧ μ.map e = a • μ :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) μ).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  obtain ⟨c, hc0, hnu⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ ν.map t = c • ν :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (ν.map t) ν).ne',
      Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hfib := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg t (fun _ => rfl) a c hmu hnu
  refine ⟨c / a, div_ne_zero hc0 ha0, fun S S' hS => ?_⟩
  have hS' : S' = t S := Subtype.ext hS
  have h := hfib S
  rw [← hS'] at h
  calc m S' = a⁻¹ • (a • m S') := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
    _ = (c / a) • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
      rw [h, smul_smul, div_eq_inv_mul]

theorem fib_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], GlobalTheory.CompanionTheory.SW.IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HermR R σ n, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g → m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg
  exact fib_scale_core F E σ hσ M J hJ R hR n μ ν m hμ hν hm g hg

end GlobalTheory.CompanionTheory.SW.FibSch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExistsStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_subgroup_exists : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a), ∃ c : ℝ → GL (Fin a) (Cinf E), Continuous c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 ∧ ((Matrix.of X)ᴴ = -(Matrix.of X) → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  first | exact @GlobalTheory.CompanionTheory.LieCurve.exists_curve | exact GlobalTheory.CompanionTheory.LieCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.LieCurve.exists_curve <;> assumption)
end

