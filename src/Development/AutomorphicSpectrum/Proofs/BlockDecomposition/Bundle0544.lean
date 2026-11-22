import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.GlobalFields.TateThesis.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosed
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
  GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviOne

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem coef_mul_eq_one (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {d d' : Fin r → R} (e : g * Xm = Xm * diagonal d) (e' : g * Ym = Ym * diagonal d') (i : Fin r) :
    s (d' i) * d i = 1 := by
  have h := hF.inv_coef hg e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := Matrix.ext fun a b => by
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [h2, diagonal_mul_diagonal] at h
  simpa using congrFun (congrFun h i) i

theorem inv_act {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {d e : Fin r → R}
    (he : ∀ i, e i * d i = 1) (h : g * Xm = Xm * diagonal d) : g' * Xm = Xm * diagonal e := by
  have h1 : diagonal d * diagonal e = (1 : Matrix (Fin r) (Fin r) R) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm, he i]
  calc g' * Xm = g' * (Xm * (diagonal d * diagonal e)) := by rw [h1, Matrix.mul_one]
    _ = g' * g * Xm * diagonal e := by
        rw [← Matrix.mul_assoc Xm, ← h]
        simp only [Matrix.mul_assoc]
    _ = Xm * diagonal e := by rw [hg, Matrix.one_mul]

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem one_mem_minParOne : (1 : GAd σ J) ∈ minParOne σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp, fun i => ⟨1, by simp, map_one _⟩⟩

theorem mul_mem_levi {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

theorem inv_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {m : GAd σ J}
    (hm : m ∈ leviMin σ J X Y) (hm1 : m ∈ minParOne σ J X) :
    m⁻¹ ∈ leviMin σ J X Y ∧ m⁻¹ ∈ minParOne σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  have hu := unitaryA_matHom m
  have h1 := coef_mul_eq_one hF hu e e'
  have hss := hF.ss
  have hinv : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : ∀ i, d i * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d' i) = 1 := fun i => by rw [mul_comm, h1 i]
  have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d i) * d' i = 1 := coef_mul_eq_one (pfr_swap hF) hu e' e
  have f := inv_act hinv h1 e
  have f' := inv_act hinv h3 e'
  refine ⟨⟨_, _, f, f'⟩, ?_⟩
  obtain ⟨B, -, eB, hB⟩ := hm1
  have hBd : B = diagonal d := by rw [← Bm_eq hF eB, Bm_eq hF e]
  refine ⟨_, Matrix.blockTriangular_diagonal _, f, fun i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hB i
  refine ⟨u⁻¹, ?_, by rw [map_inv, hu2, inv_one]⟩
  have hd : d i = u := by rw [← hu1, hBd, Matrix.diagonal_apply_eq]
  rw [Matrix.diagonal_apply_eq]
  exact (Units.inv_eq_of_mul_eq_one_left (by rw [← hd]; exact h1 i)).symm ▸ rfl

theorem leviMin_eq (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (adMat F X) (adMat F Y)) :
    leviMin σ J X Y = {m | (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => Bm σ J X Y m i i)} ∩
      {m | (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => Bm σ J Y X m i i)} := by
  ext m
  constructor
  · rintro ⟨d, d', e, e'⟩
    have a1 : (fun i => Bm σ J X Y m i i) = d := funext fun i => by
      rw [Bm_eq hF e, Matrix.diagonal_apply_eq]
    have a2 : (fun i => Bm σ J Y X m i i) = d' := funext fun i => by
      rw [Bm_eq (pfr_swap hF) e', Matrix.diagonal_apply_eq]
    exact ⟨by simpa only [Set.mem_setOf_eq, a1] using e, by simpa only [Set.mem_setOf_eq, a2] using e'⟩
  · rintro ⟨e, e'⟩
    exact ⟨_, _, e, e'⟩

theorem isClosed_leviMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (leviMin σ J X Y) := by
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hc : ∀ {X' Y' : Matrix (Fin n) (Fin r) E}, Continuous fun m : GAd σ J =>
      adMat F X' * diagonal (fun i => Bm σ J X' Y' m i i) := fun {X' Y'} => by
    have hd : Continuous fun m : GAd σ J => diagonal (fun i => Bm σ J X' Y' m i i) :=
      continuous_matrix fun a b => by
        by_cases hab : a = b
        · subst hab
          simpa using (continuous_Bm (σ := σ) (J := J) (X := X') (Y := Y')).matrix_elem a a
        · simpa [Matrix.diagonal_apply_ne _ hab] using continuous_const
    exact continuous_const.matrix_mul hd
  rw [leviMin_eq hF]
  exact (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc).inter
    (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc)

end GlobalTheory.CompanionTheory.ParCocompact.LeviOne

open GlobalTheory.CompanionTheory.ParCocompact.LeviOne in

theorem GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  refine ⟨{ carrier := leviMin σ J X Y ∩ minParOne σ J X
            mul_mem' := fun {a b} ha hb => ⟨mul_mem_levi ha.1 hb.1, (minParOne_props h hJ hW).2 a ha.2 b hb.2⟩
            one_mem' := ⟨one_mem_leviMin σ J X Y, one_mem_minParOne⟩
            inv_mem' := fun {a} ha => inv_mem h hJ hW ha.1 ha.2 }, rfl, ?_⟩
  exact (isClosed_leviMin h hJ hW).inter (minParOne_props h hJ hW).1

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralVecSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS PositivityTheory.AdelicQuotientData
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem map_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) :
    (vecMeasure E ι).map (fun x p => a p • x p) =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) • vecMeasure E ι := by
  classical
  let c : ι → NNReal := fun p => Real.toNNReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹
  have hm : ∀ p, (GroundTheory.Global.adeleMeasure E).map (fun x => a p • x) = c p • GroundTheory.Global.adeleMeasure E := fun p => by
    rw [GroundTheory.Global.map_smul_adeleMeasure]; rfl
  have : ∀ p, SigmaFinite ((GroundTheory.Global.adeleMeasure E).map (fun x => a p • x)) := fun p => by
    rw [hm]; infer_instance
  have hmeas : ∀ p, Measurable (fun x : Ad E => a p • x) := fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable
  have h := Measure.pi_map_pi (μ := fun _ : ι => GroundTheory.Global.adeleMeasure E) (f := fun p x => a p • x)
    (fun p => (hmeas p).aemeasurable)
  rw [vecMeasure, h]
  simp_rw [hm]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem lintegral_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) (G : (ι → Ad E) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G (fun p => a p • x p) ∂vecMeasure E ι =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) * ∫⁻ x, G x ∂vecMeasure E ι := by
  have hf : Measurable (fun (x : ι → Ad E) p => a p • x p) := measurable_pi_lambda _ fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
  rw [← lintegral_map hG hf, map_vec_smul, lintegral_smul_measure]
  rfl

theorem conj_blkU {R : Type} [CommRing R] (D : GL (Fin k) R) (u : Fin k → Rˣ)
    (hD : D.val = diagonal fun i => (u i : R)) {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → R) :
    D * blkU x * D⁻¹ = blkU (fun t => ((u t.1.1 * (u t.1.2)⁻¹ : Rˣ) : R) * x t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  change D.val * (1 + posM Subtype.val x) = (1 + posM Subtype.val _) * D.val
  rw [hD]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply, mul_add, add_mul]
  congr 1
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · simp only [posM, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1.1 = i ∧ t.1.2 = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same, Units.val_mul]
      have e : ((u t.1.2)⁻¹ : Rˣ).val * (u t.1.2).val = 1 := Units.inv_mul _
      linear_combination (-(u t.1.1).val * x t) * e
    · have e : ∀ y : R, Matrix.single t.1.1 t.1.2 y i j = 0 := fun y => by
        rw [Matrix.single_apply_of_ne]; exact h
      rw [e, e]; simp

def locId (w : Pl E) : (w.adicCompletion E)ˣ →* (Ad E)ˣ := (finId E).comp (Units.map (corner (sLoc E w)))

theorem fl_torus (w : Pl E) (l : Fin k → ℤ) :
    (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)).val =
      diagonal fun i => ((locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l i) : (Ad E)ˣ) : Ad E) := by
  ext i j
  change (1 : Matrix (Fin k) (Fin k) (Ad E)) i j - sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j - sLoc E w ((1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) i j) +
      sLoc E w ((Iwasawa.torusPow (w.adicCompletion E) k l).val i j)) = _
  rw [Iwasawa.torusPow, Iwasawa.coe_diagGL]
  by_cases h : i = j
  · subst h
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · simp [h]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def colS (e : Fin k → ℤ) (j : ℕ) : ℤ := ∑ p : UnipotentBlockColumnIndex k j j, (e p.1.1 - e p.1.2)

def totS (e : Fin k → ℤ) (d : ℕ) : ℤ := ∑ i ∈ Finset.range d, colS e (k - (i + 1))

theorem prod_ofReal_zpow {ι : Type} (s : Finset ι) {q : ℝ} (hq : 0 < q) (e : ι → ℤ) :
    ∏ p ∈ s, ENNReal.ofReal (q ^ e p) = ENNReal.ofReal (q ^ ∑ p ∈ s, e p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq.ne', ENNReal.ofReal_mul (zpow_nonneg hq.le _)]

theorem sFinite_nuD (d : ℕ) : SFinite (nuD E k d) := by
  induction d with
  | zero => change SFinite (Measure.dirac _); infer_instance
  | succ d ih => change SFinite (Measure.map _ _); infer_instance

theorem measurable_blkMul (j : ℕ) : Measurable (fun p : (UnipotentBlockColumnIndex k j j → Ad E) × GA E k => blkU p.1 * p.2) :=
  ((continuous_posU _).measurable.comp measurable_fst).mul measurable_snd

theorem nuD_conj (t : GA E k) (u : Fin k → (Ad E)ˣ) (ht : t.val = diagonal fun i => (u i : Ad E)) {q : ℝ} (hq : 0 < q)
    (e : Fin k → ℤ) (hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E (u a * (u b)⁻¹) : ℝ))⁻¹ = q ^ (e a - e b))
    (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k d = ENNReal.ofReal (q ^ totS e d) * ∫⁻ h, F h ∂nuD E k d := by
  have hc : Measurable (fun h : GA E k => t * h * t⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  induction d generalizing F with
  | zero =>
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    change ∫⁻ h, F (t * h * t⁻¹) ∂Measure.dirac 1 = _ * ∫⁻ h, F h ∂Measure.dirac 1
    rw [lintegral_dirac' _ hFc, lintegral_dirac' _ hF]
    simp [totS]
  | succ d ih =>
    have := sFinite_nuD (E := E) (k := k) d
    have hM := measurable_blkMul (E := E) (k := k) (k - (d + 1))
    let a : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → (Ad E)ˣ := fun p => u p.1.1 * (u p.1.2)⁻¹
    let G : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) → ℝ≥0∞ := fun y => ∫⁻ h, F (blkU y * h) ∂nuD E k d
    have hFM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => F (blkU p.1 * p.2) := hF.comp hM
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    have hFcM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k =>
        F (t * (blkU p.1 * p.2) * t⁻¹) := hFc.comp hM
    have hG : Measurable G := hFM.lintegral_prod_right'
    have hf : Measurable (fun (x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) p => a p • x p) :=
      measurable_pi_lambda _ fun p =>
        (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
    have hR : ∫⁻ h, F h ∂nuD E k (d + 1) = ∫⁻ y, G y ∂vecMeasure E _ := by
      change ∫⁻ h, F h ∂(Measure.map _ _) = _
      rw [lintegral_map hF hM, lintegral_prod _ hFM.aemeasurable]
    have hL : ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k (d + 1) =
        ∫⁻ x, ENNReal.ofReal (q ^ totS e d) * G (fun p => a p • x p) ∂vecMeasure E _ := by
      change ∫⁻ h, F (t * h * t⁻¹) ∂(Measure.map _ _) = _
      rw [lintegral_map hFc hM, lintegral_prod _ hFcM.aemeasurable]
      refine lintegral_congr fun x => ?_
      have key : ∀ h, t * (blkU x * h) * t⁻¹ = blkU (fun p => a p • x p) * (t * h * t⁻¹) := fun h => by
        have e1 : blkU (fun p => a p • x p) = t * blkU x * t⁻¹ := (conj_blkU t u ht x).symm
        rw [e1]; group
      simp only [key]
      exact ih (fun y => F (blkU (fun p => a p • x p) * y)) (hF.comp (measurable_const_mul _))
    have hstep : (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) =
        ENNReal.ofReal (q ^ colS e (k - (d + 1))) := by
      simp only [a, hmod]
      exact prod_ofReal_zpow _ hq _
    have hGf : Measurable fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E => G (fun p => a p • x p) := hG.comp hf
    rw [hL, hR, lintegral_const_mul _ hGf, lintegral_vec_smul a G hG, hstep, ← mul_assoc,
      ← ENNReal.ofReal_mul (zpow_nonneg hq.le _), ← zpow_add₀ hq.ne']
    simp only [totS, Finset.sum_range_succ]

theorem nuP_zero : nuP E k 0 = nuD E k (k - 1) := by
  have h1 : IsMir 0 (1 : GL (Fin k) E) := fun i j _ => rfl
  let i0 : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _) := ⟨1, h1⟩
  have hu : ∀ γ : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _), γ = i0 := fun γ => Subtype.ext (Units.ext (Matrix.ext fun i j =>
    γ.2 i j (Or.inl (Nat.zero_le _))))
  ext s hs
  rw [nuP, nuG, Measure.sum_apply _ hs, tsum_eq_single i0 (fun b hb => absurd (hu b) hb)]
  simp [i0]

theorem colS_eq (l : Fin k → ℤ) (c : Fin k) : colS l c = ∑ i : Fin k, if i < c then l i - l c else 0 := by
  classical
  unfold colS
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin k × Fin k => (p.1 : ℕ) < c ∧ (c : ℕ) ≤ p.2 ∧ (p.2 : ℕ) ≤ c)
    (by simp) (fun p => l p.1 - l p.2), Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single c]
  · simp only [le_refl, and_true, Fin.val_fin_lt]
  · intro b _ hb
    rw [if_neg]
    rintro ⟨-, h1, h2⟩
    have h1' : (c : ℕ) ≤ b := h1
    have h2' : (b : ℕ) ≤ c := h2
    exact hb (Fin.ext (by omega))
  · simp

theorem sum_cols (l : Fin k → ℤ) : ∑ c : Fin k, ∑ i : Fin k, (if i < c then l i - l c else 0) = rhoPair l :=
  _root_.UpperTheory.Reformulated.B.CountingPairs.main l

theorem totS_eq (l : Fin k → ℤ) : totS l (k - 1) = rhoPair l := by
  rw [← sum_cols l]
  simp only [← colS_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => colS l j) k]
  rcases k with _ | n
  · simp [totS]
  · have h0 : colS l 0 = 0 := Finset.sum_eq_zero fun t _ => absurd t.2.1 (Nat.not_lt_zero _)
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp only [totS, Nat.add_sub_cancel]
    rw [Nat.sub_self, h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    have := Finset.mem_range.1 hi
    omega

variable [IsTotallyComplex E]

theorem mod_locId (hD : D0) (w : Pl E) (m : ℤ) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m)) : ℝ) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hD E 1
  have h2 := h w (fun _ => m)
  have e : GeneralLinearGroup.det (fl 1 w (Iwasawa.torusPow (w.adicCompletion E) 1 fun _ => m)) =
      locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, fl_torus, Matrix.det_diagonal]
    simp
  rw [Dt, e] at h2
  simpa using h2

theorem main : PositivityTheory.AdelicQuotientData.D0 → PositivityTheory.jumpWindows.G0 → PositivityTheory.AdelicQuotientData.N2 := by
  intro hD _ E _ _ _ k w l F hF
  have hm1 := mod_locId hD w 1
  have hq : 0 < (Ideal.absNorm w.asIdeal : ℝ) := by
    have h0 := (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ (1 : ℤ)))).2
    rw [hm1] at h0
    by_contra hc
    have h00 : (Ideal.absNorm w.asIdeal : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [h00] at h0
    simp at h0
  have hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E
      (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l a) *
        (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l b))⁻¹) : ℝ))⁻¹ =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (l a - l b) := fun a b => by
    rw [← map_inv, ← map_mul, ← _root_.zpow_neg, ← _root_.zpow_add, ← sub_eq_add_neg, mod_locId hD, _root_.zpow_neg, inv_inv]
  rw [nuP_zero, nuD_conj _ _ (fl_torus w l) hq l hmod (k - 1) F hF, totS_eq]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

def chartHom (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : Γ(PSpace ℤ N, chart ℤ N c) →+* ℂ :=
  (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c)).comp
    (chartAlgEquiv ℤ N c).symm.toRingEquiv.toRingHom

def ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : CxPts (PSpace.str ℤ N) σ₀ :=
  CxPts.ofHom (isAffineOpen_chart ℤ N c) (chartHom N c w)
    (fun a => RingHom.congr_fun (RingHom.ext_int ((chartHom N c w).comp (DVR.FlatBC.algX _ _)) σ₀) a)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def multiprojectivePoint (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) : CxPts (mpStr ℤ m n) σ₀ :=
  ⟨GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (spMap σ₀)
      (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).1) (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).2),
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ _ _ _ _⟩

theorem map_prB_ptMP (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) :
    (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ (multiprojectivePoint c z)) =
      ptP (n k) (c k) (fun i => z ⟨k, i⟩) :=
  Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ k)

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCoord (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph Θ ∧ (∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) ∧
    (∀ x w, Θ ((1 : Ainf F) ⊗ₜ[F] x) w = τ w x) ∧
    ∀ z w, ((e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w : ℝ) : ℂ) = Θ z w + conj (Θ z w)

def tupC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n M : ℕ} (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    InfinitePlace F → Fin n → Fin M → ℂ :=
  fun w a i => Θ (X a i) w

def matC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) : Matrix (Fin n) (Fin n) ℂ :=
  fun a c => Θ (b a c) w

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem mem_ptIdeal_iff_aeval_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (f : Geo.MRing (Bk n)) (a : Fin (m + 1) → ℕ), Geo.IsMultiHomog f a → (f ∈ ptIdeal x ↔ aeval (ptCoord x) f = 0) := by
  intro m n x f a hf
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff (ptCoord x) hf

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGlStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_commutes_infinite_gl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    ∀ y : GL (Fin a) (Cinf E),
      GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | exact GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt | (intros; apply GlobalTheory.CompanionTheory.HCRep.omegaOp_comm_rt <;> assumption)
end

