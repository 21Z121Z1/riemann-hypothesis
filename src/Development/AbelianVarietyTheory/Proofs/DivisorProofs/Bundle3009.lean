import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ}

def ldTop (j : Fin s) : {a : Fin s // (a : ℕ) < j + 1} := ⟨j, Nat.lt_succ_self _⟩

@[simp] theorem ldTop_val (j : Fin s) : (ldTop j).1 = j := rfl

theorem eq_ldTop_iff {j : Fin s} (a : {a : Fin s // (a : ℕ) < j + 1}) : a = ldTop j ↔ a.1 = j :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

theorem sum_eq_sum_lt_of_zero (m : ℕ) (f : Fin s → ℂ) (hf : ∀ l : Fin s, ¬ (l : ℕ) < m → f l = 0) :
    ∑ l, f l = ∑ b : {a : Fin s // (a : ℕ) < m}, f b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < m) f]
  have : ∑ b : {a : Fin s // ¬ (a : ℕ) < m}, f b = 0 := Finset.sum_eq_zero (fun b _ => hf b b.2)
  rw [this, add_zero]

theorem prod_lt_eq (m : ℕ) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < m}, f a = ∏ a : Fin s, if (a : ℕ) < m then f a else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) f).symm

theorem prod_lt_succ (j : Fin s) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < j + 1}, f a = (∏ a : {a : Fin s // (a : ℕ) < j}, f a) * f j := by
  have hj : f j = ∏ a : Fin s, if a = j then f a else 1 := by simp
  rw [prod_lt_eq, prod_lt_eq, hj, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h1 : (a : ℕ) < j
  · have h2 : a ≠ j := fun h => by subst h; omega
    simp [h1, h2, show (a : ℕ) < j + 1 by omega]
  · by_cases h3 : a = j
    · subst h3; simp
    · have : ¬ (a : ℕ) < j + 1 := fun h => h3 (Fin.ext (by omega))
      simp [h1, h3, this]

theorem submatrix_mul_conjTranspose_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ρ : κ → Fin s) (m : ℕ) :
    (M * gᴴ).submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) =
      M.submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) *
        gᴴ.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [Matrix.conjTranspose_apply, hg c.1 l (by have := c.2; rw [Fin.lt_iff_val_lt_val]; omega), star_zero, mul_zero]

theorem submatrix_mul_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ν : κ → Fin s) (m : ℕ) :
    (g * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν =
      g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [hg a.1 l (by have := a.2; rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem det_submatrix_lt (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val).det =
      ∏ a : {a : Fin s // (a : ℕ) < m}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · rfl
  · intro a b h
    exact hg a.1 b.1 h

theorem leadMinor_conj_lower (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    leadMinor (g * G * gᴴ) m =
      (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) * leadMinor G m * star (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) := by
  unfold leadMinor
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, submatrix_mul_lt g G hg]
  erw [Matrix.det_mul]
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, det_submatrix_lt g hg]

theorem det_updateRow_finset_sum {ι κ : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (r : ι)
    (t : Finset κ) (c : κ → ℂ) (v : κ → ι → ℂ) :
    (A.updateRow r (∑ l ∈ t, c l • v l)).det = ∑ l ∈ t, c l * (A.updateRow r (v l)).det := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r (fun c => by simp)
  · intro a t ha ih
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih, Finset.sum_insert ha]

theorem submatrix_ld_eq_updateRow (X : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    X.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val =
      (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j)
        (fun c : {a : Fin s // (a : ℕ) < j + 1} => X i c) := by
  ext a c
  rw [Matrix.updateRow_apply]
  by_cases h : a.1 = j
  · simp [h, (eq_ldTop_iff a).2 h]
  · have : a ≠ ldTop j := fun e => h ((eq_ldTop_iff a).1 e)
    simp [h, this]

theorem updateRow_mul_lower (g X : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s)
    (v : {a : Fin s // (a : ℕ) < j + 1} → ℂ) :
    ((g * X).submatrix Subtype.val Subtype.val).updateRow (ldTop j) v =
      (g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1) *
        (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j) v := by
  ext a c
  by_cases h : a = ldTop j
  · subst h
    simp [Matrix.mul_apply, Pi.single_apply]
  · have ha : (a.1 : ℕ) < j := by
      have := a.2
      have : (a.1 : ℕ) ≠ j := fun e => h ((eq_ldTop_iff a).2 (Fin.ext e))
      omega
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_eq_sum_lt_of_zero ((j : ℕ) + 1) _ fun l hl => by
      rw [hg a.1 l (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.updateRow_apply]
    by_cases hb : b = ldTop j
    · subst hb
      rw [ldTop_val, hg a.1 j (by rw [Fin.lt_iff_val_lt_val]; exact ha)]
      simp
    · simp [hb]

theorem det_frameRow (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s) :
    ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j + 1} → Fin s) Subtype.val).updateRow
      (ldTop j) (Pi.single (ldTop j) 1)).det =
      ∏ a : {a : Fin s // (a : ℕ) < j}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · have e : ∀ a : {a : Fin s // (a : ℕ) < j + 1},
        ((g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1)) a a =
          (fun b : Fin s => if b = j then 1 else g b b) a := by
      intro a
      by_cases h : a = ldTop j
      · subst h; simp
      · have : a.1 ≠ j := fun e => h ((eq_ldTop_iff a).2 e)
        simp [Matrix.updateRow_ne h, this]
    rw [Fintype.prod_congr _ _ e, prod_lt_succ j (fun b : Fin s => if b = j then 1 else g b b)]
    simp only [if_true, mul_one]
    refine Fintype.prod_congr (fun a : {a : Fin s // (a : ℕ) < j} => if (a : Fin s) = j then (1 : ℂ) else g a a)
      (fun a => g a a) fun a => ?_
    have : a.1 ≠ j := fun e => by have := a.2; rw [e] at this; omega
    simp [this]
  · intro a b hab
    have hab' : (a.1 : ℕ) < b.1 := hab
    by_cases h : a = ldTop j
    · subst h
      have := b.2
      simp at hab'
      omega
    · rw [Matrix.updateRow_ne h, Matrix.submatrix_apply]
      exact hg a.1 b.1 (Fin.lt_iff_val_lt_val.mpr hab')

end GlobalTheory.ChernCalc

namespace GlobalTheory.ChernCalc

theorem ldNum_conj_lower {s : ℕ} (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (i j : Fin s) :
    ((g * G * gᴴ).submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det =
      (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) *
        (∑ l, g i l * (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then l else a.1)
          Subtype.val).det) * star (∏ a : {a : Fin s // (a : ℕ) < j + 1}, g a a) := by
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    det_submatrix_lt g hg, submatrix_ld_eq_updateRow, updateRow_mul_lower g G hg]
  erw [Matrix.det_mul]
  rw [det_frameRow g hg]
  have hrow : (fun c : {a : Fin s // (a : ℕ) < j + 1} => (g * G) i c) =
      ∑ l, g i l • (fun c : {a : Fin s // (a : ℕ) < j + 1} => G l c) := by
    funext c; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow, det_updateRow_finset_sum]
  simp only [submatrix_ld_eq_updateRow]

theorem ldPart_conj_lower : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) →
    IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧
      ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  intro s G g hG hg hdet
  have hgd : g.det = ∏ a, g a a := Matrix.det_of_lowerTriangular g (fun a b h => hg a b h)
  have hdiag : ∀ a, g a a ≠ 0 := by
    intro a
    have h := hdet.ne_zero
    rw [hgd] at h
    exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ _)
  have hP : ∀ m : ℕ, (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) ≠ 0 :=
    fun m => Finset.prod_ne_zero_iff.mpr fun a _ => hdiag a
  have hlm : ∀ m : ℕ, leadMinor G m ≠ 0 := fun m => by
    unfold leadMinor
    exact ((hG.submatrix Subtype.val_injective).det_pos).ne'
  have hsq : ∀ z w : ℂ, (z * w * star z).re = ‖z‖ ^ 2 * w.re := by
    intro z w
    rw [mul_comm z w, mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.re_mul_ofReal]
    ring
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    simp only [ldPart, Matrix.of_apply]
    rw [ldNum_conj_lower g G hg, leadMinor_conj_lower g G hg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.mul_apply, prod_lt_succ j (fun b => g b b)]
    simp only [Matrix.of_apply, ← mul_div_assoc, Pi.star_apply]
    rw [← Finset.sum_div, star_mul]
    have h1 := hP (j : ℕ)
    have h2 := hlm (j : ℕ)
    have h3 : star (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) ≠ 0 := star_ne_zero.mpr h1
    field_simp
  · unfold grD
    rw [leadMinor_conj_lower g G hg, leadMinor_conj_lower g G hg, hsq, hsq, prod_lt_succ i (fun b => g b b),
      norm_mul, mul_pow]
    have hn : ‖∏ a : {a : Fin s // (a : ℕ) < i}, g a a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hP _))
    rw [mul_assoc, mul_div_mul_left _ _ hn, mul_div_assoc]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

theorem exists_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → ∀ (hI : RingHom.ker π = I)
    (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left), IsGrpPullback X₀.A A (spMap π) i →
    IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
    ∀ (E : Submodule R (Crys κ (spMap π) X₀.A)), (∃ N : Submodule R (Crys κ (spMap π) X₀.A), IsCompl E N) →
      (∀ y : HdR X₀.A, y ∈ Fil X₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI X₀.A).Corr d y) →
      (∀ (a : 𝓞 F), ∀ d ∈ E, act κ (spMap π) X₀.rm a d ∈ E) →
      (∀ (c : 𝔠.elt) (φ : Crys κ (spMap π) X₀.A →ₗ[R] Crys κ (spMap π) X₀.A →ₗ[R] R),
        GlobalTheory.AbDual.IsCorrForm κ (spMap π) X₀.A X₀.A (X₀.P c) φ → ∀ a ∈ E, ∀ b ∈ E, φ a b = 0) →
      ∃ (X' : Obj F 𝔠 (Sp R)) (i' : X₀.A.left ⟶ X'.A.left) (pull : X₀.IsPullBy X' (spMap π) i'), liftFil κ pull.grp = E := by
  intro GD ADR ADC F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i h hA hg E hE hFil hstab hiso
  obtain ⟨A', _, i', h', hA', hg', rfl⟩ := exists_lift_abelian GD ADR κ hκ π hπ hI h hA hg E hE hFil
  haveI : IsCommMonObj A' := hA'.comm
  obtain ⟨rm', hrm'⟩ := GlobalTheory.T.abelian_lift_crystalline_comparison GD R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' (𝓞 F) X₀.rm hstab
  obtain ⟨l, l₁, l₂⟩ := GlobalTheory.AbDual.exists_prod_pullback h' h'
  have hsq : IsSquare i' l := ⟨l₁, l₂⟩
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hdiag₀ : (X₀.diag cp).IsLB := pull_isLB (X₀.isLB cp) _
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ hI hA' hg' hA' hg' h' h'
  have hP : ∀ c : 𝔠.elt, ∃ P : LB (G2 A').left, P.IsLB ∧ HasGen (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left) ∧ LBIso (P.pull l) (X₀.P c) := by
    intro c
    obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.AbDual.exists_isCorrForm C (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c)
    obtain ⟨P, hP, t₁, t₂, -, -, e⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ hI hA' hg' hA' hg' h' h' l₁ l₂
      hdiag₀ (X₀.pos cp hcp) hdiag₀ (X₀.pos cp hcp) (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c) hφ₀ (hiso c φ₀ hφ₀)
    exact ⟨P, hP, t₁, t₂, e⟩
  choose P' hP'LB hr₁ hr₂ hP'e using hP
  have wΔ : (lift (𝟙 X₀.A) (𝟙 X₀.A)).left ≫ l = i' ≫ (lift (𝟙 A') (𝟙 A')).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have pos' : ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' ((P' c).pull (lift (𝟙 A') (𝟙 A')).left) := by
    intro c hc
    haveI := hA'.smooth
    exact GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening R R₀ I κ hκ π hπ hI A' X₀.A i' h'.1 inferInstance _ (X₀.diag c) (pull_isLB (hP'LB c) _)
      (pull_isLB (X₀.isLB c) _) (lbIso_pull_square (hP'LB c) (X₀.isLB c) (hP'e c) _ _ i' wΔ) (X₀.pos c hc)
  have hL := pull_isLB (hP'LB cp) (lift (𝟙 A') (𝟙 A')).left
  have symm' : ∀ c, LBIso (P' c) ((P' c).pull (lift (snd A' A') (fst A' A')).left) := fun c ↦
    GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.isLB c)
      (X₀.symm c) (P' c) (hP'LB c) (hr₁ c) (hr₂ c) (hP'e c)
  have add' : ∀ c c', LBIso (P' c') (LB.div (P' (c + c')) (P' c)) := fun c c' ↦
    GlobalTheory.T.abelian_lift_de_rham_unique GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.P c')
      (X₀.P (c + c')) (X₀.isLB c) (X₀.isLB c') (X₀.isLB (c + c')) (X₀.add c c') (P' c) (P' c') (P' (c + c'))
      (hP'LB c) (hP'LB c') (hP'LB (c + c')) (hr₁ c) (hr₂ c) (hr₁ c') (hr₂ c') (hr₁ (c + c')) (hr₂ (c + c'))
      (hP'e c) (hP'e c') (hP'e (c + c'))
  have smul' : ∀ (a : 𝓞 F) c, LBIso (P' (a • c)) ((P' c).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) :=
    fun a c ↦ by
      haveI := X₀.rm.hom a
      haveI := rm'.hom a
      exact GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.rm.act a)
        (rm'.act a) (hrm' a) (X₀.P c) (X₀.P (a • c)) (X₀.isLB c) (X₀.isLB (a • c)) (X₀.smul a c) (P' c) (P' (a • c))
        (hP'LB c) (hP'LB (a • c)) (hr₁ c) (hr₂ c) (hr₁ (a • c)) (hr₂ (a • c)) (hP'e c) (hP'e (a • c))
  have ker' := GlobalTheory.T.real_mult_lift_divided_powers GD ADR ADC F 𝔠 R R₀ I κ hκ π hπ hI X₀ A' i' h' hA' hg' rm' hrm' P' l hsq hP'LB hr₁ hr₂ hP'e
    symm' add' smul' pos'
  let X' : Obj F 𝔠 (Sp R) :=
    { A := A', ab := hA', dim := hg', rm := rm', P := P', isLB := hP'LB, rig₁ := hr₁, rig₂ := hr₂, symm := symm',
      add := add', smul := smul', pos := pos', ker := ker' }
  exact ⟨X', i', ⟨h', hrm', ⟨l, hsq, fun c ↦ (hP'e c).symm⟩⟩, rfl⟩

end GlobalTheory.RMDeform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjSmoothOfGeometricallyReduced
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_smooth_of_geometricallyReduced : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G], LocallyOfFiniteType G.hom → GeometricallyReduced G.hom → Smooth G.hom := by
  intro K _ G _ h1 h2
  letI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  exact smooth_of_grpObj (f := G.hom)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValCmp

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem pt_eq_comp (M : RatModel k Ω) (z : M.Z) :
    M.pt = spMap (M.O z).val.toRingHom ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z) := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine h1.symm.trans ?_
  rw [← h2, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem hasDiv_of_forall_cDvr : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (J J' : Type) [Fintype J] (th : J → Ω) (e : J' → Ω) (D : ℕ), 1 ≤ D → Geo.Tor.IsNormalScheme M.Z → M.HasDiv e → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V), jK V ≫ ξ = spMap emb ≫ M.pt → ∀ j₀, e j₀ ≠ 0 → (∀ j, emb (e j / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V))) → M.HasDiv th := by
  intro k Ω _ _ _ _ _ M J J' _ th e D hD hN he H z
  obtain ⟨j₀, hj₀, hej⟩ := he z
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧
        ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V)) := by
    intro V _ _ _ hV φ hφ
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have e1 : jK V ≫ spMap φ = spMap emb ≫ spMap (M.O z).val.toRingHom := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact (hemb r).symm
    have hcomp : jK V ≫ (spMap φ ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z)) = spMap emb ≫ M.pt := by
      rw [pt_eq_comp M z, ← Category.assoc, e1, Category.assoc]
    refine ⟨emb, hemb, H V hV _ emb hcomp j₀ hj₀ fun j => ⟨φ ⟨_, hej j⟩, (hemb ⟨_, hej j⟩).symm⟩⟩
  have hmem : ∀ b, th b ^ D / e j₀ ∈ M.O z := by
    intro b
    obtain ⟨a, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (th b ^ D / e j₀)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ a := GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian (M.O z) a s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, h1, -⟩ := key V hV φ hφ
      obtain ⟨v, hv⟩ := h1 b
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  obtain ⟨emb, hemb, -, b, hb, w, hw⟩ := key V hV φ hφ
  have hu : IsUnit (⟨th b ^ D / e j₀, hmem b⟩ : M.O z) := by
    apply isUnit_of_map_unit φ
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, map_one, hw, ← hemb, ← map_mul]
    have e2 : algebraMap (M.O z) Ω ⟨th b ^ D / e j₀, hmem b⟩ * (e j₀ / th b ^ D) = 1 := by
      change th b ^ D / e j₀ * (e j₀ / th b ^ D) = 1
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      field_simp
    rw [e2, map_one]
  have hinv := ((RatModel.isUnit_O_iff _).1 hu).2
  refine ⟨b, hb, fun b' => ?_⟩
  have hp : (th b' / th b) ^ D ∈ M.O z := by
    have h3 := mul_mem (hmem b') hinv
    have e3 : th b' ^ D / e j₀ * (th b ^ D / e j₀)⁻¹ = (th b' / th b) ^ D := by
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      rw [inv_div, div_pow]
      field_simp
    simpa only [e3] using h3
  have hint : IsIntegral (M.O z) (th b' / th b) := by
    refine IsIntegral.of_pow (n := D) (by omega) ?_
    have := isIntegral_algebraMap (R := M.O z) (A := Ω) (x := ⟨_, hp⟩)
    simpa using this
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionEulerProductConvergentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_group_points_injective_mul : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  first | exact @GlobalTheory.GrpPullback.points_conj | exact GlobalTheory.GrpPullback.points_conj | (intros; apply GlobalTheory.GrpPullback.points_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_sectionBall_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  first | exact @GlobalTheory.HSNef.bl_finite | exact GlobalTheory.HSNef.bl_finite | (intros; apply GlobalTheory.HSNef.bl_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundRightStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_bound_right : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → RowsB B := by
  first | exact @GlobalTheory.RowsAtRealTBClose.rowsB_of_decay | exact GlobalTheory.RowsAtRealTBClose.rowsB_of_decay | (intros; apply GlobalTheory.RowsAtRealTBClose.rowsB_of_decay <;> assumption)
end

