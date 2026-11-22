import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0100
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

def lowP {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.LPidx w => q.1) y

def lowS {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.Lstidx w => q.1) x

def utc {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : G.UT m → ℂ := fun q => u q.1.1 q.1.2

def lsc {m : ℕ} (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) : C2.Lstidx w → ℂ := fun q => l q.1.1 q.1.2

def SplitUT : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)), ∃ e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT m → ℂ),
    MeasurePreserving e volume volume ∧ ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ

def UTLeft : Prop :=
  ∀ (m : ℕ) (a : Matrix (Fin m) (Fin m) ℂ), a ∈ C2.UTset m →
    MeasurePreserving (fun u : G.UT m → ℂ => utc (a * G.upper u)) volume volume

def LstLeft : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ x0 : C2.Lstidx w → ℂ,
    MeasurePreserving (fun x : C2.Lstidx w → ℂ => lsc w (lowS w x0 * lowS w x)) volume volume ∧
    ∀ x, lowS w x0 * lowS w x = lowS w (lsc w (lowS w x0 * lowS w x))

def MinorsLU : Prop :=
  ∀ (r : ℕ) (L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), L ∈ C2.LTset (r + 1) → U ∈ C2.UTset (r + 1) →
    (L * M * U).det = M.det ∧
      ((L * M * U).submatrix Fin.castSucc Fin.castSucc).det = (M.submatrix Fin.castSucc Fin.castSucc).det

def PhiTopCoords : Prop :=
  ∀ (m : ℕ) (σ w : Equiv.Perm (Fin m)) (d d' : Fin m → ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat m → V), (∀ a, d' a ≠ 0) → U.hMat σ d = C2.monoP w d' →
    U.PhiTop (p := m) (s := 0) U.betaU σ d Φ (fun x => x.elim0) =
      ∫ q : (C2.LPidx w → ℂ) × (G.UT m → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w q.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper q.2)))) •
          Φ (Matrix.of.symm (lowP w q.1 * C2.monoP w d' * G.upper q.2))

def ExistsHaarStabilizer : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ0 : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ0

def DisintN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 μN : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → B.IsHaarOn (Nset k r) μN →
    ∃ c : NNReal, 0 < c ∧ μN = c • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r z (G.upper p.1) * Matrix.of p.2))

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FourthExpansionIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem vec_wsum (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (p : Fin (2 * r + k + 1)) :
    v p = ∑ w : Fin (k + 1), v (wI k r w) * (if p = wI k r w then 1 else 0) := by
  by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
  · rw [Finset.sum_eq_single ⟨p.val - r, by omega⟩]
    · have : p = wI k r ⟨p.val - r, by omega⟩ := by ext; simp [wI]; omega
      rw [if_pos this, mul_one, ← this]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; apply hb; ext; simp only [h, wI]; omega
    · simp
  · rw [hv p (by omega)]; symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg, mul_zero]
    intro h; apply hp; rw [h]; simp only [wI]; omega

theorem keyS_wI (k r : ℕ) (w : Fin (k + 1)) : keyS k r (wI k r w) = r + w.val + r := by
  have := w.isLt
  unfold keyS wI; simp only; rw [if_neg (by omega)]

theorem fourth_expansion_identity : ExpansionDualCovector := by
  intro A _ _ M _ _ k r z' yb E La y i0 s h t ell hs hj hG hR hh ht hz' hyb hzy hya hyi0
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef
  set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun l => sR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef
  have hfv : ∀ l, (f l).val = 2 * (i0 + s'' + 1) + k - (i.succAbove l).val := by intro l; simp [f, sR, esI]
  have hfk : ∀ l, keyS k _ (f l) = (i.succAbove l).val := by intro l; simp only [f]; rw [keyS_sR]
  set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef
  have hew : ∀ w, StrictMono (fun l => keyS k _ (ew w l)) := by
    intro w
    have e : (fun l => keyS k _ (ew w l)) = Fin.snoc (α := fun _ => ℕ) (fun l => keyS k (i0 + s'' + 1) (f l)) (keyS k (i0 + s'' + 1) (wI k (i0 + s'' + 1) w)) := by
      funext l
      induction l using Fin.lastCases with
      | last => simp [ew]
      | cast l => simp [ew]
    rw [e]
    apply strictMono_snoc
    · intro a b hab; simp only [hfk]; exact Fin.strictMono_succAbove _ hab
    · intro l; rw [hfk, keyS_wI]; have := (i.succAbove l).isLt; omega
  have hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _ := by
    intro w j
    constructor
    · intro hj
      by_contra hne
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have := congrArg Fin.val hj
      simp only [ew, Fin.snoc_castSucc] at this
      rw [hfv] at this; simp [wI] at this; have := (i.succAbove l).isLt; omega
    · rintro rfl; simp [ew]
  have hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
      else y (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'') := by
    intro w
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]
    · simp only [Matrix.of_apply, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one, Fin.succAbove_last]
      have hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
          else y (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc =
          (starRingEnd ℂ).mapMatrix (Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val) := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply]
        rw [if_neg (Fin.succAbove_ne i a)]
        simp only [ew, Fin.snoc_castSucc]
        have hb := (i.succAbove b).isLt
        have hbne : (i.succAbove b).val ≠ i0 := fun h' => Fin.succAbove_ne i b (Fin.ext h')
        have hane : (i.succAbove a).val ≠ i0 := fun h' => Fin.succAbove_ne i a (Fin.ext h')
        rw [hya _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; omega⟩, hfv]
        rw [show 2 * (i0 + s'' + 1) + k - (2 * (i0 + s'' + 1) + k - (i.succAbove b).val) = (i.succAbove b).val by omega]
        simp [i]
      rw [hsub, ← RingHom.map_det, third_polynomial_expansion, starRingEnd_apply]
      simp only [Fin.val_last]
      rw [show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]
      norm_num
    · intro j _ hj
      simp only [Matrix.of_apply, if_pos rfl]
      rw [if_neg (fun h' => hj ((hew_last w j).mp h'))]; simp
    · simp
  have harg : ell + (((i0 + s'' + 1 : ℕ)) : ℂ) - 1 = ell + ((i0 + s'' : ℕ) : ℂ) := by push_cast; ring
  have hAA : AAv k (i0 + s'' + 1) E y (i0 + s'' + 1) le_rfl ell =
      ((-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'')) • ∑ w, yb (wI k _ w) •
        qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ)) := by
    unfold AAv
    rw [harg]
    rw [sum_lin (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => y (Fin.castLE le_rfl a) p) i
      (fun w => yb (wI k _ w)) (fun w p => if p = wI k _ w then 1 else 0)
      (fun p => by rw [hyi0 _ (by simp [i])]; exact vec_wsum k _ yb hyb p)]
    rw [Finset.smul_sum]
    congr 1; ext w
    rw [sum_single (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0)
      else y (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]
    · intro a p hp
      by_cases ha : a = i
      · rw [if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩
      · rw [if_neg ha]
        have hane : a.val ≠ i0 := fun h' => ha (Fin.ext h')
        rw [hya _ _ (by simpa using hane)]
        rw [if_neg]
        rintro ⟨hp1, hp2⟩
        apply hp
        refine ⟨Fin.castSucc ⟨if 2 * (i0 + s'' + 1) + k - p.val < i0 then 2 * (i0 + s'' + 1) + k - p.val
          else 2 * (i0 + s'' + 1) + k - p.val - 1, by split_ifs <;> omega⟩, ?_⟩
        ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega
    · intro c hc hS; exact uniq_key (keyS k _) (keyS_inj k _) _ _ (hew w) hc hS
  have hhead : AAv k (i0 + s'' + 1) E y i0 (by omega) ell =
      star h.det • qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hya _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * (i0 + s'' + 1) + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * (i0 + s'' + 1) + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dif_pos ha, dif_neg hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hya _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k (i0 + s'' + 1) i0 (by omega) b).val = 2 * (i0 + s'' + 1) + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ i0 + s'' + 1) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dif_pos a.isLt, dif_pos (by omega)]
      congr 2
      apply Fin.ext; simp only; omega
  have hP := fourth_peeling_identity A k (i0 + s'') z' yb E hG i ell hz' hyb
  have hLa : (∑ w, yb (wI k _ w) • La (qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ)))) =
      star t • La (qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1)) := by
    have := la_congr hR hP
    rw [map_sum] at this
    simp only [map_smul] at this
    rw [herm_swap, hzy] at this
    exact this
  have hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s'' := by
    rw [show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]
  rw [hAA, hhead, map_smul, map_smul, map_sum]
  simp only [map_smul]
  rw [hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show s'' + 2 - 1 = s'' + 1 by omega]
  simp only [star_mul', star_pow, star_neg, star_sgnW]
  have h1 := star_ne_zero.mpr hh
  have h2 := star_ne_zero.mpr ht
  rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h3 | h3 <;> rw [h3] <;> field_simp <;> ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtEpart
section
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma Rw_cons' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : Mat k r) (w : List (Mat k r))
    (f : Mat k r → E) : Rw (X :: w) f = Dx (false, X) (Rw w f) := by
  rfl

lemma ckOn_Rw_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (Mat k r)} {f : Mat k r → E}
    (hf : CkOn ⊤ UU f) {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) : CkOn ⊤ UU (Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    rw [Rw_cons']
    have h := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    exact CkOn_Dx (x := (false, X)) (hw X (by simp)) (by simpa using h)

theorem hasDerivAt_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ Y ∈ e.2, inLie k r Y) →
      HasDerivAt (fun s => C6.Epart fib es (crv (false, X) g s))
        (∑ i : Fin es.length, C6.Epart fib (es.set i ((es.get i).1, X :: (es.get i).2)) g) 0 := by
  intro es
  induction es with
  | nil =>
    intro _
    simp only [C6.Epart, List.map_nil, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasDerivAt_const _ _
  | cons e es ih =>
    intro hes
    have h1 : HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s)) (Rw (X :: e.2) (fib e.1) g) 0 := by
      rw [Rw_cons']
      exact CkOn_diff (x := (false, X)) hX
        (sCkOn_mono le_top (ckOn_Rw_top (hfib e.1) (hes e (by simp)))) hg hg.1
    have h2 := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have h3 := h1.mul h2
    show HasDerivAt (fun s => Rw e.2 (fib e.1) (crv (false, X) g s) * C6.Epart fib es (crv (false, X) g s)) _ 0
    refine h3.congr_deriv ?_
    have key : ∀ f : Fin (e :: es).length → C6.EndH Wp Wq,
        ∑ i, f i = f ⟨0, by simp⟩ + ∑ i : Fin es.length, f i.succ := fun f => Fin.sum_univ_succ f
    rw [key, crv_zero]
    simp [C6.Epart, Finset.mul_sum]

lemma list_sum_apply {α : Type*} (L : List α) (f : α → C6.EndH Wp Wq) (x : Wq →L[ℂ] Wp) :
    (L.map f).sum x = (L.map fun t => f t x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma list_sum_smul {α : Type*} (L : List α) (f : α → ℂ) (E : C6.EndH Wp Wq) :
    (L.map fun t => f t • E).sum = (L.map f).sum • E := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, add_smul]

lemma dscal_es (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) :
    ∀ t' ∈ dscal D X t, t'.es = t.es := by
  intro t' ht'
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h <;> (try split_ifs) <;> rfl

theorem hasDerivAt_cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) {X : Mat k r} (hX : inLie k r X) {g : Mat k r} (hg : g ∈ GPos D)
    (t : CT k r nf) (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) (hes : ∀ e ∈ t.es, ∀ Y ∈ e.2, inLie k r Y) :
    HasDerivAt (fun s => cv D fib t (crv (false, X) g s)) (((dco D X t).map fun t' => cv D fib t' g).sum) 0 := by
  have h1 := hasDerivAt_cvs D X g t hnz hG
  have h2 := hasDerivAt_epart D fib hfib hX hg t.es hes
  have h3 := h1.smul h2
  show HasDerivAt (fun s => cvs D t (crv (false, X) g s) • C6.Epart fib t.es (crv (false, X) g s)) _ 0
  refine h3.congr_deriv ?_
  rw [crv_zero, dco, List.map_append, List.sum_append, add_comm]
  symm
  congr 1
  · rw [← list_sum_smul]
    exact congrArg List.sum (List.map_congr_left (fun t' ht' => by simp only [cv, dscal_es D X t t' ht']))
  · simp only [dfib, List.map_ofFn, List.sum_ofFn, Function.comp_def, cv, cvs, Finset.smul_sum]

abbrev FS (k r nf : ℕ) : Type := List (CT k r nf × List (Mat k r))

def shape (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (L : FS k r nf) (g : Mat k r) : Wq →L[ℂ] Wp :=
  (L.map fun e => cv D fib e.1 g (Rw e.2 F g)).sum

def stepOne (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) : FS k r nf :=
  (dco D X e.1).map (fun t' => (t', e.2)) ++ [(e.1, X :: e.2)]

def step (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (L : FS k r nf) : FS k r nf := L.flatMap (stepOne D X)

def steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} (w : List (Mat k r)) (L : FS k r nf) : FS k r nf := w.foldr (step D) L

def Good {nf : ℕ} (L : Finset (Fin (r + 2))) (e : CT k r nf × List (Mat k r)) : Prop :=
  (∀ l, (e.1.a l ≠ 0 ∨ e.1.b l ≠ 0) → l ∈ L ∨ l = Fin.last (r + 1)) ∧
  (∀ x ∈ e.1.es, ∀ Y ∈ x.2, inLie k r Y) ∧ (∀ Y ∈ e.2, inLie k r Y)

private lemma dscal_support_prop_of_support_prop (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf)
    (P : Fin (r + 2) → Prop) (hP : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → P l) :
    ∀ t' ∈ dscal D X t, ∀ l, (t'.a l ≠ 0 ∨ t'.b l ≠ 0) → P l := by
  intro t' ht' l hl
  simp only [dscal, List.mem_append, List.mem_singleton, List.mem_ofFn, Set.mem_range] at ht'
  rcases ht' with ((h | ⟨m, h⟩) | ⟨m, h⟩) | h <;> subst h
  · exact hP l hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inl hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl with hm
    · exact hP l hl
    · by_cases hlm : l = m
      · subst hlm; exact hP l (Or.inr hm)
      · apply hP l
        simpa [Pi.single_apply, hlm] using hl
  · split_ifs at hl <;> exact hP l hl

lemma good_step (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {X : Mat k r} (hX : inLie k r X)
    {e : CT k r nf × List (Mat k r)} (he : Good L e) :
    ∀ e' ∈ stepOne D X e, Good L e' ∧ e'.2.length ≤ e.2.length + 1 := by
  unfold Good at he ⊢
  obtain ⟨hab, hes, hw⟩ := he
  intro e' he'
  simp only [stepOne, List.mem_append, List.mem_map, List.mem_singleton] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · refine ⟨⟨?_, ?_, hw⟩, by simp⟩
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · exact dscal_support_prop_of_support_prop D X e.1 _ hab t' ht'
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        exact hab
    · simp only [dco, List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · rw [dscal_es D X e.1 t' ht']; exact hes
      · simp only [dfib, List.mem_ofFn, Set.mem_range] at ht'
        obtain ⟨i, rfl⟩ := ht'
        intro x hx Y hY
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hes x hx Y hY
        · rcases List.mem_cons.1 hY with rfl | hY
          · exact hX
          · exact hes _ (by simp) Y hY
  · refine ⟨⟨hab, hes, ?_⟩, by simp⟩
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact hX
    · exact hw Y hY

lemma good_steps (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ (Lf : FS k r nf), (∀ e ∈ Lf, Good L e) →
      ∀ e' ∈ steps D w Lf, Good L e' ∧ ∃ e ∈ Lf, e'.2.length ≤ e.2.length + w.length := by
  intro w
  induction w with
  | nil =>
    intro _ Lf hLf e' he'
    exact ⟨hLf e' he', e', he', by simp⟩
  | cons X w ih =>
    intro hw Lf hLf e' he'
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨hg, e, he, hlen⟩ := ih hw' Lf hLf e'' he''
    obtain ⟨hg', hlen'⟩ := good_step D hX hg e' he'
    refine ⟨hg', e, he, ?_⟩
    simp only [List.length_cons]
    omega

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCKer
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem sum_sub_weight {Z J : Type} (P : Finset Z) (Y : J → Finset Z) (hY : ∀ j, Y j ⊆ P) (a : J → Z → ℂ)
    (j : J) (g : Z → ℂ) :
    ∑ p : P, (if (p : Z) ∈ Y j then a j p else 0) * g p = ∑ z ∈ Y j, a j z * g z := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun z => if z ∈ Y j then a j z * g z else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (hY j)]

theorem psd_wcompress {Z J : Type} [Fintype J] (P : Finset Z) (H : Z → Z → ℂ) (hH : TB.PSDOn P H)
    (Y : J → Finset Z) (a : J → Z → ℂ) (hY : ∀ j, Y j ⊆ P) :
    Matrix.PosSemidef (Matrix.of fun j k : J =>
      ∑ z ∈ Y j, ∑ z' ∈ Y k, star (a j z) * H z z' * a k z') := by
  let B : Matrix P J ℂ := Matrix.of fun x j => if (x : Z) ∈ Y j then a j x else 0
  have h := hH.conjTranspose_mul_mul_same B
  convert h using 1
  ext j k
  have inner : ∀ x : P, ∑ y : P, star (if (x : Z) ∈ Y j then a j x else 0) * H x y *
      (if (y : Z) ∈ Y k then a k y else 0) =
      (if (x : Z) ∈ Y j then star (a j x) else 0) * ∑ z' ∈ Y k, a k z' * H x z' := by
    intro x
    rw [← sum_sub_weight P Y hY a k (fun z' => H x z'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [inner]
  rw [sum_sub_weight P Y hY (fun j z => star (a j z)) j (fun z => ∑ z' ∈ Y k, a k z' * H z z')]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z' _ => ?_
  ring

theorem psd_herm {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : K q p = conj (K p q) := by
  have h := hK.1.apply ⟨p, hp⟩ ⟨q, hq⟩
  simp only [Matrix.of_apply] at h
  rw [← h]
  simp

theorem psd_diag {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p : Z} (hp : p ∈ P) :
    0 ≤ K p p := by
  have h := hK.diag_nonneg (i := ⟨p, hp⟩)
  simpa [Matrix.of_apply] using h

theorem psd_entry {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) : ‖K p q‖ ^ 2 ≤ (K p p).re * (K q q).re := by
  let f : Fin 2 → P := ![⟨p, hp⟩, ⟨q, hq⟩]
  have h := (hK.submatrix f).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.of_apply, f, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at h
  have hqp := psd_herm P K hK hp hq
  rw [hqp, Complex.mul_conj] at h
  have hpd := psd_diag P K hK hp
  have hqd := psd_diag P K hK hq
  have e1 : (K p p) = ((K p p).re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hpd).2.symm]
  have e2 : (K q q) = ((K q q).re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hqd).2.symm]
  rw [e1, e2, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.zero_le_real] at h
  linarith

theorem psd_entry_le {Z : Type} (P : Finset Z) (K : Z → Z → ℂ) (hK : TB.PSDOn P K) {p q : Z} (hp : p ∈ P)
    (hq : q ∈ P) (B : ℝ) (hBp : ‖K p p‖ ≤ B) (hBq : ‖K q q‖ ≤ B) : ‖K p q‖ ≤ B := by
  have h := psd_entry P K hK hp hq
  have hp' : (K p p).re ≤ B := (Complex.re_le_norm _).trans hBp
  have hq' : (K q q).re ≤ B := (Complex.re_le_norm _).trans hBq
  have hpd := (Complex.nonneg_iff.mp (psd_diag P K hK hp)).1
  have hqd := (Complex.nonneg_iff.mp (psd_diag P K hK hq)).1
  have hB : 0 ≤ B := (norm_nonneg _).trans hBp
  have h2 : ‖K p q‖ ^ 2 ≤ B ^ 2 := h.trans (by nlinarith)
  nlinarith [norm_nonneg (K p q)]

end

end Formalism.FourierDecayAlt.P.PBC
end

