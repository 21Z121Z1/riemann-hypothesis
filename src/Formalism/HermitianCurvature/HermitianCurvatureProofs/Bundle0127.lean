import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0118
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0116
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ListMapSumApply
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def TermClause (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ (P : Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) ∧
      ∀ g ∈ C6.domL D L, T.coef g = (P g * C6.monoM D a b c g) • C6.Epart fib es g

theorem toFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) {o κ : ℕ} :
    ∀ Θ : DiffOp k r Wp Wq, TermClause D fib L o κ Θ →
      ∃ Lf : FS k r nf, (∀ e ∈ Lf, Good L e ∧ e.1.q.totalDegree ≤ κ ∧ e.2.length + fo e.1.es ≤ o) ∧
        (∀ T ∈ Θ, ∃ e ∈ Lf, e.2 = T.word) ∧
        ∀ (H : Mat k r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL D L, opApply Θ H g = shape D fib H Lf g := by
  intro Θ hΘ
  induction Θ with
  | nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨Lf, h1, h2, h3⟩ := ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩ := hΘ T (by simp)
    refine ⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, hqdeg, hlen⟩
        unfold Good
        refine ⟨?_, hes, T.word_lie⟩
        intro l hl
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hab l hcon.1 hcon.2
        rcases hl with hl | hl
        · exact hl ha
        · exact hl hb
      · exact h1 e' he'
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨e', he', h⟩ := h2 T' hT'
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · intro H g hg
      have h3' := h3 H g hg
      simp only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢
      rw [h3', hcoef g hg]
      congr 1
      simp only [cv, cvs]
      rw [hq g]
      rfl

section mk

variable [FiniteDimensional ℂ Wp]

open Classical in

def mkTerm (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (e : CT k r nf × List (Mat k r)) : DTerm k r Wp Wq where
  coef := cv D fib e.1
  coefAdj := fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 x)
  word := if ∀ X ∈ e.2, inLie k r X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec _ A B

lemma mkTerm_word (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    {e : CT k r nf × List (Mat k r)} (h : ∀ X ∈ e.2, inLie k r X) : (mkTerm D fib e).word = e.2 := by
  dsimp only [mkTerm]
  rw [if_pos h]

lemma opApply_mk (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  simp only [Function.comp_apply]
  rw [mkTerm_word D fib (hL e he)]
  rfl

end mk

def compFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (L₁ L₂ : FS k r nf) : FS k r nf :=
  L₁.flatMap fun e₁ => (steps D e₁.2 L₂).map fun e => (mulCT e₁.1 e.1, e.2)

lemma compFS_bound (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by
  intro e he
  simp only [compFS, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e₁, he₁, e', he', rfl⟩ := he
  obtain ⟨hG₁, hq₁, ho₁⟩ := h₁ e₁ he₁
  obtain ⟨hG₁a, hG₁b, hG₁c⟩ := hG₁
  have hG' := (good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1
  obtain ⟨hG'a, hG'b, hG'c⟩ := hG'
  obtain ⟨e₂, he₂, hdeg, hlen⟩ := bound_steps D e₁.2 L₂ e' he'
  obtain ⟨-, hq₂, ho₂⟩ := h₂ e₂ he₂
  have hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂ := by
    intro l₁ l₂
    simp [fo, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold Good
    refine ⟨?_, ?_, hG'c⟩
    · intro l hl
      simp only [mulCT, Pi.add_apply] at hl
      by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
      · exact hG₁a l h1
      · apply hG'a l
        push_neg at h1
        rcases hl with hl | hl
        · left; omega
        · right; omega
    · intro x hx Y hY
      simp only [mulCT, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hG₁b x hx Y hY
      · exact hG'b x hx Y hY
  · simp only [mulCT]
    have hmul := MvPolynomial.totalDegree_mul e₁.1.q e'.1.q
    have hw : e₁.2.length ≤ o₁ := by omega
    have := Nat.mul_le_mul_left (2 * r + 2) hw
    omega
  · simp only [mulCT]
    rw [hfo]
    omega

lemma list_map_sum_apply {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by
  rw [map_list_sum, List.map_map]
  rfl

private lemma rw_congr_on_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ {H H' : Mat k r → (Wq →L[ℂ] Wp)},
      (∀ g ∈ C6.domL D L, H g = H' g) → ∀ g ∈ C6.domL D L, Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ H H' hH g hg; exact hH g hg
  | cons X w ih =>
    intro hw H H' hH g hg
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH
    rw [Rw_cons', Rw_cons', Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hGV : g ∈ GV k r := ((mem_domL D L g).1 hg).1
    have hV0 : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
    filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht
    apply ih'
    rw [mem_domL]
    exact ⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩

theorem comp_identity (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by
  show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _
  unfold compFS
  rw [shape_flatMap']
  congr 1
  refine List.map_congr_left fun e₁ he₁ => ?_
  obtain ⟨-, -, hw⟩ := hg₁ e₁ he₁
  rw [rw_congr_on_domL D L e₁.2 hw hH g hg]
  rw [expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]
  unfold shape
  rw [list_map_sum_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasSgsPow
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem one_le_gN (hNI : NormInv) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : 1 ≤ B.gN g :=
  ((hNI k r).2 g hg).2

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

def trivS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

private lemma measurable_det_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) : Measurable fun p => (F p).det := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hF (σ i) i)

private lemma measurable_inv_apply_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) : ∀ i j, Measurable fun p => (F p)⁻¹ i j := by
  intro i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine (measurable_det_of_measurable_entries hF).inv.mul (measurable_det_of_measurable_entries fun a c => ?_)
  rcases eq_or_ne a j with h | h <;> simp [Matrix.updateRow_apply, h, hF a c, measurable_const]

private lemma measurable_mul_apply_of_measurable_entries {α : Type*} [MeasurableSpace α] {n : ℕ} {F G : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i j, Measurable fun p => F p i j) (hG : ∀ i j, Measurable fun p => G p i j) :
    ∀ i j, Measurable fun p => (F p * G p) i j := by
  intro i j
  simp_rw [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hF i l).mul (hG l j)

theorem meas_sgs_pow (γ : Mx k r) (b : ℝ) : Measurable fun p : B.SS k r => B.gN (B.sgs p γ) ^ (-b) := by
  have e : ∀ f : B.SS k r → Mt k r, Measurable f → ∀ i j, Measurable fun p => Matrix.of (f p) i j :=
    fun f hf i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)
  have h11 := e (fun p => p.1.1) (measurable_fst.comp measurable_fst)
  have h12 := e (fun p => p.1.2) (measurable_snd.comp measurable_fst)
  have h22 := e (fun p => p.2.2) (measurable_snd.comp measurable_snd)
  have h21 := e (fun p => p.2.1) (measurable_fst.comp measurable_snd)
  have hγ : ∀ i j, Measurable fun _ : B.SS k r => γ i j := fun _ _ => measurable_const
  have hS : ∀ i j, Measurable fun p => B.sgs p γ i j := by
    unfold B.sgs
    exact measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_mul_apply_of_measurable_entries (measurable_inv_apply_of_measurable_entries h11)
      (measurable_inv_apply_of_measurable_entries h12)) hγ) h22) h21
  unfold B.gN
  refine Measurable.pow_const (Measurable.sqrt ?_) _
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.measurable.comp (hS i j)

def fZ (b : ℝ) (g : B.Mat k r) : ℂ →L[ℂ] ℂ := ((B.gN g ^ (-b) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)

theorem fZ_inCC (hNI : NormInv) (b : ℝ) : B.InCC b 0 (fZ (k := k) (r := r) b) := by
  have hge : ∀ g ∈ B.GV k r, 1 ≤ B.gN g := fun g hg => ((hNI k r).2 g hg).2
  have hcont : Continuous fun g : B.Mat k r => B.gN g := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)
  refine ⟨1, ?_, ?_⟩
  · intro g₀ hg₀
    refine ⟨{g | 1 / 2 < B.gN g}, fZ b, isOpen_lt continuous_const hcont,
      show (1 / 2 : ℝ) < B.gN g₀ by linarith [hge g₀ hg₀], ?_, fun g _ _ => rfl⟩
    have hc : ContinuousOn (fun g : B.Mat k r => fZ (k := k) (r := r) b g) {g | 1 / 2 < B.gN g} := by
      have h0 : ContinuousOn (fun g : B.Mat k r => B.gN g ^ (-b)) {g | 1 / 2 < B.gN g} :=
        hcont.continuousOn.rpow_const fun g hg =>
          Or.inl (ne_of_gt (by have : (1 / 2 : ℝ) < B.gN g := hg; linarith))
      exact (Complex.continuous_ofReal.comp_continuousOn h0).smul continuousOn_const
    exact (contDiffOn_zero.2 hc).of_le (by norm_num)
  · intro u v _ _ hlen g hg
    obtain rfl : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hpos : 0 < B.gN g := lt_of_lt_of_le one_pos (hge g hg)
    simp only [B.dLR, B.Rw, List.foldr_nil, fZ, norm_smul, Complex.norm_real, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le (-b))]
    rw [Real.rpow_neg hpos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos b).ne']

theorem orb_gN (hJC : JF.JConv) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (hNI : NormInv) {b : ℝ}
    (hThr : JF.TransportedAlt k r b 0) {γ : Mx k r} (hγ : γ ∈ JF.Om k r D.z D.z') :
    Integrable (fun p => B.gN (B.sgs p γ) ^ (-b)) D.μSS := by
  obtain ⟨-, h2⟩ := hJC k r ℂ ℂ (trivS D) b (fZ b) hThr (fZ_inCC (k := k) (r := r) hNI b)
  obtain ⟨bd, hbd, hle⟩ := h2 {γ} isCompact_singleton (Set.singleton_subset_iff.2 hγ)
  refine hbd.mono' (meas_sgs_pow γ b).aestronglyMeasurable ?_
  filter_upwards [hle γ rfl] with p hp

  have e : B.rho (trivS D) p (fZ b) γ = fZ b (B.sgs p γ) := by
    ext
    simp [B.rho, trivS]
  have e2 : ‖fZ (k := k) (r := r) b (B.sgs p γ)‖ = ‖B.gN (B.sgs p γ) ^ (-b)‖ := by
    simp [fZ, norm_smul, Complex.norm_real]
  rw [← e2, ← e]
  exact hp

end Formalism.FourierDecayAlt.P.S3dx6
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Rad

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_uEquiv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : Mx k r) {h h' : Mx k r} (hh : h ∈ UWset k r D.z)
    (hh' : h' ∈ UWset k r D.z') : B.JF D F (h * g * h') = (D.π h).comp ((B.JF D F g).comp (D.π' h')) := by
  have := P.B5.haar_sigmaFinite D.haarW
  have := P.B5.haar_sigmaFinite D.haarN
  have := P.B5.haar_sigmaFinite D.haarW'
  exact bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

theorem radJFExists : RadJFExists := by
  intro Wp Wq _ _ _ _ _ _ Pa z z' π π' D F _hP hz hz' hπ hπ' hF
  subst hz hz' hπ hπ'
  classical
  let Φf : Fn Pa.k Pa.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) c g else 0
  have hsm := sf_resG (jf_smoothLev D F hF.1)
  have hmem : Φf ∈ RadSp Pa.k Pa.r D.z D.z' D.π D.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = 0
      rw [if_neg (by simpa using hx)]
    · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
        ⟨hx₀.1, wCell_mem_omPlus D.z_mem D.z'_mem hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
      have hV : IsOpen {x : (Fin Pa.r → ℂ) × Mx Pa.k Pa.r | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2} :=
        ((P.Qx3.isOpen_OmX Pa.r).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((P.Qx5.GGl_continuous Pa.k Pa.r D.z D.z').comp continuous_snd))
      refine ⟨U ∩ {x | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2}, Fe, hU.inter hV,
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
      rw [if_pos hxD]
      exact hΦ x hx.1 hxG
    · have hx' : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := by simpa using hx
      show (if (x.1, h * x.2 * h') ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 (h * x.2 * h') else 0) =
        (D.π h).comp ((if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0).comp (D.π' h'))
      rw [if_pos (domR_uw hx hh hh'), if_pos hx']
      unfold resG
      have e : wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * (h * x.2 * h') =
          h * (wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) * h' := by
        have hc := P.Qx3.wlist_comm (k := Pa.k) (Fin.last Pa.r) x.1
          ((List.finRange Pa.r).filter fun a => a.val < (Fin.last Pa.r).val)
          (fun a ha => by simpa using (List.mem_filter.1 ha).2) (P.Qx3.uw_glev (Fin.last Pa.r) hh)
        change wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * h = h * wCell Pa.k Pa.r (Fin.last Pa.r) x.1 at hc
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
      rw [e, jf_uEquiv D F _ hh hh']
      ext v
      simp
  exact ⟨⟨Φf, hmem⟩, fun x hx => by
    show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
    rw [if_pos (by simpa using hx)]⟩

end Formalism.FourierDecayAlt.P5
end
end

