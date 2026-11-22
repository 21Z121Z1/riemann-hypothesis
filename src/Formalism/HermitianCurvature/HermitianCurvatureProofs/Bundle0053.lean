import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0049

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeRulesA1
section
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma one_le_gN {g : Mat k r} (hg : g ∈ GV k r) : 1 ≤ gN g := (Formalism.FourierDecayAlt.P.norm_of_inverse k r g hg).2

lemma gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := lt_of_lt_of_le one_pos (one_le_gN hg)

lemma rpow_mono_G {g : Mat k r} (hg : g ∈ GV k r) {a b : ℝ} (h : a ≤ b) : gN g ^ a ≤ gN g ^ b :=
  Real.rpow_le_rpow_of_exponent_le (one_le_gN hg) h

lemma loss_bound_nonneg (r : ℕ) : 0 ≤ C2.B0 r := by unfold C2.B0; positivity

lemma top_ge_nat (m : ℕ) : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

lemma ckOn_top_nat {f : Mat k r → E} (hf : CkOn (⊤ : ℕ∞) (GV k r) f) (m : ℕ) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (top_ge_nat m), hff⟩

lemma top_ne_zero' : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp

lemma top_succ_le : (((⊤ : ℕ∞)) : WithTop ℕ∞) + 1 ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ⊤)

lemma ckOn_op_top {f : Mat k r → E} {X : Mat k r} (b : Bool) (hf : CkOn (⊤ : ℕ∞) (GV k r) f)
    (hX : inLie k r X) : CkOn (⊤ : ℕ∞) (GV k r) (op b X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, op' b X f', hU, hgU, ?_, ?_⟩
  · exact (hc.fderiv_of_isOpen hU top_succ_le).clm_apply (vf b X).contDiff.contDiffOn
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hc.differentiableOn top_ne_zero').differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_ext b hU hg hgG hd hff hX).deriv

lemma ckOn_W_top {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn (⊤ : ℕ∞) (GV k r) f) : CkOn (⊤ : ℕ∞) (GV k r) (W w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [W_cons]
    exact ckOn_op_top x.1 (ih fun y hy => hw y (List.mem_cons_of_mem _ hy)) (hw x List.mem_cons_self)

lemma right_word_eq_word (v : List (Mat k r)) (f : Mat k r → E) : Rw v f = W (lr [] v) f := by
  rw [← dLR_eq]; rfl

lemma foldr_LdV_eq_W_lr (u : List (Mat k r)) (f : Mat k r → E) : u.foldr LdV f = W (lr u []) f := by
  rw [← dLR_eq]; rfl

lemma allLie_lr' {u v : List (Mat k r)} (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, inLie k r X) :
    AllLie (lr u v) := by
  intro x hx
  simp only [lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

lemma L_Rw_comm {X : Mat k r} (hX : inLie k r X) : ∀ (v : List (Mat k r)), (∀ Y ∈ v, inLie k r Y) →
    ∀ K : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      Rw v (LdV X K) g = LdV X (Rw v K) g := by
  intro v
  induction v with
  | nil => intro _ K _ g _; rfl
  | cons Y v ih =>
    intro hv K hK g hg
    have hv' : ∀ Z ∈ v, inLie k r Z := fun Z hZ => hv Z (List.mem_cons_of_mem _ hZ)
    have hY := hv Y List.mem_cons_self
    show op false Y (Rw v (LdV X K)) g = op true X (op false Y (Rw v K)) g
    rw [op_congr false hY (ih hv' K hK) g hg]
    have hc : CkOn (⊤ : ℕ∞) (GV k r) (Rw v K) := by
      rw [right_word_eq_word]; exact ckOn_W_top _ (allLie_lr' (by simp) hv') hK
    exact op_comm (ckOn_top_nat hc 2) hX hY hg

lemma dLR_R (u v : List (Mat k r)) (X : Mat k r) (F : Mat k r → E) :
    dLR u v (RdV X F) = dLR u (v ++ [X]) F := by
  unfold dLR Rw; rw [List.foldr_append]; rfl

lemma dLR_L {u v : List (Mat k r)} {X : Mat k r} (hu : ∀ Y ∈ u, inLie k r Y) (hv : ∀ Y ∈ v, inLie k r Y)
    (hX : inLie k r X) {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, dLR u v (LdV X F) g = dLR (u ++ [X]) v F g := by
  intro g hg
  have e1 : dLR u v (LdV X F) = W (lr u []) (Rw v (LdV X F)) := by
    rw [← foldr_LdV_eq_W_lr]; rfl
  have e2 : dLR (u ++ [X]) v F = W (lr u []) (LdV X (Rw v F)) := by
    rw [← foldr_LdV_eq_W_lr]; unfold dLR; rw [List.foldr_append]; rfl
  rw [e1, e2]
  exact W_congr _ (allLie_lr' hu (by simp)) (L_Rw_comm hX v hv F hF) g hg

lemma chart_rho {g0 x : Mat k r} (hg0 : g0 ∈ GV k r) (hx : x ∈ Sr g0) (hxG : x ∈ GV k r) :
    chart g0 (rho g0 x) = x := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
  obtain ⟨hl, -, hk⟩ := iot_facts hh hx
  show kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0 = x
  rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]

lemma rho_self {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : rho g0 g0 = 0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  funext i
  simp only [Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
  exact co_zero i

lemma self_mem_Sr {g0 : Mat k r} (hg0 : g0 ∈ GV k r) : g0 ∈ Sr g0 := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
  show IsUnit (g0 * g0⁻¹ + 1).det
  rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _

lemma chart_comp_cd {F : Mat k r → E} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) (m : ℕ)
    (hF : CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨U, f', hU, hcU, hcd, hff⟩ := hF _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y' => f' (chart g0 Y')) Y :=
    (hcd.contDiffAt (hU.mem_nhds hcU)).comp Y
      (((chart_cd g0).contDiffAt (dom_open.mem_nhds hY)).of_le (top_ge_nat m))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact hff _ h1 (chart_mem hg0 h2)

theorem ckOn_top_of_all {F : Mat k r → E} (hF : ∀ m : ℕ, CkOn ((m : ℕ) : ℕ∞) (GV k r) F) :
    CkOn (⊤ : ℕ∞) (GV k r) F := by
  intro g0 hg0
  have hAL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Dom k r) :=
    contDiffOn_infty.2 fun m => chart_comp_cd hg0 m (hF m)
  set U := Sr g0 ∩ rho g0 ⁻¹' Dom k r with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) dom_open
  have hg0U : g0 ∈ U := ⟨self_mem_Sr hg0, by show rho g0 g0 ∈ Dom k r; rw [rho_self hg0]; exact zero_mem_dom⟩
  refine ⟨U, fun x => F (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · exact hAL.comp ((rho_cd g0).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    show F x = F (chart g0 (rho g0 x))
    rw [chart_rho hg0 hx.1 hxG]

theorem rule_A1_derivatives : C2.FiniteOrderIntersectionInSmooth := by
  intro k r E _ _ A F hF
  refine ⟨ckOn_top_of_all fun m => (hF m).choose_spec.1, ?_⟩
  intro u v hu hv
  obtain ⟨c, hc⟩ := hF (u.length + v.length)
  refine ⟨c, fun g hg => le_trans ?_ (hc.2 u v hu hv le_rfl g hg)⟩
  refine mul_le_mul_of_nonneg_right (rpow_mono_G hg ?_) (norm_nonneg _)
  have : 0 ≤ C2.B0 r * ((u.length : ℝ) + v.length) := mul_nonneg (loss_bound_nonneg r) (by positivity)
  linarith

theorem ruleB : C2.RuleB := by
  intro k r E _ _ A F hF X hX
  refine ⟨⟨ckOn_op_top false hF.1 hX.1, ?_⟩, ⟨ckOn_op_top true hF.1 hX.1, ?_⟩⟩
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 u (v ++ [X]) hu (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hv Y h
      · rw [List.mem_singleton.1 h]; exact hX)
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * ((u.length : ℝ) + (v ++ [X]).length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_R] at this
    exact this
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 (u ++ [X]) v (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hu Y h
      · rw [List.mem_singleton.1 h]; exact hX) hv
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * (((u ++ [X]).length : ℝ) + v.length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_L (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) hX.1 hF.1 g hg] at this
    exact this

end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic

namespace Formalism.FourierDecayAlt.P

theorem rule_A1_of_derivatives : C2.FiniteOrderIntersectionInSmooth := SmoothnessOrderArithmetic.rule_A1_derivatives

theorem rule_B_derivatives : C2.RuleB := SmoothnessOrderArithmetic.ruleB

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetSubmatrixUnitriangularEqOne
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x2 CardInsertEmbedding DeterminantReindex

lemma det_submatrix_unitriangular_eq_one {m k : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ C2.UTset m) (e : Fin k → Fin m)
    (he : ∀ t, (e t).val = t.val) : (u.submatrix e e).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply, hu.2, Finset.prod_const_one]
  · intro t s h
    simp only [Matrix.submatrix_apply]
    apply hu.1
    rw [Fin.lt_def, he, he]
    exact h

lemma lower_parabolic_entry_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LPg (C2.monoP w d)) (x y : Fin m) (hxy : x < y) :
    l (w x) (w y) = 0 := by
  have := hl.2.1 x y hxy
  rw [monomialMatrix_conj_apply w d hd] at this
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (hd x))
    · exact h'
  · exact absurd h (hd y)

theorem lower_minor_identity : C2.MinorL := by
  intro m w d hd a i hi
  have ham : a.val + 1 ≤ m := a.isLt
  have hR0c : (C2.wSet w (a.val + 1)).card = a.val + 1 := c2x3_wSet_card w ham
  have hIc : (C2.iSet m (a.val + 1)).card = a.val + 1 := c2x3_iSet_card ham
  have hR'c : (insert i (C2.wSet w a.val)).card = a.val + 1 := by
    rw [Finset.card_insert_of_notMem hi, c2x3_wSet_card w (by omega)]
  set eR0 := (C2.wSet w (a.val + 1)).orderEmbOfFin rfl with heR0
  set eR' := (insert i (C2.wSet w a.val)).orderEmbOfFin rfl with heR'
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Fin (C2.wSet w (a.val + 1)).card → Fin m,
      ∀ t, ρ0 t = w ⟨t.val, by have := t.isLt; omega⟩ := ⟨fun t => w ⟨t.val, by have := t.isLt; omega⟩, fun t => rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin (insert i (C2.wSet w a.val)).card → Fin m,
      ∀ t, ρ t = if ht : t.val < a.val then w ⟨t.val, by omega⟩ else i :=
    ⟨fun t => if ht : t.val < a.val then w ⟨t.val, by omega⟩ else i, fun t => rfl⟩
  obtain ⟨τ0, hτ0⟩ := perm_of_range eR0 ρ0 eR0.injective (fun t => by
    have := Finset.orderEmbOfFin_mem (C2.wSet w (a.val + 1)) rfl t
    obtain ⟨j, hj, hw⟩ := Finset.mem_image.mp this
    have hjv : j.val < a.val + 1 := by simpa [C2.iSet] using hj
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    rw [hρ0, ← hw])
  obtain ⟨τ, hτ⟩ := perm_of_range eR' ρ eR'.injective (fun t => by
    have := Finset.orderEmbOfFin_mem (insert i (C2.wSet w a.val)) rfl t
    rcases Finset.mem_insert.mp this with h | h
    · refine ⟨⟨a.val, by omega⟩, ?_⟩
      rw [hρ, dif_neg (lt_irrefl _)]; exact h.symm
    · obtain ⟨j, hj, hw⟩ := Finset.mem_image.mp h
      have hjv : j.val < a.val := by simpa [C2.iSet] using hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      rw [hρ, dif_pos hjv, ← hw])
  refine ⟨((Equiv.Perm.sign τ0 : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ), ?_, fun l hl u' hu => ?_⟩
  · rcases sign_pm τ0 with h0 | h0 <;> rcases sign_pm τ with h1 | h1 <;> rw [h0, h1] <;> norm_num
  unfold C2.minorS
  rw [dif_pos (hR0c.trans hIc.symm), dif_pos (hR'c.trans hIc.symm)]
  set eI := (C2.iSet m (a.val + 1)).orderEmbOfFin (hR0c.trans hIc.symm).symm with heI
  set eI' := (C2.iSet m (a.val + 1)).orderEmbOfFin (hR'c.trans hIc.symm).symm with heI'
  have hI : ∀ t, (eI t).val = t.val := fun t => iemb ham _ t
  have hI' : ∀ t, (eI' t).val = t.val := fun t => iemb ham _ t
  rw [U_mul_sub (by omega) (l * C2.monoP w d) u' (fun x y h => hu.1 x y h) eR' eI' hI', Matrix.det_mul,
    det_submatrix_unitriangular_eq_one u' hu eI' hI', mul_one, submatrix_mul_monomialMatrix, Matrix.det_mul, Matrix.det_diagonal,
    det_reindex l eR' ρ _ τ hτ]
  conv_lhs => rw [← Matrix.one_mul (C2.monoP w d)]
  rw [submatrix_mul_monomialMatrix, Matrix.det_mul, Matrix.det_diagonal, det_reindex 1 eR0 ρ0 _ τ0 hτ0]
  have h1 : ((1 : Matrix (Fin m) (Fin m) ℂ).submatrix ρ0 (fun s => w (eI s))).det = 1 := by
    have : (1 : Matrix (Fin m) (Fin m) ℂ).submatrix ρ0 (fun s => w (eI s)) = 1 := by
      ext t s
      simp only [Matrix.submatrix_apply, Matrix.one_apply, hρ0]
      by_cases hts : t = s
      · subst hts; rw [if_pos (congrArg w (Fin.ext (hI t).symm)), if_pos rfl]
      · rw [if_neg, if_neg hts]
        intro e; apply hts
        have := congrArg Fin.val (w.injective e); simp only [hI] at this; exact Fin.ext this
    rw [this, Matrix.det_one]
  have hL : (l.submatrix ρ (fun s => w (eI' s))).det = l i (w a) := by
    rw [Matrix.det_of_lowerTriangular]
    · have ht0 : a.val < (insert i (C2.wSet w a.val)).card := by omega
      rw [Finset.prod_eq_single ⟨a.val, ht0⟩]
      · simp only [Matrix.submatrix_apply, hρ, dif_neg (lt_irrefl _)]
        congr 2; exact Fin.ext (hI' _)
      · intro t _ ht
        have htv : t.val < a.val := by
          have := t.isLt; have : t.val ≠ a.val := fun e => ht (Fin.ext e); omega
        simp only [Matrix.submatrix_apply, hρ, dif_pos htv]
        have : eI' t = ⟨t.val, by omega⟩ := Fin.ext (hI' t)
        rw [this]; exact hl.1.2 _
      · simp
    · intro t s hts
      have hts' : t.val < s.val := by
        have := OrderDual.toDual_lt_toDual.mp hts; rw [Fin.lt_def] at this; exact this
      have htv : t.val < a.val := by have := s.isLt; omega
      simp only [Matrix.submatrix_apply, hρ, dif_pos htv]
      have : eI' s = ⟨s.val, by have := s.isLt; omega⟩ := Fin.ext (hI' s)
      rw [this]
      exact lower_parabolic_entry_zero w d hd l hl _ _ (by rw [Fin.lt_def]; exact hts')
  rw [h1, hL, prod_emb hR0c d eI hI, prod_emb hR'c d eI' hI']
  linear_combination (-(((Equiv.Perm.sign τ0 : ℤ) : ℂ) * l i (w a) *
    ∏ j ∈ Finset.range (a.val + 1), (if h : j < m then d ⟨j, h⟩ else 1))) * sign_sq τ

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterPairStep
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.LetterPairRecursion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

lemma step_pair (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
    (b : Bool) {X : Mat k r} (hX : unitLie k r X) {u v u2 v2 : List (Mat k r)}
    (hu : ∀ Y ∈ u, unitLie k r Y) (hv : ∀ Y ∈ v, unitLie k r Y) (hu2 : ∀ Y ∈ u2, unitLie k r Y)
    (hv2 : ∀ Y ∈ v2, unitLie k r Y) (hl2 : u2.length + v2.length ≤ m)
    (hl : u.length + v.length + 1 ≤ u2.length + v2.length)
    (hdl : ∀ f : Mat k r → (Wq →L[ℂ] Wp), dLR u2 v2 f = op b X (dLR u v f))
    (IH : ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS) :
    ∀ g ∈ Om k r D.z D.z', dLR u2 v2 (JF D F) g = ∫ p, xiP D p • dLR u2 v2 (rho D p F) g ∂D.μSS := by
  intro g hg
  have hgG : g ∈ GV k r := hg.1
  have hXL : inLie k r X := hX.1
  obtain ⟨ε, hε, hball⟩ := curve_ball D hg b hXL
  obtain ⟨K, hKc, hKO, hcvK⟩ : ∃ K : Set (Mat k r), IsCompact K ∧ K ⊆ Om k r D.z D.z' ∧
      ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ K :=
    ⟨(fun t : ℝ => cv b X t g) '' Metric.closedBall (0 : ℝ) ε,
      (isCompact_closedBall (0 : ℝ) ε).image (cv_continuous b X g),
      by rintro _ ⟨t, ht, rfl⟩; exact hball t ht,
      fun t ht => ⟨t, ht, rfl⟩⟩
  have hgK : g ∈ K := by
    have h0 := hcvK 0 (Metric.mem_closedBall_self hε.le)
    rwa [cv_zero] at h0
  have hKG : K ⊆ GV k r := fun x hx => (hKO hx).1
  obtain ⟨bb, hbbi, hbb⟩ := hDom2 K hKc hKO
  have hWSc : ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))).Countable :=
    (Set.countable_singleton _).insert _
  have hWSl : ∀ uv ∈ ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))),
      (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m := by
    intro uv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl
    · exact ⟨hu, hv, show u.length + v.length ≤ m by omega⟩
    · exact ⟨hu2, hv2, hl2⟩
  have hgood := good_set D hFm hKc hKG hWSc hWSl bb (fun uv huv x hx =>
    hbb uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 x hx)
  obtain ⟨S, hSae, hSprop⟩ : ∃ S : Set (SS k r), (∀ᵐ p ∂D.μSS, p ∈ S) ∧ ∀ p ∈ S, D.inSS p ∧
      ∀ uv ∈ ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))), ∀ x ∈ K,
        ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ bb p :=
    ⟨_, hgood, fun p hp => hp⟩
  obtain ⟨G, hGin, hGout⟩ : ∃ G : SS k r → Mat k r → (Wq →L[ℂ] Wp),
      (∀ p ∈ S, G p = dLR u v (rho D p F)) ∧ (∀ p ∉ S, G p = 0) :=
    ⟨fun p => S.indicator (fun p => dLR u v (rho D p F)) p,
      fun p hp => by dsimp only; exact Set.indicator_of_mem hp _,
      fun p hp => by dsimp only; simp [hp]⟩
  have hop0 : op b X (0 : Mat k r → (Wq →L[ℂ] Wp)) = 0 := by
    have h := hdl (fun _ => 0)
    rw [dLR_zero, dLR_zero] at h
    exact h.symm
  have hG1 : ∀ p, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G p) := by
    intro p
    by_cases hp : p ∈ S
    · rw [hGin p hp]
      exact ckOn_dLR_rho D (hSprop p hp).1 hFm hu hv 1 (by omega)
    · rw [hGout p hp]
      exact ckOn_zero _
  have hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun p => G p (cv b X t g)) D.μSS := by
    intro t ht
    refine (hDom1 u v hu hv (by omega) _ (hball t (Metric.ball_subset_closedBall ht))).congr ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp, dLR_rho D (hSprop p hp).1]
  have hG'm : AEStronglyMeasurable (fun p => op b X (G p) g) D.μSS := by
    refine (hDom1 u2 v2 hu2 hv2 hl2 g hg).congr ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp, ← hdl, dLR_rho D (hSprop p hp).1]
  have hb0 : ∀ p, ‖G p g‖ ≤ ‖bb p‖ := by
    intro p
    by_cases hp : p ∈ S
    · rw [hGin p hp]
      exact ((hSprop p hp).2 (u, v) (by simp) g hgK).trans (Real.le_norm_self _)
    · rw [hGout p hp]
      simp
  have hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ p, ‖op b X (G p) (cv b X t g)‖ ≤ ‖bb p‖ := by
    intro t ht p
    by_cases hp : p ∈ S
    · rw [hGin p hp, ← hdl]
      exact ((hSprop p hp).2 (u2, v2) (by simp) _
        (hcvK t (Metric.ball_subset_closedBall ht))).trans (Real.le_norm_self _)
    · rw [hGout p hp, hop0]
      simp
  have hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε,
      dLR u v (JF D F) (cv b X t g) = ∫ p, xiP D p • G p (cv b X t g) ∂D.μSS := by
    intro t ht
    rw [IH _ (hball t (Metric.ball_subset_closedBall ht))]
    refine integral_congr_ae ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp]
  have key := step_loc hXL (xiP D) (norm_xiP D) (continuous_xiP D).aestronglyMeasurable G hG1 hgG hε
    hGm hG'm (fun p => ‖bb p‖) hbbi.norm hb0 hb1 (dLR u v (JF D F)) hΦ
  rw [hdl, key]
  refine integral_congr_ae ?_
  filter_upwards [hSae] with p hp
  rw [hGin p hp, hdl]

end Formalism.FourierDecayAlt.P.LetterPairRecursion
end
end

