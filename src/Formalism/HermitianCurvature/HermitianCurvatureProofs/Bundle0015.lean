import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Mathlib
import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction
section
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem lagrangeLead : LagrangeLead := by
  intro d y hy V _ _ a
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, lagCo y j * y j ^ (k : ℕ)) = if k = Fin.last d then 1 else 0 := by
    intro k
    rw [ChebyshevExtremalPolynomials.sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.2)]
    simp [Fin.ext_iff]
  simp [this]

theorem extractK : ExtractK := by
  intro V _ _ K
  induction K with
  | zero =>
    intro d s W grid _ _ y₀
    simp
    congr 1
    exact Subsingleton.elim _ _
  | succ K ih =>
    intro d s W grid hP hg y₀
    set c := y₀ (Fin.last K) with hc
    have hP' : PolyStep K d (fun a => s a.castSucc)
        (fun m (y' : Fin K → ℝ) => W m (Fin.snoc (α := fun _ => ℝ) y' c)) := by
      intro a y'
      obtain ⟨cc, h1, h2⟩ := hP a.castSucc (Fin.snoc (α := fun _ => ℝ) y' c)
      refine ⟨cc, by simpa using h1, fun t => ?_⟩
      have := h2 t
      rw [← Fin.snoc_update] at this
      simpa using this
    have ih' := ih d _ _ (fun a => grid a.castSucc) hP' (fun a => hg _) (Fin.init y₀)
    simp only [hc, Fin.snoc_init_self] at ih'
    have hl : ∀ y' : Fin K → ℝ, s (Fin.last K) • W K (Fin.snoc (α := fun _ => ℝ) y' c) =
        ∑ i, ((lagCo (grid (Fin.last K)) i : ℝ) : ℂ) •
          W (K + 1) (Fin.snoc (α := fun _ => ℝ) y' (grid (Fin.last K) i)) := by
      intro y'
      obtain ⟨cc, h1, h2⟩ := hP (Fin.last K) (Fin.snoc (α := fun _ => ℝ) y' c)
      rw [Fin.val_last] at h1 h2
      rw [← h1, ChebyshevExtremalPolynomials.lead_complex (grid (Fin.last K)) (hg _) cc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h2, Fin.update_snoc_last]
    rw [Fin.prod_univ_castSucc, mul_comm, mul_smul, ih', Finset.smul_sum]
    rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [smul_comm, ← hc, hl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun a => grid a (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1)) (i, j') a)) =
        Fin.snoc (α := fun _ => ℝ) (fun a : Fin K => grid a.castSucc (j' a)) (grid (Fin.last K) i) := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [Fin.snocEquiv]
    rw [e, smul_smul, Fin.prod_univ_castSucc]
    congr 1
    simp [Fin.snocEquiv]

lemma sum_prod_abs {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j : Fin K → Fin (d + 1), ∏ a, |lagCo (grid a) (j a)| = ∏ a, ∑ i, |lagCo (grid a) i| := by
  first
  | rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  | exact (Finset.prod_univ_sum (fun a i => |lagCo (grid a) i|)).symm
  | simp [Finset.prod_univ_sum]

lemma norm_le_sum {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {K d : ℕ} (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ) (hP : PolyStep K d s W)
    (hg : ∀ a, Function.Injective (grid a)) (y₀ : Fin K → ℝ) :
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      ∑ j : Fin K → Fin (d + 1), (∏ a, |lagCo (grid a) (j a)|) * ‖W K fun a => grid a (j a)‖ := by
  have h := extractK V K d s W grid hP hg y₀
  calc (∏ a, ‖s a‖) * ‖W 0 y₀‖ = ‖(∏ a, s a) • W 0 y₀‖ := by rw [norm_smul, norm_prod]
    _ = ‖∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ := by
        rw [h]
    _ ≤ ∑ j : Fin K → Fin (d + 1), ‖((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ :=
        norm_sum_le _ _
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]

theorem extractBound : ExtractBound := by
  intro V _ _ K d s W grid hP hg y₀ B hB
  refine (norm_le_sum s W grid hP hg y₀).trans ?_
  rw [← sum_prod_abs, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hB j) (Finset.prod_nonneg fun a _ => abs_nonneg _)

lemma lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    lagCo y j ≠ 0 := by
  unfold lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.mem_erase.mp hi).1 (hy h).symm

lemma sum_abs_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) :
    0 < ∑ i, |lagCo y i| := Finset.sum_pos' (fun i _ => abs_nonneg _)
    ⟨0, Finset.mem_univ _, abs_pos.mpr (lagCo_ne_zero y hy 0)⟩

theorem extractProb : ExtractProb := by
  intro V _ _ K d s W grid hP hg y₀
  set Pr : ℝ := ∏ a, ∑ i, |lagCo (grid a) i| with hPr
  have hPpos : 0 < Pr := Finset.prod_pos fun a _ => sum_abs_pos (grid a) (hg a)
  have hth : ∀ j, thGrid grid j = (∏ a, |lagCo (grid a) (j a)|) / Pr := by
    intro j; unfold thGrid; rw [Finset.prod_div_distrib]
  have h0 : ∀ j, 0 ≤ thGrid grid j := fun j => by
    rw [hth]; exact div_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg _) hPpos.le
  have h1 : (∑ j, thGrid grid j) = 1 := by
    simp only [hth]
    rw [← Finset.sum_div, sum_prod_abs, div_self hPpos.ne']
  have h3 : (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) := by
    refine (norm_le_sum s W grid hP hg y₀).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hth]; field_simp
  refine ⟨h0, h1, h3, ?_⟩
  have hL : 0 ≤ (∏ a, ‖s a‖) * ‖W 0 y₀‖ :=
    mul_nonneg (Finset.prod_nonneg fun a _ => norm_nonneg _) (norm_nonneg _)
  have hcs : (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 ≤
      (∑ j, thGrid grid j) * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => h0 j)
      (fun j _ => mul_nonneg (h0 j) (sq_nonneg _)) (fun j _ => le_of_eq (by ring))
  rw [h1, one_mul] at hcs
  calc ((∏ a, ‖s a‖) * ‖W 0 y₀‖) ^ 2
      ≤ (Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖)) ^ 2 :=
        pow_le_pow_left₀ hL h3 2
    _ = Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 := mul_pow _ _ _
    _ ≤ Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)

theorem extractCheb : ExtractCheb := by
  intro V _ _ K d s W α β hd hαβ hP y₀ B hB
  have h := extractBound V K d s W (fun a => Formalism.SA.C.chebPt (α a) (β a) d) hP
    (fun a => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).1) y₀ B hB
  have e : (∏ a, ∑ i, |lagCo (Formalism.SA.C.chebPt (α a) (β a) d) i|) =
      ∏ a, (1 / 2) * (4 / (β a - α a)) ^ d :=
    Finset.prod_congr rfl fun a _ => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).2
  rw [← e]
  exact h

end Formalism.FourierDecayAlt.P.LagrangeExtraction

namespace Formalism.FourierDecayAlt.P

theorem lagrange_leading_coeff : Formalism.FourierDecayAlt.F7.LagrangeLead := LagrangeExtraction.lagrangeLead

theorem extract_K_bound : Formalism.FourierDecayAlt.F7.ExtractK := LagrangeExtraction.extractK

theorem extractBound_statement : Formalism.FourierDecayAlt.F7.ExtractBound := LagrangeExtraction.extractBound

theorem extract_probability_bound : Formalism.FourierDecayAlt.F7.ExtractProb := LagrangeExtraction.extractProb

theorem extract_chebyshev_bound : Formalism.FourierDecayAlt.F7.ExtractCheb := LagrangeExtraction.extractCheb

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanNormSquaredBound
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace MeanNormSquaredBound

section Abstract

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_sum_sum {ι κ : Type} (S : Finset ι) (S' : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (v : ι → E) (v' : κ → E) :
    inner ℂ (∑ j ∈ S', d j • v' j) (∑ i ∈ S, c i • v i) =
      ∑ i ∈ S, ∑ j ∈ S', c i * conj (d j) * inner ℂ (v' j) (v i) := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

lemma normSq_sum {ι : Type} (S : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ((‖∑ i ∈ S, c i • v i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * inner ℂ (v j) (v i) := by
  rw [← inner_sum_sum, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

lemma sum_sum_sum_sum_comm {α β M : Type} [AddCommMonoid M] (P : Finset α) (H : Finset β)
    (f : α → α → β → β → M) :
    ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h' =
      ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' := by
  calc ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h'
      = ∑ p ∈ P, ∑ h ∈ H, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' := Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ h' ∈ H, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm

lemma normSq_mean {X α : Type} (L : E →ₗ[ℂ] E) (k : ℂ) (hk : conj k = k) (P : Finset α)
    (c : α → ℂ) (F : Finset X) (a : X → ℂ) (u : X → α → E) :
    ((‖L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        (k ^ 2 * ∑ p ∈ P, ∑ p' ∈ P, c p * conj (c p') * inner ℂ (L (u h' p')) (L (u h p))) := by
  have h1 : L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p) =
      ∑ p ∈ P, (k * c p) • ∑ h ∈ F, a h • L (u h p) := by
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul, mul_assoc]
  rw [h1, normSq_sum]
  simp only [inner_sum_sum, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [map_mul, hk]
  ring

lemma sum_sub_prod {α β M : Type} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (f : α × β → M) : ∑ p : ↥A × ↥B, f (p.1.1, p.2.1) = ∑ p ∈ A ×ˢ B, f p := by
  rw [Fintype.sum_prod_type, Finset.sum_product, ← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_coe_sort B]

lemma abstract_bound (AB : AvgBound) {X Y : Type} (F : Finset X) (a : X → ℂ) (A B : Finset Y)
    (u : X → Y × Y → E) (T : E →ₗ[ℂ] E) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (e₁ e₂ : Y → ℂ)
    (he₁ : ∀ ρ ∈ A, ‖e₁ ρ‖ = 1)
    (horth : ∀ h ∈ F, ∀ h' ∈ F, ∀ ρ ∈ A, ∀ ρ' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, ρ ≠ ρ' →
      inner ℂ (u h (ρ, b)) (u h' (ρ', b')) = 0) :
    ∃ r₁ r₂ : ℝ, r₁ ≤ r₂ ∧
      (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((((A.card : ℂ) * (B.card : ℂ))⁻¹) ^ 2 * ∑ p ∈ A ×ˢ B, ∑ p' ∈ A ×ˢ B,
          (e₁ p.1 * e₂ p.2) * conj (e₁ p'.1 * e₂ p'.2) * inner ℂ (T (u h' p')) (T (u h p))) ∧
      (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((A.card : ℂ)⁻¹ * ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b)))) := by
  set w : Y × Y → E := fun p => ∑ h ∈ F, a h • u h p with hw
  have key := AB E ↥A ↥B (fun p => w (p.1.1, p.2.1)) T (fun ρ => e₁ ρ.1) (fun b => e₂ b.1) hT
    (fun ρ => he₁ ρ.1 ρ.2) (by
      intro ρ ρ' b b' hne
      have hne' : ρ.1 ≠ ρ'.1 := fun h => hne (Subtype.ext h)
      simp only [hw]
      rw [inner_sum_sum]
      refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
      rw [horth h' hh' h hh ρ.1 ρ.2 ρ'.1 ρ'.2 b.1 b.2 b'.1 b'.2 hne', mul_zero])
  simp only [Fintype.card_coe] at key
  have e1 : (∑ p : ↥A × ↥B, (e₁ p.1.1 * e₂ p.2.1) • w (p.1.1, p.2.1)) =
      ∑ p ∈ A ×ˢ B, (e₁ p.1 * e₂ p.2) • w p :=
    sum_sub_prod A B (fun p => (e₁ p.1 * e₂ p.2) • w p)
  have e2 : (∑ ρ : ↥A, ‖(B.card : ℂ)⁻¹ • ∑ b : ↥B, e₂ b.1 • w (ρ.1, b.1)‖ ^ 2) =
      ∑ ρ ∈ A, ‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.sum_coe_sort B]
  rw [e1, e2] at key
  refine ⟨_, _, key, ?_, ?_⟩
  · exact normSq_mean T _ (by simp) (A ×ˢ B) (fun p => e₁ p.1 * e₂ p.2) F a u
  · have h3 : ∀ ρ, ((‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') * (((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b))) := fun ρ =>
      normSq_mean LinearMap.id _ (by simp) B e₂ F a (fun h b => u h (ρ, b))
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sum]
    simp only [h3, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring

end Abstract

lemma norm_psi {K : Type} [CommRing K] (ψ : AddChar K ℂ) (hu : ∀ x : K, conj (ψ x) = ψ (-x))
    (x : K) : ‖ψ x‖ = 1 := by
  have h1 : ψ x * conj (ψ x) = 1 := by
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖ψ x‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (‖ψ x‖ - 1) * (‖ψ x‖ + 1) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · have := norm_nonneg (ψ x); linarith

end MeanNormSquaredBound

open MeanNormSquaredBound in
theorem thetaAverageLower : Formalism.FourierDecayAlt.A6.ThxLower := by
  intro GI A2V UGE ExponentialIntegralMeasures CSA MM CPSD KG GRC AB CNE CM PL K _ _ _ R ψ hD hchar m hm n₀ F Om Lc hF hOm D
  classical
  set Sg : Finset K := (D.A ×ˢ D.B).image (fun p => p.1 + p.2) with hSg
  have hLat : IsLat (perp ψ D.L₂) := (PL K R ψ hD hchar D.L₂ D.lat₂).1
  have hAL : ∀ ρ ∈ D.A, ρ ∈ D.L₂ := D.repsA.1
  have hBR : ∀ b ∈ D.B, b ∈ R.toAddSubgroup := D.repsB.1
  have hmemSg : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ Sg := by
    intro ρ hρ b hb
    exact Finset.mem_image.mpr ⟨(ρ, b), Finset.mem_product.mpr ⟨hρ, hb⟩, rfl⟩
  have hSgL : ∀ σ ∈ Sg, σ ∈ D.L₂ := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact D.L₂.add_mem (hAL _ hp1) (D.le₂ (hBR _ hp2))
  obtain ⟨V, hV, hGI⟩ := GI K R ψ hD hchar m hm n₀ F hF Om Sg (perp ψ D.L₂) hOm hLat D.omStable
    D.nsInv (by
      intro σ hσ σ' hσ' l hl
      exact hl _ (D.L₂.sub_mem (hSgL σ hσ) (hSgL σ' hσ')))
  refine ⟨V, hV, ?_⟩
  intro t τ cr ht hcr hsh z₁ hz₁ a

  set F' : Finset (Point K × Kˣ) := F ×ˢ Sg.image τ with hF'
  have hmemF' : ∀ h ∈ F, ∀ ρ ∈ D.A, ∀ b ∈ D.B, (h, τ (ρ + b)) ∈ F' := by
    intro h hh ρ hρ b hb
    exact Finset.mem_product.mpr ⟨hh, Finset.mem_image_of_mem τ (hmemSg ρ hρ b hb)⟩
  obtain ⟨hc1, hc2⟩ := CPSD KG ExponentialIntegralMeasures MM K R ψ hD m cr (cutSet m Om t) F' hcr (by
    intro p hp p' hp'
    rw [hF _ (Finset.mem_product.mp hp).1, hF _ (Finset.mem_product.mp hp').1])
  obtain ⟨n, u₀, T, hT, hG, hGc⟩ := GRC (Point K × Kˣ) F'
    (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2)
    (fun p p' => uGram R ψ m cr (cutSet m Om t) p.1 p'.1 p.2 p'.2) hc1 hc2

  obtain ⟨r₁, r₂, hr, hr₁, hr₂⟩ := abstract_bound AB F a D.A D.B
    (fun h p => u₀ (h, τ (p.1 + p.2))) T hT (fun ρ => ψ (-(z₁ * ρ))) (fun b => ψ (-(z₁ * b)))
    (fun ρ _ => norm_psi ψ hD.unitary _) (by
      intro h hh h' hh' ρ hρ ρ' hρ' b hb b' hb' hne
      simp only
      rw [hG _ (hmemF' h' hh' ρ' hρ' b' hb') _ (hmemF' h hh ρ hρ b hb)]
      simp only
      rw [UGE ExponentialIntegralMeasures CSA MM K R ψ hD m h' h _ _ cr (by rw [hF h hh, hF h' hh']) hcr]
      by_contra hcon
      have hNs : Ns R ψ m h' h (τ (ρ' + b')) (τ (ρ + b)) ≠ 0 := fun h0 => hcon (by rw [h0, mul_zero])
      have hmem := A2V K R ψ hD m hm h' h _ _ (by rw [hF h hh, hF h' hh']) hNs
      rw [hsh ρ' hρ' b' hb', hsh ρ hρ b hb] at hmem
      have h5 : ρ' - ρ ∈ R.toAddSubgroup := by
        have h6 : ρ' - ρ = (((t⁻¹ : Kˣ) : K) + (ρ' + b') - (((t⁻¹ : Kˣ) : K) + (ρ + b))) + (b - b') := by
          ring
        rw [h6]
        exact R.toAddSubgroup.add_mem hmem (R.toAddSubgroup.sub_mem (hBR b hb) (hBR b' hb'))
      obtain ⟨x, _, hx⟩ := D.repsA.2 ρ' (hAL ρ' hρ')
      have e1 := hx ρ ⟨hρ, h5⟩
      have e2 := hx ρ' ⟨hρ', by rw [sub_self]; exact R.toAddSubgroup.zero_mem⟩
      exact hne (e1.trans e2.symm))
  have hr₁' : (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * NsK R ψ (m + 1) h h' z₁) := by
    rw [hr₁]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    rw [← CNE CM PL K R ψ hD hchar (m + 1) F Om Lc D hOm.2.1 z₁ hz₁ h hh h' hh']
    congr 1
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1', hp2'⟩ := Finset.mem_product.mp hp'
    rw [hGc _ (hmemF' h hh p.1 hp1 p.2 hp2) _ (hmemF' h' hh' p'.1 hp1' p'.2 hp2')]
    simp only
    rw [hGI t _ _ cr ht hcr _ (hmemSg p.1 hp1 p.2 hp2) _ (hmemSg p'.1 hp1' p'.2 hp2')
      (hsh p.1 hp1 p.2 hp2) (hsh p'.1 hp1' p'.2 hp2') h hh h' hh']
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    have q1 : -(z₁ * p.1) + -(z₁ * p.2) = -(z₁ * (p.1 + p.2)) := by ring
    have q2 : -(z₁ * p'.1) + -(z₁ * p'.2) = -(z₁ * (p'.1 + p'.2)) := by ring
    rw [q1, q2]
  have hr₂' : (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * thx R ψ m cr D.A D.B τ z₁ h h') := by
    rw [hr₂]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 2
    unfold thx
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    congr 1
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
    simp only
    rw [hG _ (hmemF' h hh ρ hρ b hb) _ (hmemF' h' hh' ρ hρ b' hb')]
  have hApos : 0 < (D.A.card : ℝ) := by
    obtain ⟨x, hx, _⟩ := D.repsA.2 0 D.L₂.zero_mem
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx.1⟩
  have hAne : (D.A.card : ℂ) ≠ 0 := by
    exact_mod_cast hApos.ne'
  have hfin : ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      (thx R ψ m cr D.A D.B τ z₁ h h' - NsK R ψ (m + 1) h h' z₁) =
      (((D.A.card : ℝ) * (r₂ - r₁) : ℝ) : ℂ) := by
    push_cast
    rw [hr₁', hr₂', ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    field_simp
  rw [hfin]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact mul_nonneg hApos.le (sub_nonneg.mpr hr)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialMeansOrthogonal
section
open Formalism.FourierDecayAlt.A6

namespace Formalism.FourierDecayAlt.P

namespace A6x1

theorem norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ

end A6x1

theorem doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by
  intro E _ _ A B _ _ u e₁ e₂
  rw [Fintype.sum_prod_type, mul_inv, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, Finset.smul_sum (r := e₁ ρ)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]

theorem partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by
  intro E _ _ A B _ _ u e₂ h ρ ρ' hne
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp [h ρ ρ' _ _ hne]

theorem orthogonalMeanNorm : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]

theorem averageBoundOfSteps : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := by
  intro hM hP hO E _ _ A B _ _ u T e₁ e₂ hT he h
  rw [hM E A B u e₁ e₂]
  have h1 := hO E A (fun ρ => (Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)) e₁ he
    (hP E A B u e₂ h)
  have h2 := hT ((Fintype.card A : ℂ)⁻¹ •
    ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)))
  calc _ ≤ ‖(Fintype.card A : ℂ)⁻¹ •
        ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))‖ ^ 2 := by
        gcongr
    _ = _ := by rw [h1]; ring

theorem averageBound : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm

end Formalism.FourierDecayAlt.P
end

