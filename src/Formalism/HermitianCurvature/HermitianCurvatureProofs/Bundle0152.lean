import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
import Mathlib.LinearAlgebra.Lagrange

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem re_mix_le (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (U : Finset (List C.Letter))
    (θ : List C.Letter → ℝ) (hθ : ∀ a, 0 ≤ θ a) (p : C.LPt) (B : List C.Letter → ℝ)
    (hB : ∀ u ∈ U, ‖KB.gN S v ε i u p p‖ ≤ B u) :
    (KB.mix S v ε i U θ p p).re ≤ ∑ u ∈ U, θ u * max (B u) 0 := by
  unfold KB.mix
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left
    ((Complex.re_le_norm _).trans ((hB u hu).trans (le_max_left _ _))) (hθ u)

private lemma two_mul_norm_le_add_of_psdOn_pair {α : Type} [DecidableEq α] (G : α → α → ℂ) (p q : α) (hpq : p ≠ q)
    (h : TB.PSDOn ({p, q} : Finset α) G) : 2 * ‖G p q‖ ≤ ‖G p p‖ + ‖G q q‖ := by
  set Y : Finset α := {p, q} with hY
  let e : Fin 2 → Y := ![⟨p, by simp [Y]⟩, ⟨q, by simp [Y]⟩]
  have hN := Matrix.PosSemidef.submatrix h e
  have hqp : G q p = conj (G p q) := by
    have h0 := hN.1.apply 1 0
    simp [e] at h0
    rw [← h0]
  by_cases hw : G p q = 0
  · rw [hw, norm_zero, mul_zero]
    positivity
  set w := G p q with hwdef
  set ζ : ℂ := conj w / (‖w‖ : ℂ) with hζ
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  have hcw : conj w * w = (‖w‖ : ℂ) ^ 2 := Complex.conj_mul' w
  have h1 : ζ * w = ‖w‖ := by
    rw [hζ, div_mul_eq_mul_div, hcw, pow_two, mul_div_assoc, div_self hw', mul_one]
  have h2 : conj ζ * conj w = ‖w‖ := by
    rw [← map_mul, h1, Complex.conj_ofReal]
  have hnz : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]
  have h3 : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hnz]
    simp
  have key := hN.re_dotProduct_nonneg ![1, -ζ]
  have hform : star (![1, -ζ] : Fin 2 → ℂ) ⬝ᵥ
      Matrix.mulVec ((Matrix.of fun x y : Y => G x y).submatrix e e) ![1, -ζ] =
      G p p - ζ * w - conj ζ * G q p + conj ζ * ζ * G q q := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e, w]
    try ring
  rw [hform, hqp, h1, h2, h3, one_mul] at key
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at key
  have ha := Complex.re_le_norm (G p p)
  have hb := Complex.re_le_norm (G q q)
  linarith

theorem gN_entry (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (p q : C.LPt) (B : ℝ) (hp : ‖KB.gN S v ε j (w.1 v) p p‖ ≤ B)
    (hq : ‖KB.gN S v ε j (w.1 v) q q‖ ≤ B) : ‖KB.gN S v ε j (w.1 v) p q‖ ≤ B := by
  by_cases hpq : p = q
  · subst hpq
    exact hp
  have hps := hpos v ε hε j hj w {p, q}
  have hcs := two_mul_norm_le_add_of_psdOn_pair (S.gramLoc v ε j (w.1 v)) p q hpq hps
  unfold KB.gN at hp hq ⊢
  rw [norm_div] at hp hq ⊢
  rcases (norm_nonneg (S.sizeAt v (w.1 v) : ℂ)).eq_or_lt with h0 | hs
  · rw [← h0, div_zero] at hp ⊢
    exact hp
  · rw [div_le_iff₀ hs] at hp hq ⊢
    linarith

theorem locSup_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛ0 : 0 ≤ Λ b (n - 1) v) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (hIH : ∀ u, D.AdmAt S v u → u.length + (n - 2) * C.Kst ≤ S.Ntop → LocSup S v ε (n - 1) b u h)
    (a : List C.Letter) (ha : D.AdmAt S v a) (hlen : a.length + (n - 1) * C.Kst ≤ S.Ntop) :
    LocSup S v ε n b a h := by
  have hk : (n - 1) * C.Kst = (n - 2) * C.Kst + C.Kst := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, add_mul, one_mul]
  have hl2 : b + (n - 1) - 1 = b + n - 2 := by omega
  obtain ⟨Ba, hBa⟩ := hIH a ha (by omega)
  rw [hl2] at hBa
  obtain ⟨w, rfl⟩ := exists_word_of_admissible_at_place S ha

  have hsup : ∃ B : ℝ, ∀ p ∈ ({h} : Finset C.LPt), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w.1 v) (p ++ [(n - 1, t)]) (p ++ [(n - 1, t)])‖ ≤ B :=
    ⟨Ba, fun p hp t ht => by rw [Finset.mem_singleton] at hp; subst hp; exact hBa t ht⟩
  obtain ⟨hcont, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩ :=
    hGL ε hε b n hb hn hbn (w.1 v) ha {h} (by simp [hh]) hsup

  obtain ⟨Up, θp, Um, θm, hUp, hUm, hLB⟩ := hLL b (n - 1) hb (by omega) (by omega) (w.1 v) ha (by omega)
  have hBu : ∀ u ∈ Up ∪ Um, LocSup S v ε (n - 1) b u h := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact hIH u (hUp.2 u hu).1 (by have := (hUp.2 u hu).2; omega)
    · exact hIH u (hUm.2 u hu).1 (by have := (hUm.2 u hu).2; omega)
  choose! Bu hBu' using hBu
  set Bp := ∑ u ∈ Up, θp u * max (Bu u) 0 with hBp
  set Bq := ∑ u ∈ Um, θm u * max (Bu u) 0 with hBq
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg fun u _ => mul_nonneg (hUp.1.1 u) (le_max_right _ _)
  have hBq0 : 0 ≤ Bq := Finset.sum_nonneg fun u _ => mul_nonneg (hUm.1.1 u) (le_max_right _ _)
  set Bt := max (max Ba 0) (Bp + Bq) with hBt
  have hBt0 : 0 ≤ Bt := (le_max_right _ _).trans (le_max_left _ _)

  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts 1 1 one_pos
  have := i1; have := i2
  have hgR : (0 : ℝ) < S.g := by exact_mod_cast hg
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem (Lstd 1 1) (S.g : ℝ) hgR.ne'
  have := j1; have := j2
  obtain ⟨Cs, -, hCsum⟩ := pbc_lstdSum
  obtain ⟨hsm, -⟩ := hCsum 1 1 (S.g : ℝ) (fun _ => Λ b (n - 1) v) one_pos hgR (fun _ => hΛ0)
  let D : Fin 1 → C.LPt → C.LPt → ℂ → ℂ := fun _ p q c =>
    KB.gN S v ε (b + n - 1) (w.1 v) (p ++ [(n, c)]) (q ++ [(n, c)])
  let U : Fin 1 → C.LPt × ℂ → C.LPt × ℂ → ℂ := fun _ p q =>
    KB.gN S v ε (b + n - 2) (w.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])
  have hGD : GermData {h} U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) := by
    refine ⟨fun _ Xs hXs => hblk Xs hXs, ⟨max Ba B' ⊔ 0, le_max_right _ _, fun _ p hp x hx => ?_⟩,
      fun _ p hp q hq σ => (hlim p hp q hq σ).1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.1,
      fun _ p hp q hq σ => (hlim p hp q hq σ).2.2⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨(hBa x⁻¹ (inv_ne_zero hx)).trans ?_, (hB' p (Finset.mem_singleton_self p) x hx).trans ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hD : ∀ (v' : Fin 1) (z : ℂ), z ≠ 0 → TB.PSDOn ({h} : Finset C.LPt) (fun p q => D v' p q z) := by
    intro v' z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w (({h} : Finset C.LPt).image fun p => p ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this {h} (fun p => p ++ [(n, z)]) (fun p hp => Finset.mem_image_of_mem _ hp)

  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd 1 1), ∀ x : crystallineComparison.V 1, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ)‖ ≤
        Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ) := by
    intro σ _ x hx hx'
    set t := (x 0)⁻¹ with ht_def
    set t' := ((x + (S.g : ℝ) • σ) 0)⁻¹ with ht'_def
    have ht : t ≠ 0 := inv_ne_zero (hx 0)
    have ht' : t' ≠ 0 := inv_ne_zero (hx' 0)
    have ephi : phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ) =
        KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')]) := by
      simp [phi, U, t, t']
    rw [ephi, mL_one]
    set a0 := ‖((S.g : ℝ) • σ) 0‖
    have ediff : t⁻¹ - t'⁻¹ = -(((S.g : ℝ) • σ) 0) := by
      simp only [t, t', inv_inv, Pi.add_apply]; ring

    have hcs : ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ ≤ Ba :=
      gN_entry S hpos v ε hε _ (by omega) w _ _ Ba (hBa t ht) (hBa t' ht')

    obtain ⟨u, hu, hB⟩ := hLB ε hε t t' {h} ht ht' (by simp [hh])
    have hob := offdiag_bound _ _ _ h {h} (Finset.mem_singleton_self h) hB
      (Λ b (n - 1) v ^ C.Kst * Bp) (Λ b (n - 1) v ^ C.Kst * Bq) ?_ ?_
    rotate_left
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Up θp hUp.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_left _ hu) t ht; rwa [hl2] at this
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')])
          (h ++ [(n - 1, t')])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Um θm
          (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Um θm hUm.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_right _ hu) t' ht'; rwa [hl2] at this
    rw [hl2, norm_mul, norm_mul, hu, one_mul, norm_pow, ediff, norm_neg] at hob
    set X := ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    have hl : a0 ^ C.Kst * X ≤ Λ b (n - 1) v ^ C.Kst * (Bp + Bq) := by
      have h1 : (a0 ^ C.Kst * X) ^ 2 ≤ (Λ b (n - 1) v ^ C.Kst * (Bp + Bq)) ^ 2 := by
        refine hob.trans ?_
        have hL := pow_nonneg hΛ0 C.Kst
        nlinarith [mul_nonneg hL hBp0, mul_nonneg hL hBq0, mul_nonneg (mul_nonneg hL hL) (mul_nonneg hBp0 hBq0)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rw [mul_one]; exact hcs.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have ha0 : 0 < a0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [mul_min_of_nonneg _ _ hBt0, mul_one]
      refine le_min (hcs.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
      have h2 : X ≤ (Λ b (n - 1) v / a0) ^ C.Kst * (Bp + Bq) := by
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 _)]
        linarith [hl]
      refine h2.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hΛ0 ha0.le) _)
  refine ⟨(∏ _v : Fin 1, KB.dlB S b n) *
    ∑' σ : crystallineComparison.dualSet (Lstd 1 1), Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V 1)),
    fun t ht => ?_⟩
  have hH := herglotz_germ (H := C.LPt) (f := 1) {h} (fun _ _ => 1) (psd_single_one h) D hD
    (fun _ p hp q hq => (hcont p hp q hq).1) (fun _ p hp q hq => (hcont p hp q hq).2) (S.g : ℝ) hgR
    (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U (fun _ => Pua) (fun _ => Paa)
    (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) hGD (fun _ _ _ _ => rfl) (Lstd 1 1) Lm hLm
    (fun σ => Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ)) (hsm.mul_left Bt) hF
    (fun _ => t) {fun _ => t} (by simp)
  rw [hcov, Finset.sum_singleton] at hH
  have hgood : Good (fun _ : Fin 1 => t) := fun _ => ht
  have hN : Nz {h} (fun _ _ => (1 : ℂ)) D (fun _ => t) =
      (KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re := by
    simp [Nz, hgood, Fz, D]
  rw [hN, one_pow, one_mul] at hH
  have h0 := psd_diag _ _ (PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w {h ++ [(n, t)]})
    (Finset.mem_singleton_self _)
  have hc := Complex.nonneg_iff.1 h0
  have e : KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)]) =
      ((KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re : ℂ) :=
    Complex.ext (by simp) (by simp [hc.2.symm])
  rw [e, Complex.norm_real, Real.norm_of_nonneg hc.1]
  exact hH

theorem locSup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) :
    ∀ n, 1 ≤ n → ∀ b, 1 ≤ b → b + n ≤ S.G.r + 2 → ∀ h, D.ptSize h = b - 1 → ∀ a, D.AdmAt S v a →
      a.length + (n - 1) * C.Kst ≤ S.Ntop → LocSup S v ε n b a h := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ m ih =>
    intro _ b hb hbn h hh a ha hlen
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact locSup_one S hI v ε hε b hb (by omega) a ha h hh
    · refine locSup_step S hpos hg v Λ hLL hGL ε hε (m + 1) (by omega) b hb hbn
        (by rw [Nat.add_sub_cancel]; exact hΛ0 b m hb hm (by omega)) h hh ?_ a ha hlen
      intro u hu hulen
      have e1 : m + 1 - 2 = m - 1 := by omega
      rw [e1] at hulen
      rw [Nat.add_sub_cancel]
      exact ih hm b hb (by omega) h hh u hu hulen

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.XepolNatDegree
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

section poly

theorem lag_weights (k : ℕ) : ∃ lam : Fin (k + 1) → ℂ, ∀ p : ℂ[X], p.natDegree ≤ k →
    ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1) := by
  classical
  let v : Fin (k + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := by
    intro a _ b _ hab
    have h' : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := hab
    exact Fin.ext (by exact_mod_cast h')
  refine ⟨fun j => (Lagrange.basis Finset.univ v j).coeff (k - 1), ?_⟩
  intro p hp
  have hdeg : p.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp) (by exact_mod_cast Nat.lt_succ_self k)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.coeff_C_mul, mul_comm]

def xpol (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Finset.Icc 1 (P.k - 1), (X + C ((M.rho P ρ i : ℝ) : ℂ))

def xepol (P : M.Par) (l : ℕ) (ρ : M.Ty P) : ℂ[X] :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (X + C ((M.rho P ρ i : ℝ) : ℂ))

theorem xpol_eval (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xpol P ρ).eval Y = M.xC P ρ Y := by
  simp [xpol, M.xC, Polynomial.eval_prod]

theorem xepol_eval (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℂ) : (xepol P l ρ).eval Y = M.xEx P {l} ρ Y := by
  simp [xepol, M.xEx, Polynomial.eval_prod]

theorem xpol_monic (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem xpol_natDegree (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).natDegree = P.k - 1 := by
  unfold xpol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp [Polynomial.natDegree_X_add_C]

theorem xpol_coeff (P : M.Par) (ρ : M.Ty P) : (xpol P ρ).coeff (P.k - 1) = 1 := by
  rw [← xpol_natDegree P ρ]
  exact (xpol_monic P ρ).coeff_natDegree

theorem xepol_natDegree (P : M.Par) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    (xepol P l ρ).natDegree = P.k - 2 := by
  unfold xepol
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hl, Nat.card_Icc]
  omega

end poly

section ring

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def fl (P : M.Par) (l : ℕ) (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ0 => if M.Up P l ρ0 ρ then 1 else 0

theorem up_func {l : ℕ} {ρ0 ρ ρ' : M.Ty P} (h1 : M.Up P l ρ0 ρ) (h2 : M.Up P l ρ0 ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h1 i, h2 i]

theorem kap_decomp (d : Q.NFData P A) (g : M.Ty P → ℂ) : d.κ g = ∑ ρ0, g ρ0 • d.κ (dl ρ0) := by
  have h : g = ∑ ρ0, g ρ0 • dl ρ0 := by
    funext ρ
    simp [dl, Finset.sum_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  simp only [map_smul]

theorem sum_dl (d : Q.NFData P A) : ∑ ρ, d.κ (dl ρ) = 1 := by
  have h : ∑ ρ, (dl ρ : M.Ty P → ℂ) = 1 := by
    funext x
    simp [dl, Finset.sum_apply]
  rw [← map_sum, h, map_one]

theorem dl_mul_kap (d : Q.NFData P A) (ρ : M.Ty P) (g : M.Ty P → ℂ) :
    d.κ (dl ρ) * d.κ g = g ρ • d.κ (dl ρ) := by
  have h : dl ρ * g = g ρ • dl ρ := by
    funext x
    by_cases hx : x = ρ
    · subst hx
      simp [dl]
    · simp [dl, hx]
  rw [← map_mul, h, map_smul]

theorem kap_comm (d : Q.NFData P A) (hR : d.Rel) (f : M.Ty P → ℂ) {g : A}
    (hg : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : d.κ f * g = g * d.κ f := by
  have hm : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} := Or.inl (Or.inr hg)
  exact (hR.2.1 f g hm).eq

theorem fns_comm' (d : Q.NFData P A) {x y : A}
    (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : x * y = y * x :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem comb {k : ℕ} {lam : Fin (k + 1) → ℂ}
    (hlam : ∀ p : ℂ[X], p.natDegree ≤ k → ∑ j : Fin (k + 1), lam j * p.eval ((j : ℕ) : ℂ) = p.coeff (k - 1))
    (p : ℂ[X]) (hp : p.natDegree ≤ k) (O : A) :
    ∑ j : Fin (k + 1), lam j • (p.eval ((j : ℕ) : ℂ) • O) = p.coeff (k - 1) • O := by
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hlam p hp]

theorem e10 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 1 0 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nab)) +
      ((xpol P ρ) * (X + C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζb)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ ρ0, (C (fl P l ρ ρ0) * xepol P l ρ0).eval Y • (d.SS l * d.κ (dl ρ0)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζbG : d.L.GG * d.L.ζb = d.L.ζb * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * d.L.ζb := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζb * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζb * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζb * (d.L.GG * d.L.GGi)) := by rw [hζbG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζb := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.l0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.l0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.l0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.l0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.weightedSumBis, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : d.κ (dl ρ) * d.SS l = d.SS l * d.κ (fl P l ρ) := by
      apply hR.2.2.2.1 l
      intro ρ0 ρ' hup
      by_cases h : ρ' = ρ
      · subst h
        simp [dl, fl, hup]
      · have hn : ¬ M.Up P l ρ0 ρ := fun h2 => h (up_func hup h2)
        simp [dl, fl, h, hn]
    rw [← mul_assoc, hc, mul_assoc, ← map_mul, kap_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ0 _ => ?_)
    rw [mul_smul_comm]
    congr 1
    simp [Polynomial.eval_mul, Polynomial.eval_C, xepol_eval]

theorem e01 (d : Q.NFData P A) (hR : d.Rel) (ρ : M.Ty P) (Y : ℂ) :
    d.κ (dl ρ) * d.QQ Y 0 1 =
      (xpol P ρ).eval Y • (-(d.L.GG * d.κ (dl ρ) * d.L.nabs)) +
      ((xpol P ρ) * (X - C (1 / 2 : ℂ))).eval Y • (-(d.κ (dl ρ) * d.L.ζ)) +
      ∑ l ∈ Finset.Icc 1 (P.k - 1), (xepol P l ρ).eval Y • (d.κ (dl ρ) * star (d.SS l)) := by
  have hG : d.κ (dl ρ) * d.L.GG = d.L.GG * d.κ (dl ρ) := kap_comm d hR _ (by simp)
  have hGGi : d.L.GG * d.L.GGi = 1 := d.L.GG_GGi
  have hζG : d.L.GG * d.L.ζ = d.L.ζ * d.L.GG := fns_comm' d (by simp) (by simp)
  have hx : d.κ (dl ρ) * d.x Y = (xpol P ρ).eval Y • d.κ (dl ρ) := by
    rw [Q.NFData.x, dl_mul_kap]
    simp only [xpol_eval]
  have key : d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * d.L.ζ := by
    calc d.L.GG * d.κ (dl ρ) * (d.L.ζ * d.L.GGi) = d.κ (dl ρ) * (d.L.GG * d.L.ζ * d.L.GGi) := by
          rw [← hG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * (d.L.ζ * (d.L.GG * d.L.GGi)) := by rw [hζG]; simp only [mul_assoc]
      _ = d.κ (dl ρ) * d.L.ζ := by rw [hGGi, mul_one]
  show d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) = _
  rw [mul_add]
  congr 1
  · calc d.κ (dl ρ) * (d.L.GG * d.x Y * d.L.m0 Y)
          = d.L.GG * (d.κ (dl ρ) * d.x Y) * d.L.m0 Y := by
            rw [← mul_assoc, ← mul_assoc, hG]; simp only [mul_assoc]
      _ = (xpol P ρ).eval Y • (d.L.GG * d.κ (dl ρ) * d.L.m0 Y) := by
            rw [hx, mul_smul_comm, smul_mul_assoc]
      _ = _ := by
            rw [R.LevelData.m0, mul_sub, mul_neg, ← Algebra.smul_def, mul_smul_comm, key]
            rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
            module
  · rw [Q.NFData.S12, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← mul_assoc, dl_mul_kap]
    simp only [xepol_eval, smul_mul_assoc]

end ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
end

