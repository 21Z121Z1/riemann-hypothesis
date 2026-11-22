import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0010

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillOfEmpty
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem kill_rename {R σ τ : Type} [CommRing R] (f : σ → τ) (S : Set τ) (P : MvPolynomial σ R) :
    kill S (rename f P) = rename f (kill (f ⁻¹' S) P) := by
  have h : (kill S).comp (rename f) = (rename f).comp (kill (f ⁻¹' S) : MvPolynomial σ R →ₐ[R] _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, kill, aeval_X]
    by_cases h1 : f i ∈ S
    · have h2 : i ∈ f ⁻¹' S := h1
      rw [if_pos h1, if_pos h2, map_zero]
    · have h2 : i ∉ f ⁻¹' S := h1
      rw [if_neg h1, if_neg h2, rename_X]
  exact AlgHom.congr_fun h P

theorem kill_of_empty {R σ : Type} [CommRing R] (S : Set σ) (hS : S = ∅) (P : MvPolynomial σ R) : kill S P = P := by
  subst hS
  have h : (kill (∅ : Set σ) : MvPolynomial σ R →ₐ[R] _) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [kill]
  rw [h]
  rfl

theorem li_mono_words {R σ ι α : Type} [CommRing R] [IsDomain R] (Tset : Set σ) (w : α → MvPolynomial σ R)
    (hw : LinearIndependent R w) (M : ι → σ →₀ ℕ) (x : ι → α) (hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ Tset)
    (hsup : ∀ q, w (x q) ∈ supported R Tsetᶜ) (hinj : ∀ q q', M q = M q' → x q = x q' → q = q') :
    LinearIndependent R fun q => monomial (M q) (1 : R) * w (x q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum q₀ hq₀
  obtain ⟨Φ, hΦmono⟩ : ∃ Φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R, ∀ (n : σ →₀ ℕ) (a : R),
      Φ (monomial n a) = if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) a else 0 := by
    refine ⟨(MvPolynomial.basisMonomials σ R).constr R (fun n : σ →₀ ℕ =>
      if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) (1 : R) else 0), fun n a => ?_⟩
    have e : monomial n a = a • (MvPolynomial.basisMonomials σ R) n := by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
    split_ifs
    · rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    · rw [smul_zero]
  have hkey : ∀ q, Φ (monomial (M q) (1 : R) * w (x q)) = if M q = M q₀ then w (x q) else 0 := by
    intro q
    have hwsup := hsup q
    rw [mem_supported] at hwsup
    have hT : ∀ n ∈ (w (x q)).support, (M q + n).filter (· ∈ Tset) = M q ∧
        (M q + n).filter (· ∉ Tset) = n := by
      intro n hn
      have hnv : ∀ v, n v ≠ 0 → v ∉ Tset := fun v hv =>
        hwsup ((mem_vars v).2 ⟨n, hn, Finsupp.mem_support_iff.2 hv⟩)
      constructor
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_pos hv]
          have : n v = 0 := by
            by_contra h
            exact hnv v h hv
          rw [this, add_zero]
        · rw [if_neg hv]
          by_contra h
          exact hv (hM q v (Ne.symm h))
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_neg (not_not.2 hv)]
          by_contra h
          exact hnv v (Ne.symm h) hv
        · rw [if_pos hv]
          have : M q v = 0 := by
            by_contra h
            exact hv (hM q v h)
          rw [this, zero_add]
    conv_lhs => rw [(w (x q)).as_sum]
    rw [Finset.mul_sum, map_sum]
    simp only [monomial_mul, one_mul, hΦmono]
    split_ifs with hMq
    · conv_rhs => rw [(w (x q)).as_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(hT n hn).1, (hT n hn).2, if_pos hMq]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [(hT n hn).1, if_neg hMq]
  have hxinj : Function.Injective (fun q : {q // M q = M q₀} => x q.1) := by
    intro a b h
    exact Subtype.ext (hinj a.1 b.1 (a.2.trans b.2.symm) h)
  have hfib : LinearIndependent R (w ∘ fun q : {q // M q = M q₀} => x q.1) := hw.comp _ hxinj
  have h2 : ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0) = 0 := by
    have h := congrArg Φ hsum
    rw [map_sum, map_zero] at h
    calc ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0)
        = ∑ q ∈ s, Φ (g q • (monomial (M q) (1 : R) * w (x q))) :=
          Finset.sum_congr rfl fun q _ => by rw [map_smul, hkey]
      _ = 0 := h
  have h3 : ∑ q ∈ s.subtype (fun q => M q = M q₀), g q.1 • (w ∘ fun q : {q // M q = M q₀} => x q.1) q = 0 := by
    simp only [Function.comp_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun q => g q • w (x q)), Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h2
    split_ifs <;> simp
  exact linearIndependent_iff'.1 hfib (s.subtype (fun q => M q = M q₀)) (fun q => g q.1) h3 ⟨q₀, rfl⟩
    (Finset.mem_subtype.2 hq₀)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TailTGlueT
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def tailT (t : ℕ) (la : Fin (r + K) → ℤ) : Fin (K + t) → ℤ := fun l =>
  if h : (r - t) + l.val < r + K then la ⟨(r - t) + l.val, h⟩ else 0

def glueT (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) : Fin (r + K) → ℤ := fun m =>
  if h : m.val < r - t then be else if h' : m.val - (r - t) < K + t then τ ⟨m.val - (r - t), h'⟩ else 0

theorem tailT_glueT (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) : tailT (r := r) t (glueT t be τ) = τ := by
  funext l
  have hl := l.2
  have h1 : (r - t) + l.val < r + K := by omega
  simp only [tailT, glueT, dif_pos h1]
  simp

theorem tailT_apply (t : ℕ) (ht : t ≤ r) (la : Fin (r + K) → ℤ) (l : Fin (K + t)) :
    tailT t la l = la ⟨(r - t) + l.val, by have := l.2; omega⟩ := by
  unfold tailT; rw [dif_pos]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem finite_SAll [NeZero r] [NeZero K] (H : HypT N n0 r K LL B od bb a La p) :
    (SAll (r := r) (K := K) LL n0 B).Finite := by
  have hS : (SP (r := r) (K := K) LL n0 B).Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.pi Set.univ fun _ : Fin (r + K) => Set.Icc (-(beA n0 B : ℤ)) (beA n0 B)) fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _).subset ?_
    rintro μ ⟨dd, hpa⟩
    obtain ⟨P, rfl⟩ := hpa.path
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, true_implies]
    intro s m
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast dminus_le_beA H hpa.degs s.val)) (neg_dminus_le_mu P s.val s.2 m), path_le_beA H P hpa s.val s.2 m⟩
  refine (hS.biUnion fun μ _ => (Set.finite_singleton μ).prod (finite_St (tanPart μ))).subset ?_
  rintro ⟨μ, I⟩ ⟨h1, h2⟩
  exact Set.mem_biUnion h1 ⟨rfl, h2⟩

open Classical in

def Af (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) :
    Finset (QT N r K) :=
  hfin.toFinset.filter fun q => ∀ t : Fin (N + 1), t.val ≤ s → q.1 t = μ0 t

open Classical in
theorem Af_fiber (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (la' : Fin (r + K) → ℤ) :
    (Af hfin s μ0).filter (fun q => q.1 (⟨s, hs⟩ : Fin N).succ = la') =
      Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la') := by
  ext q
  simp only [Af, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, h⟩, h'⟩
    refine ⟨hq, fun t ht => ?_⟩
    by_cases e : t = (⟨s, hs⟩ : Fin N).succ
    · subst e
      rw [Function.update_apply, if_pos rfl]
      exact h'
    · rw [Function.update_of_ne e]
      apply h
      have : t.val ≠ s + 1 := fun h2 => e (Fin.ext (by simp [h2]))
      omega
  · rintro ⟨hq, h⟩
    refine ⟨⟨hq, fun t ht => ?_⟩, ?_⟩
    · have e : t ≠ (⟨s, hs⟩ : Fin N).succ := by
        rintro rfl
        simp at ht
      rw [h t (by omega), Function.update_of_ne e]
    · rw [h _ (by simp)]
      simp

theorem Af_step (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ)
    (hs : s < N) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (q : QT N r K) (hq : q ∈ Af hfin s μ0) :
    Dominant (q.1 (⟨s, hs⟩ : Fin N).succ) ∧
      StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (q.1 (⟨s, hs⟩ : Fin N).succ) := by
  classical
  simp only [Af, Finset.mem_filter, Set.Finite.mem_toFinset] at hq
  obtain ⟨⟨hsp, -⟩, hμ⟩ := hq
  obtain ⟨dd, hpa⟩ := hsp
  obtain ⟨P, hP⟩ := hpa.path
  have hc : q.1 (⟨s, hs⟩ : Fin N).castSucc = μ0 (⟨s, hs⟩ : Fin N).castSucc := hμ _ (by simp)
  rw [← hc]
  have hstep := P.step ⟨s, hs⟩
  rw [hP] at hstep
  refine ⟨by rw [← hP]; exact P.dom _, fun hlt => ?_, fun hge => ⟨⟨dd ⟨s, hs⟩, ?_⟩, fun m hm => hpa.head _ m hge hm⟩⟩
  · rwa [← hpa.degs _ hlt]
  · have hv : LL.vec ⟨s, hs⟩ = true := H.vec_true_of_late _ (Nat.le_add_right_of_le hge)
    rwa [if_pos hv] at hstep

open Classical in

theorem Af_card_sum (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (E : Finset (Fin (r + K) → ℤ))
    (hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ E) :
    (Af hfin s μ0).card = ∑ la' ∈ E, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la')).card := by
  rw [Finset.card_eq_sum_card_fiberwise hE]
  refine Finset.sum_congr rfl fun la' _ => ?_
  rw [Af_fiber hfin s hs]

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ThresholdPowerBoundOfCounts
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem threshold_arith_letter_case (k Ns c q bo : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hc : 40 * (k * Ns) ≤ c) (hq : 9 / 10 * c ≤ q)
    (hb : q - k < bo) : c / 2 ≤ 2 / 3 * bo - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem threshold_arith_w_case (k Ns c q fl r : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hr : r ≤ k) (hc : 40 * (k * Ns) ≤ c)
    (hq : 9 / 10 * c ≤ q) (hfl : q - 1 < fl) :
    c / 2 ≤ 2 / 3 * (fl - (k + r + 1) - (k * Ns + 1)) - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem natDiv_gt (n m : ℕ) (hm : 0 < m) : (n : ℝ) / (m : ℝ) - 1 < ((n / m : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n m
  have hr := Nat.mod_lt n hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have e2 : ((n % m : ℕ) : ℝ) < m := by exact_mod_cast hr
  rw [div_sub_one hm'.ne', div_lt_iff₀ hm']
  linarith

theorem threshold_power_bound_of_counts (C₀ : ℝ) (h41 : TopCountLowerBounds C₀) (hOld : OldestLetterInSegment) : ThresholdPowerLowerBound C₀ := by
  unfold ThresholdPowerLowerBound
  intro p n' r K _ _ _ X hX hC1 hC2 j bb hS x hx
  have b0 := basics hX
  have hO := hOld p n' r K X hX j x hx
  have hob := mem_letters_bounds hO.1
  have h41' := (h41 p n' r K X hX hC1 hC2).1 _ hob.2.2
  have hdeg := (hX.degs _ hob.2.2).1
  have hk : Dat.k (r := r) K = ((r : ℝ) + (K : ℝ)) := by unfold Dat.k; push_cast; rfl
  have hk5 : (5 : ℝ) ≤ ((r : ℝ) + (K : ℝ)) := hk ▸ b0.k5
  have hN := b0.Ns1
  have hY := b0.Y1
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := b0.p1.le
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ (X.Rj p K j) := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have hden := den_pos hX j
  have hTa : 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j = X.a := by
    rw [← hk]
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hEW : (X.F.dist j (X.F.oldest j x)) ≤ (X.F.dist j (X.F.fr (j - 1) 0)) := by
    unfold Frames.dist
    omega
  have hPe : (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) := pow_le_pow_right₀ hP1 hEW
  have hDpos : 0 < ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by positivity
  have hc : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    rw [le_div_iff₀ hDpos, pow_add]
    have hkN : 0 ≤ ((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ) := by positivity
    have h40 : (40 : ℝ) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) := by nlinarith
    have h1 : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h40 hkN]
    have hq0 : 0 ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j := by positivity
    calc 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) * (p : ℝ) ^ (X.Rj p K j))
        ≤ 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hPe hRT hRp (by positivity)) (by positivity)
      _ ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) := mul_le_mul_of_nonneg_right h1 hq0
      _ = X.a := by rw [← hTa]; ring
      _ ≤ ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) := hdeg
  have hq : 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    calc 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) = (9 / 10 * ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ)) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by ring
      _ ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by gcongr
  have hsplit : ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) / 2 = (p : ℝ) ^ (X.Rj p K j) * ((((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) / 2) := by
    rw [pow_add]
    field_simp
  unfold Dat.th Dat.Bo Dat.thc
  rw [hsplit]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ hRp
  split_ifs with hW
  · have hfl := natDiv_gt (X.a' p K (posOf n' (X.F.oldest j x))) (p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) (pow_pos (by have := hX.p13; omega) _)
    push_cast at hfl
    have := threshold_arith_w_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ (r : ℝ) hk5 hN (by linarith) hc hq hfl
    unfold Dat.Bw Dat.m0
    push_cast
    have hcast : ((((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℤ) / ((p : ℤ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) : ℤ) : ℝ) = (((X.a' p K (posOf n' (X.F.oldest j x))) / p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← Int.natCast_div, Int.cast_natCast]
    rw [hcast]
    linarith
  · have hb := hS _ (hO.2 hW)
    rw [hk] at hb
    have := threshold_arith_letter_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ hk5 hN hc hq hb
    linarith

theorem order_numeric_bound_of_oldest (C₀ : ℝ) (hOld : OldestLetterInSegment) : OrderNumericBound C₀ := by
  unfold OrderNumericBound
  intro p n' r K _ _ _ X hX _ _ j x hx
  have b := basics hX
  have hO := hOld p n' r K X hX j x hx
  simp only [Dat.toLate, Finset.mem_filter] at hx
  have hxb := mem_letters_bounds hx.1
  have hob := mem_letters_bounds hO.1
  have hL : (X.L₁ : ℤ) < x - X.F.oldest j x := hX.valid.2.2.2.2.2.2.2.2 j x hx.1 hx.2
  have hde : X.F.dist j x + X.L₁ + 1 ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  have hew : X.F.dist j (X.F.oldest j x) ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    omega
  have hP : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hP0 : (0 : ℝ) < p := by linarith
  have hP1 : (1 : ℝ) ≤ p := by linarith
  have hk : (5 : ℝ) ≤ Dat.k (r := r) K := b.k5
  have hY := b.Y1
  have hNs := b.Ns1
  have hden := den_pos hX j
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ X.Rj p K j := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have ha : 0 ≤ X.a := hTa ▸ mul_nonneg hden.le hTp
  have hLd : (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) :=
    pow_le_pow_right₀ hP1 (by omega)
  have hLe : (p : ℝ) * (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hP1 (by omega)
  have hLpos : (0 : ℝ) < (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by positivity
  have hEpos : (0 : ℝ) < (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by positivity
  have hA : Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [le_div_iff₀ hLpos]
    have h8 : 1 ≤ 8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K := by nlinarith
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
      linarith
    have hq : 0 ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by positivity
    calc Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ (X.L₁ + X.F.dist j x)
        ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRT (by linarith)) hLd hLpos.le (by positivity)
      _ ≤ (8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ)) * (Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := le_mul_of_one_le_left hq h8
      _ = X.a := by rw [← hTa]; ring
  have hB : (p : ℝ) ^ X.Rj p K j * (4 * X.a * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹) ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [pow_add, mul_inv, le_div_iff₀ hLpos]
    have hRpos : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
    have e : (p : ℝ) ^ X.Rj p K j * (4 * X.a * (((p : ℝ) ^ X.F.dist j (X.F.oldest j x))⁻¹ * ((p : ℝ) ^ X.Rj p K j)⁻¹)) = 4 * X.a / (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hEpos]
    nlinarith [mul_le_mul_of_nonneg_left hLe ha, mul_nonneg (mul_nonneg ha hLpos.le) (by linarith : (0 : ℝ) ≤ p - 4)]
  have z1 : (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) = ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have z2 : (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ))) = ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have hkne : Dat.k (r := r) K ≠ 0 := by linarith
  have hT1 : (p : ℝ) ^ X.Rj p K j * (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j))) = X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ X.F.dist j x) := by
    rw [pow_add]
    field_simp
  rw [div_eq_mul_inv] at hA hB
  have hI : 0 ≤ X.a * ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := mul_nonneg ha (inv_nonneg.mpr hLpos.le)
  unfold Dat.oc Dat.o
  push_cast
  rw [z1, z2, mul_add, hT1]
  split_ifs <;> linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

