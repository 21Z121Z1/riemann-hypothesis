import Formalism.LocalToGlobal.Columns.Bundle0023
import Formalism.LocalToGlobal.Columns.Bundle0044
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
import Formalism.LocalToGlobal.Columns.OcbPhiFIdxFPos
import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral
import Formalism.LocalToGlobal.Columns.Bundle0045
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.Columns.ChainOneB
import Formalism.LocalToGlobal.Columns.Bundle0013

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawLev
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Bridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clL_base (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true) :
    OcbBase Ch sel mu cst m2 where
  hX := hX
  hPr := hPr
  hCh := hCh
  hm := hok.hm
  cst_ok := hok.cst_ok
  sharp := hs
  psi0 := hok.psi0
  depthG := hok.depthG

theorem clL_bridge (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j) (hb : ∀ P, L.h j b P = 1) (w : {w // w ∈ Pr.vGs}) (g : ↥(L.levG j b w).H)
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w.1)
    (hred : ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (κ x) = g.1.1.mulVec (redV w.1 x)) :
    clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) ∧
      LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t j (R.N j) (cOf R j) (clL_ext (cOf R j) κ).toLinearMap =
        (((L.levG j b w).lam g : X.Kˣ) : X.K) := by
  classical
  have hB := clL_base hok hX hPr hCh hs

  have hpat : ocbXPat R.k R.rS j R.t g.1 := by
    obtain ⟨g', hg', hred'⟩ := (hok.grpG j b w g.1).1 g.2
    rw [hb] at hg'
    exact (ocbGrpGLoc_holds Ch sel mu cst m2 hB j hj w g.1).1 ⟨g', hg', hred'⟩
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm hj
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr w.2
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hrr : R.r = R.k + 2 * R.rS + 1 := by
    unfold Ranks.r
    omega
  have hcj : cOf R j + j = 2 * R.rS + 1 := by
    have := hB.hm
    unfold cOf
    omega
  have hJat : Jat (Pr := Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat
    rw [if_pos w.2, hB.sharp, if_pos rfl]

  set Gm := LinearMap.toMatrix' κ.toLinearMap with hGm
  have hκi : κ.symm ∈ GLint X.E (R.N j) w.1 := (GLint X.E (R.N j) w.1).inv_mem hκ
  have hGi : ∀ i i', IntAt w.1 (Gm i i') := by
    intro i i'
    rw [hGm, LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκ _).2 (ciSingle_mem i')) i
  have hGii : ∀ i i', IntAt w.1 (LinearMap.toMatrix' κ.symm.toLinearMap i i') := by
    intro i i'
    rw [LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκi _).2 (ciSingle_mem i')) i
  have hGred : ∀ i i', redP w.1 (Gm i i') = g.1.1 i i' := by
    intro i i'
    rw [ciEntry hred i i', hGm, LinearMap.toMatrix'_apply]
    rfl
  have hE1 := clL_extM_mul (cOf R j) κ
  have hE2 := clL_extM_mul' (cOf R j) κ
  have hap : ∀ v, clL_ext (cOf R j) κ v = (ciExtM (cOf R j) Gm).mulVec v := fun v => clL_ext_apply _ κ v
  have he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j),
      IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1)) := by
    intro A hA l l'
    rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
    exact hA _ _
  have hS : clL_ext (cOf R j) κ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) :=
    ciEquiv_stab (fun v hv => ciExtM_maps hq0 Gm _ (he Gm hGi) v hv)
      (fun v hv => ciExtM_maps hq0 _ _ (he _ hGii) v hv)
  have hM := reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) Gm _ hap
  have hJ : clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_
    · intro y y' hlt
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := fun he' => by
          have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) <
              betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1) := hlt
          rw [he'] at hlt'
          exact lt_irrefl _ hlt'
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        refine not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall
        rw [← hrr]
        exact hlt
      · subst h2
        exact absurd hlt (lt_irrefl _)
      · rfl
    · intro y hy
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        have hyk : y.1 < R.k + j := by
          rw [framePos_of_lt_dim h1.1, hrr] at hy
          split_ifs at hy <;> omega
        have h3 := hpat.1 y.1 hyk
        unfold ocbM at h3
        rw [dif_pos ⟨h1.1, h1.1⟩] at h3
        exact h3
      · rfl
      · exact absurd rfl h2
    · intro y y' hy hy'
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := by
          intro he'
          rw [he'] at hy
          omega
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        exact not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall
      · subst h2
        omega
      · rfl
  refine ⟨hJ, ?_⟩

  have hr1 : clL_ext (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
    rw [hb]
    refine Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction _ _ hE1 hE2, Subgroup.mem_comap.2 ?_⟩
    simpa [MulAut.conj_apply, hJat] using hJ
  have hlam := hok.chrG j b w g κ (clL_ext (cOf R j) κ) hr1 (fun x => clL_ext_inX _ κ x) hred
  rw [hlam]
  unfold chiInv
  rw [hb]
  have hn1 : Loc.n1Arg (clL_ext (cOf R j) κ) = 0 := by
    unfold Loc.n1Arg
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < cOf R j - 1 := Finset.mem_range.1 hi
    unfold Loc.atN
    rw [dif_pos (by omega)]
    have e1 : (⟨R.N j + i, by omega⟩ : Fin (R.N j + cOf R j)) = Fin.natAdd (R.N j) ⟨i, by omega⟩ := rfl
    rw [e1, clL_ext_natAdd]
    unfold Loc.eN
    simp
  rw [hn1, hok.cst_ok.psi_int _ 0 (ChainCounts.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  rw [if_pos w.2, hs, if_pos rfl]
  simp

end Bridge

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainOneOkL
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section E1

variable {E K L : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field L] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable (P) in

def ookRed {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') => redP P (Loc.atN (xj (Loc.eN E n' s.1)) l.1))

theorem ookRed_spec {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : ocbXRed P xj (ookRed P xj) := by
  intro l s hl hs
  unfold ookRed
  rw [ocbS_atN_toLin' _ hl hs]
  rfl

theorem ookAtN_add {N : ℕ} (v w : Fin N → E) (l : ℕ) : Loc.atN (v + w) l = Loc.atN v l + Loc.atN w l := by
  unfold Loc.atN
  split_ifs
  · rfl
  · rw [add_zero]

theorem xInt_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (hc' : c' = c + 1) (Ψ : Loc.SF E K (n' + c') (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj ≠ 0) : ocbXInt P xj := by
  by_contra hx
  exact h (firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi vals wt xj hx)

theorem firstUnfolding_reduction_independent (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B A' B' : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (hA' : c + 1 ≤ A') (hB' : 1 ≤ B') (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A' B') ((q : K) ^ B')⁻¹ Ψ xj =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  by_cases hx : ocbXInt P xj
  · apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA' hB' xj (ookRed P xj) hx (ookRed_spec xj),
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx]

theorem firstUnfolding_add_eq_self_of_intAt_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (xj z : (Fin n' → E) →ₗ[E] (Fin n → E))
    (hz : ∀ l s, l < n → s < n' → IntAt P (Loc.atN (z (Loc.eN E n' s)) l / (q : E))) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ (xj + z) =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hD : ∀ l s, l < n → s < n' → Loc.atN ((xj + z) (Loc.eN E n' s)) l =
      Loc.atN (xj (Loc.eN E n' s)) l + (q : E) * (Loc.atN (z (Loc.eN E n' s)) l / (q : E)) := by
    intro l s _ _
    rw [LinearMap.add_apply, ookAtN_add, mul_div_cancel₀ _ hq0]
  have hint : ocbXInt P (xj + z) ↔ ocbXInt P xj := by
    constructor
    · intro h l s hl hs
      have h1 := h l s hl hs
      rw [hD l s hl hs] at h1
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).1 h1
    · intro h l s hl hs
      rw [hD l s hl hs]
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).2 (h l s hl hs)
  by_cases hx : ocbXInt P xj
  · have hred' : ocbXRed P (xj + z) (ookRed P xj) := by
      intro l s hl hs
      rw [ookRed_spec xj l s hl hs, hD l s hl hs, redP_add_natCast_mul hq (hz l s hl hs)]
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB (xj + z) (ookRed P xj) (hint.2 hx) hred',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ (xj + z) (fun h => hx (hint.1 h))]

end E1

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ookLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hkr : k₀ ≤ r) (hra : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  congr 1
  · congr 1
    have hb1 : ∀ i ∈ Finset.range (k₀ - 1), i < a ∧ i + 1 < a := fun i hi => by simp at hi; omega
    have hb2 : ∀ i ∈ Finset.range (r - k₀ - 1), k₀ + i < a ∧ k₀ + i + 1 < a := fun i hi => by simp at hi; omega
    rw [reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1)]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.2)
      (Finset.sum_congr rfl fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.2)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < j := by simpa using hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < a := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right _ hi'
      nlinarith
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).1)]
    congr 1
    ext s s'
    exact (h _ _ (hb s) (hb s')).2.2

open Classical in

theorem ookPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hkr : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  rw [phiGS_eq, phiGS_eq]
  set M := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set M' := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' with hM'
  set a := r + (j - 1) * t with ha
  have hra : r ≤ a := Nat.le_add_right _ _
  have k1 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < a → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : symPhiCond P q k₀ rS r t j c n M' ↔ symPhiCond P q k₀ rS r t j c n M := by
    unfold symPhiCond
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').1 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [← k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [← k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [← k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').2 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
  by_cases hC : symPhiCond P q k₀ rS r t j c n M
  · rw [if_pos (hc.2 hC), if_pos hC]
    have htrip : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => ⟨hC.1 p p' (by omega) hp', (hc.2 hC).1 p p' (by omega) hp', k3 p p' (by omega) hp'⟩
    congr 1
    · exact ookLamGvS_congr ψ₀ χ M M' hkr hra (le_refl _) htrip
    · congr 1
      apply ciUnitV_congr
      rw [redP_det (Matrix.of fun s s' : Fin a => M' s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).2.1),
        redP_det (Matrix.of fun s s' : Fin a => M s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).1)]
      congr 1
      ext s s'
      exact (htrip s.1 s'.1 s.2 s'.2).2.2
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

theorem ookEntB_joinX (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (hk : k₀ ≤ n') (x₀ : HomE E n' n) (y' : Sp E n)
    {p s : ℕ} (hp : p < n) (hs : s < n') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p (LocE.fPos k₀ c' n' s) =
      x₀ (Pi.single ⟨s, hs⟩ 1) ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' (LocE.fPos k₀ 1 n' s) = s := ocbPhi_fIdx_fPos hk (by omega)
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, ciScE_lt _ hs, dif_pos (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) s) = (Pi.single ⟨s, hs⟩ 1 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) s (Fin.castAdd 1 i) = _
    unfold Loc.eN
    simp only [Fin.val_castAdd, Pi.single_apply, Fin.ext_iff]
  have e2 : Loc.eN E (n' + 1) s ⟨n', by omega⟩ = 0 := by
    unfold Loc.eN
    rw [if_neg (by simp; omega)]
  rw [e1, e2, zero_mul, add_zero, sub_zero, zpow_zero, mul_one]

theorem ookFIdx_lt {k₀ c' n' p' : ℕ} (hc' : c' = 1) (hk : k₀ ≤ n') (hp' : p' < n' + c') (hne : p' ≠ k₀) :
    LocE.fIdx k₀ c' n' p' < n' ∧ LocE.fPos k₀ c' n' (LocE.fIdx k₀ c' n' p') = p' := by
  subst hc'
  exact ⟨by unfold LocE.fIdx; split_ifs <;> omega, symFPos_fIdx hk hp'⟩

theorem ookPrX_le {k₀ rS r t n c : ℕ} :
    Loc.prX (Loc.Cbe (LocE.JGsym P q k₀ rS r t n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JGsym P q k₀ rS r t n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← ciMem_lamY (P := P) (q := q) (c := c) (fun i => i + 1) (g x), ← hg]
  exact (hr'.1 _).trans (ciMem_lamY _ _)

end Cong

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.KernelEquivTrivialTuple
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Asm

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {Am : Amb X} {u : Pr.Word}

theorem xiEquiv_one (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hM : MatEquiv W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2))
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h1 : Cp1EquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY)
    (hTop : RefKEquiv W Λ Ch sel mu cst hQ m2 Am u (m2 + 1)) :
    XiEquiv W Λ Ch sel mu cst Am u
      (refXi1 Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) hQ m2 (oneAl Λ sel mu m2) u) := by
  refine xiEquiv_of_refK fun i => ?_
  rcases lt_trichotomy i m2 with h | h | h
  · exact refKEquiv_of_mat h hM
  · subst h
    exact referenceKernelEquiv_of_lastComponent hX hPr hF hY h1
  · rcases Nat.lt_or_ge (m2 + 1) i with h' | h'
    · exact refKEquiv_above h'
    · have e : i = m2 + 1 := by omega
      subst e
      exact hTop

end Asm

section Mu0

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem kernelEquiv_trivialTuple (hX : X.Ok) (hPr : Pr.Ok) (hm : m2 + 1 < R.m) (hTh : ThHyp W Ch sel (mu0 X.F X.E X.K S) cst Am u m2) {G : ChGlob X R.m}
    (hL : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).Ok Ch sel (mu0 X.F X.E X.K S) cst G m2)
    (hXi : ∀ i, i < m2 → ∀ (al : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).β i)
      (be : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).β (i + 1)),
      XiLaw Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) i al be)
    (hPsi : ∀ al, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) m2 al
      (oneAl Λ sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl))
    (hF : FixE (R := R) Λ m2) (hTop : RefKEquiv W Λ Ch sel (mu0 X.F X.E X.K S) cst (exceptional_primes_trivial_tuple sel S) m2 Am u (m2 + 1)) :
    XiEquiv W Λ Ch sel (mu0 X.F X.E X.K S) cst Am u
      (refXi1 Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) (exceptional_primes_trivial_tuple sel S) m2
        (oneAl Λ sel (mu0 X.F X.E X.K S) m2) u) :=
  xiEquiv_one hX hPr hF (matrix_equivariance_trivial_tuple W Ch sel S cst _ Am u m2 hm hPr hTh hL hXi) (coupling_index_set_finite sel _ cst _ u m2 _)
    (penultimate_equivariance_trivial_tuple W Ch sel S cst _ Am u m2 hm hPr hTh hL _ _ hPsi) hTop

end Mu0

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbLevIsSym
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def FixESym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → FixE (R := R) (colLevSym Ch) m2

def OcbLevIsSym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → OcbLevIs Ch (colLevSym Ch) m2

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQTop
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl)

section QTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
  {H : Subgroup (GLG E n SG)}

def recClsFOf (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q)
    (hE : FrExists (n := n) ST SG Q) (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q)
    (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) : RecClsF hc n ST SG Q H q s :=
  recClsF q (decoPtSurjF_of hS hQ q hF (qdf_lift q)) hF hE s hs

end QTop

end Formalism.L2.Col
end
end

