import Formalism.LocalToGlobal.Columns.Bundle0050
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.Bundle0049
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.Bundle0044
import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawXiTgt
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clT_stab0 {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) :
    κ ∈ stabL E (n + 0) (LocE.lamY P q n 0 (fun i => i + 1)) := by
  intro x
  have e : ∀ y : Sp E (n + 0), y ∈ LocE.lamY P q n 0 (fun i => i + 1) ↔ y ∈ stdAt E n P := by
    intro y
    unfold LocE.lamY
    rw [ciMem_sclLat, ciMem_stdAt]
    refine forall_congr' fun l => ?_
    unfold LocE.scE
    rw [if_pos (show l.1 < n from l.2), zpow_zero, inv_one, one_mul]
  rw [e, e]
  exact hκ x

theorem clT_extEnt {n c : ℕ} (κ₁ : Sp E n ≃ₗ[E] Sp E n) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    redP P (ocbBEnt n n q (clL_ext c κ₁).toLinearMap l s) =
      if l < n ∧ s < n then redP P (Loc.atN (κ₁ (Loc.eN E n s)) l) else if l = s then 1 else 0 := by
  unfold ocbBEnt
  by_cases hsn : s < n
  · have hsc : LocE.scE n (fun i => i + 1) s = 0 := by unfold LocE.scE; rw [if_pos hsn]
    rw [ciEN hsn, LinearEquiv.coe_coe, clL_ext_inX, ocbS_atN_of_lt _ hl, ciInX_apply]
    by_cases hln : l < n
    · have hlc : LocE.scE n (fun i => i + 1) l = 0 := by unfold LocE.scE; rw [if_pos hln]
      rw [dif_pos hln, if_pos ⟨hln, hsn⟩, hsc, hlc, sub_zero, zpow_zero, mul_one, ocbS_eN_single hsn, ocbS_atN_of_lt _ hln]
    · rw [dif_neg hln, zero_mul, redP_zero, if_neg (fun h => hln h.1), if_neg (by omega)]
  · rw [LinearEquiv.coe_coe, clX_ext_eN κ₁ (by omega), ocbS_atN_of_lt _ hl]
    by_cases hls : l = s
    · subst hls
      simp only [Loc.eN, if_true, sub_self, zpow_zero, mul_one, redP_one]
      rw [if_neg (fun h => hsn h.2)]
    · have h1 : Loc.eN E (n + c) s ⟨l, hl⟩ = 0 := by
        simp only [Loc.eN]
        exact if_neg hls
      rw [h1, zero_mul, redP_zero, if_neg (fun h => hsn h.2), if_neg hls]

end Gen

section Tgt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem clT_inX_apply {k : Type} [CommRing k] {n c : ℕ} (x : Fin n → k) (l : Fin (n + c)) :
    Loc.inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  by_cases h : l.1 < n <;> simp [LinearMap.pi_apply, h]

theorem clT_vec_std {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {v : Sp E n}
    (h : ∀ l, l < n → IntAt P (Loc.atN v l)) : v ∈ stdAt E n P := by
  rw [ciMem_stdAt]
  intro i
  have := h i.1 i.2
  rwa [ocbS_atN_of_lt _ i.2] at this

theorem clT_bEnt0 {E : Type} [Field E] {n : ℕ} (q : ℕ) (g : Sp E n →ₗ[E] Sp E n) {l s : ℕ} (hl : l < n) (hs : s < n) :
    ocbBEnt n n q g l s = Loc.atN (g (Loc.eN E n s)) l := by
  unfold ocbBEnt LocE.scE
  rw [if_pos hs, if_pos hl, sub_zero, zpow_zero, mul_one]

set_option maxHeartbeats 800000 in

theorem clT_xiTgtLaw (σ : X.K →+* ℂ) {m2 i : ℕ} (hB : OcbBase Ch sel mu cst m2) (hi : i < m2) (hA : cOf R (i + 1) + 1 ≤ cst.A) :
    XiTgtLaw Ch sel mu cst i := by
  intro P hP κ' hκ' hJ w
  classical
  have hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := ciQ_mem P.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr hP
  have hp := ciQOf_prime hB.hPr hP
  have hcard := ciCard P.1
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero hu
  have hr := ocbRanks_step (R := R) hB.hm hi
  have hc' : cOf R i = cOf R (i + 1) + 1 := by
    unfold cOf
    have := hB.hm
    omega
  have hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1)
      (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
    unfold PhiAt
    rw [if_pos hP, hB.sharp]
    rfl
  let Φ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
    LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1))
  let Φr := @ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))
  have hsupp0 : ∀ y, Φ y ≠ 0 → ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s) :=
    fun y hy => ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) hr hc' y hy
  have hred0 : ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
      (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
        Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) → σ (Φ y) = Φr ybar :=
    fun y ybar hint hrd => ocbPhiGS_red hq hu σ (psi0P Ch P.1) (chiP Ch P.1) hr hc' y ybar hint hrd
  set h₀ := clL_ext (cOf R (i + 1)) κ' with hh₀def
  have hh₀ : h₀ ∈ stabL X.E (R.N (i + 1) + cOf R (i + 1))
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1) := (Subgroup.mem_inf.1 hJ).1
  obtain ⟨hbar, hred₀⟩ := ocbA_red_exists hq0 hh₀
  obtain ⟨htsupp, htred⟩ := ocbT_trans hq0 σ hc' hh₀ hred₀ Φ Φr hsupp0 hred0
  obtain ⟨gbar, hgred⟩ := ocbA_red_exists (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ')

  have hent : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) →
      Loc.atN (hbar (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l =
        if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) s)) l)
        else if l = s then 1 else 0 := by
    intro l s hl hs
    rw [(hred₀ l s hl hs).2]
    exact clT_extEnt κ' hl hs
  have hent' : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) →
      Loc.atN (hbar.symm (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l =
        if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ'.symm (Loc.eN X.E (R.N (i + 1)) s)) l)
        else if l = s then 1 else 0 := by
    intro l s hl hs
    rw [ocbT_red_symm hq0 hh₀ hred₀ hl hs, hh₀def, clL_ext_symm]
    exact clT_extEnt κ'.symm hl hs
  obtain ⟨hfix, hvec, hact⟩ := clX_fix_of_ent hbar _ hent
  obtain ⟨hfix', hvec', -⟩ := clX_fix_of_ent hbar.symm _ hent'
  have hR1 : hbar ∈ Loc.R1 (𝓞 X.E ⧸ P.1.asIdeal) (R.N (i + 1)) (cOf R (i + 1)) :=
    ⟨clX_R1cond hbar hfix hvec, clX_R1cond hbar.symm hfix' hvec'⟩
  have hn1 : Loc.n1Arg hbar = 0 := by
    unfold Loc.n1Arg
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [hvec _ (by omega), ocbS_atN_of_lt _ (by omega)]
    simp only [Loc.eN]
    exact if_neg (by simp)
  have hgent : ∀ (l m : Fin (R.N (i + 1))), gbar (Pi.single m 1) l = redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) m.1)) l.1) := by
    intro l m
    have h1 := (hgred l.1 m.1 l.2 m.2).2
    have e1 : LocE.scE (R.N (i + 1)) (fun i => i + 1) m.1 = 0 := by unfold LocE.scE; rw [if_pos m.2]
    have e2 : LocE.scE (R.N (i + 1)) (fun i => i + 1) l.1 = 0 := by unfold LocE.scE; rw [if_pos l.2]
    rw [e1, e2, sub_zero, zpow_zero, mul_one] at h1
    calc gbar (Pi.single m 1) l = Loc.atN (gbar (Loc.eN _ (R.N (i + 1) + 0) m.1)) l.1 := by
          rw [ocbS_eN_single (show m.1 < R.N (i + 1) + 0 from m.2), ocbS_atN_of_lt _ (show l.1 < R.N (i + 1) + 0 from l.2)]
          rfl
      _ = _ := h1
  have hg : ∀ x, hbar (Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) (gbar x) := by
    intro x
    funext m
    by_cases hm : m.1 < R.N (i + 1)
    · obtain ⟨l', rfl⟩ : ∃ l' : Fin (R.N (i + 1)), m = Fin.castAdd (cOf R (i + 1)) l' := ⟨⟨m.1, hm⟩, Fin.ext rfl⟩
      rw [hact, clT_inX_apply, dif_pos (by simp), residue_linearEquiv_apply_eq_sum gbar x]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [clT_inX_apply, dif_pos (by simp), hgent]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j : Fin (cOf R (i + 1)), m = Fin.natAdd (R.N (i + 1)) j :=
        ⟨⟨m.1 - R.N (i + 1), by omega⟩, Fin.ext (by simp; omega)⟩
      rw [hfix, clT_inX_apply, clT_inX_apply, dif_neg (by simp), dif_neg (by simp)]

  rw [hPhi, ← clL_ext_symm]
  have hgl : ∀ v ∈ stdAt X.E (R.N (i + 1)) P.1, κ'.symm v ∈ stdAt X.E (R.N (i + 1)) P.1 :=
    fun v hv => (hκ' (κ'.symm v)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hv)
  by_cases hx : ocbXInt P.1 w
  · have hxI' : ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w) := by
      intro l s hl hs
      have hv := clT_vec_std (P := P.1) (fun l' hl' => hx l' s hl' hs)
      have h2 := hgl _ hv
      rw [ciMem_stdAt] at h2
      rw [LinearMap.comp_apply, ocbS_atN_of_lt _ hl]
      exact h2 _
    let xbar : (Fin (R.N i) → 𝓞 X.E ⧸ P.1.asIdeal) →ₗ[𝓞 X.E ⧸ P.1.asIdeal] (Fin (R.N (i + 1)) → 𝓞 X.E ⧸ P.1.asIdeal) :=
      Matrix.toLin' (Matrix.of fun l s => redP P.1 (Loc.atN (w (Loc.eN X.E (R.N i) s.1)) l.1))
    have hxR : ocbXRed P.1 w xbar := by
      intro l s hl hs
      show Loc.atN (Matrix.toLin' _ (Loc.eN _ (R.N i) s)) l = _
      rw [ocbS_atN_toLin' _ hl hs]
      rfl
    have hIκ : ∀ l m, l < R.N (i + 1) → m < R.N (i + 1) →
        IntAt P.1 (Loc.atN (κ'.symm.toLinearMap (Loc.eN X.E (R.N (i + 1)) m)) l) := by
      intro l m hl hm
      have hv : Loc.eN X.E (R.N (i + 1)) m ∈ stdAt X.E (R.N (i + 1)) P.1 := by
        rw [ocbS_eN_single hm]
        exact ciSingle_mem _
      have h2 := hgl _ hv
      rw [ciMem_stdAt] at h2
      rw [ocbS_atN_of_lt _ hl]
      exact h2 _
    have hxR' : ocbXRed P.1 (κ'.symm.toLinearMap ∘ₗ w) (gbar.symm.toLinearMap ∘ₗ xbar) := by
      intro l s hl hs
      rw [ocbS_atN_comp _ _ hl hs, ocbS_atN_comp _ _ hl hs,
        redP_sum _ _ fun m _ => (hIκ l m.1 hl m.2).mul (hx m.1 s m.2 hs)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [reduction_mul (hIκ l m.1 hl m.2) (hx m.1 s m.2 hs), ← hxR m.1 s m.2 hs]
      congr 1
      have h3 := ocbT_red_symm (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ') hgred hl m.2
      rw [clT_bEnt0 _ _ hl m.2] at h3
      exact h3
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Φ Φr hsupp0 hred0 (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u)
        (fun a ha => by rw [hB.psi0 P a hP ha]; rfl) hA hB.cst_ok.B_pos _ _ hxI' hxR',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ _ (fun x => Φr (hbar.symm.toLinearMap ∘ₗ x)) htsupp htred (cst.psi P)
        (fun u => ocbPsiC Ch σ P.1 u) (fun a ha => by rw [hB.psi0 P a hP ha]; rfl) hA hB.cst_ok.B_pos w xbar hx hxR]
    have hres : Loc.E1 (k := 𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n := R.N (i + 1)) (c := cOf R (i + 1))
        (fun u => ocbPsiC Ch σ P.1 u) (@Finset.univ _ (resFintype P.1)) 1 Φr (gbar.symm.toLinearMap ∘ₗ xbar) =
        Loc.E1 (k := 𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n := R.N (i + 1)) (c := cOf R (i + 1))
          (fun u => ocbPsiC Ch σ P.1 u) (@Finset.univ _ (resFintype P.1)) 1 (fun x => Φr (hbar.symm.toLinearMap ∘ₗ x)) xbar := by
      letI := resFintype P.1
      have h := unfolding_equivalence _ _ _ _ _ (fun u => ocbPsiC Ch σ P.1 u) (fun a b => AddChar.map_add_eq_mul _ a b) 1 Φr hbar gbar hR1 hg xbar
      rw [show PI.UnfoldEquiv.Loc.n1Arg hbar = 0 from hn1, neg_zero] at h
      simp only [AddChar.map_zero_eq_one, one_mul] at h
      exact h.symm
    rw [hres]
  · have hx' : ¬ ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w) := by
      intro h
      apply hx
      intro l s hl hs
      have hv := clT_vec_std (P := P.1) (fun l' hl' => by
        have := h l' s hl' hs
        rwa [LinearMap.comp_apply] at this)
      have h2 := (hκ' _).2 hv
      rw [show κ' (κ'.symm.toLinearMap (w (Loc.eN X.E (R.N i) s))) = w (Loc.eN X.E (R.N i) s) from κ'.apply_symm_apply _,
        ciMem_stdAt] at h2
      rw [ocbS_atN_of_lt _ hl]
      exact h2 _
    rw [firstUnfolding_eq_zero_of_not_integral hc' Φ hsupp0 _ _ _ _ hx', firstUnfolding_eq_zero_of_not_integral hc' _ htsupp _ _ _ _ hx]

end Tgt

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainOneOkF
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Closed

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

theorem oneIdx_ok_closed (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) :
    (oneIdx (colLevSym Ch) (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).Ok Ch sel (mu0 X.F X.E X.K S)
      (ookCstR Ch sel S G) G m2 := by
  have hB := ookCstR_base sel S hX hPr hCh h4 G hm
  have hJ := oneCosetSymmetric_and_nonvanishing G.σ₀ hB (ciMemG sel S) (liftFromResidueParabolicProduct_holds Ch sel _ _ m2) (ocbGrpGLoc_holds Ch sel _ _ m2)
    (ocbChrGLoc_holds Ch sel _ _ m2) (closedLevels_by_entries_holds X Pr R Ch m2 hm)
  exact oneIdx_ok sel S hX hPr hCh h4 G hT hW hval hm hJ.1 hJ.2

end Closed

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainTwL
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

open Classical

theorem tw_mem_vGs_of_not {P : rowSG Pr sel mu} (hP : P.1 ∉ twQOff (Pr := Pr) sel mu) : P.1 ∈ Pr.vGs := by
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · by_contra hn
    exact hP (Finset.mem_sdiff.2 ⟨h, hn⟩)

theorem tw_mem_QOff {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : P.1 ∈ twQOff (Pr := Pr) sel mu :=
  Finset.mem_sdiff.2 ⟨(Finset.mem_union.1 P.2).resolve_left hP, hP⟩

theorem twCFin_sub {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)} (hD : D ∈ twCFin Ch sel mu cst st P) :
    D ∈ twCSet Ch sel mu cst st P := by
  unfold twCFin at hD
  split_ifs at hD with hf
  · exact (Set.Finite.mem_toFinset hf).1 hD
  · exact absurd hD (Finset.notMem_empty _)

theorem twCFin_mem {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    (hf : (twCSet Ch sel mu cst st P).Finite) {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : D ∈ twCSet Ch sel mu cst st P) : D ∈ twCFin Ch sel mu cst st P := by
  unfold twCFin
  rw [dif_pos hf]
  exact (Set.Finite.mem_toFinset hf).2 hD

def TwNormAt {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) : Prop :=
  ∀ (P : twQOff (Pr := Pr) sel mu) D, D ∈ twCSet Ch sel mu cst st P →
    ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1

theorem twRep_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} {P : twQOff (Pr := Pr) sel mu}
    {D : Quotient (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1)}
    (hD : ∃ h, Quotient.mk _ h = D ∧ TwCand Ch sel mu cst st P h ∧ TwNF (Pr := Pr) (i + 1) P.1 h ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1) :
    Quotient.mk _ (twRep Ch sel mu cst st P D) = D ∧ TwCand Ch sel mu cst st P (twRep Ch sel mu cst st P D) ∧
      TwNF (Pr := Pr) (i + 1) P.1 (twRep Ch sel mu cst st P D) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 (twRep Ch sel mu cst st P D) ≤ GLint X.E (R.N (i + 1)) P.1 :=
  Classical.epsilon_spec hD

theorem twNext_h_g {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) : (twNext Ch sel mu cst st).h b P = 1 := by
  dsimp only [twNext]
  rw [dif_neg (fun h => (Finset.mem_sdiff.1 h).2 hP)]

theorem twNext_h_Q {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i) (b : (twNext Ch sel mu cst st).β)
    (P : twQOff (Pr := Pr) sel mu) :
    (twNext Ch sel mu cst st).h b (twRow P) = twRep Ch sel mu cst st P (b.1 P).1 := by
  dsimp only [twNext]
  rw [dif_pos (show (twRow P).1 ∈ twQOff (Pr := Pr) sel mu from P.2)]
  rfl

theorem twNext_spec {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : twQOff (Pr := Pr) sel mu) :
    Quotient.mk _ ((twNext Ch sel mu cst st).h b (twRow P)) = (b.1 P).1 ∧
      TwCand Ch sel mu cst st P ((twNext Ch sel mu cst st).h b (twRow P)) ∧
      TwNF (Pr := Pr) (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ∧ prCat (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b (twRow P)) ≤ GLint X.E (R.N (i + 1)) P.1 := by
  rw [twNext_h_Q]
  exact twRep_spec (hN P _ (twCFin_sub (b.1 P).2))

theorem twNext_nonvan {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu) :
    ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) ((twNext Ch sel mu cst st).h b P) := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · obtain ⟨-, ⟨-, al, hal⟩, -, -⟩ := twNext_spec hN b ⟨P.1, hP⟩
    exact ⟨al, hal⟩
  · have hG := tw_mem_vGs_of_not hP
    obtain ⟨al, hal⟩ := b.2 P hG
    exact ⟨al, by rw [twNext_h_g st b P hG]; exact hal⟩

theorem twNext_inj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (b b' : (twNext Ch sel mu cst st).β)
    (H : ∀ P : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) ((twNext Ch sel mu cst st).h b' P)) :
    b = b' := by
  apply Subtype.ext
  funext P
  apply Subtype.ext
  have h1 := (twNext_spec hN b P).1
  have h2 := (twNext_spec hN b' P).1
  rw [← h1, ← h2]
  exact Quotient.sound (H (twRow P))

theorem twNext_surj {i : ℕ} {st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i} (hN : TwNormAt (Ch := Ch) (cst := cst) st)
    (hfin : ∀ P, (twCSet Ch sel mu cst st P).Finite) (hg1 : ∀ al (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → st.h al P = 1)
    (hSG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1),
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h → SameDC (Pr := Pr) cst.sharp (i + 1) P.1 1 h)
    (hNV : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 1)
    (hh : rowSG Pr sel mu → AutY X R (i + 1)) (hs : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1))
    (hb : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwBdd (Pr := Pr) (i + 1) P.1 (hh P))
    (H : ∀ P, ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) (hh P)) :
    ∃ b : (twNext Ch sel mu cst st).β, ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h b P) (hh P) := by
  have hmem : ∀ P : twQOff (Pr := Pr) sel mu,
      Quotient.mk (twSetoid (Pr := Pr) (R := R) cst.sharp (i + 1) P.1) (hh (twRow P)) ∈ twCFin Ch sel mu cst st P := fun P => by
    apply twCFin_mem (hfin P)
    have hc : TwCand Ch sel mu cst st P (hh (twRow P)) := ⟨hb (twRow P) (Finset.mem_sdiff.1 P.2).2, H (twRow P)⟩
    exact ⟨hh (twRow P), rfl, hc⟩
  have hne : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∃ al : st.β, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (st.h al P) 1 := fun P hP => by
    obtain ⟨al, -⟩ := H P
    exact ⟨al, by rw [hg1 al P hP]; exact hNV P hP⟩
  let b : (twNext Ch sel mu cst st).β := ⟨fun P => ⟨_, hmem P⟩, hne⟩
  refine ⟨b, fun P => ?_⟩
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · have h1 := (twNext_spec hN b ⟨P.1, hP⟩).1
    exact Quotient.exact h1
  · have hG := tw_mem_vGs_of_not hP
    rw [twNext_h_g st b P hG]
    obtain ⟨al, hal⟩ := H P
    rw [hg1 al P hG] at hal
    exact hSG P hG (hh P) (hs P hG) hal

variable (Ch sel mu cst)

theorem twSt_zero (m2 : ℕ) : twSt Ch sel mu cst m2 0 = twUnitSt _ 0 := rfl

theorem twSt_succ_le {m2 i : ℕ} (h : i + 1 ≤ m2) : twSt Ch sel mu cst m2 (i + 1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) := by
  rw [twSt, if_pos h]

theorem twSt_last (m2 : ℕ) : twSt Ch sel mu cst m2 (m2 + 1) = twUnitSt _ (m2 + 1) := by
  rw [twSt, if_neg (by omega), if_pos rfl]

theorem twSt_le (m2 : ℕ) : ∀ (j : ℕ) (_b : (twSt Ch sel mu cst m2 j).β), j ≤ m2 + 1
  | 0, _ => Nat.zero_le _
  | i + 1, b => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · intro _; omega
      · by_cases h2 : i + 1 = m2 + 1
        · intro _; omega
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

theorem twSt_h_g (m2 : ℕ) : ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
    (twSt Ch sel mu cst m2 j).h b P = 1
  | 0, _, _, _ => rfl
  | i + 1, b, P, hP => by
      revert b
      by_cases h1 : i + 1 ≤ m2
      · rw [twSt_succ_le Ch sel mu cst h1]
        intro b; exact twNext_h_g _ b P hP
      · by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _; rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

end TwL

end Formalism.L2.Col
end
end

