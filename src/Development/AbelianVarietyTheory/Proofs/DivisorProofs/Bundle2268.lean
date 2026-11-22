import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterPrecisionLeLengthAndRank
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbundleFrameAffineAtlasIsFlagFrameCover
section
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_embK_ne {σ σ' : E →+* ℂ} (h : σ ≠ σ') : ∃ a : 𝓞 E, embK c σ a ≠ embK c σ' a := by
  by_contra hc
  push_neg at hc
  refine h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_))
  have := congrArg Subtype.val (hc a)
  simpa [embK, embF] using this

theorem pm_mul_pm {Y : Model Xo c (RingHom.id c.F)} (p : Proj (RingHom.id c.F)) (M : MChart Y) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : LowRank.pm p M σ * LowRank.pm p M σ' = 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c c.F (RingHom.id c.F) Y M
  letI : Algebra c.F Γ(Y.X, M.U) := (str (tau M.hU)).toAlgebra
  have hP : ∀ τ, LowRank.pm p M τ =
      ∑ k, algebraMap c.F Γ(Y.X, M.U) (RingHom.id c.F (p.κ τ k)) • ρ (p.a τ k) :=
    fun τ => by simp only [LowRank.pm, hρ]; rfl
  obtain ⟨a, ha⟩ := exists_embK_ne (c := c) h
  have h1 := (p.spec σ Γ(Y.X, M.U) M.n ρ).1 a
  have h1' := (p.spec σ' Γ(Y.X, M.U) M.n ρ).1 a
  rw [← hP] at h1 h1'
  have hc : ρ a * LowRank.pm p M σ = LowRank.pm p M σ * ρ a := by
    rw [hP, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, mul_comm]
  have e1 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, h1, Matrix.smul_mul]
  have e2 : ρ a * (LowRank.pm p M σ * LowRank.pm p M σ') =
      algebraMap c.F Γ(Y.X, M.U) (embK c σ' a) • (LowRank.pm p M σ * LowRank.pm p M σ') := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, h1', Matrix.mul_smul]
  have hd : embK c σ a - embK c σ' a ≠ 0 := sub_ne_zero.2 ha
  have e3 : algebraMap c.F Γ(Y.X, M.U) (embK c σ a - embK c σ' a) •
      (LowRank.pm p M σ * LowRank.pm p M σ') = 0 := by
    rw [map_sub, sub_smul, ← e1, ← e2, sub_self]
  calc LowRank.pm p M σ * LowRank.pm p M σ'
      = algebraMap c.F Γ(Y.X, M.U) ((embK c σ a - embK c σ' a)⁻¹ * (embK c σ a - embK c σ' a)) •
        (LowRank.pm p M σ * LowRank.pm p M σ') := by
        rw [inv_mul_cancel₀ hd, map_one, one_smul]
    _ = 0 := by rw [map_mul, mul_smul, e3, smul_zero]

theorem eCh_w_mul_u {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (k : ECh Y p) {σ σ' : E →+* ℂ}
    (h : σ ≠ σ') : k.w σ * k.u σ' = 0 := by
  calc k.w σ * k.u σ' = (k.w σ * k.u σ) * k.w σ * (k.u σ' * (k.w σ' * k.u σ')) := by
        rw [k.wu, k.wu, Matrix.one_mul, Matrix.mul_one]
    _ = k.w σ * ((k.u σ * k.w σ) * (k.u σ' * k.w σ')) * k.u σ' := by simp only [Matrix.mul_assoc]
    _ = 0 := by
        rw [k.uw, k.uw, ← Matrix.map_mul, pm_mul_pm p _ h, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
          Matrix.zero_mul]

end GlobalTheory.FlagMod.FieldFlag

open GlobalTheory.FlagMod.FieldFlag MonoidalCategory CartesianMonoidalCategory MonObj in

theorem GlobalTheory.FlagMod.FieldFlag.atlas_isCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  intro E _ _ _ H Dw l Xo c Y p A
  classical
  refine ⟨fun b => ?_, fun b => ?_, fun k _ b b' φ φ' hx => ?_⟩
  · rw [RingHom.comp_id]
    exact (spMap_ev_top (tau (A.aff b) ≫ Y.s)).symm
  · rintro ⟨σ, i⟩ ⟨σ', j⟩
    have e : ∑ r, A.Dv b ⟨σ, i⟩ r * A.cv b ⟨σ', j⟩ r = ((A.k b).w σ * (A.k b).u σ') i j := by
      have : (A.k b).w σ * (A.k b).u σ' = ((A.k b).w σ * A.C b) * (A.A b * (A.k b).u σ') := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.C b), A.CA, Matrix.one_mul]
      rw [this, Matrix.mul_apply]
      rfl
    rw [e]
    by_cases hs : σ = σ'
    · subst hs
      rw [(A.k b).wu]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.one_apply_ne hij, if_neg]
        intro h'
        exact hij (eq_of_heq (Sigma.mk.inj_iff.1 h').2)
    · rw [eCh_w_mul_u _ hs, Matrix.zero_apply, if_neg]
      intro h'
      exact hs (congrArg Sigma.fst h')
  · have h0 : ⊤ ≤ (spMap φ ≫ (A.V b).2.fromSpec) ⁻¹ᵁ (A.k b).V := le_preimage_comp _ (tau_le (A.aff b) le_rfl)
    have h0' : ⊤ ≤ (spMap φ' ≫ (A.V b').2.fromSpec) ⁻¹ᵁ (A.k b').V :=
      le_preimage_comp _ (tau_le (A.aff b') le_rfl)
    set x := spMap φ ≫ (A.V b).2.fromSpec with hxdef
    have h : ⊤ ≤ x ⁻¹ᵁ (A.k b).V := h0
    have h' : ⊤ ≤ x ⁻¹ᵁ (A.k b').V := hx ▸ h0'
    have hφ : ev x _ h = φ := ev_spMap_tau (A.aff b) φ h
    have hφ' : ev x _ h' = φ' := (ev_congr hx _ h' h0').trans (ev_spMap_tau (A.aff b') φ' h0')
    have hM : ⊤ ≤ x ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h
    have hM' : ⊤ ≤ x ⁻¹ᵁ (A.k b').M.U := le_preimage_mono (A.k b').le h'
    have hMM : ⊤ ≤ x ⁻¹ᵁ ((A.k b).M.U ⊓ (A.k b').M.U) := le_preimage_inf hM hM'
    obtain ⟨a, ha⟩ := A.tw k x b' b h' h hMM
    rintro ⟨σ, j⟩
    set v : Fin (A.k b').M.n → k := (((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) with hvdef
    set y := ((chg (A.k b).M.toMChart (A.k b').M.toMChart).map (ev x _ hMM)).mulVec v with hydef
    have hv : ((LowRank.pm p (A.k b').M.toMChart σ).map (ev x _ hM')).mulVec v = v :=
      ((A.k b').fix_iff σ x h' hM' v).2 ⟨_, rfl⟩
    have hy : ((LowRank.pm p (A.k b).M.toMChart σ).map (ev x _ hM)).mulVec y = y := by
      have h2 := congrArg (vec (A.k b').M.toMChart x hM') hv
      rw [LowRank.vec_pm, ← vec_chg (A.k b).M.toMChart (A.k b').M.toMChart x hM hM' hMM, ← LowRank.vec_pm] at h2
      exact (vec _ _ _).injective h2
    obtain ⟨t, ht⟩ := ((A.k b).fix_iff σ x h hM y).1 hy
    have key : φ' ∘ A.cv b' ⟨σ, j⟩ = ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t := by
      calc φ' ∘ A.cv b' ⟨σ, j⟩
          = ((A.A b').map (ev x _ h') * ((A.k b').u σ).map (ev x _ h')).mulVec (Pi.single j 1) := by
            rw [hφ']
            funext r
            rw [Matrix.mulVec_single_one, ← Matrix.map_mul]
            rfl
        _ = (a : k) • ((A.A b).map (ev x _ h)).mulVec y := by
            rw [← Matrix.mulVec_mulVec, ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
        _ = (a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ).mulVec t := by
            rw [← ht, Matrix.mulVec_mulVec, hφ]
        _ = _ := (Matrix.smul_mulVec _ _ _).symm
    have col : ∀ i, φ ∘ A.cv b ⟨σ, i⟩ = fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := fun i => by
      funext r
      rw [← Matrix.map_mul]
      rfl
    have hsum : ((a : k) • ((A.A b).map φ * ((A.k b).u σ).map φ)).mulVec t =
        ∑ i, ((a : k) * t i) • fun r => ((A.A b).map φ * ((A.k b).u σ).map φ) r i := by
      funext r
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    show φ' ∘ A.cv b' ⟨σ, j⟩ ∈ Submodule.span k (Set.range fun i => φ ∘ A.cv b ⟨σ, i⟩)
    rw [key, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, col i⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntRCloudSub
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

section Rec

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)

theorem six_le_r (R : Ranks) : 6 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem one_le_Dp : 1 ≤ T.Dp := by
  rw [T.Dp_eq]
  have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  exact Nat.mul_pos h2 (Nat.choose_pos (by have := six_le_r D.R; omega))

theorem forty_le_PP : 40 ≤ T.PP := le_trans (by exact_mod_cast T.nW_40) T.nW_le

theorem len_ge : 4 * T.Dp + 4 ≤ ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ := by
  have h1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast one_le_Dp T
  have h2 := forty_le_PP T
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h3 : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]; exact mul_le_mul_of_nonneg_left hmk (by positivity)
  have h4 : (8 : ℝ) * (T.Dp : ℝ) ^ 2 ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have h5 : ((4 * T.Dp + 4 : ℕ) : ℝ) ≤ T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h5.trans (Nat.le_ceil _)

theorem cZeroN_le_TO (j : ℕ) : cZeroN D j ≤ 12 * T.TO := by
  have h1 := cZeroN_le D j
  have h2 := T.TO_11D2
  have h6 := six_le_r D.R
  have h3 : D.R.r ^ 4 ≤ 6 * (D.R.r.choose 2) ^ 2 := by
    obtain ⟨s, hs⟩ : ∃ s, D.R.r = s + 1 := ⟨D.R.r - 1, by omega⟩
    have e : 2 * (D.R.r.choose 2) = D.R.r * s := by
      rw [hs, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' (by
        rw [mul_comm]; exact (Nat.even_mul_succ_self s).two_dvd)]
    have e2 : 4 * (D.R.r.choose 2) ^ 2 = D.R.r ^ 2 * s ^ 2 := by
      rw [← mul_pow, ← e]; ring
    have e3 : 4 * D.R.r ^ 2 ≤ 6 * s ^ 2 := by
      have : 5 ≤ s := by omega
      rw [hs]; nlinarith
    have e4 : D.R.r ^ 2 * (4 * D.R.r ^ 2) ≤ D.R.r ^ 2 * (6 * s ^ 2) := Nat.mul_le_mul_left _ e3
    nlinarith
  have h4 : D.R.f ^ 2 * D.R.r ^ 4 ≤ D.R.f ^ 2 * (6 * (D.R.r.choose 2) ^ 2) := Nat.mul_le_mul_left _ h3
  rw [T.Dp_eq, mul_pow] at h2
  nlinarith

theorem spacing_ge (j n : ℕ) (hn : n ≤ T.TO) :
    4 * ((cZeroN D j : ℝ) + 2 * D.R.r + n + T.Dp + 1) ≤ LevelStarExponents.h0 L ∧ 24 * (D.R.r : ℝ) * n ≤ LevelStarExponents.h0 L ∧
      4 * (n : ℝ) ^ 2 ≤ LevelStarExponents.h0 L := by
  have a1 : (cZeroN D j : ℝ) ≤ 12 * T.TO := by exact_mod_cast cZeroN_le_TO T j
  have a2 : 6 * (D.R.r : ℝ) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have : 6 * D.R.r ≤ T.TO := by nlinarith [Nat.zero_le (D.R.r * T.Dp)]
    exact_mod_cast this
  have a3 : 40 * ((T.Dp : ℝ) + 2) ≤ T.TO := by exact_mod_cast T.TO_40
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have a5 := T.heightBound_ge_order_sq
  have b0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have b1 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have b2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have b3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  have : 6 * (D.R.r : ℝ) * n ≤ T.TO * T.TO := mul_le_mul a2 a4 b2 (by linarith)
  nlinarith

theorem prod_bounds (n : ℕ) (hn : n ≤ T.TO) :
    T.PP * n * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp ≤ LevelStarExponents.h0 L ∧
    T.PP ^ 2 * D.R.r * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b ∧
    T.PP * n * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b := by
  have a4 : (n : ℝ) ≤ T.TO := by exact_mod_cast hn
  have hP := forty_le_PP T
  have hP0 : 0 ≤ T.PP := by linarith
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ T.heightBound_ge_order_product
    have e1 : T.PP * n * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) := by
      gcongr
    have e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k *
          (T.Dp : ℝ)) := le_mul_of_one_le_left (by positivity) T.ChT_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  · refine le_trans ?_ T.b_ge
    have e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3) :=
      le_mul_of_one_le_left (by positivity) T.CbN_ge
    calc _ ≤ _ := e2
      _ = _ := by ring
  · have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
    have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
    have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have c1 := T.TD2'
    have c2 := T.TO_PP'
    rw [hlb] at c1
    have c3 : (1 : ℝ) ≤ T.TO := by
      have := T.TO_40
      exact_mod_cast (by omega : 1 ≤ T.TO)
    have c4 : T.PP ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_left hP0 c3) c2
    have c5 : (n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (by gcongr) c1
    have c6 : L.sc.b ^ (1 / 2 : ℝ) * L.sc.b ^ (1 / 2 : ℝ) = L.sc.b := by
      rw [← Real.rpow_add hb0]; norm_num
    calc _ = T.PP * ((n : ℝ) * (T.Dp : ℝ) ^ 2 * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul c4 c5 (by positivity) (by positivity)
      _ = _ := c6

theorem abs_logOm_le (hS : SizesAt L) (hL : 3 ≤ L.sc.L) : |L.logOm| ≤ 3 * L.sc.L := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have h1 := log_rdE_le_L D L hCond hQD
  have hrd : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have h0 := Real.log_nonneg hrd
  have h2 : |L.logDerivativeAtOne| ≤ L.sc.L := hQD.2.2.2.2.2.1
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 := Real.eulerMascheroniConstant_lt_two_thirds
  have h5 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h6 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_le_four]
  have h7 := Real.log_two_lt_d9
  have h8 := Real.log_two_gt_d9
  unfold SizeData₂.logOm Host.v
  rw [Real.log_div Real.pi_pos.ne' (by positivity), Real.log_div (by positivity) (by norm_num)]
  obtain ⟨h9, h10⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

def entR (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℝ :=
  sgR D t n + DV.wSz D ((i : ℕ) + 1) t + n - ((D.R.k : ℝ) + i) + ((D.R.r : ℝ) + 1) / 2 -
    if n < D.R.k + i then 0 else (D.R.r : ℝ)

theorem ent_cast (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ((ent D i t n : ℚ) : ℝ) = entR D i t n := by
  unfold ent entR sgR
  rw [← DV.eQ_cast, eQ_succ]
  split_ifs <;> push_cast <;> ring

theorem entR_cloud (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k - 1) :
    DV.wSz D ((i : ℕ) + 1) t - D.R.r ≤ entR D i t n ∧ entR D i t n ≤ DV.wSz D ((i : ℕ) + 1) t + L.Sc + D.R.r := by
  unfold entR
  rw [if_pos (by omega), sgR_cloud D t n hn]
  obtain ⟨v0, v1⟩ := L.cloud_v t ⟨n, hn⟩
  have c1 : (n : ℝ) + 2 ≤ D.R.k := by exact_mod_cast (by omega : n + 2 ≤ D.R.k)
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c4 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
  have := r_cast D.R
  constructor <;> linarith

theorem entR_node (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : D.R.k - 1 ≤ n) (hr : n < D.R.r) :
    |entR D i t n| ≤ L.etaSz + D.R.r := by
  obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t n hn hr)
  have c1 : (D.R.k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k ≤ n + 1)
  have c2 : (n : ℝ) + 1 ≤ D.R.r := by exact_mod_cast hr
  have c3 : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have c5 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have c7 : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  have := r_cast D.R
  unfold entR
  split_ifs with h
  · have c8 : (n : ℝ) + 1 ≤ (D.R.k : ℝ) + (i : ℕ) := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · have c8 : (D.R.k : ℝ) + (i : ℕ) ≤ n := by exact_mod_cast not_lt.1 h
    rw [abs_le]; constructor <;> linarith

theorem entR_step (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) :
    entR D i t n - entR D i t (n + 1) =
      sgR D t n - sgR D t (n + 1) - 1 + if n + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
  unfold entR
  split_ifs <;> first | omega | (push_cast; ring)

theorem entR_cloud_sub (L : SizeData₂ D) (i : Fin D.R.m) (t : D.what₂.Tau)
    (hs : ∀ a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1)) (n : ℕ) (hn : n < D.R.k - 1) :
    0 ≤ entR D i t n - entR D i t (D.R.k - 1 - 1) ∧ entR D i t n - entR D i t (D.R.k - 1 - 1) ≤ L.Sc := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 := steps_sum (sgR D t) 0 D.R.r 1 (fun a _ ha => hs a ha) n (Nat.zero_le _) (D.R.k - 1 - 1) (by omega) (by omega)
  have h2 : (n : ℝ) ≤ ((D.R.k - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ D.R.k - 1 - 1)
  have h3 := (L.cloud_v t ⟨n, hn⟩).2
  have h4 := (L.cloud_v t ⟨D.R.k - 1 - 1, by omega⟩).1
  rw [← sgR_cloud] at h3 h4
  unfold entR
  rw [if_pos (by omega), if_pos (by omega)]
  constructor <;> linarith

end Rec

end GlobalTheory.CovTop.WtShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdjointApplyOfWeightedQuadraticSumPolar
section
open GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem qW_polar_eq_sum_add_transpose {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (β : LinearMap.BilinForm ℤ X) (hβ : ∀ a b, β a b = β b a) (y z : Fin s → X) :
    qW W β (y + z) - qW W β y - qW W β z = ∑ u, ∑ v, (W + W.transpose) u v * β (y u) (z v) := by
  have h : ∑ u, ∑ v, W u v * β (z u) (y v) = ∑ u, ∑ v, W v u * β (y u) (z v) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hβ]
  simp only [qW, Pi.add_apply, map_add, LinearMap.add_apply, mul_add, add_mul, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, h]
  ring

theorem eq_adjoint_apply_of_qW_polar (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : PosW W) (X₀ : Type) [AddCommGroup X₀]
    (β : LinearMap.BilinForm ℤ X₀) (hβ : ∀ a b, β a b = β b a) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (E E' : Matrix (Fin 8) (Fin 8) ℤ) (hE : (W + W.transpose) * E' = E.transpose * (W + W.transpose))
    (z z' : Fin 8 → X₀)
    (h : ∀ y : Fin 8 → X₀, qW W β ((fun a => ∑ b, E a b • y b) + z) - qW W β (fun a => ∑ b, E a b • y b) - qW W β z =
      qW W β (y + z') - qW W β y - qW W β z') :
    z' = fun a => ∑ b, E' a b • z b := by
  simp only [qW_polar_eq_sum_add_transpose W β hβ] at h
  unfold PosW at hW
  set M := W + W.transpose with hM
  have hdet : M.det ≠ 0 := by
    have h1 := hW.det_pos
    have h2 : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
      rw [Int.cast_det]
    rw [h2] at h1
    intro h0
    simp [h0] at h1
  have key : ∀ x : X₀, (fun v => β x (z' v)) = E' *ᵥ (fun v => β x (z v)) := by
    intro x
    rw [← sub_eq_zero]
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hE, sub_eq_zero]
    funext w
    have h1 := h (Pi.single w x)
    have h2 : ∀ a, ∑ b, E a b • (Pi.single w x : Fin 8 → X₀) b = E a w • x := by
      intro a
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    have h3 : ∑ u, ∑ v, M u v * β ((Pi.single w x : Fin 8 → X₀) u) (z' v) = ∑ v, M w v * β x (z' v) := by
      rw [Finset.sum_eq_single w] <;> simp +contextual [Pi.single_apply]
    simp only [h2, h3, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  funext a
  rw [← sub_eq_zero]
  by_contra hne
  have h1 := hpos _ hne
  generalize hd : z' a - ∑ b, E' a b • z b = d at h1
  have h2 := congrFun (key d) a
  have h3 : β d d = 0 := by
    conv_lhs => rw [show β d d = β d (z' a - ∑ b, E' a b • z b) by rw [hd]]
    simp only [map_sub, map_sum, map_zsmul, smul_eq_mul, h2, Matrix.mulVec, dotProduct, sub_self]
  omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.EssFiniteDescent

theorem essFiniteType_of_eq_div : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  intro K _ c R hcR E hcE hRE hft hloc
  let f : R →+* E :=
    { toFun := fun r => ⟨(r : K), hRE r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Submonoid R :=
    { carrier := {s | (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
        refine ⟨by simpa using mul_ne_zero ha0 hb0, ?_⟩
        have : ((a * b : R) : K)⁻¹ = (b : K)⁻¹ * (a : K)⁻¹ := by
          push_cast; exact mul_inv_rev _ _
        rw [this]; exact E.mul_mem _ _ hb ha
      one_mem' := ⟨by simp, by simpa using E.one_mem⟩ }
  letI : Algebra ℂ R := (c.codRestrict R hcR).toAlgebra
  letI : Algebra R E := f.toAlgebra
  letI : Algebra ℂ E := (c.codRestrict E hcE).toAlgebra
  haveI : IsScalarTower ℂ R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℂ R := hft
  haveI : IsLocalization M E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs0, hs⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hs⟩, ?_⟩
      apply Subtype.ext
      change (s : K) * (s : K)⁻¹ = 1
      exact mul_inv_cancel₀ hs0
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, s, hs, hsE, rfl⟩ := hloc e he
      by_cases hs0 : s = 0
      · refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change a / s * ((1 : M) : R) = (((0 : R)) : K)
        simp [hs0]
      · refine ⟨(⟨a, ha⟩, ⟨⟨s, hs⟩, by simpa using hs0, hsE⟩), ?_⟩
        apply Subtype.ext
        change a / s * s = a
        exact div_mul_cancel₀ a hs0
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : K) = y := congrArg (fun z : E => (z : K)) hxy
      simp [Subtype.ext this]
  haveI : Algebra.EssFiniteType R E := Algebra.EssFiniteType.of_isLocalization E M
  have h : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ R E
  exact h

end GlobalTheory.EssFiniteDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianKeyValue_norm_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  first | exact @GlobalTheory.MBLow.AbKey.exists_bKey | exact GlobalTheory.MBLow.AbKey.exists_bKey | (intros; apply GlobalTheory.MBLow.AbKey.exists_bKey <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultiplStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G)) (x : KeyIn R'), L.IsLB → IsFibreOf x G L rig θ w f → ∀ (θ₀ : L.Sec) (b : R), IsMul (X := G) θ b θ₀ → ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀), (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧ IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  first | exact @GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | exact GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | (intros; apply GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul <;> assumption)
end

