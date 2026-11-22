import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.Bundle0023

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace LimTy

variable {C : Type} [Field C] {V : VF C}

theorem tendsS_sum {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} {F : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, TendsS V (f i) (F i)) : TendsS V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, F i) := by
  intro μ
  simp only [map_sum]
  exact Tends.sum S (fun i hi => h i hi μ)

theorem tendsS_smul {σ : Type} (c : C) {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => c • f k) (c • F) := by
  intro μ
  first
    | simp only [map_smul, smul_eq_mul]
    | simp only [MvPowerSeries.coeff_smul]
  exact (tends_const c).mul (h μ)

theorem tendsS_ite {σ : Type} (P : Prop) [Decidable P] {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => if P then f k else 0) (if P then F else 0) := by
  split_ifs
  · exact h
  · exact TendsS.const 0

theorem coeff_tyS_mv (l : ℕ) (b : ℕ → C) (μ : Unit →₀ ℕ) :
    MvPowerSeries.coeff μ (tyS l b) = ∑ s ∈ Finset.range (μ () + 1), if l ^ s = μ () then b s else 0 := rfl

theorem tendsS_tyS (l : ℕ) {a : ℕ → ℕ → C} {a' : ℕ → C} (h : ∀ s, Tends V (fun k => a k s) (a' s)) :
    TendsS V (fun k => tyS l (a k)) (tyS l a') := by
  intro μ
  simp only [coeff_tyS_mv]
  refine Tends.sum _ (fun s _ => ?_)
  split_ifs
  · exact h s
  · exact tends_const 0

theorem tendsP {f : ℕ → PowerSeries C} {F : PowerSeries C} (h : TendsS V f F) (n : ℕ) :
    Tends V (fun k => PowerSeries.coeff n (f k)) (PowerSeries.coeff n F) :=
  h (Finsupp.single () n)

private theorem eq_zero_of_tends_const_zero {y : C} (h : Tends V (fun _ => (0 : C)) y) : y = 0 := by
  by_contra hy
  have hne : V.v y ≠ ⊤ := fun ht => hy ((AddValuation.top_iff V.v).mp ht)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨n0, hn0⟩ := h (r + 1)
  have h1 : ((r + 1 : ℝ) : WithTop ℝ) ≤ V.v (y - 0) := hn0 n0 le_rfl
  rw [sub_zero, ← hr] at h1
  have h2 := WithTop.coe_le_coe.mp h1
  linarith

private theorem ge_zero_of_tends_of_forall_ge_zero {s : ℕ → C} {y : C} (h : Tends V s y) (hs : ∀ k, V.Ge 0 (s k)) :
    V.Ge 0 y := by
  obtain ⟨n0, hn0⟩ := h 0
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (y - s n0) := hn0 n0 le_rfl
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (s n0) := hs n0
  have e : y = (y - s n0) + s n0 := by ring
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v y
  rw [e]
  exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem isCv_lim {σ : Type} {γ : ℕ → σ → PowerSeries C} {Γ : σ → PowerSeries C}
    (h : ∀ i, TendsS V (fun k => γ k i) (Γ i)) (hc : ∀ k, IsCv V (γ k)) : IsCv V Γ := by
  intro i
  have hcoef : ∀ n, Tends V (fun k => PowerSeries.coeff n (γ k i)) (PowerSeries.coeff n (Γ i)) :=
    fun n => tendsP (h i) n
  refine ⟨?_, fun n => ge_zero_of_tends_of_forall_ge_zero (hcoef n) (fun k => (hc k i).2 n)⟩
  have e : ∀ k, PowerSeries.coeff 0 (γ k i) = 0 := fun k => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hc k i).1
  have h0 := hcoef 0
  simp only [e] at h0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact eq_zero_of_tends_const_zero h0

theorem constantCoeff_lin {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    (X : RawChart C d I κ) (l : ℕ) (hl : 2 ≤ l) (g : Fin 2) (b : I g → ℕ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS l (b c)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  first
    | rw [map_smul, coeff_tyS_mv]
    | rw [MvPowerSeries.coeff_smul, coeff_tyS_mv]
  simp

private theorem hasSubst_of_constantCoeff_eq_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

theorem lim_mem {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
    (hl : 2 ≤ V.l)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0) (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C)
    (hx : ∀ k, x k ∈ X.TySet V g) (hlim : VLim V x x') : x' ∈ X.TySet V g := by
  classical
  unfold RawChart.TySet at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  choose γk lamk hγk hlamk hA hB using hx
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → κ → PowerSeries C,
      T = fun k i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x k s (Sum.inl c)) := ⟨_, rfl⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : κ → PowerSeries C,
      T' = fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x' s (Sum.inl c)) := ⟨_, rfl⟩
  have hT0 : ∀ k i, MvPowerSeries.constantCoeff (T k i) = 0 := by
    intro k i
    rw [hTdef]
    exact constantCoeff_lin X V.l hl g (fun c s => x k s (Sum.inl c)) i
  have hT'0 : ∀ i, MvPowerSeries.constantCoeff (T' i) = 0 := by
    intro i
    rw [hT'def]
    exact constantCoeff_lin X V.l hl g (fun c s => x' s (Sum.inl c)) i
  have hTlim : ∀ i, TendsS V (fun k => T k i) (T' i) := by
    intro i
    simp only [hTdef, hT'def]
    exact tendsS_sum Finset.univ (fun c _ => tendsS_smul (X.u g c i)
      (tendsS_tyS (a := fun k s => x k s (Sum.inl c)) (a' := fun s => x' s (Sum.inl c)) V.l
        (fun s w => hlim w s (Sum.inl c))))
  have hHSlg : MvPowerSeries.HasSubst X.lg := hasSubst_of_constantCoeff_eq_zero' hlg0
  have hHSex : MvPowerSeries.HasSubst X.ex := hasSubst_of_constantCoeff_eq_zero' hex0
  have hHS : ∀ k, MvPowerSeries.HasSubst (γk k) := fun k =>
    hasSubst_of_constantCoeff_eq_zero' (fun i => (hγk k i).1)
  have hHST' : MvPowerSeries.HasSubst T' := hasSubst_of_constantCoeff_eq_zero' hT'0
  have hγeq : ∀ k i, γk k i = MvPowerSeries.subst (T k) (X.ex i) := by
    intro k i
    have e1 : T k = fun j => MvPowerSeries.subst (γk k) (X.lg j) := by
      funext j
      rw [hTdef]
      exact (hA k j).symm
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hHSlg (hHS k), hexlg, MvPowerSeries.subst_X (hHS k)]
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : κ → PowerSeries C, γ' = fun i => MvPowerSeries.subst T' (X.ex i) :=
    ⟨_, rfl⟩
  have hγlim : ∀ i, TendsS V (fun k => γk k i) (γ' i) := by
    intro i
    simp only [hγeq, hγ'def]
    exact TendsS.subst (fun k j => hT0 k j) hT'0 hTlim (TendsS.const _)
  have hγ' : IsCv V γ' := isCv_lim hγlim hγk
  have hγ'0 : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hrel : ∀ i, alongCv γ' (X.lg i) = T' i := by
    intro i
    unfold alongCv
    rw [hγ'def, ← MvPowerSeries.subst_comp_subst_apply hHSex hHST', hlgex, MvPowerSeries.subst_X hHST']
  obtain ⟨lam', hlam'def⟩ : ∃ lam' : JJ I g → PowerSeries C, lam' = fun q =>
      tyS V.l (fun s => x' s (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x' s (Sum.inl c)) else 0) := ⟨_, rfl⟩
  have hlamlim : ∀ q, TendsS V (fun k => lamk k q) (lam' q) := by
    intro q
    have e : ∀ k, lamk k q = tyS V.l (fun s => x k s (Sum.inr q)) + alongCv (γk k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x k s (Sum.inl c)) else 0) := by
      intro k
      rw [hB k q]
      ring
    simp only [e, hlam'def]
    refine TendsS.sub (TendsS.add ?_ ?_) ?_
    · exact tendsS_tyS (a := fun k s => x k s (Sum.inr q)) (a' := fun s => x' s (Sum.inr q)) V.l
        (fun s w => hlim w s (Sum.inr q))
    · unfold alongCv
      exact TendsS.subst (fun k j => (hγk k j).1) hγ'0 hγlim (TendsS.const _)
    · refine tendsS_sum _ (fun c _ => ?_)
      split_ifs
      · exact tendsS_smul _ (tendsS_tyS (a := fun k s => x k s (Sum.inl c))
          (a' := fun s => x' s (Sum.inl c)) V.l (fun s w => hlim w s (Sum.inl c)))
      · exact TendsS.const 0
  refine ⟨γ', lam', hγ', isCv_lim hlamlim hlamk, fun i => ?_, fun q => ?_⟩
  · rw [hrel i, hT'def]
  · simp only [hlam'def]
    ring

end LimTy

theorem limTy_holds : LimTySt := by
  unfold LimTySt AllFB
  intro C _ _ V O _ _ dd Y d _ I _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.raw p) V.l_prime.two_le
    (fun i => FBChart.chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.raw_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.raw_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OAct

open PartialDerivEval LogEx OActLog OActSg

variable {C : Type} [Field C]

theorem tyS_smul (l : ℕ) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  ext n
  rw [PowerSeries.coeff_smul]
  simp only [tyS, PowerSeries.coeff_mk, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

variable {dd : ℕ}

theorem uncurry_sub (f g : PS C 1 dd) : un1 (f - g) = un1 f - un1 g := by
  funext μ
  show MvPowerSeries.coeff _ (f - g) = MvPowerSeries.coeff _ f - MvPowerSeries.coeff _ g
  exact map_sub _ _ _

theorem uncurry_C_mul (c : C) (f : PS C 1 dd) : un1 (MvPowerSeries.C c * f) = MvPowerSeries.C c * un1 f := by
  funext μ
  show MvPowerSeries.coeff _ (MvPowerSeries.C c * f) = MvPowerSeries.coeff μ (MvPowerSeries.C c * un1 f)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem uncurry_linear_combination (c : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, MvPowerSeries.C (c j) * un1 (f j) := by
  funext μ
  show MvPowerSeries.coeff _ (∑ j, MvPowerSeries.C (c j) * f j) =
    MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (c j) * un1 (f j))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem integralSeries_uncurry_one {V : VF C} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) := fun _ => hf _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem sgP_smul (Y : FBChart C V O dd) (c : C) (v : Fin dd → C) :
    Y.sgP (c • v) = MvPowerSeries.C c * Y.sgP v := by
  unfold FBChart.sgP
  rw [mul_neg, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem em_flip {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {Y : FBChart C V O dd} (p : PairData Y d I)
    (g : Fin 2) (a : ZMod d) (α : O) : p.em (1 - g) a (star α) = p.em g a α := by
  fin_cases g
  · simp [p.em_conj]
  · simp [p.em_conj]

theorem oActTySt_holds : OActTySt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g α x hx
  obtain ⟨γ, lam, hγ, hlam, hlg, hsg⟩ := hx
  set φ : Pt C 1 dd := Y.B.A.act α with hφdef
  set ψ : Pt C 1 dd := Y.B.A.act (star α) with hψdef
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := Y.B.A.const α
  have hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_ps.2 (hγ j).2
  have hSγ : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
  have hφu0 : ∀ j, MvPowerSeries.constantCoeff (un1 (φ j)) = 0 := fun j => by rw [constantCoeff_uncurry, hφ0 j]

  set γ' : Fin dd → PowerSeries C := fun j => alongCv γ (un1 (φ j)) with hγ'def
  have hγ'0 : ∀ j, MvPowerSeries.constantCoeff (γ' j) = 0 := fun j => constantCoeff_subst_zero hγ0 (hφu0 j)
  have hγ'cv : IsCv V γ' := fun j =>
    ⟨hγ'0 j, intS_ps.1 (IntS.subst hγ0 hγI (integralSeries_uncurry_one (Y.intAct α j)))⟩
  have hcomp : ∀ f : PS C 1 dd, alongCv γ' (un1 f) = alongCv γ (un1 (ev (n := 1) ![φ] f)) := by
    intro f
    unfold alongCv
    rw [hγ'def]
    unfold alongCv
    rw [← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hφu0) hSγ]
    congr 1
    rw [subst_singlePointUncurry hφu0, eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => φ p.2) (fun p => hφ0 p.2)]
  have hsubC : ∀ (c : C) (f : MvPowerSeries (Fin dd) C), alongCv γ (MvPowerSeries.C c * f) = c • alongCv γ f := by
    intro c f
    unfold alongCv
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.coe_substAlgHom hSγ, map_smul]
  have hsub : ∀ f f' : MvPowerSeries (Fin dd) C, alongCv γ (f - f') = alongCv γ f - alongCv γ f' := by
    intro f f'
    unfold alongCv
    rw [← MvPowerSeries.coe_substAlgHom hSγ, map_sub]
  have hsum : ∀ (c : Fin dd → C) (f : Fin dd → MvPowerSeries (Fin dd) C),
      alongCv γ (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, c j • alongCv γ (f j) := by
    intro c f
    have e : alongCv γ (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, alongCv γ (MvPowerSeries.C (c j) * f j) := by
      unfold alongCv
      rw [← MvPowerSeries.coe_substAlgHom hSγ, map_sum]
    rw [e]
    exact Finset.sum_congr rfl fun j _ => hsubC (c j) (f j)

  have hsg0 : ∀ w, MvPowerSeries.constantCoeff (Y.sgP w) = 0 := fun w => by
    have h := (Y.raw p).constantCoeff_sg (Y.raw_axis0 p) w
    rwa [Y.raw_sg p, constantCoeff_uncurry] at h
  set Dq : JJ I g → PS C 1 dd := fun q =>
    ev (n := 1) ![φ] (Y.sgP ((Y.raw p).u (1 - g) q)) - Y.sgP (linAct ψ ((Y.raw p).u (1 - g) q)) with hDq
  have hDcc : ∀ q, MvPowerSeries.constantCoeff (alongCv γ (un1 (Dq q))) = 0 := fun q =>
    constantCoeff_subst_zero hγ0 (by
      rw [constantCoeff_uncurry, hDq]
      simp only
      rw [map_sub, constantCoeff_ev (z0_1 φ hφ0), hsg0, hsg0, sub_zero])
  have hDint : ∀ q, IntS V (alongCv γ (un1 (Dq q))) := fun q =>
    IntS.subst hγ0 hγI (integralSeries_uncurry_one (sg_act Y α _ (p.u_int (1 - g) q)))
  have hlin_v : ∀ q, linAct ψ ((Y.raw p).u (1 - g) q) = p.em g ((Y.raw p).ty (1 - g) q) α • (Y.raw p).u (1 - g) q := by
    intro q
    have h := p.u_eig (1 - g) q (star α)
    rw [em_flip] at h
    exact h
  have hE : ∀ q, alongCv γ' ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) =
      p.em g ((Y.raw p).ty (1 - g) q) α • alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) + alongCv γ (un1 (Dq q)) := by
    intro q
    rw [hDq]
    simp only
    rw [Y.raw_sg p, hcomp, uncurry_sub, hsub, hlin_v, sgP_smul, uncurry_C_mul, hsubC]
    abel
  set lam' : JJ I g → PowerSeries C := fun q => p.em g ((Y.raw p).ty (1 - g) q) α • lam q + alongCv γ (un1 (Dq q))
    with hlam'def
  have hlam'cv : IsCv V lam' := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [hlam'def]
      simp only
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, PowerSeries.coeff_smul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, (hlam q).1]
      rw [show PowerSeries.constantCoeff (alongCv γ (un1 (Dq q))) = 0 from hDcc q]
      simp
    · rw [hlam'def]
      simp only
      rw [map_add, PowerSeries.coeff_smul, smul_eq_mul]
      exact ((p.em_int g _ α).mul_int ((hlam q).2 n)).add (intS_ps.1 (hDint q) n)
  refine ⟨γ', lam', hγ'cv, hlam'cv, fun i => ?_, fun q => ?_⟩
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl]
    have hu : ∀ c, ∑ j, linM φ i j * (Y.raw p).u g c j = p.em g ((Y.raw p).ty g c) α * (Y.raw p).u g c i :=
      fun c => congrFun (p.u_eig g c α) i
    rw [show (Y.raw p).lg i = un1 (Y.lg i) from rfl, hcomp,
      show ev (n := 1) ![φ] (Y.lg i) = comp1 Y.lg φ i from rfl,
      log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add φ hφ0 (Y.B.A.hom α) i, uncurry_linear_combination, hsum]
    simp only [show ∀ j, un1 (Y.lg j) = (Y.raw p).lg j from fun j => rfl, hlg, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, hu c, mul_comm]
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl, Sum.elim_inr]
    rw [hsg q, hE q, hlam'def]
    simp only
    rw [smul_add, smul_sub, Finset.smul_sum]
    have hs : ∀ c : I g, p.em g ((Y.raw p).ty (1 - g) q) α •
        (if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
          (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
          (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) •
            (p.em g ((Y.raw p).ty g c) α • tyS V.l (fun s => x s (Sum.inl c))) else 0 := by
      intro c
      split_ifs with h
      · rw [h, smul_comm]
      · rw [smul_zero]
    rw [Finset.sum_congr rfl fun c _ => hs c]
    abel

end OAct

end Formalism.L2.FormalSeriesBounds
end
end

