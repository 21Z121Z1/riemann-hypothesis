import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.CMTypeLowModes
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def FinMu (X : Data E r) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ FF : Set (V (nd X)), IsFundSet X x0 FF → muF X x0 FF < ⊤

def IsInvariant (X : Data E r) (ps : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ps (rmul x b) = ps x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ps (lact γ x) = ps x

def TwoBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ Cη : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ Cη + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ

def PointBound (X : Data E r) (la : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x → ∀ M : ℝ,
    (∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom → ps (cpt X x z) ≤ M) →
    X.pnorm la P x ≤ C * Real.exp (M / 2)

def NoModesBelow (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (a : ℝ) : Prop :=
  ∀ ξ : Fin r → E, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ < a → ∀ x ∈ X.dom, X.fj la ξ ν P x = 0

def LowModes (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ), 0 ≤ a →
    X.IsSec la P → IsInvariant X ps → TwoBounds X ps a → PointBound X la ps P →
    NoModesBelow X la P a

def Inputs (X : Data E r) : Prop := FinMu X ∧ LowModes X

def InputsStatement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r), Inputs X

end

end GlobalTheory.IndefiniteRowSideFullHecke.CMTypeLowModes
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.LowSpanCombinations
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def OnQuot {α : Type*} (X : Data E r) (φ : Frame X.Ψ r → α) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x

def SamePt (X : Data E r) (x y : Frame X.Ψ r) : Prop :=
  ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((φ (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

def Admissible (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ OnQuot X ps ∧ ExtraBounds X ps a

def famNorm (X : Data E r) (L : Wt X.Ψ r) {ι : Type} [Fintype ι] (g : ι → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm L (g j) x ^ 2)

def IsComb (X : Data E r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : Fin N → ℂ, ∀ x ∈ X.dom, f x = ∑ j, c j * w j x

def zMap (X : Data E r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (x0 : Frame X.Ψ r) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun i => s i (cpt X x0 u) / w0 (cpt X x0 u)

structure IsFlat (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) {del : ℕ}
    (P : Fin del → Frame X.Ψ r) : Prop where
  w_sec : ∀ j, X.IsSec L (w j)
  base_weight_isComb : IsComb X w w0
  s_comb : ∀ i, IsComb X w (s i)
  w_pos : ∀ x ∈ X.dom, 0 < famNorm X L w x
  del_pos : 0 < del
  rep_mem : ∀ k, P k ∈ X.dom
  rep_inj : ∀ k k', SamePt X (P k) (P k') → k = k'
  zero_iff : ∀ x ∈ X.dom, (∀ i, s i x = 0) ↔ ∃ k, SamePt X (P k) x
  w0_ne : ∀ k, w0 (P k) ≠ 0
  coord : ∀ k, ∃ T : V (nd X) ≃L[ℂ] V (nd X),
    HasFDerivAt (zMap X w0 s (P k)) (T : V (nd X) →L[ℂ] V (nd X)) 0
  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) → ∃ C : ℝ, ∀ x ∈ X.dom,
    (∀ u ∈ U, u ∈ X.dom → ¬ SamePt X u x) → famNorm X L w x ≤ C * famNorm X L s x
  weight_le_base_weight : ∃ C : ℝ, ∀ x ∈ X.dom,
    famNorm X L w x ≤ C * famNorm X L (fun o : Option (Fin (nd X)) => o.elim w0 s) x

def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T

theorem mem_lowIdx {D T : ℕ} {al : Fin D → ℕ} : al ∈ lowIdx D T ↔ ∑ i, al i + D < T := by
  simp only [lowIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro h i
  have := Finset.single_le_sum (f := al) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

def gen {α : Type*} {D : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : α → ℂ) (al : Fin D → ℕ)
    (x : α) : ℂ :=
  (∏ i, s i x ^ al i) * w0 x ^ (T - ∑ i, al i) * t x

def lowComb {α : Type*} {D del : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : Fin del → α → ℂ)
    (c : (Fin D → ℕ) → Fin del → ℂ) (x : α) : ℂ :=
  ∑ al ∈ lowIdx D T, ∑ k, c al k * gen T w0 s (t k) al x

def InLowSpan (X : Data E r) (T : ℕ) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    {del : ℕ} (t : Fin del → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : (Fin (nd X) → ℕ) → Fin del → ℂ, ∀ x ∈ X.dom, f x = lowComb T w0 s t c x

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

theorem admissible_zero (X : Data E r) : Admissible X (fun _ => 0) 0 :=
  ⟨le_rfl, ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, 0,
    fun _ _ => ⟨0, fun _ _ _ _ _ => by simp⟩, 0, fun _ _ => by simp⟩

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  have h : mat (nmat X 0) τ = 1 := by
    ext a b
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    split_ifs with h1 h2
    · exact absurd h2 h1.ne'
    all_goals first | rfl | simp
  simp only [cpt, rmul, h, Matrix.mul_one]
  rfl

theorem isFlat_rank_one (X : Data E 1) (x0 : Frame X.Ψ 1) (h0 : x0 ∈ X.dom) :
    IsFlat X 0 (fun _ : Fin 1 => fun _ => 1) (fun _ => 1) (fun _ _ => 0) (fun _ : Fin 1 => x0) := by
  have hE : IsEmpty (Ent X) := ⟨fun p => absurd p.2.2 (by rw [Subsingleton.elim p.2.1.2 p.2.1.1]; exact lt_irrefl _)⟩
  have hnd : nd X = 0 := Fintype.card_eq_zero
  have hF : IsEmpty (Fin (nd X)) := by rw [hnd]; infer_instance
  have hV : Subsingleton (V (nd X)) := ⟨fun u v => by ext i; exact hF.elim i⟩
  have hsame : ∀ x ∈ X.dom, SamePt X x0 x := by
    intro x hx
    have ha : ∀ τ, x0 τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (h0 τ).1
    have hb : ∀ τ, x τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (hx τ).1
    refine ⟨1, X.Γ.one_mem, fun τ _ _ => x τ 0 0 / x0 τ 0 0, fun τ => ⟨?_, fun a c h => ?_⟩, ?_⟩
    · simpa [mat] using ⟨hb τ, ha τ⟩
    · exact absurd h (by rw [Subsingleton.elim c a]; exact lt_irrefl _)
    · funext τ a c
      rw [Subsingleton.elim a 0, Subsingleton.elim c 0]
      have := ha τ
      simp [lact, rmul, mat, Matrix.mul_apply]
      change x τ 0 0 = ∑ j : Fin 1, x0 τ 0 j * (x τ 0 0 / x0 τ 0 0)
      simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
      field_simp
  have hχ : ∀ γ ∈ X.Γ, X.χ 0 γ = 1 := by
    intro γ hγ
    obtain ⟨n, hn, h⟩ := X.χ_fin 0
    have hne : X.χ 0 γ ≠ 0 := fun e => by
      have := h γ hγ
      rw [e, zero_pow hn.ne'] at this
      exact zero_ne_one this
    have h2 := X.χ_add 0 0 γ hγ
    rw [add_zero] at h2
    exact (mul_right_eq_self₀.1 h2.symm).resolve_right hne
  have hp : ∀ x, X.pnorm 0 (fun _ => 1) x = 1 := fun x => by simp [Data.pnorm]
  refine ⟨fun _ => ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar],
      fun γ hγ x _ => by simp [hχ γ hγ]⟩, ⟨fun _ => 1, fun _ _ => by simp⟩,
    fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun x _ => by simp [famNorm, hp], Nat.one_pos,
    fun _ => h0, fun _ _ _ => Subsingleton.elim _ _,
    fun x hx => ⟨fun _ => ⟨0, hsame x hx⟩, fun _ _ => rfl⟩, fun _ => one_ne_zero,
    fun _ => ⟨ContinuousLinearEquiv.refl ℂ _, ?_⟩,
    fun U _ hU => ⟨0, fun x hx h => absurd (hsame x hx) (h x0 (hU 0) h0)⟩,
    1, fun x _ => ?_⟩
  · have := hasFDerivAt_of_subsingleton (𝕜 := ℂ) (zMap X (fun _ => 1) (fun _ _ => 0) x0) 0
    convert this using 1
    ext v i
    exact hF.elim i
  · unfold famNorm
    rw [Fintype.sum_option]
    simp [hp]

example : lowIdx 1 3 = {![0], ![1]} := by decide

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ r) : Frame Ψ' r :=
  fun τ => x ⟨τ.1, h.symm ▸ τ.2⟩

def castWt {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) : Wt Ψ r :=
  fun τ => la ⟨τ.1, h ▸ τ.2⟩

def deMul (Ψ : Finset (E →+* ℂ)) (r p0 s : ℕ) : Wt Ψ r :=
  fun _ i => if (i : ℕ) < p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)

def GapsGe {Ψ : Finset (E →+* ℂ)} (p0 : ℕ) (la : Wt Ψ r) (a : ℤ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ p0 → a ≤ la τ i - la τ j

def PairGe {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (a : ℝ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (i : ℕ) = 0 → (j : ℕ) = r - 1 → a ≤ ((la τ j - la τ i : ℤ) : ℝ)

structure TwoLevels (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (U C : Type) [Group U] [MulAction U C] where
  Ψ : Finset (E →+* ℂ)
  Gm : Matrix (Fin r) (Fin r) E
  p0 : ℕ
  ξ0 : E
  comp : C → DataX E r
  comp_Ψ : ∀ c, (comp c).Ψ = Ψ
  comp_Gm : ∀ c, (comp c).Gm = Gm
  comp_basePoint : ∀ c, (comp c).p0 = p0
  comp_ξ0 : ∀ c, (comp c).ξ0 = ξ0

  χ_one : ∀ c la, ∀ γ ∈ (comp c).Γ, (comp c).χ la γ = 1

  Γ_L' : ∀ c, ∀ γ ∈ (comp c).Γ, ∀ v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ (comp c).L'

  tr : U → C → GL (Fin r) E
  tr_herm : ∀ u c v w, herm Gm (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v)
    (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) w) = herm Gm v w
  tr_Λ : ∀ u c v,
    v ∈ (comp c).Λ ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).Λ
  tr_L' : ∀ u c v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).L'
  tr_conj : ∀ u c γ, γ ∈ (comp c).Γ ↔ tr u c * γ * (tr u c)⁻¹ ∈ (comp (u • c)).Γ
  tr_mul : ∀ u v c, tr (u * v) c * (tr u (v • c) * tr v c)⁻¹ ∈ (comp ((u * v) • c)).Γ

  tr_faithful : ∀ u c, u • c = c → tr u c ∈ (comp c).Γ → u = 1

namespace TwoLevels

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

def dom : Set (Frame M.Ψ r) := GG M.Ψ M.Gm M.p0

def dimX : ℕ := M.Ψ.card * (M.p0 * (r - M.p0))

def dimY : ℕ := M.Ψ.card * (r * (r - 1) / 2)

def upper (c : C) : Set (GL (Fin r) E) :=
  {β | ∃ u : U, u • c = c ∧ ∃ γ ∈ (M.comp c).Γ, β = γ * M.tr u c}

def UnipotentOver (g : ℕ) : Prop :=
  ∀ c, ∀ β ∈ M.upper c, ∀ P : Ideal (𝓞 E), P.IsPrime → (g : 𝓞 E) ∈ P → ∀ v ∈ (M.comp c).L',
    Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • (M.comp c).L'

def SS (la : Wt M.Ψ r) : Set (C → Frame M.Ψ r → ℂ) :=
  {F | ∀ c, (fun x => F c (castFrame (M.comp_Ψ c) x)) ∈ (M.comp c).SS (castWt (M.comp_Ψ c) la)}

def pull (h : U) (F : C → Frame M.Ψ r → ℂ) : C → Frame M.Ψ r → ℂ :=
  fun c x => F (h • c) (lact (M.tr h c) x)

def res (F : C → Frame M.Ψ r → ℂ) : C → M.dom → ℂ := fun c x => F c x.1

def cusp (la : Wt M.Ψ r) : Submodule ℂ (C → M.dom → ℂ) := Submodule.span ℂ (M.res '' M.SS la)

def cuspPsi (la : Wt M.Ψ r) (ψ : U →* ℂˣ) : Submodule ℂ (C → M.dom → ℂ) :=
  Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧
    ∀ h c, ∀ x ∈ M.dom, M.pull h F c x = ((ψ h : ℂˣ) : ℂ) * F c x})

def detTr [Fintype U] [DecidableEq U] (F : C → Frame M.Ψ r → ℂ) (c : C) (x : Frame M.Ψ r) : ℂ :=
  (Matrix.of fun h h' : U => M.pull (h * h') F c x).det

end TwoLevels

def SplitsCompletely (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P}.ncard = Module.finrank ℚ E

def LevelHyp {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C) : Prop :=
  ∃ g : ℕ, SplitsCompletely E g ∧ 3 * r < g ∧ M.UnipotentOver g

def IndependentTranslates (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Fintype U] [DecidableEq U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s →
      ∃ u0 ∈ M.SS (deMul M.Ψ r M.p0 s), ∀ c : C, ∃ x ∈ M.dom, M.detTr u0 c x ≠ 0

def sqSum (X : Data E r) (la : Wt X.Ψ r) {n : ℕ} (w : Fin n → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ∑ k, X.pnorm la (w k) x ^ 2

def IsFlat (X : Data E r) (L Fp : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) : Prop :=
  ∃ (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (Δ : MvPolynomial (Fin (nd X)) ℂ)
    (thp : Frame X.Ψ r → ℂ),
    (∃ a : Fin N → ℂ, ∀ x ∈ X.dom, w0 x = ∑ j, a j * w j x) ∧
    (∀ k, ∃ a : Fin N → ℂ, ∀ x ∈ X.dom, s k x = ∑ j, a j * w j x) ∧
    (∃ x ∈ X.dom, ∀ k, s k x = 0) ∧
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0) ∧
    (∀ O : Set (Frame X.Ψ r), IsOpen O → (∀ x ∈ X.dom, (∀ k, s k x = 0) → x ∈ O) →
      (∀ x ∈ O, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ O) →
      ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ O → sqSum X L w x ≤ K * sqSum X L s x) ∧
    (∃ K : ℝ, ∀ x ∈ X.dom, sqSum X L w x ≤ K * (X.pnorm L w0 x ^ 2 + sqSum X L s x)) ∧
    MvPolynomial.constantCoeff Δ ≠ 0 ∧
    (∀ x ∈ X.dom, w0 x ≠ 0 → MvPolynomial.eval (fun k => s k x / w0 x) Δ ≠ 0 →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0 ∧ thp x ≠ 0) ∧
    (∀ K : Set (Fin (nd X) → ℂ), IsCompact K → (∀ z ∈ K, MvPolynomial.eval z Δ ≠ 0) →
      ∃ Q : Set (Frame X.Ψ r), IsCompact Q ∧ Q ⊆ X.dom ∧ ∀ x ∈ X.dom, w0 x ≠ 0 →
        (fun k => s k x / w0 x) ∈ K → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Q) ∧
    thp ∈ X.SS Fp

def ThetaInputs (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ (N : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (th1 th2 η : Frame X.Ψ r → ℂ) (φ : Frame X.Ψ r → ℝ)
    (i g0 : ℕ) (c : ℝ),
    (∀ j, w j ∈ X.SS L) ∧ (∀ x ∈ X.dom, ∃ j, w j x ≠ 0) ∧ IsFlat X L Fp w ∧
    X.IsBddSec (2 • L - deMul X.Ψ r X.p0 2) th1 ∧ (∃ x ∈ X.dom, th1 x ≠ 0) ∧
    X.IsBddSec ((nd X + 4) • L - Fp) th2 ∧ (∃ x ∈ X.dom, th2 x ≠ 0) ∧
    1 ≤ i ∧ 1 ≤ g0 ∧ Even g0 ∧ 0 < c ∧ (T : ℝ) * c * g0 ≤ 1 ∧
    X.IsSec (deMul X.Ψ r X.p0 (i * g0)) η ∧ (∃ x ∈ X.dom, η x ≠ 0) ∧
    (∀ x ∈ X.dom, 0 ≤ φ x) ∧
    (∃ K : ℝ, ∀ x ∈ X.dom,
      X.pnorm (deMul X.Ψ r X.p0 (i * g0)) η x ≤ K * Real.exp (-(i * φ x))) ∧
    ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * φ x)) ≤ K * sqSum X L w x

def kLog (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Wt Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)

def ShareIndefinite (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M → 0 < M.p0 → M.p0 < r →
    ∀ (L Fp : Wt M.Ψ r) (T s : ℕ),
      2 ≤ M.dimY → 11 * M.dimY ^ 2 ≤ T →
      Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → s ≤ T →
      GapsGe M.p0 L 1 → PairGe L (1.9 * T) →
      GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 →
      PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 →
      (∀ c, ThetaInputs (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T) →
      ∀ ψ : U →* ℂˣ,
        Module.Finite ℂ (M.cusp (Fp + T • L)) ∧
        (1 - (M.dimY : ℝ) * (M.dimY + 6) / T) * Module.finrank ℂ (M.cusp (Fp + T • L)) ≤
          (Nat.card U : ℝ) * Module.finrank ℂ (M.cuspPsi (Fp + T • L) ψ)

def ShareDefinite (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M → (M.p0 = 0 ∨ M.p0 = r) →
    ∀ (κ : Wt M.Ψ r) (ψ : U →* ℂˣ),
      Module.Finite ℂ (M.cusp κ) ∧
      Nat.card U * Module.finrank ℂ (M.cuspPsi κ ψ) = Module.finrank ℂ (M.cusp κ)

def EpsBound : Prop :=
  ∀ (f k D T : ℕ) (P : ℝ), 2 ≤ f * k → 6 ≤ D → ((f * k : ℕ) : ℝ) ≤ P →
    P ^ 3 * (D : ℝ) ^ 3 * k * f ≤ T →
    (D : ℝ) * (D + 6) / T ≤ (((f * k : ℕ) : ℝ) ^ 3)⁻¹ / 4

def Statement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  IndependentTranslates E ∧ ShareIndefinite E ∧ ShareDefinite E ∧ EpsBound

def TwoLevels.regular (X : DataX E r) (U : Type) [Group U]
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1)
    (hL : ∀ γ ∈ X.Γ, ∀ v, v ∈ X.L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ X.L') :
    TwoLevels E r U U where
  Ψ := X.Ψ
  Gm := X.Gm
  p0 := X.p0
  ξ0 := X.ξ0
  comp := fun _ => X
  comp_Ψ := fun _ => rfl
  comp_Gm := fun _ => rfl
  comp_basePoint := fun _ => rfl
  comp_ξ0 := fun _ => rfl
  χ_one := fun _ => hχ
  Γ_L' := fun _ => hL
  tr := fun _ _ => 1
  tr_herm := by intro u c v w; simp
  tr_Λ := by intro u c v; simp
  tr_L' := by intro u c v; simp
  tr_conj := by intro u c γ; simp
  tr_mul := by intro u v c; simp
  tr_faithful := by intro u c h _; simpa using h

theorem epsBound : EpsBound := by
  intro f k D T P h2 h6 hP hT
  have h2' : (2 : ℝ) ≤ ((f * k : ℕ) : ℝ) := by exact_mod_cast h2
  have h6' : (6 : ℝ) ≤ D := by exact_mod_cast h6
  have hkf : (k : ℝ) * f = ((f * k : ℕ) : ℝ) := by push_cast; ring
  set a : ℝ := ((f * k : ℕ) : ℝ) with ha
  have ha0 : 0 < a := by linarith
  have h3 : a ^ 3 ≤ P ^ 3 := pow_le_pow_left₀ ha0.le hP 3
  have hT' : a ^ 3 * ((D : ℝ) ^ 3 * a) ≤ T := by
    calc a ^ 3 * ((D : ℝ) ^ 3 * a) ≤ P ^ 3 * ((D : ℝ) ^ 3 * a) := by gcongr
      _ = P ^ 3 * (D : ℝ) ^ 3 * k * f := by rw [← hkf]; ring
      _ ≤ T := hT
  have hD : 4 * ((D : ℝ) * (D + 6)) ≤ (D : ℝ) ^ 3 * a := by
    have : (D : ℝ) ^ 3 * 2 ≤ (D : ℝ) ^ 3 * a := by gcongr
    nlinarith [mul_nonneg (sub_nonneg.2 h6') (sq_nonneg (D : ℝ)), sq_nonneg (D : ℝ)]
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT'
  rw [div_le_iff₀ hT0, inv_eq_one_div, div_div, div_mul_eq_mul_div, one_mul,
    le_div_iff₀ (by positivity)]
  have : a ^ 3 * (4 * ((D : ℝ) * (D + 6))) ≤ a ^ 3 * ((D : ℝ) ^ 3 * a) := by gcongr
  linarith

end

end GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
end

