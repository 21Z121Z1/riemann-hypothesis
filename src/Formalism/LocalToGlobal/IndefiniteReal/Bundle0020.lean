import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MultGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_of_enum {n p q : ℕ} (L : Fin n → ℚ) (s : Fin n → Bool) (hL : StrictAnti L)
    (hi : ∀ a, ∃ z : ℤ, (L a : ℝ) - ((n : ℝ) - 1) / 2 = z)
    (hp : (Finset.univ.filter fun a => s a = true).card = p)
    (hq : (Finset.univ.filter fun a => s a = false).card = q) :
    GoodPar n p q (Finset.univ.image fun a => (L a, s a)) :=
  ⟨fun a => (L a : ℝ), s, ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, L, fun _ => rfl, rfl⟩,
    ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, hi⟩, hp, hq⟩

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem card_false_eq {n : ℕ} (s : Fin n → Bool) :
    (Finset.univ.filter fun a => s a = false).card = n - (Finset.univ.filter fun a => s a = true).card := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => s a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  omega

theorem sum_first_or_even (K c : ℕ) :
    ∑ i ∈ Finset.range (K + 2 * c), (if i < K ∨ Even (i - K) then 1 else 0) = K + c := by
  induction c with
  | zero =>
    simp only [mul_zero, add_zero]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Or.inl (Finset.mem_range.mp hi)))]
    simp
  | succ c ih =>
    rw [show K + 2 * (c + 1) = K + 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_pos (Or.inr ⟨c, by omega⟩), if_neg (by rintro (h | ⟨d, hd⟩) <;> omega)]
    omega

theorem sum_first (p q : ℕ) : ∑ i ∈ Finset.range (p + q), (if i < p then 1 else 0) = p := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have : (Finset.range (p + q)).filter (fun i => i < p) = Finset.range p := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

theorem lamAt_half {R : Ranks} (h : HCParam R) (a : Fin R.r) :
    ∃ z : ℤ, ((lamAt h a : ℚ) : ℝ) - ((R.r : ℝ) - 1) / 2 = z := by
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  rw [hz, hs]
  push_cast
  ring

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem parA_eq (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)) (τ : D.what₂.Tau) :
    parA (tparHC D eta h) 0 τ = Finset.univ.image fun a : Fin D.R.r => (lamAt (D.hc τ) a, sgA D.R a) := by
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold parA TPar.Dpar
  ext ⟨x, s⟩
  simp only [tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and, Prod.mk.injEq,
    Finset.mem_biUnion, Finset.mem_filter, Nat.not_lt_zero, false_and, exists_false, or_false,
    Nat.not_odd_zero, if_false, add_zero]
  constructor
  · rintro ⟨⟨y, s'⟩, (⟨i, hi⟩ | ⟨i, hi⟩), rfl, rfl⟩
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt; rw [dif_pos i.2]
      · unfold sgA; simp [i.2]
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨D.R.k - 1 + i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt
        rw [dif_neg (show ¬ (D.R.k - 1 + (i : ℕ) < D.R.k - 1) by omega),
          dif_pos (show D.R.k - 1 + (i : ℕ) - (D.R.k - 1) < D.R.m by have := i.2; omega)]
        simp only [Nat.add_sub_cancel_left]
      · unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)
  · rintro ⟨a, rfl, rfl⟩
    have ha := a.2
    by_cases c : (a : ℕ) < D.R.k - 1
    · refine ⟨_, Or.inl ⟨⟨a, c⟩, rfl⟩, ?_, ?_⟩
      · change (D.hc τ).v ⟨a, c⟩ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_pos c]
      · change true = sgA D.R a
        unfold sgA; simp [c]
    · refine ⟨_, Or.inr ⟨⟨(a : ℕ) - (D.R.k - 1), by omega⟩, rfl⟩, ?_, ?_⟩
      · change -(D.hc τ).b _ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_neg c, dif_pos (by omega)]
      · change decide _ = sgA D.R a
        unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)

theorem card_sgA (R : Ranks) :
    (Finset.univ.filter fun a : Fin R.r => sgA R a = true).card = R.k - 1 + R.m / 2 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if sgA R i = true then 1 else 0) R.r]
  have hr : R.r = (R.k - 1) + 2 * (R.m / 2) := by
    have := R.m_add_three_le_k
    obtain ⟨c, hc⟩ := R.m_even
    unfold Ranks.r; omega
  rw [hr]
  simp only [sgA, decide_eq_true_eq]
  exact sum_first_or_even _ _

theorem goodPar_parA (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) : GoodPar D.R.r D.R.sigY0.1 D.R.sigY0.2 (parA (tparHC D eta h) 0 τ) := by
  rw [parA_eq]
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) ?_ ?_
  · rw [card_sgA]; simp only [Ranks.sigY0, Ranks.rS]; omega
  · rw [card_false_eq, card_sgA]; simp only [Ranks.sigY0, Ranks.rS, Ranks.r]; omega

theorem good_parameter_first_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parA (tparHC D eta h) 0 τ) := by
  rw [D.sp.baseSpace_signature_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  have : D.R.rankY 0 = D.R.r := by simp [Ranks.rankY]
  rw [this]
  exact goodPar_parA D eta h τ

theorem good_parameter_second_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parB (tparHC D eta h) 0 τ) :=
  goodPar_dualPar (good_parameter_first_base_space D eta h τ)

theorem goodPar_parA_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parA (tparRec D) 0 τ) :=
  good_parameter_first_base_space D _ _

theorem goodPar_parB_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parB (tparRec D) 0 τ) :=
  good_parameter_second_base_space D _ _

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

theorem card_lt_first {n : ℕ} (p q : ℕ) (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if decide (i < p) = true then 1 else 0) n, ← hpq]
  simp only [decide_eq_true_eq]
  exact sum_first p q

theorem goodPar_parW (D : D7) (W : HSp D) (τ : D.what₂.Tau)
    (hr : (W.sig (tauE D τ)).1 + (W.sig (tauE D τ)).2 = D.R.r) :
    GoodPar D.R.r (W.sig (tauE D τ)).1 (W.sig (tauE D τ)).2 (parW W (wtOf D W) τ) := by
  show GoodPar D.R.r _ _ (holPar _ _ (kapW (D.hc τ) _ _))
  rw [holPar_kapW_eq _ _ _ hr]
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) (card_lt_first _ _ hr) ?_
  rw [card_false_eq, card_lt_first _ _ hr]
  omega

theorem goodPar_parW_rec (D : D7) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) :
    ∀ τ, GoodPar (D.sp.W j).rank ((D.sp.W j).sig (tauE D τ)).1 ((D.sp.W j).sig (tauE D τ)).2
      (parW (D.sp.W j) (wtOf D (D.sp.W j)) τ) := by
  intro τ
  rw [D.sp.W_rank j hj1 hjm]
  refine goodPar_parW D _ τ ?_
  rw [D.sp.W_sigval j hj1 hjm]
  simp only [Ranks.sigW, Ranks.r]
  omega

end Formalism.IndefR.Mult
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem foldr_rderC_zero (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (τ : D.what₂.Tau) :
    (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons Z l ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    exact rderC_zero θ V τ Z

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) where
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}

theorem isMultMap_zero (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : IsMultMap θ M J χ 0 where
  aut v := by
    show IsAutFunSm θ V (fun _ => 0)
    exact isAutFunSm_zero θ V
  cusp v := by
    show IsCuspFun V (fun _ => 0)
    exact isCuspFun_zero V
  lev v k _ g := by simp
  equiv τ g _ v w _ := by
    funext x
    simp [rTr]
  cont τ v x := by
    refine ⟨0, ⟨[], 0, by simp, fun w _ => by simp⟩, fun w => by simp⟩

variable (V) in

theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _

variable (V) in

theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) where
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (V) in

theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]

theorem isMultMap_smul {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : IsMultMap θ M J χ T) (c : ℂ) : IsMultMap θ M J χ (c • T) where
  aut v := by
    show IsAutFunSm θ V (c • T v)
    exact isAutFunSm_smul θ V (hT.aut v) c
  cusp v := by
    show IsCuspFun V (c • T v)
    exact isCuspFun_smul V (hT.cusp v) c
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    rw [_root_.smul_apply, _root_.smul_apply, hT.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, ⟨L, C, hL, hC⟩, hℓ⟩ := hT.cont τ v x
    refine ⟨c • ℓ, ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩, fun w => ?_⟩
    · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, _root_.smul_apply, Pi.smul_apply, hℓ w]

theorem heckeLin_indep {D : D7} {V : HSp D} (K : Set (GA D V)) (x : GA D V) (R R' : Finset (GA D V))
    (F : GA D V → ℂ)
    (hinv : ∀ a ∈ K, a⁻¹ ∈ K)
    (hK : ∀ k ∈ K, ∀ g, F (g * k) = F g) (hR : IsCosetRep V K x R) (hR' : IsCosetRep V K x R') :
    heckeLin V R F = heckeLin V R' F := by
  funext g
  show ∑ γ ∈ R, F (g * γ) = ∑ γ ∈ R', F (g * γ)
  have ex1 : ∀ γ ∈ R, ∃ γ', γ' ∈ R' ∧ γ'⁻¹ * γ ∈ K := fun γ hγ => (hR'.2 γ (hR.1 γ hγ).2).exists
  have ex2 : ∀ γ ∈ R', ∃ γ', γ' ∈ R ∧ γ'⁻¹ * γ ∈ K := fun γ hγ => (hR.2 γ (hR'.1 γ hγ).2).exists
  choose! i hiR hiK using ex1
  choose! j hjR hjK using ex2
  refine Finset.sum_nbij' i j hiR hjR ?_ ?_ ?_
  · intro γ hγ
    have hk := hinv _ (hiK γ hγ)
    rw [_root_.mul_inv_rev, _root_.inv_inv] at hk
    exact (hR.2 (i γ) (hR'.1 (i γ) (hiR γ hγ)).2).unique
      ⟨hjR (i γ) (hiR γ hγ), hjK (i γ) (hiR γ hγ)⟩ ⟨hγ, hk⟩
  · intro γ hγ
    have hk := hinv _ (hjK γ hγ)
    rw [_root_.mul_inv_rev, _root_.inv_inv] at hk
    exact (hR'.2 (j γ) (hR.1 (j γ) (hjR γ hγ)).2).unique
      ⟨hiR (j γ) (hjR γ hγ), hiK (j γ) (hjR γ hγ)⟩ ⟨hγ, hk⟩
  · intro γ hγ
    show F (g * γ) = F (g * i γ)
    rw [← hK _ (hiK γ hγ) (g * i γ), _root_.mul_assoc, _root_.mul_inv_cancel_left]

theorem heckeOn_indep {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Set (GA D V))
    (x : GA D V) (R R' : Finset (GA D V)) (T : MMap M)
    (hinv : ∀ a ∈ K, a⁻¹ ∈ K)
    (hT : ∀ v, ∀ k ∈ K, ∀ g, T v (g * k) = T v g) (hR : IsCosetRep V K x R) (hR' : IsCosetRep V K x R') :
    heckeOn M R T = heckeOn M R' T := by
  ext v g
  exact congrFun (heckeLin_indep K x R R' (T v) hinv (hT v) hR hR') g

end Formalism.IndefR.Mult

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.WeilFull
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
  Formalism.IndefR.Fock.Sk MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.WeilFull

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SuppV (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = (mt V g - 1) i j

def UnrAtV (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, (1 - algebraMap (AF D.host.F) (AE D) ε) * (x : AE D) = 1 - algebraMap (AF D.host.F) (AE D) ε →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def SphInertAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
      Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (2 : 𝓞 D.host.F) ∉ v.asIdeal →
      (∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) →
      UnrAtV ε χS → UnrAtV ε χT →
    ∀ (g : GA D S) (h : GA D T), SuppV ε S g → SuppV ε T h →
      Lev.finE S g ∈ Formalism.L2.DIV.St βS → Lev.finE T h ∈ Formalism.L2.DIV.St βT →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f → om (g, h) f = f

def RealAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  LineAtExists D →
  ∀ (θ : InfFam D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

structure IsWeilFull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  datum : IsWeilDatumO ψ S T χS χT om
  inert : SphInertAtO ψ S T χS χT om
  real : RealAtO ψ S T χS χT om

def WeilExistsFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilFull ψ S T χS χT om

def InertAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → SphInertAtO ψ S T χS χT om

def RealAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → RealAtO ψ S T χS χT om

theorem weilExistsFull_of (h : AutomorphicFormsHyp.WeilExistsO D) (hi : InertAllO D) (hr : RealAllO D) : WeilExistsFull D := by
  intro ψ S T χS χT hψ hS hT hrS hrT
  obtain ⟨om, hom⟩ := h ψ S T χS χT hψ hS hT hrS hrT
  exact ⟨om, hom, hi ψ S T χS χT om hom, hr ψ S T χS χT om hom⟩

end Formalism.IndefR.WeilFull

end
end

