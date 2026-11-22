import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodOfMemSlots
section
noncomputable section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.LeafTerm

variable {C : Type} [Field C]

def KerLe (V : VF C) {σ τ : Type} [Fintype τ] (M : σ → τ → C) (r : ℕ) : Prop :=
  ∀ (N : ℕ) (y : Fin N → τ → C), (∀ ν t, V.Ge 0 (y ν t)) →
    (∀ ν s, V.MM (∑ t, M s t * y ν t)) → IndepMod V y → N ≤ r

def Wt (V : VF C) {σ : Type} (ρ : σ → ℝ) (w : ℝ) (f : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((w - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤
    V.v (MvPowerSeries.coeff α f)

def lin {ι I : Type} [Fintype ι] (e : ι → I → C) : I → MvPowerSeries ι C :=
  fun x => ∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)

def psi {I : Fin 2 → Type} (g : Fin 2) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : WV I → MvPowerSeries (ι ⊕ ι') C :=
  fun w => (∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', toW (1 - g) (v' b) w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

section Chain

variable {Z I J : Type} [Fintype I]

def slots (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : Finset I :=
  Finset.univ.filter fun c => D.lev c = s ∧ s < Formalism.BaseCaseIdentities.Kn D.i

def piM (D : Formalism.BaseCaseIdentities.Data C Z I) (s : ℕ) : I → Z → C :=
  Nat.rec (motive := fun _ => I → Z → C) (fun c j => if D.ι j = c then 1 else 0)
    (fun s p e j => ∑ c ∈ slots D s, (D.l : C) * D.al c 2 e * p c j ^ (D.l ^ 2)) s

variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}

def phiT (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (j : Z) (κ : J) : C :=
  (-1) ^ (Formalism.BaseCaseIdentities.s0 D.i + 1) * ∑ c ∈ slots D (Formalism.BaseCaseIdentities.s0 D.i),
    piM D (Formalism.BaseCaseIdentities.s0 D.i) c j ^ D.l * ((D.l : C) * S.be c 1 κ)

def Adapted (S : Sys X) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ) : Prop :=
  D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
    (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
    (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i → X.ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d))

theorem al_zero (S : Sys X) (c x : I) : S.al c 0 x = S.tan c x := by
  simp [Sys.al, (S.curve c).2.1]

theorem tan_int (S : Sys X) (c x : I) : V.Ge 0 (S.tan c x) := by
  rw [← al_zero]
  exact X.t2 _ (S.curve c).1 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}

theorem Adapted.good (h : Adapted S D a i) {c : I} (hc : D.good c) :
    X.Good (X.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  refine ⟨S.curve c, fun x => ?_⟩
  have := h.2.2.2.1 c 1 x le_rfl
  simpa [D.al_one c hc, Sys.al] using this

end Chain

end GlobalTheory.LeafTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MainTermImpliesRowHypothesis
section
open Formalism.L2.FormalSeriesBounds

noncomputable section

open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.MainToRows

variable {C : Type} [Field C]

theorem killCompl_subst {σ τ κ : Type} [Finite κ] (e : σ ↪ τ) (a : κ → MvPowerSeries τ C)
    (ha : ∀ k, constantCoeff (a k) = 0) (H : MvPowerSeries κ C) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  have hc : ∀ k, constantCoeff (killCompl e (a k)) = 0 := fun k => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply, ha]
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hc)]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

def eps {n0 n : ℕ} (hn : n0 ≤ n) : Fin n0 ⊕ Fin n0 ↪ Fin n0 ⊕ Fin n :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hn)

theorem kill_inl {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inl c) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = X (Sum.inl c) :=
  killCompl_X (e := eps hn) (Sum.inl c)

theorem kill_inr {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inr (Fin.castLE hn c)) : MvPowerSeries (Fin n0 ⊕ Fin n) C) =
      X (Sum.inr c) :=
  killCompl_X (e := eps hn) (Sum.inr c)

theorem kill_inr_zero {n0 n : ℕ} (hn : n0 ≤ n) (b : Fin n) (hb : b ∉ Set.range (Fin.castLE hn)) :
    killCompl (eps hn) (X (Sum.inr b) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = 0 := by
  refine killCompl_X_eq_zero ?_
  rintro ⟨x | x, hx⟩
  · simp [eps] at hx
  · exact hb ⟨x, by simpa [eps] using hx⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → M)
    (hf : ∀ b, b ∉ Set.range (Fin.castLE hn) → f b = 0) :
    ∑ b, f b = ∑ b : Fin n0, f (Fin.castLE hn b) :=
  (Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ f hf (fun _ => rfl)).symm

theorem kill_hPullW {I : Fin 2 → Type} [∀ g, Fintype (I g)] {n0 n : ℕ} (hn : n0 ≤ n)
    (H : MvPowerSeries (WV I) C) (e : Fin n0 → WV I → C) (e' : Fin n → WV I → C) :
    killCompl (eps hn) (hPullW H e e') = hPullW H e (fun b => e' (Fin.castLE hn b)) := by
  unfold hPullW
  rw [killCompl_subst _ _ (fun k => by simp)]
  congr 1
  funext w
  rw [map_add, map_sum, map_sum, sum_castLE hn (fun b => killCompl (eps hn) (e' b w • X (Sum.inr b)))]
  · simp only [map_smul, kill_inl, kill_inr]
  · intro b hb
    rw [map_smul, kill_inr_zero hn b hb, smul_zero]

theorem kill_mainM (V : VF C) (i : ℕ) {n0 n : ℕ} (hn : n0 ≤ n) (Φ : Fin n → Fin n0 → C) :
    killCompl (eps hn) (mainM V i Φ) = mainM V i (fun b c => Φ (Fin.castLE hn b) c) := by
  unfold mainM
  rw [map_smul, map_sum, sum_castLE hn]
  · simp only [map_sum, map_smul, map_mul, map_pow, kill_inl, kill_inr]
  · intro b hb
    simp only [map_sum, map_smul, map_mul, kill_inr_zero hn b hb, mul_zero, smul_zero,
      Finset.sum_const_zero]

theorem sum_inl_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inl c) = ∑ c, μ (Sum.inl c) :=
  Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inl c)

theorem sum_inr_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = ∑ c, μ (Sum.inr c) := by
  rw [sum_castLE hn]
  · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inr c)
  · intro b hb
    refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨x | x, hx⟩
    · simp [eps] at hx
    · exact hb ⟨x, by simpa [eps] using hx⟩

def rowE {n0 : ℕ} (ρ : Fin n0) : Fin n0 ⊕ Fin n0 ↪ PVar n0 :=
  Function.Embedding.sumMap (Function.Embedding.sectR ρ (Fin n0)) (Function.Embedding.sectR ρ (Fin n0))

theorem hRows_eq (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    hRows n0 H = ∑ ρ : Fin n0, rename (rowE ρ) H := by
  unfold hRows
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [rename_eq_subst]
  congr 1
  funext x
  rcases x with x | x <;> rfl

theorem coeff_row {n0 : ℕ} (ρ : Fin n0) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) (m : PVar n0 →₀ ℕ) :
    coeff m (rename (rowE ρ) H) = 0 ∨ ∃ μ : Fin n0 ⊕ Fin n0 →₀ ℕ,
      coeff m (rename (rowE ρ) H) = coeff μ H ∧ degL m = ∑ c, μ (Sum.inl c) ∧
        degR m = ∑ c, μ (Sum.inr c) ∧ ∀ x ∈ m.support, rowOf x = ρ := by
  by_cases h : m ∈ Set.range (Finsupp.mapDomain (rowE ρ))
  · obtain ⟨μ, rfl⟩ := h
    rw [← Finsupp.embDomain_eq_mapDomain]
    have hout : ∀ x : PVar n0, rowOf x ≠ ρ → Finsupp.embDomain (rowE ρ) μ x = 0 := by
      intro x hx
      refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
      rintro ⟨y | y, rfl⟩ <;> exact hx rfl
    refine Or.inr ⟨μ, coeff_embDomain_rename _ _ _, ?_, ?_, ?_⟩
    · unfold degL
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inl c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · unfold degR
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inr c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · intro x hx
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hx) (hout x hne)
  · exact Or.inl (coeff_rename_eq_zero _ _ h)

theorem le_add_iff (w r : ℝ) (t : WithTop ℝ) :
    (w : WithTop ℝ) ≤ t + (r : WithTop ℝ) ↔ ((w - r : ℝ) : WithTop ℝ) ≤ t := by
  induction t with
  | top => simp
  | coe t => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

theorem rows_main (V : VF C) (i n0 : ℕ) :
    ∑ ρ : Fin n0, rename (rowE ρ) (mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)) =
      -((V.l : C) ^ (expE V.l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
        (X (Sum.inl (b, c)) ^ (V.l ^ i) * X (Sum.inr (b, c)) : MvPowerSeries (PVar n0) C)) := by
  unfold mainM
  refine Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) (Finset.smul_sum).symm
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul, map_sum,
    map_mul, map_pow, rename_X, neg_smul, one_smul, map_neg, Finset.sum_neg_distrib, smul_neg]
  rfl

end GlobalTheory.MainToRows

open GlobalTheory.MainToRows in

theorem GlobalTheory.mainTerm_to_rowHypothesis :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
      [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  intro C _ V d _ I J _ _ X g a i U U' n0 e v' Φ hM hn
  obtain ⟨-, -, -, -, -, hΦ, hwt, hax⟩ := hM
  set H := X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)
    with hH
  have hkill : H = killCompl (eps hn) (X.hM g a i e v' - mainM V i Φ) := by
    rw [hH, map_sub, kill_mainM]
    unfold RowData.hGood RowData.hM
    rw [kill_hPullW]
    congr 2
    funext b c
    rw [hΦ _ c (by simp)]
    simp [Fin.ext_iff]
  have hco : ∀ μ, coeff μ H = coeff (Finsupp.embDomain (eps hn) μ) (X.hM g a i e v' - mainM V i Φ) :=
    fun μ => by rw [hkill, coeff_killCompl]
  have h1 : X.restrictedCurveSystemSeries g a i hn e v' = ∑ ρ : Fin n0, rename (rowE ρ) H := hRows_eq _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, hRows_eq, hP, ← rows_main, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← map_add, hH, add_sub_cancel]
  · intro m
    rw [h1, le_add_iff, map_sum]
    refine V.v.map_le_sum fun ρ _ => ?_
    rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
    · rw [h, V.v.map_zero]; exact le_top
    · rw [h, hco, ← le_add_iff, hL, hR, ← sum_inl_eps hn, ← sum_inr_eps hn]
      exact hwt _
  · intro m hm
    rw [h1, map_sum] at hm
    obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rcases coeff_row ρ H m with h | ⟨μ, h, -, hR, -⟩
    · exact absurd h hρ
    · rw [h, hco] at hρ
      by_contra hlt
      refine hρ (hax _ ?_)
      have h0 : ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = 0 := by
        rw [sum_inr_eps, ← hR]; omega
      exact fun b => (Finset.sum_eq_zero_iff.1 h0) b (Finset.mem_univ b)
  · intro hi hP
    subst hi
    refine ⟨fun ρ => rename (rowE ρ) H, h1, fun ρ m hm => ?_, fun ρ m hl hr => ?_⟩
    · rcases coeff_row ρ H m with h | ⟨μ, -, -, -, h⟩
      · exact absurd h hm
      · exact h
    · rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
      · rw [h, V.v.map_zero]; exact le_top
      · rw [h, hco]
        exact hP _ (by rw [sum_inl_eps, ← hL]; exact hl) (by rw [sum_inr_eps, ← hR]; exact hr)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem sumMvList_eq_ptSumL {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {τ : Type} (l : List (Fin d → MvPowerSeries τ C)) :
    sumMvList G l = ptSumL G l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [sumMvList, ptSumL, ih]; rfl

theorem basisMap_eq_ptBasisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) : basisMap G γ = ptBasisMap G γ :=
  sumMvList_eq_ptSumL G _

theorem typicalBasis_coordinates : TypicalCurveEigenspace → TypicalCurveBasisExists := by
  intro h2 C _ _ _ v p hp hvp d h hh ty G μ
  refine ⟨?_, fun γ hγ => ?_⟩
  · have key : ∀ a : Fin d, ∃ γ : Fin d → PowerSeries C,
        IsCurve v γ ∧ G.IsOfType p ty (ty a) γ ∧ tangent γ = Pi.single a 1 := by
      intro a
      refine h2 C v p hp hvp d h hh ty G μ (ty a) (Pi.single a 1) (fun b => ?_) (fun b hb => ?_)
      · unfold IsIntV
        by_cases e : b = a
        · subst e; simp
        · simp [Pi.single_eq_of_ne e]
      · exact Pi.single_eq_of_ne (fun e => hb (by rw [e])) _
    choose γ h1 h2' h3 using key
    refine ⟨γ, h1, h2', ?_⟩
    have : (Matrix.of fun a b => tangent (γ a) b) = (1 : Matrix (Fin d) (Fin d) C) := by
      ext a b
      simp [h3, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, v.map_one]
  · rw [basisMap_eq_ptBasisMap]
    exact ⟨ptBasisMap_inv G hγ.1 hγ.2.2, ptBasisMap_lg G hγ.1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalCurvesOfTypeOfTypicalTangents
section
namespace GlobalTheory.TypicalCurve

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem pow_pow_mod {p h : ℕ} (hp : 0 < p) {ζ : C} (hζ : ζ ^ (p ^ h - 1) = 1) (e : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ (e % h)) := by
  have h1 : ∀ y : C, y ^ (p ^ h - 1) = 1 → y ^ (p ^ h) = y := by
    intro y hy
    have : p ^ h = (p ^ h - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [this, pow_succ, hy, one_mul]
  have h2 : ∀ k : ℕ, ζ ^ ((p ^ h) ^ k) = ζ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, h1 ζ hζ]
  conv_lhs => rw [← Nat.div_add_mod e h, pow_add, pow_mul, pow_mul, h2]

theorem pow_pow_eq_iff {p h : ℕ} (hp : 1 < p) (hh : 0 < h) {ζ : C}
    (hζ : IsPrimitiveRoot ζ (p ^ h - 1)) (e e' : ℕ) :
    ζ ^ (p ^ e) = ζ ^ (p ^ e') ↔ (e : ZMod h) = (e' : ZMod h) := by
  have hp0 : 0 < p := by omega
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  rw [ZMod.natCast_eq_natCast_iff', pow_pow_mod hp0 hζ.pow_eq_one e,
    pow_pow_mod hp0 hζ.pow_eq_one e']
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  have key : ∀ a, a < h → p ^ a - 1 < p ^ h - 1 := fun a ha => by
    have h1 := Nat.pow_lt_pow_right hp ha
    have h2 := Nat.one_le_pow a p hp0
    omega
  have s : ∀ a, ζ ^ (p ^ a) = ζ ^ (p ^ a - 1) * ζ := fun a => by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp0)]
  rw [s, s] at H
  have H2 := hζ.pow_inj (key _ (Nat.mod_lt _ hh)) (key _ (Nat.mod_lt _ hh))
    (mul_right_cancel₀ hζ0 H)
  have h1 := Nat.one_le_pow (e % h) p hp0
  have h2 := Nat.one_le_pow (e' % h) p hp0
  exact Nat.pow_right_injective hp (show p ^ (e % h) = p ^ (e' % h) by omega)

theorem isCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n, IsCurve v (G.nsmulF n ga)
  | 0 => isCurve_zero
  | n + 1 => isCurve_add G h (isCurve_nsmulF G h n)

theorem lgCurve_nsmulF (G : LogFGL v d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    ∀ n a, G.lgCurve (G.nsmulF n ga) a = (n : C) • G.lgCurve ga a
  | 0, a => by
    rw [Nat.cast_zero, zero_smul]; exact lgCurve_zero G a
  | n + 1, a => by
    rw [LogFGL.nsmulF, lgCurve_add G (fun b => (h b).1) (fun b => (isCurve_nsmulF G h n b).1),
      lgCurve_nsmulF G h n a, Nat.cast_succ, add_smul, one_smul, add_comm]

def muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty) (z : C)
    (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (μ.mul z a)

theorem isCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    IsCurve v (muCurve μ z ga) := fun a =>
  ⟨constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun b => (hga b).1)
      (fun b => (hga b).1) (μ.mul_const z a),
    psIsInt_iff.2 (mvIsInt_subst v (μ.mul_int z hz a) (fun b => psIsInt_iff.1 (hga b).2)
      (fun b => (hga b).1))⟩

theorem lgCurve_muCurve {G : LogFGL v d} {p h : ℕ} {ty : Fin d → ZMod h} (μ : MuAction G p h ty)
    {z : C} (hz : z ^ (p ^ h - 1) = 1) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga)
    (a : Fin d) :
    G.lgCurve (muCurve μ z ga) a = (z ^ (p ^ (ty a).val)) • G.lgCurve ga a := by
  have hs : HasSubst ga := hasSubst_of_constantCoeff_zero fun b => (hga b).1
  have hm : HasSubst (μ.mul z) := hasSubst_of_constantCoeff_zero (μ.mul_const z)
  have e := subst_comp_subst_apply hm hs (G.lg a)
  rw [μ.lg_mul z hz a, subst_smul hs] at e
  exact e.symm

theorem typicalCurves_of_type_of_typical_tangents :
  (∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d : ℕ) (G : LogFGL v d) (u : Fin d → C), (∀ a, IsIntV v (u a)) → ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsPTypical p γ ∧ tangent γ = u) →
  TypicalCurveEigenspace := by
  intro H C _ _ _ v p hp hv d h hh ty G μ i u hu hui
  obtain ⟨γ, hγ, hγt, hγu⟩ := H C v p hp hv d G u hu
  have : NeZero h := ⟨hh.ne'⟩
  have hN : p ^ h - 1 ≠ 0 := by
    have := Nat.one_lt_pow hh.ne' hp.one_lt
    omega
  have hpN : ¬ p ∣ p ^ h - 1 := by
    intro hd
    have h1 : p ∣ p ^ h := dvd_pow_self p hh.ne'
    have h2 := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN0 : ((p ^ h - 1 : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 hN
  have : NeZero ((p ^ h - 1 : ℕ) : C) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C (p ^ h - 1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have hpow : ∀ y : C, y ^ (p ^ h - 1) = 1 → ∀ j : ℕ, (y ^ j) ^ (p ^ h - 1) = 1 := fun y hy j => by
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hζi : ζ⁻¹ ^ (p ^ h - 1) = 1 := by rw [inv_pow, hζ.pow_eq_one, inv_one]
  let x : ℕ → C := fun j => (ζ⁻¹ ^ (p ^ i.val)) ^ j
  have hx : ∀ j, IsIntV v (x j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one hN (hpow _ (hpow _ hζi _) j)]
  let g : Fin (p ^ h - 1) → Fin d → PowerSeries C := fun j =>
    muCurve μ (ζ ^ (j : ℕ)) (rescaleCurve (x j) γ)
  have hg : ∀ j, IsCurve v (g j) := fun j =>
    isCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ)
  obtain ⟨ε, ⟨hε, hεe⟩, -⟩ := pt1 C v p hp hv d G (p ^ h - 1) hpN (G.sumF g) (isCurve_sumF G g hg)
  have hlg : ∀ a m, ((p ^ h - 1 : ℕ) : C) * PowerSeries.coeff m (G.lgCurve ε a) =
      (∑ j ∈ Finset.range (p ^ h - 1), (ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ i.val * m)) ^ j) *
        PowerSeries.coeff m (G.lgCurve γ a) := by
    intro a m
    have e := congrArg (PowerSeries.coeff m) (lgCurve_nsmulF G hε (p ^ h - 1) a)
    rw [hεe, lgCurve_sumF G g hg, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at e
    rw [← e, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g]
    rw [lgCurve_muCurve μ (hpow _ hζ.pow_eq_one _) (isCurve_rescale (hx j) hγ),
      lgCurve_rescale G _ (fun b => (hγ b).1), PowerSeries.coeff_smul, smul_eq_mul,
      PowerSeries.coeff_rescale]
    simp only [x]
    ring
  have hlc : ∀ a n, G.lc p ε n a = if ty a = i + (n : ZMod h) then G.lc p γ n a else 0 := by
    intro a n
    have e := hlg a (p ^ n)
    rw [← pow_add] at e
    have hiff := pow_pow_eq_iff hp.one_lt hh hζ (ty a).val (i.val + n)
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hiff
    have hne : ζ ^ (p ^ (i.val + n)) ≠ 0 := pow_ne_zero _ hζ0
    split_ifs with hc
    · rw [hiff.2 hc, inv_pow, mul_inv_cancel₀ hne] at e
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at e
      exact mul_left_cancel₀ hN0 e
    · have h1 : ζ ^ (p ^ (ty a).val) * ζ⁻¹ ^ (p ^ (i.val + n)) ≠ 1 := by
        intro h1
        rw [inv_pow, mul_inv_eq_one₀ hne] at h1
        exact hc (hiff.1 h1)
      rw [geom_sum_eq h1, mul_pow, hpow _ hζ.pow_eq_one, hpow _ hζi, mul_one, sub_self, zero_div,
        zero_mul] at e
      exact (mul_eq_zero.1 e).resolve_left hN0
  refine ⟨ε, hε, ⟨fun a m hm => ?_, fun n a ha => ?_⟩, ?_⟩
  · have e := hlg a m
    rw [hγt a m hm, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hN0
  · rw [hlc, if_neg ha]
  · rw [tangent_eq_lc_zero G p (fun b => (hε b).1)]
    funext a
    rw [hlc, ← tangent_eq_lc_zero G p (fun b => (hγ b).1), hγu, Nat.cast_zero, add_zero]
    split_ifs with hc
    · rfl
    · exact (hui a hc).symm

end

end GlobalTheory.TypicalCurve
end

