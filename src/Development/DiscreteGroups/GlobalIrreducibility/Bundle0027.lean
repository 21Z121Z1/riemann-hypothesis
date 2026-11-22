import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroInertiaBig : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (t : G E Ω), t ∈ Ine (F := E) A →
    Formalism.L2.NT.TameCoupled A κ t L.gen →
    ∀ n : ℕ, (n = 1 ∨ 16 * n ^ 2 < g) → ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)), (cls σ).IsCusp →
    ∀ (τ : FDRep ℂ (Gn g n)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    (rc (cls σ)).inePol t = GlobalTheory.SerSys.TameGen.liftPoly L.teich P

theorem depthZeroInertiaBig_of (H : GlobalTheory.Published.DepthZeroInertia) : DepthZeroInertiaBig :=
  fun E Ω _ _ _ _ _ _ g _ A w h rc hrc i hi κ L t ht hT n _ => H E Ω g A w h rc hrc i hi κ L t ht hT n

theorem big_of_le_nV (D : Formalism.BasicNotions.D7) (k : Fin 2) {n : ℕ} (hn : n ≤ D.R.nV) : 16 * n ^ 2 < D.host.g k := by
  have hg : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  have hq := D.host.qd_big
  have ht : 0 < D.R.t := D.R.t_odd.pos
  have hr : 1 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; have := D.R.two_le_m; omega
  have h2 : 2 ≤ D.host.g k := (D.host.g_prime k).two_le
  have hQ0 : 0 < D.host.QS := by
    rcases Nat.eq_zero_or_pos D.host.QS with h | h
    · rw [h] at hg; simp at hg; omega
    · exact h
  have h16 : 16 ≤ D.host.QS :=
    Nat.le_of_dvd hQ0 ((pow_dvd_pow 2 (m := 4) (by have := D.host.two_le_e; omega)).trans D.host.tower_dvd)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have := Nat.mod_add_div (D.host.g k) (D.host.QS * D.host.q * D.host.d)
    rw [hg] at this
    exact ⟨D.host.g k / (D.host.QS * D.host.q * D.host.d), Nat.sub_eq_of_eq_add' this.symm⟩
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hn' : n ≤ 4 * D.R.t * D.R.r + 1 := by
    unfold Formalism.BasicNotions.Ranks.nV at hn
    nlinarith
  have hq1 : n ≤ D.host.q := by omega
  have hd1 : n ≤ D.host.d := by omega
  have h5 : n * n ≤ D.host.q * D.host.d := Nat.mul_le_mul hq1 hd1
  have h6 : 16 * (D.host.q * D.host.d) ≤ D.host.QS * D.host.q * D.host.d := by
    rw [mul_assoc D.host.QS]
    exact Nat.mul_le_mul_right _ h16
  rw [sq]
  omega

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix

namespace DiscreteGroups.sglob.DzFe

theorem cycM_mul_tr (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨l, rfl⟩ := (finRotate n).surjective i
  rw [Finset.sum_eq_single l]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
  · intro b _ hb
    have : ¬ finRotate n l = finRotate n b := fun h => hb ((finRotate n).injective h).symm
    rw [Matrix.of_apply, Matrix.of_apply, if_neg this, zero_mul]
  · simp

theorem tr_mul_cycM (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (finRotate n i)]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h ((finRotate n).injective e))]
  · intro b _ hb
    rw [Matrix.of_apply, Matrix.of_apply, if_neg (Ne.symm hb), zero_mul]
  · simp

def cyc (g n : ℕ) : GL (Fin n) (ZMod g) :=
  ⟨Matrix.of fun i k => if i = finRotate n k then 1 else 0, Matrix.of fun i k => if finRotate n i = k then 1 else 0,
    cycM_mul_tr g n, tr_mul_cycM g n⟩

def IsColFix {g n : ℕ} (j : ℕ) (h : GL (Fin n) (ZMod g)) : Prop :=
  (∀ i k : Fin n, (k : ℕ) ≠ 0 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = if i = k then 1 else 0) ∧
    ∀ i k : Fin n, (k : ℕ) = 0 → j < (i : ℕ) → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = 0

def IsRowFix {g n : ℕ} (j : ℕ) (h : GL (Fin n) (ZMod g)) : Prop :=
  (∀ i k : Fin n, (i : ℕ) ≠ 0 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = if i = k then 1 else 0) ∧
    ∀ i k : Fin n, (i : ℕ) = 0 → 0 < (k : ℕ) → (k : ℕ) ≤ j + 1 → (h : Matrix (Fin n) (Fin n) (ZMod g)) i k = 0

def FunctionalEquationAtIndex : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (m : ℕ) (ψ₀ : AddChar (ZMod g) Circle), ψ₀ ≠ 1 →
    ∀ τ : FDRep ℂ (Gn g (m + 1)), IsCusp τ.character → ∀ γ : ℂ,
    (∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v) →
    ∀ l : Module.Dual ℂ τ, IsFunctional ψ₀ τ.ρ l →
    ∀ j : ℕ, j < m → ∀ v : τ, (∀ h, IsColFix j h → τ.ρ h v = v) → (∀ h, IsRowFix j h → τ.ρ h v = v) →
      γ * l v = (g : ℂ) ^ ((m + 1) * m / 2 + m - j) * l (τ.ρ (cyc g (m + 1))⁻¹ v)

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeSv
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def sv (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1))) (x : Mt g (m + 1)) (v : τ) : τ :=
  ∑ y : Gn g (m + 1), (ψ₀ (trace (x * (y : Mt g (m + 1)))) : ℂ) • τ.ρ y⁻¹ v

def Hm (b : Fin (m + 1) → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if k = 0 then b i else (1 : Mt g (m + 1)) i k

def Ez : Mt g (m + 1) := Matrix.diagonal fun i : Fin (m + 1) => if i = 0 then (0 : ZMod g) else 1

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem rho_inv_mul_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ (y⁻¹ * a⁻¹) (τ.ρ a v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem rho_mul_inv_apply (y a : Gn g (m + 1)) (v : τ) : τ.ρ a (τ.ρ (a⁻¹ * y⁻¹) v) = τ.ρ y⁻¹ v := by
  rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ.ρ a), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

theorem sv_mul_right (x : Mt g (m + 1)) (a : Gn g (m + 1)) (v : τ) :
    sv ψ₀ τ (x * (a : Mt g (m + 1))) v = sv ψ₀ τ x (τ.ρ a v) := by
  unfold sv
  refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun y => ?_)
  rw [Equiv.coe_mulLeft]
  beta_reduce
  rw [Units.val_mul, ← Matrix.mul_assoc, _root_.mul_inv_rev, rho_inv_mul_apply]

theorem sv_mul_left (a : Gn g (m + 1)) (x : Mt g (m + 1)) (v : τ) :
    sv ψ₀ τ ((a : Mt g (m + 1)) * x) v = τ.ρ a (sv ψ₀ τ x v) := by
  unfold sv
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun y => ?_)
  have ht : trace ((a : Mt g (m + 1)) * x * (y : Mt g (m + 1))) =
      trace (x * ((y * a : Gn g (m + 1)) : Mt g (m + 1))) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm (x * (y : Mt g (m + 1))), ← Matrix.mul_assoc]
  rw [Equiv.coe_mulRight]
  beta_reduce
  rw [map_smul, _root_.mul_inv_rev, rho_mul_inv_apply, ht]

theorem sv_unit {γ : ℂ}
    (hγ : ∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v)
    (a : Gn g (m + 1)) (v : τ) : sv ψ₀ τ (a : Mt g (m + 1)) v = γ • τ.ρ a v := by
  have h1 : sv ψ₀ τ 1 v = γ • v := by
    unfold sv
    rw [← hγ v, finsum_eq_sum_of_fintype]
    simp only [Matrix.one_mul]
  have := sv_mul_left ψ₀ τ a 1 v
  rw [Matrix.mul_one, h1, map_smul] at this
  exact this

theorem sv_sum {ι : Type} (s : Finset ι) (x : Mt g (m + 1)) (f : ι → τ) :
    sv ψ₀ τ x (∑ i ∈ s, f i) = ∑ i ∈ s, sv ψ₀ τ x (f i) := by
  unfold sv
  simp_rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem sv_zero (x : Mt g (m + 1)) : sv ψ₀ τ x 0 = 0 := by
  simp [sv]

theorem Ez_mul_unip (u : Gn g (m + 1))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) :
    (Ez : Mt g (m + 1)) * (u : Mt g (m + 1)) = Ez := by
  ext i k
  rw [Ez, Matrix.diagonal_mul]
  by_cases hi : i = 0
  · subst hi
    simp [Matrix.diagonal_apply]
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hb : GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 k ≤ GlobalTheory.FiniteGL.twoBlocks (m + 1) 1 i := by
      simp only [GlobalTheory.FiniteGL.twoBlocks]
      split_ifs <;> omega
    have h0 := (GlobalTheory.FiniteGL.mem_unipRadical.1 hu) i k hb
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [if_neg hi, one_mul, h0, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all

theorem sv_Ez (hτ : IsCusp τ.character) (hm : 0 < m) (v : τ) : sv ψ₀ τ Ez v = 0 := by
  have h1 : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
      sv ψ₀ τ Ez v = sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := fun u => by
    rw [← sv_mul_right, Ez_mul_unip _ u.2]
  have hsum := DiscreteGroups.sglob.DzLc.sum_unip_eq_zero τ hτ (a := 1) one_pos (by omega)
  have h2 : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1)) : ℂ) •
      sv ψ₀ τ Ez v = 0 := by
    calc _ = ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          sv ψ₀ τ Ez (τ.ρ (u : Gn g (m + 1)) v) := by
          rw [← Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
      _ = sv ψ₀ τ Ez ((∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks (m + 1) 1),
          τ.ρ (u : Gn g (m + 1))) v) := by rw [LinearMap.sum_apply, sv_sum]
      _ = 0 := by rw [hsum, LinearMap.zero_apply, sv_zero]
  exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem hm_mul (b c : Fin (m + 1) → ZMod g) :
    (Hm b : Mt g (m + 1)) * Hm c = Hm (fun i => b i * c 0 + if i = 0 then 0 else c i) := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hk : k = 0
  · subst hk
    rw [Fin.sum_univ_succ]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero]
      exact Finset.sum_eq_zero (fun x _ => if_neg (Fin.succ_ne_zero x).symm)
    · simp [Hm, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj]
  · have hc : ∀ l, Hm c l k = (1 : Mt g (m + 1)) l k := fun l => by simp [Hm, hk]
    rw [Finset.sum_congr rfl (fun l _ => by rw [hc l]), ← Matrix.mul_apply, Matrix.mul_one]
    simp [Hm, hk]

theorem hm_zero : (Hm (0 : Fin (m + 1) → ZMod g) : Mt g (m + 1)) = Ez := by
  ext i k
  simp only [Hm, Ez, Matrix.of_apply, Pi.zero_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hk : k = 0
  · subst hk; split_ifs <;> simp_all
  · split_ifs <;> simp_all

theorem det_hm (b : Fin (m + 1) → ZMod g) : (Hm b : Mt g (m + 1)).det = b 0 := by
  have hl : (Hm b : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
    intro i k hik
    have hik' : i < k := hik
    have hk : k ≠ 0 := fun h => by subst h; exact absurd hik' (Fin.not_lt_zero i)
    simp [Hm, hk, Matrix.one_apply, ne_of_lt hik']
  rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_succ]
  simp [Hm, Fin.succ_ne_zero]

def hmGL (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Hm b) (by rw [det_hm]; exact hb)

theorem hmGL_val (b : Fin (m + 1) → ZMod g) (hb : b 0 ≠ 0) : ((hmGL b hb : Gn g (m + 1)) : Mt g (m + 1)) = Hm b :=
  rfl

theorem sv_singular (hτ : IsCusp τ.character) (hm : 0 < m) (u : Gn g (m + 1)) (b : Fin (m + 1) → ZMod g)
    (hb : b 0 = 0) (v : τ) : sv ψ₀ τ ((u : Mt g (m + 1)) * Hm b) v = 0 := by
  set c : Fin (m + 1) → ZMod g := fun i => (if i = 0 then 1 else 0) - b i with hc
  have hc0 : c 0 ≠ 0 := by simp [hc, hb]
  have hprod : (Hm b : Mt g (m + 1)) * ((hmGL c hc0 : Gn g (m + 1)) : Mt g (m + 1)) = Ez := by
    rw [hmGL_val, hm_mul, ← hm_zero]
    congr 1
    funext i
    by_cases hi : i = 0
    · subst hi; simp [hc, hb]
    · simp [hc, hi, hb]
  have hH : (Hm b : Mt g (m + 1)) = Ez * (((hmGL c hc0)⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [← hprod, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [sv_mul_left, hH, sv_mul_right, sv_Ez ψ₀ τ hτ hm, map_zero]

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.RankOneTopLeftZero
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
section
noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical

attribute [local instance] GlobalTheory.SerSys.Bridge.factT

theorem labParamLe_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) :
    LabParamLe D.R.nV D L rc := fun k v n hn π hπ f hf =>
  ine_eq_of_has_green_le D.R.nV (OfLabel.ofLabel (L k) (five_le D k) hG) (L k) _ _ _ (h1 k v) (h2 k) hG (h3 k v)
    (labelsCusp _ _ _) ⟨n, π⟩ hn hπ.1 hπ.2 f hf

theorem serLocLe_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (locType_of_tiesLe hL hS hC hP)

theorem serLoc_of_tiesLe (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  serLocLe_of D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)

end DiscreteGroups.sglob.DzType.Rt

end
end

