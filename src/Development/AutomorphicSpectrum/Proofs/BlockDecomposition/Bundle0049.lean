import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RemoveNthSuccVecCons
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KDelFormula

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem removeNth_succ_vecCons {n : ℕ} (x : P) (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    t.succ.removeNth (Matrix.vecCons x Y) = Matrix.vecCons x (t.removeNth Y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem map_vecCons_removeNth {n : ℕ} (η : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (x : P)
    (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    η (Matrix.vecCons x (t.removeNth Y)) = (-1 : ℤ) ^ (t : ℕ) • η (Function.update Y t x) := by
  have hW : Matrix.vecCons x (t.removeNth Y) = Function.update Y t x ∘ t.cycleRange.symm := by
    rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm]
    simp only [Function.update_self, Fin.removeNth_update]
    rfl
  rw [hW, η.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def]
  push_cast
  rfl

theorem kD_vecCons (T : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (x : P)
    (Y : Fin q → P) :
    kD T η (Matrix.vecCons x Y) =
      T x (η Y) - ∑ t, T (Y t) (η (Function.update Y t x)) := by
  have hs : ∀ t : ℕ, ((-1 : ℤ) ^ (t + 1) * (-1) ^ t) = -1 := fun t => by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨t, by ring⟩
  cases q with
  | zero =>
    rw [kD_apply, Fin.sum_univ_succ]
    simp [Fin.removeNth_zero]
  | succ n =>
    rw [kD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp [Fin.removeNth_zero]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.val_succ, Matrix.cons_val_succ, removeNth_succ_vecCons, map_vecCons_removeNth,
        map_zsmul, smul_smul, hs, neg_one_zsmul]

theorem kDel_kD {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ}
    (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P) :
    kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) -
      ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by
  rw [kDel_apply]
  simp only [kD_vecCons, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.KDelFormula
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
section
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) :
    R ⧸ lev ϖ k →+* R ⧸ lev ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((Ideal.Quotient.mk (lev ϖ k)).comp σ) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

@[simp] theorem barσ_mk {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (a : R) :
    barσ σ ϖ h k (Ideal.Quotient.mk (lev ϖ k) a) = Ideal.Quotient.mk (lev ϖ k) (σ a) := rfl

structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)

theorem resAlg_split_two :
    ResAlg (ZMod 2 × ZMod 2) (RingEquiv.prodComm : ZMod 2 × ZMod 2 ≃+* ZMod 2 × ZMod 2).toRingHom 2 1 := by
  refine ⟨fun a => ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · first
      | rfl
      | simp
      | (ext <;> rfl)
  · rintro ⟨x, y⟩ h hne
    fin_cases x <;> fin_cases y
    all_goals first
      | exact (hne rfl).elim
      | exact absurd h (by decide)
      | exact isUnit_one
      | (convert isUnit_one using 1; decide)
  · refine ⟨(1, 0), ?_, ?_⟩
    · convert isUnit_one using 1
      decide
    · rintro ⟨p, r⟩
      refine ⟨(r, r), (p - r, p - r), rfl, rfl, ?_⟩
      ext <;> first | simp | (simp; ring) | ring
  · first
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | decide
  · right
    refine ⟨rfl, fun hF => ?_⟩
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := ((1, 0) : ZMod 2 × ZMod 2)) (by decide)
    have h2 := congrArg Prod.snd hb
    simp at h2

variable {E : Type} [CommRing E] {τ : E →+* E}

structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

variable {V : Type} [AddCommGroup V] [Module E V]

namespace HermSp

variable (B : HermSp E τ V)

theorem zero_left (w : V) : B.h 0 w = 0 := by
  have h0 := B.smul_left 0 0 w
  rwa [zero_smul, zero_mul] at h0

theorem zero_right (v : V) : B.h v 0 = 0 := by
  rw [B.symm 0 v, B.zero_left, map_zero]

theorem add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add, ← B.symm, ← B.symm]

theorem smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]

theorem self_fixed (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by
  exact (B.symm v v).symm

def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [B.smul_left, hx, mul_zero]

theorem mem_perp {w v : V} : v ∈ B.perp w ↔ B.h v w = 0 := by
  exact Iff.rfl

noncomputable def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)

theorem coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hu : ((hw.unit⁻¹ : Eˣ) : E) * B.h w w = 1 := by
    have h1 := hw.unit.inv_mul
    simpa using h1
  have hc : B.coef hw z * B.h w w = B.h z w := by
    unfold coef
    rw [mul_assoc, hu, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by
    rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e

noncomputable def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := by simp [B.add_left]
  smul_left a v x := by simp [B.smul_left]
  symm v x := B.symm _ _
  nondeg := by
    intro v hv
    apply Subtype.ext
    apply B.nondeg
    intro z
    have h1 := hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩
    have hz : z = (z - B.coef hw z • w) + B.coef hw z • w := by abel
    have h0 : B.h (v : V) w = 0 := v.2
    rw [hz, B.add_right, B.smul_right, h0, mul_zero, add_zero]
    exact h1

@[simp] theorem perpForm_h {w : V} (hw : IsUnit (B.h w w)) (a b : B.perp w) :
    (B.perpForm hw).h a b = B.h a b := rfl

noncomputable def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := by
    rintro ⟨a, v⟩
    have h0 : B.h (v : V) w = 0 := v.2
    have hc : B.coef hw (a • w + (v : V)) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, h0, add_zero, mul_assoc]
      have : B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 := by
        have := hw.unit.mul_inv
        simpa using this
      rw [this, mul_one]
    ext
    · exact hc
    · simp [hc]
  right_inv := by
    intro z
    simp

theorem perpEquiv_apply {w : V} (hw : IsUnit (B.h w w)) (p : E × B.perp w) :
    B.perpEquiv hw p = p.1 • w + (p.2 : V) := rfl

theorem norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by
  have hwv : B.h w v = 0 := by rw [B.symm v w, hv, map_zero]
  simp only [B.add_left, B.smul_left, B.add_right, B.smul_right, hv, hwv, mul_zero, add_zero]
  ring

end HermSp

def HermSp.self (hτ : ∀ a, τ (τ a) = a) : HermSp E τ E where
  h a b := a * τ b
  add_left u v w := by ring
  smul_left a v w := by simp [mul_assoc]
  symm v w := by simp [hτ, mul_comm]
  nondeg v hv := by simpa using hv 1

def HermSp.ofMatrix (hτ : ∀ a, τ (τ a) = a) {m : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) : HermSp E τ (Fin m → E) where
  h v w := dotProduct (fun i => τ (w i)) (S.mulVec v)
  add_left u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  smul_left a v w := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  symm v w := by
    have hij : ∀ i j, τ (S j i) = S i j := fun i j => by
      have := congrFun (congrFun hS i) j
      simpa [cT] using this
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, hij]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg v hv := by
    have h0 : S.mulVec v = 0 := by
      funext i
      have := hv (Pi.single i 1)
      simpa [dotProduct, Pi.single_apply] using this
    have := congrArg (S⁻¹).mulVec h0
    have hu : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hd
    simpa [Matrix.mulVec_mulVec, hu] using this

theorem gram_apply (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by
  show (cT τ x * S * x) i j = dotProduct (fun a => τ (x a i)) (S.mulVec (fun a => x a j))
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelRows

open PositivityTheory.Rg.BcB.E1

theorem rowInt_of_kerBasic : KerBasic → RowInt := by
  intro hK X φ hφ
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hc : Continuous φ := hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hc' : Continuous fun z : X.G => φ z⁻¹ := hc.comp continuous_inv
  have hcs' : HasCompactSupport fun z : X.G => φ z⁻¹ :=
    hcs.comp_homeomorph (Homeomorph.inv X.G)
  have hfin1 : ∫⁻ z, ‖φ z‖ₑ ∂X.μ ≠ ⊤ :=
    (hc.integrable_of_hasCompactSupport (μ := X.μ) hcs).2.ne
  have hfin2 : ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ ≠ ⊤ :=
    (hc'.integrable_of_hasCompactSupport (μ := X.μ) hcs').2.ne
  have hb := (hK X φ hφ).2.2.2.2.2
  have hν : X.ν = X.μ.restrict X.F := rfl
  refine ⟨∫⁻ z, ‖φ z‖ₑ ∂X.μ + ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ, ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, ?_, ?_⟩
  · intro x
    calc ∫⁻ y, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ y, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν := lintegral_mono (hb x)
      _ = ∑' γ : X.Γ, ∫⁻ y in X.F, ‖φ (x⁻¹ * (γ • y))‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          · refine tsum_congr fun γ => lintegral_congr fun y => ?_
            rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]
          · intro γ
            exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun y => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ y, ‖φ y‖ₑ ∂X.μ := lintegral_mul_left_eq_self (fun y => ‖φ y‖ₑ) x⁻¹
      _ ≤ _ := le_self_add
  · intro y
    calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ x, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν :=
          lintegral_mono fun x => hb x y
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          intro γ
          exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ ((γ • x)⁻¹ * y)‖ₑ ∂X.μ := by
          rw [← (Equiv.inv X.Γ).tsum_eq]
          refine tsum_congr fun γ => lintegral_congr fun x => ?_
          simp [Subgroup.smul_def, smul_eq_mul, mul_inv_rev]
      _ = ∫⁻ x, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun x => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ := by
          rw [← lintegral_mul_left_eq_self (fun x => ‖φ (x⁻¹ * y)‖ₑ) y]
          refine lintegral_congr fun z => ?_
          simp [mul_inv_rev]
      _ ≤ _ := le_add_self

end GlobalTheory.CompanionTheory.KernelRows
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Schur

open PositivityTheory.Rg.BcB.E1

variable {α : Type} [MeasurableSpace α] {ν : Measure α}

theorem eLpNorm_two_sq (f : α → ℂ) : eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := 2) (by norm_num)
  simpa [ENNReal.rpow_ofNat] using h

theorem schur_memLp (hS : SchurL) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hA : A ≠ ⊤)
    (hr : ∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) (hc : ∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A)
    (g : α → ℂ) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, k x y * g y ∂ν) 2 ν ∧
      eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun y => k x y * g y) ν := by
  have hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν := hg.1.enorm
  have key := hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc
  have hgfin : eLpNorm g 2 ν ≠ ⊤ := hg.2.ne
  have hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2 := (eLpNorm_two_sq g).symm
  have hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2 := by
    rw [mul_pow, ← hsq]; exact key
  have hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)
  have hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν) :=
    (hk.stronglyMeasurable.aestronglyMeasurable).mul hg.1.comp_snd
  have hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν :=
    hprod.integral_prod_right'
  have hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν := by
    have : AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν) := by
      simpa [enorm_mul] using hprod.enorm
    exact this.lintegral_prod_right'
  have hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν := by
    refine (ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_
    rw [eLpNorm_two_sq]
    refine le_trans (lintegral_mono fun x => ?_) hbound
    refine pow_le_pow_left' ?_ 2
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp [enorm_mul]
  refine ⟨⟨hSm, lt_of_le_of_lt hle (ENNReal.mul_ne_top hA hgfin).lt_top⟩, hle, ?_⟩
  have hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤ :=
    ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)
  filter_upwards [hae] with x hx
  have hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hcon => ?_
    simp [hcon] at hx
  have hkx : Measurable (k x) := hk.of_uncurry_left
  refine ⟨hkx.aestronglyMeasurable.mul hg.1, ?_⟩
  simpa [HasFiniteIntegral, enorm_mul] using hxf

theorem schurOp_of_schurL (hS : SchurL) : SchurOp := by
  intro α _ ν _ k A hk hA hr hc
  have H := fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (H f).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        have h1 := (H (f + g)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h3 := (H g).1.coeFn_toLp
        have h4 := Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)
        filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2
        rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have h1 := (H (c • f)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h4 := Lp.coeFn_smul c ((H f).1.toLp _)
        filter_upwards [h1, h2, h4] with x e1 e2 e4
        rw [e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩
  intro f
  change ‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).2.ne) (H f).2.1

end GlobalTheory.CompanionTheory.Schur

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScoreTZeroEqLevelCount
section
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem score_tZero_level : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n,
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ)
      - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  intro n lev hm a
  have hlt : ∀ b, lev a < lev b → a < b := fun b h => by
    by_contra hc
    exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
  have h1 : ((tZero lev).filter fun p => p.1 = a).card
      = (univ.filter fun b => lev a < lev b).card := by
    symm
    refine Finset.card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    · intro b hb
      have hb' : lev a < lev b := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb', hlt b hb']
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨x, b⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨_, h⟩, rfl⟩ := hp
      exact ⟨b, by simp [h], rfl⟩
  have h2 : (((prs n) \ tZero lev).filter fun p => p.2 = a).card
      = (univ.filter fun b => b < a ∧ lev b = lev a).card := by
    symm
    refine Finset.card_bij (fun b _ => (b, a)) ?_ ?_ ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb'.1, hb'.2]
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).1
    · rintro ⟨b, x⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and,
        not_lt] at hp
      obtain ⟨⟨h, h'⟩, rfl⟩ := hp
      exact ⟨b, by simp [h, le_antisymm (hm h.le) (h' h)], rfl⟩
  have h3 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    simpa [Finset.filter_gt_eq_Iio] using Fin.card_Iio a
  have h4 : (univ.filter fun b => lev b < lev a).card
      + (univ.filter fun b => b < a ∧ lev b = lev a).card = (a : ℕ) := by
    rw [← h3, ← Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a)
      (fun b => lev b < lev a)]
    congr 2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, h⟩
        by_contra hc
        exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
      · exact fun h => h.2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, fun hc => absurd h' (ne_of_lt hc)⟩
      · rintro ⟨h, h'⟩
        exact ⟨h, le_antisymm (hm h.le) (not_lt.mp h')⟩
  unfold score
  rw [h1, h2]
  have h4' : ((univ.filter fun b => lev b < lev a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ lev b = lev a).card : ℤ) = ((a : ℕ) : ℤ) := by
    exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.CoefId
end

