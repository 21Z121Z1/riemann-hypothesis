import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockMinorExtremal

open MvPolynomial GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor GlobalTheory.Capelli

section General

variable {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {n l : ℕ}
  (y : Matrix (Fin n) (Fin l) A)

theorem der_minor {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0)
    {m : ℕ} (row : Fin m → Fin n) (h : m ≤ l) :
    D (y.submatrix row (Fin.castLE h)).det =
      (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) • (y.submatrix row (Fin.castLE h)).det := by
  rw [← Matrix.det_transpose, derivation_det]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hD]
  by_cases hb : b.1 < m
  · rw [Finset.sum_eq_single (⟨b.1, hb⟩ : Fin m)]
    · have e : Fin.castLE h ⟨b.1, hb⟩ = b := rfl
      simp only [e, if_true]
      split_ifs with h1 h2
      · subst h1
        rw [one_smul]
        congr 1
        exact Matrix.updateRow_eq_self _ _
      · exact absurd (h1 ▸ hb) h2
      · have hlt : a.1 < b.1 := lt_of_le_of_ne hab fun e => h1 (Fin.ext e)
        have hne : (⟨a.1, hlt.trans hb⟩ : Fin m) ≠ ⟨b.1, hb⟩ := fun e => by
          rw [Fin.ext_iff] at e; simp at e; omega
        rw [zero_smul]
        refine Matrix.det_zero_of_row_eq hne ?_
        rw [Matrix.updateRow_self, Matrix.updateRow_ne hne]
        rfl
    · intro i _ hi
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hi (Fin.ext (congrArg Fin.val e :))]
    · simp
  · have h0 : (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb
      · rfl
      · rfl
    rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hb (e ▸ i.2)]

theorem sum_rows (α : Fin l → ℕ) (hα : Antitone α) (a : Fin l) :
    ∑ i : Fin l, ((α i - nextRow α i : ℕ) : ℂ) * (if a.1 < i.1 + 1 then 1 else 0) = α a := by
  let f : ℕ → ℕ := fun i => if h : i < l then α ⟨i, h⟩ else 0
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [f]
    split_ifs with h1 h2 h2
    · exact hα (by simp [Fin.le_def])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := telescope f hf a l
  have hl : f l = 0 := by simp [f]
  rw [if_pos a.2.le, hl, ← Fin.sum_univ_eq_sum_range
    (fun i => ((f i - f (i + 1) : ℕ) : ℂ) * (if a.1 < i + 1 then 1 else 0))] at h
  have e1 : ∀ i : Fin l, f i = α i := fun i => by simp [f, i.2]
  have e2 : ∀ i : Fin l, f (i + 1) = nextRow α i := fun i => rfl
  simpa only [e1, e2, Nat.cast_zero, sub_zero] using h

theorem der_minorProd (α : Fin l → ℕ) (hα : Antitone α) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0) :
    D (minorProd α y row) = (if a = b then (α a : ℂ) else 0) • minorProd α y row := by
  rw [minorProd, derivation_prod_pow D _ _ _ _ fun i => der_minor D y hab hD (row i) i.2]
  congr 1
  split_ifs with h
  · exact sum_rows α hα a
  · simp

theorem der_minorProd_zero (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    (hD : ∀ i c k, D (y (row i c) k) = 0) : D (minorProd α y row) = 0 := by
  rw [minorProd, derivation_prod_pow D _ _ _ (fun _ => 0) fun i => ?_]
  · simp
  · rw [zero_smul, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_apply, hD]

end General

theorem minorProd_ne_zero {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (hz : Function.Injective z)
    (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) (hrow : ∀ i, Function.Injective (row i)) :
    minorProd α (Matrix.of fun c k => (X (z (c, k)) : MvPolynomial σ ℂ)) row ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
    (lead_ne_zero (fun w : Fin (i.1 + 1) × Fin l => z (row i w.1, w.2))
      (hz.comp ((hrow i).prodMap Function.injective_id)) le_rfl i.2)

variable {p q n : ℕ}

def vPlus (p q n : ℕ) : Fin p × Fin n → Ln p q n 0 := fun w => (.inl w.1, .inl w.2)

def vMinus (p q n : ℕ) : Fin q × Fin n → Ln p q n 0 := fun w => (.inr w.1, .inl w.2)

theorem vPlus_inj : Function.Injective (vPlus p q n) := fun u w h => by
  simpa [vPlus, Prod.ext_iff] using h

theorem vMinus_inj : Function.Injective (vMinus p q n) := fun u w h => by
  simpa [vMinus, Prod.ext_iff] using h

theorem act_plus (i j : Fin p) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inl i) (.inl j)) P =
      rowDer (vPlus p q n) i j P + (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.1, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zA, vPlus, cPair]

theorem act_minus (i j : Fin q) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inr j) (.inr i)) P =
      -rowDer (vMinus p q n) i j P - (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.2, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zD, vMinus, cPair, eq_comm]

theorem der_plus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hp : Antitone ap) {i j : Fin p}
    (hij : i ≤ j) :
    rowDer (vPlus p q n) i j (delta hn ap am) = (if i = j then (ap i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zPlus p q n) ap hp _ hij
    fun c k => rowDer_X _ vPlus_inj i j k c, der_minorProd_zero _ (zMinus p q n) am _ fun _ c k => ?_]
  · simp [mul_comm]
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zMinus, vPlus, pderiv_X, Pi.single_apply]

theorem der_minus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hm : Antitone am) {i j : Fin q}
    (hij : i ≤ j) :
    rowDer (vMinus p q n) i j (delta hn ap am) = (if i = j then (am i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zMinus p q n) am hm _ hij
    fun c k => rowDer_X _ vMinus_inj i j k c, der_minorProd_zero _ (zPlus p q n) ap _ fun _ c k => ?_]
  · simp
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zPlus, vMinus, pderiv_X, Pi.single_apply]

theorem lower (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro a b
  rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.lowerOp]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 : pderiv ((.inr b, .inl c) : Ln p q n 0) (minorProd ap (zPlus p q n) (topRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  have h2 : pderiv ((.inl a, .inl c) : Ln p q n 0) (minorProd am (zMinus p q n) (botRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  rw [delta, Derivation.leibniz, h1, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, pderiv_swap, h2,
    map_zero, smul_zero, zero_add, smul_eq_mul]
  by_cases hc : c.1 < p
  · rw [der_minorProd_zero (pderiv ((.inr b, .inl c) : Ln p q n 0)) (zMinus p q n) am (botRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      zero_mul]
    have := i.2
    simp only [botRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · rw [der_minorProd_zero (pderiv ((.inl a, .inl c) : Ln p q n 0)) (zPlus p q n) ap (topRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      mul_zero]
    have := i.2
    have := d.2
    simp only [topRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega

theorem delta_extremal : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro p q n hn ap am hp hm
  refine ⟨mul_ne_zero ?_ ?_, ?_, fun i j h => ?_, fun i j h => ?_, lower hn ap am⟩
  · exact minorProd_ne_zero (fun w => vPlus p q n w.swap) (vPlus_inj.comp Prod.swap_injective) ap _
      fun i c d h => by simpa [topRows, Fin.ext_iff] using h
  · exact minorProd_ne_zero (fun w => vMinus p q n w.swap) (vMinus_inj.comp Prod.swap_injective) am _
      fun i c d h => by simpa [botRows, Fin.ext_iff] using h
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, sub_eq_zero]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [act_plus, der_plus hn ap am hp le_rfl]
      simp [wtExt, add_smul]
    · rw [act_minus, der_minus hn ap am hm le_rfl]
      simp [wtExt, sub_smul]
  · rw [act_plus, der_plus hn ap am hp h.le]
    simp [h.ne]
  · rw [act_minus, der_minus hn ap am hm h.le]
    simp [h.ne]

end GlobalTheory.FockMinorExtremal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor

namespace GlobalTheory.DeltaHighest

def ext0 {l : ℕ} (a : Fin l → ℕ) (i : ℕ) : ℕ := if h : i < l then a ⟨i, h⟩ else 0

theorem partitionExtendByZero_antitone {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) : Antitone (ext0 a) := by
  intro i j hij
  unfold ext0
  split_ifs with h h'
  · exact ha (by simpa using hij)
  · omega
  · omega
  · omega

def leadProd {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ) :
    MvPolynomial σ ℂ :=
  ∏ i : Fin l, lead z (n := i.1 + 1) (le_trans i.2 h) i.2 ^ (ext0 a i - ext0 a (i + 1))

theorem partition_row_difference_eq_extendByZero_difference {l : ℕ} (a : Fin l → ℕ) (i : Fin l) :
    a i - nextRow a i = ext0 a i - ext0 a (i + 1) := by
  simp [ext0, nextRow]

theorem leadProd_rows {σ : Type} {n l : ℕ} (h : l ≤ n) {a : Fin l → ℕ} (ha : Antitone a)
    (z : Fin n × Fin l → σ) (hz : Function.Injective z) :
    (∀ c d : Fin n, c < d → rowDer z c d (leadProd h a z) = 0) ∧
      ∀ c : Fin n, rowDer z c c (leadProd h a z) = (ext0 a c : ℂ) • leadProd h a z := by
  have := what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega))
    (fun i => le_trans i.2 h) (fun i => i.2)
  simpa only [rowOp_eq_rowDer, leadProd] using this

theorem leadProd_kill {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (hD : ∀ w, D (X (z w)) = 0) :
    D (leadProd h a z) = 0 := by
  rw [leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]
  · simp
  · intro i
    rw [zero_smul, lead, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self]
    exact hD _

theorem rowDer_X_other {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (c d : Fin n) (v : σ)
    (hv : ∀ w, z w ≠ v) : rowDer z c d (X v) = 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_X_of_ne (hv _).symm, mul_zero]

variable (p q n : ℕ)

def vp : Fin n × Fin p → Ln p q n 0 := fun w => (Sum.inl w.2, Sum.inl w.1)

def vm : Fin n × Fin q → Ln p q n 0 := fun w => (Sum.inr w.2, Sum.inl w.1.rev)

theorem vp_inj : Function.Injective (vp p q n) := fun u w h => by
  simpa [vp, Prod.ext_iff, and_comm] using h

theorem vm_inj : Function.Injective (vm p q n) := fun u w h => by
  simpa [vm, Prod.ext_iff, and_comm] using h

theorem top_eq (h : p ≤ n) (a : Fin p → ℕ) :
    minorProd a (zPlus p q n) (topRows h) = leadProd h a (vp p q n) := by
  unfold minorProd leadProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference]
  rfl

theorem bot_eq (h : q ≤ n) (a : Fin q → ℕ) :
    ∃ u : ℂ, minorProd a (zMinus p q n) (botRows h) = u • leadProd h a (vm p q n) := by
  refine ⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^
    (ext0 a i - ext0 a (i + 1)), ?_⟩
  unfold minorProd leadProd
  rw [Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]
  congr 2
  ext1 c b
  simp only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]
  congr 3
  apply Fin.ext
  have := i.2
  have := c.2
  simp [botRows, Fin.revPerm, Fin.val_rev]
  omega

theorem act_eq (c d : Fin n) (P : Pol p q n 0) :
    fockAct2 p q n 0 (Eab (.inl c) (.inl d)) P =
      rowDer (vp p q n) c d P - rowDer (vm p q n) d.rev c.rev P +
        (if c = d then ((p : ℂ) - q) / 2 else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer,
    ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]
  simp only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl,
    omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
  by_cases h : c = d <;> simp [h] <;> module

theorem delta_mem_hwSub : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  intro p q n hn ap am hp hm
  have h1 : p ≤ n := by omega
  have h2 : q ≤ n := by omega
  obtain ⟨u, hu⟩ := bot_eq p q n h2 am
  have e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n)) := by
    rw [delta, top_eq, hu, mul_smul_comm]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  have a1 := leadProd_rows h1 hp _ (vp_inj p q n)
  have a2 := leadProd_rows h2 hm _ (vm_inj p q n)
  have k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  have k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall,
    posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · have hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) =
        (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2 := by
      have := c.2
      have hr := c.val_rev
      simp only [wtH, ext0]
      split_ifs with h h' h'
      · omega
      all_goals simp
    rw [hw]
    generalize leadProd h1 ap (vp p q n) = A
    generalize leadProd h2 am (vm p q n) = B
    simp only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]
    module
  · rw [a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]
    simp

end GlobalTheory.DeltaHighest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem cup_eq_coboundary_vanishing_on_inertia : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hC1 : IsFirstChernClassOfLineBundle K := GlobalTheory.T.tsen_theorem k K
  have hnorm : ∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 →
      ∃ x : L, Algebra.norm K x = c := fun L _ c hc => GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass K L hC1 c hc
  obtain ⟨η₀, hη₀c, hη₀⟩ := GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj K Ω N ζ hN hζ hfix hnorm a b α β ha0 hb0 hα hβ
  obtain ⟨θ, hθ0, hθE, hθη, hθs⟩ :=
    GlobalTheory.T.kummer_cochain_character_galoisInvariant_class K Ω N ζ hN hζ hfix a b α β ha0 hb0 hα hβ η₀ hη₀c hη₀
  obtain ⟨f, hf0, hfB⟩ := GlobalTheory.T.kummer_divisor_descends_functionField k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ hθ0 hθE hθs
  obtain ⟨θ₀, hθ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω f) hN
  have hθ₀0 : θ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hθ₀
    exact hf0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hθ₀.symm)
  obtain ⟨hk0c, -, hk0add, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ θ₀ hN hζ hfix hθ₀0 ⟨f, hθ₀.symm⟩
  refine ⟨fun g => η₀ g - kum ζ θ₀ g, hη₀c.sub hk0c, ?_, ?_⟩
  · intro g h
    simp only
    rw [hη₀ g h, hk0add g h]
    ring
  · intro B hB g hg
    obtain ⟨c, hcE, hc0, hcv⟩ := hfB B hB
    rw [← hθ₀] at hcv
    obtain ⟨hgE, hk⟩ := GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ θ θ₀ hθ0 hθ₀0 hθE
      ⟨f, hθ₀.symm⟩ B hB g hg c hcE hc0 hcv
    show η₀ g - kum ζ θ₀ g = 0
    rw [hθη g hgE, hk, sub_self]

theorem thmA : GlobalTheory.NeedB.ThmA := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha0 hb0 haA hai hbA hbi hα hβ
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨z, hz⟩ := zeta_mem_range k K Ω N ζ hN hζ
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ := fun g => by rw [← hz]; exact g.commutes z
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 hβ.symm)
  obtain ⟨hαc, -, hαadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hβc, -, hβadd, -⟩ :=
    GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  exact ⟨hαadd, hαc, hβadd, hβc,
    cup_eq_coboundary_vanishing_on_inertia k K Ω N ζ hN hζ a b α β haA hai hbA hbi ha0 hb0 hα hβ⟩

end GlobalTheory.KummerCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferencesStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_sub_one_mem_span_galois_differences : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt p r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  first | exact @GlobalTheory.KumIdeal.zeta_sub_one_mem_span | exact GlobalTheory.KumIdeal.zeta_sub_one_mem_span | (intros; apply GlobalTheory.KumIdeal.zeta_sub_one_mem_span <;> assumption)
end

