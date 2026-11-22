import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalVectorValueUnitaryRankOneGindikinKarpel
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

def transv {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) : GL (Fin n) L :=
  ⟨1 + Matrix.single i j c, 1 - Matrix.single i j c,
    by rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp,
    by rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp⟩

theorem transv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    ((transv i j hij c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 + Matrix.single i j c := rfl

theorem transv_inv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    (((transv i j hij c)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 - Matrix.single i j c := rfl

theorem transv_mem_GU (σ : L →+* L) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hr : i.rev = j) (c : L)
    (hc : σ c = -c) : transv i j hij c ∈ GU σ n := by
  rw [GlobalTheory.LGrp.mem_GU_iff]
  intro p r
  have e1 : ∀ x : Fin n, i = x.rev ↔ x = j := fun x => by rw [← hr]; exact ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have e2 : ∀ x : Fin n, j = x.rev ↔ x = i := fun x => by
    rw [← hr]; exact ⟨fun h => Fin.rev_injective (by rw [← h]), fun h => by rw [h]⟩
  rw [transv_inv_val, transv_val]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.rev_inj, e1, e2]
  by_cases h : i = p ∧ j = r
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hij.symm, hc, sub_eq_add_neg]
  · have h' : ¬ (r = j ∧ p = i) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
    rw [if_neg h, if_neg h']
    by_cases hpr : p = r
    · subst hpr; simp
    · simp [hpr, Ne.symm hpr]
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_mul_apply {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((Y : Matrix (Fin n) (Fin n) L) * M) i j = (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) * M (t⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (t⁻¹ i)]
  · intro l _ hl
    rw [hY i l (fun h => hl (by rw [h]; simp)), zero_mul]
  · simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL {x : L} (hx : Valued.v x ≤ 1) : x ∈ intL L := hx

theorem transv_mem_GLint {n : ℕ} (i j : Fin n) (hij : i ≠ j) {c : L} (hc : Valued.v c ≤ 1) :
    transv i j hij c ∈ GLint (Fin n) (intL L) := by
  have hc' : c ∈ intL L := mem_intL hc
  refine P.cartan_mem_of_entries (intL L) _ (fun p r => ?_) (fun p r => ?_)
  · rw [transv_val, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'
  · rw [transv_inv_val, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply]
    refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'

theorem ordL_neg (x : L) : ordL (-x) = ordL x := by
  simp only [ordL, Valuation.map_neg]

theorem ordL_one' : ordL (1 : L) = 0 :=
  P.fIwasawa_ordL_unit 1 1 (by rw [map_one]) (by rw [map_one]) (mul_one 1)

theorem ordL_inv {x : L} (hx : x ≠ 0) : ordL x⁻¹ = -ordL x := by
  have h := P.fIwasawa_ordL_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordL_one'] at h
  omega

theorem ordL_monomial_entry {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (hYK : Y ∈ GLint (Fin n) (intL L)) (i : Fin n) :
    ordL ((Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i)) = 0 := by
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq] at h
  exact P.fIwasawa_ordL_unit _ _ (P.cartan_entries_of_mem _ Y hYK _ _)
    (P.cartan_entries_of_mem _ _ (inv_mem hYK) _ _) (by rw [mul_comm]; exact h)

theorem isBorelU_one (σ : L →+* L) (n : ℕ) : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply, ne_of_gt h]

theorem chiDeltaU_one (σ : L →+* L) (n m q : ℕ) (α : Fin m → ℂ) : chiDeltaU q α (1 : GU σ n) = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one']
  · rfl

end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_entry_ne_zero {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (i : Fin n) : (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq, h0, zero_mul] at h
  exact zero_ne_one h
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne

theorem value_rankOne : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  intro L _ _ ϖ σ q _ n k hk hn α φ hφ hφ1 y hy hyw u hu
  have hn2 : n = 2 * k.val + 2 := by obtain ⟨r, hr⟩ := hn; omega
  set a : Fin n := lo k with ha
  set a' : Fin n := (lo k).rev with ha'
  have hav : a.val = k.val := rfl
  have ha'v : a'.val = k.val + 1 := by rw [ha', Fin.val_rev]; simp; omega
  have haa' : a ≠ a' := fun h => by have := congrArg Fin.val h; omega
  have hra : a'.rev = a := by rw [ha', Fin.rev_rev]
  set b := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hb
  have hU : (u : GL (Fin n) L) = transv a a' haa' b := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [transv_val]
    by_cases h : i = a ∧ j = a'
    · obtain ⟨rfl, rfl⟩ := h
      simp [Matrix.single_apply, haa', hb]
    · rw [hu i j h, Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  have hσb : σ b = -b := by
    have h := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2 a a'
    rw [hra, ← ha', ← hb, hU, transv_inv_val] at h
    simpa [Matrix.single_apply, haa'] using h.symm
  by_cases hv : Valued.v b ≤ 1
  · rw [if_pos hv]
    have huK : u ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      show (u : GL (Fin n) L) ∈ GLint (Fin n) (intL L)
      rw [hU]; exact transv_mem_GLint a a' haa' hv
    have h := hφ 1 1 (y⁻¹ * u) (isBorelU_one σ n) (mul_mem (inv_mem hy) huK)
    rw [one_mul, one_mul] at h
    rw [h, chiDeltaU_one, hφ1, one_mul]
  · rw [if_neg hv]
    push_neg at hv
    have hb0 : b ≠ 0 := fun h => by rw [h, map_zero] at hv; exact not_lt_of_ge zero_le' hv
    set c := b⁻¹ with hc
    have hvc : Valued.v c ≤ 1 := ((Valuation.one_lt_val_iff _ hb0).1 hv).le
    have hσc : σ c = -c := by rw [hc, map_inv₀, hσb, inv_neg]
    have hbc : b * c = 1 := mul_inv_cancel₀ hb0
    let κ : GU σ n := ⟨transv a' a haa'.symm c, transv_mem_GU σ a' a haa'.symm hra c hσc⟩
    have hκ : κ ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      exact transv_mem_GLint a' a haa'.symm hvc
    set Pb : GU σ n := y⁻¹ * u * κ⁻¹ with hPb
    have e : Pb * 1 * κ = y⁻¹ * u := by rw [hPb]; group
    have hyK : (y : GL (Fin n) L) ∈ GLint (Fin n) (intL L) := hy.2
    have hyiw := IsWeylRep.inv hyw
    have hs : simpleU k = Equiv.swap a a' := by unfold simpleU; rw [if_neg hk]
    set M : Matrix (Fin n) (Fin n) L := (1 + Matrix.single a a' b) * (1 - Matrix.single a' a c) with hMdef
    have hM : ∀ l j, M l j = (1 : Matrix (Fin n) (Fin n) L) l j + (if a = l ∧ a' = j then b else 0)
        - (if a' = l ∧ a = j then c else 0) - (if a = l ∧ a = j then 1 else 0) := by
      intro l j
      rw [hMdef, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_same, hbc]
      simp [Matrix.single_apply]; ring
    have hP : ∀ i j, (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
          M (Equiv.swap a a' i) j := by
      intro i j
      have : (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
          (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M := by
        rw [hPb, hMdef, ← transv_val a a' haa' b, ← transv_inv_val a' a haa'.symm, ← hU]
        simp [Matrix.mul_assoc, κ]
      rw [this, monomial_mul_apply hyiw, inv_inv, hs]
    have hunit : ∀ i, ordL ((((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i
        (Equiv.swap a a' i)) = 0 := fun i => by
      have := ordL_monomial_entry hyiw (inv_mem hyK) i
      rwa [inv_inv, hs] at this
    have hB : IsBorelU Pb := by
      intro i j hji
      have hj : j.val < i.val := hji
      rw [hP, hM]
      apply mul_eq_zero_of_right
      simp only [Matrix.one_apply, Equiv.swap_apply_def, Fin.ext_iff]
      split_ifs <;> first | omega | ring
    rw [← e, hφ Pb 1 κ hB hκ, hφ1, mul_one]
    have hdiag : ∀ i : Fin n, i ≠ a → i ≠ a' →
        ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 0 := by
      intro i h1 h2
      rw [hP, Equiv.swap_apply_of_ne_of_ne h1 h2, hM]
      simp only [Matrix.one_apply_eq, if_neg (fun h : a = i ∧ a' = i => h1 h.1.symm),
        if_neg (fun h : a' = i ∧ a = i => h2 h.1.symm), if_neg (fun h : a = i ∧ a = i => h1 h.1.symm)]
      have := hunit i
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at this
      simpa using this
    have hdiag_a : ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = -ordL b := by
      rw [hP, Equiv.swap_apply_left, hM]
      simp only [Matrix.one_apply, if_neg haa'.symm, if_neg (fun h : a = a' ∧ a' = a => haa' h.1),
        if_pos (⟨rfl, rfl⟩ : a' = a' ∧ a = a), if_neg (fun h : a = a' ∧ a = a => haa' h.1)]
      have hy0 : (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' ≠ 0 := by
        have := monomial_entry_ne_zero hyiw a
        rwa [inv_inv, hs, Equiv.swap_apply_left] at this
      have hc0 : c ≠ 0 := inv_ne_zero hb0
      have e2 : ((0 : L) + 0 - if True ∧ True then c else 0) - (if a = a' ∧ True then 1 else 0) = -c := by
        rw [if_pos ⟨trivial, trivial⟩, if_neg (fun h => haa' h.1)]; ring
      rw [e2, P.fIwasawa_ordL_mul _ _ hy0 (neg_ne_zero.2 hc0), ordL_neg, hc, ordL_inv hb0]
      have := hunit a
      rw [Equiv.swap_apply_left] at this
      rw [this, zero_add]
    unfold chiDeltaU
    rw [Finset.prod_eq_single k]
    · rw [dif_pos (by omega)]
      show α k ^ ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) *
          (q : ℂ) ^ (-(ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) *
            ((n : ℤ) - 1 - 2 * (k.val : ℤ))) = _
      have e3 : (n : ℤ) - 1 - 2 * (k.val : ℤ) = 1 := by omega
      rw [hdiag_a, e3, neg_neg, mul_one]
    · intro i _ hik
      have hi : i.val < k.val := by
        have : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
      rw [dif_pos (by omega), hdiag _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)]
      simp
    · simp

end GlobalTheory.GKUnitaryRankOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWeylCellTranslate
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.UnipShiftU

variable {L : Type} [Field L]

theorem unipB_mul_apply_succ {n : ℕ} {X Y : GL (Fin n) L} (hX : X ∈ unipB L (Fin n)) (hY : Y ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (Y : Matrix (Fin n) (Fin n) L) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

theorem unipB_inv_apply_succ {n : ℕ} {X : GL (Fin n) L} (hX : X ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = -(X : Matrix (Fin n) (Fin n) L) a a' := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have e := unipB_mul_apply_succ hX (inv_mem hX) h
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hne] at e
  linear_combination -e

theorem conj_apply {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (X : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * X * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * X (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro e; apply hb; rw [e]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem inv_mul_diag {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h : ((y⁻¹ * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i), Units.val_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rw [hy.inv i b (by intro e; apply hb; rw [e]; simp), zero_mul]
  · simp

theorem swap_inversion {n : ℕ} {a a' p q : Fin n} (h : a'.val = a.val + 1) (hpq : p < q)
    (hs : Equiv.swap a a' q < Equiv.swap a a' p) : p = a ∧ q = a' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at hs
  rw [Fin.lt_iff_val_lt_val] at hpq
  split_ifs at hs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem transvection_apply' {n : ℕ} (a a' : Fin n) (d : L) (i j : Fin n) :
    Matrix.transvection a a' d i j = (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

theorem ordL_one [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 := by
  unfold ordL
  rw [dif_neg (by simp)]
  simp
  rfl

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrames_match_completedLattices_at_prime : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.frames_match_lattices | exact GlobalTheory.LatMatch.frames_match_lattices | (intros; apply GlobalTheory.LatMatch.frames_match_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwistedOrbitalIntegralsEqFinsumParametrisedStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_twistedOrbitalIntegrals_eq_finsum_parametrised : ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (Kg : Subgroup G) (S : Set G) (f : G → ℂ) (C : Type) (ι : C → G) (N : C → ℂ), (∀ c, ι c ∈ S) → (∀ y ∈ S, ∃ c g, y = g⁻¹ * ι c * θ g) → (∀ c c', (∃ g, ι c' = g⁻¹ * ι c * θ g) → c = c') → (∀ y g, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) → (∀ y g, twOrb θ Kg (g⁻¹ * y * θ g) f = twOrb θ Kg y f) → (∀ c, twOrb θ Kg (ι c) f = N c) → clSum θ Kg S (fun _ => 1) f = ∑ᶠ c, N c := by
  first | exact @GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | exact GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param | (intros; apply GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  first | exact @GlobalTheory.DegGrowth.main | exact GlobalTheory.DegGrowth.main | (intros; apply GlobalTheory.DegGrowth.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1ProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_intersection_O1_projective : ∀ (k : Type) [Field k] (N : ℕ), letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 := by
  first | exact @GlobalTheory.ProjSpaceDegree.topSelf_O1_str | exact GlobalTheory.ProjSpaceDegree.topSelf_O1_str | (intros; apply GlobalTheory.ProjSpaceDegree.topSelf_O1_str <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V) (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) → trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  first | exact @GlobalTheory.BCT.trOn_iSup_eq_sum | exact GlobalTheory.BCT.trOn_iSup_eq_sum | (intros; apply GlobalTheory.BCT.trOn_iSup_eq_sum <;> assumption)
end

