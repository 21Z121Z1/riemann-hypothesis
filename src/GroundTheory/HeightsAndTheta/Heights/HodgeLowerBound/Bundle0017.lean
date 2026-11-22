import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFrameTransition
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace HodgeFrameTransition

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨a, i₀⟩ := p
  show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      classical
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    classical
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

theorem isMultiHomog_prod_X (c : (k : K) → ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K,
      IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι)) (fun k => if k ∈ s then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, if_false]
      exact isMultiHomog_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      convert isMultiHomog_mul (isMultiHomog_X_single (ι := ι) ⟨a, c a⟩) ih using 1
      funext k
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk]
  simpa using key Finset.univ

theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem exists_value_of_mem_chartRing {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨(∏ k, z ⟨k, c' k⟩) / ∏ k, z ⟨k, c k⟩, fun _ => 1, ∏ k, X ⟨k, c' k⟩, ∏ k, X ⟨k, c k⟩,
      isMultiHomog_prod_X c', isMultiHomog_prod_X c, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hyc
    · simp only [map_prod, aeval_X]
      exact (div_mul_cancel₀ _ hyc).symm
    · simp only [map_prod, map_X, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hz k
    · simp [map_prod]
  | algebraMap n => exact ⟨n, by simpa using isValueAt_intCast y z n⟩
  | add a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v + w, LineFlag.isValueAt_add hv hw⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v * w, LineFlag.isValueAt_mul hv hw⟩

theorem exists_value_of_pow_mul_mem {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {z : (Σ k, ι k) → ℂ}
    (hzP : z ∈ mcPts (mCoordIdeal y)) (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {g a : Ω}
    (hg : IsUnitAt y g z) {n : ℕ} (ha : g ^ n * a ∈ chartRing ℤ (segreCoord y) c) :
    ∃ v, IsValueAt y a z v := by
  obtain ⟨w, hw⟩ := exists_value_of_mem_chartRing hyc hz ha
  obtain ⟨u, hu, hu0⟩ := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hu0 (isValueAt_zero hzP hu)
  refine ⟨u⁻¹ ^ n * w, ?_⟩
  have := LineFlag.isValueAt_mul (LineFlag.isValueAt_pow (LineFlag.isValueAt_inv hzP hu hu0) n) hw
  rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hg0, one_pow, one_mul] at this

end HodgeFrameTransition

open HodgeFrameTransition in

theorem HodgeFrameTransition.proof : HodgeFrameTransition.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D τ c f bfr z hz hfr hdom
  classical
  obtain ⟨hyc, -, -, hli, hiff⟩ := hfr
  obtain ⟨hzc, hfu⟩ := hdom
  obtain ⟨m, fl, al, hfl, hal, hsum, hframe⟩ := D.hodge τ c hyc
  choose vf hvf using fun l => exists_value_of_mem_chartRing hyc hzc (hfl l)
  choose va hva using fun l => exists_value_of_mem_chartRing hyc hzc (hal l)
  have h1 : ∑ l, va l * vf l = 1 := by
    have := LineFlag.isValueAt_sum _ _ fun l => LineFlag.isValueAt_mul (hva l) (hvf l)
    rw [hsum] at this
    exact isValueAt_one hz this
  obtain ⟨l, hl⟩ : ∃ l, vf l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at h1
  have hfl0 : fl l ≠ 0 := by
    intro h0
    have := hvf l
    rw [h0] at this
    exact hl (isValueAt_zero hz this)
  obtain ⟨b', ⟨-, -, -, hli', hiff'⟩, hspan⟩ := hframe l hfl0
  have hflu : IsUnitAt D.y (fl l) z := ⟨vf l, hvf l, hl⟩
  obtain ⟨uf, huf, huf0⟩ := hfu

  have hsec : ∀ {g : Ω} (b : Fin D.N → E τ),
      (∀ e, (∃ n : ℕ, g ^ n • e ∈ (D.W τ).lat c) ↔ ∃ a : Fin D.N → Ω,
        (∀ q, ∃ n : ℕ, g ^ n * a q ∈ chartRing ℤ (segreCoord D.y) c) ∧ e = ∑ q, a q • b q) →
      ∀ i, ∃ n : ℕ, g ^ n • b i ∈ (D.W τ).lat c := by
    intro g b h i
    refine (h (b i)).2 ⟨Pi.single i 1, fun q => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne q i with rfl | hq
      · simp
      · simp [hq]
    · simp [Pi.single_apply, ite_smul]
  choose n hn using hsec b' hiff'
  choose a ha hrep using fun i => (hiff (fl l ^ n i • b' i)).1 ⟨0, by simpa using hn i⟩
  choose n' hn' using hsec bfr hiff
  choose a' ha' hrep' using fun q => (hiff' (f ^ n' q • bfr q)).1 ⟨0, by simpa using hn' q⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact huf0 (isValueAt_zero hz huf)
  set R : Matrix (Fin D.N) (Fin D.N) Ω := fun q i => (fl l ^ n i)⁻¹ * a i q with hRdef
  set R' : Matrix (Fin D.N) (Fin D.N) Ω := fun i q => (f ^ n' q)⁻¹ * a' q i with hR'def
  have hR : ∀ i, b' i = ∑ q, R q i • bfr q := by
    intro i
    have e := congrArg ((fl l ^ n i)⁻¹ • ·) (hrep i)
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hfl0), one_smul, Finset.smul_sum] at e
    exact e
  have hR' : ∀ q, bfr q = ∑ i, R' i q • b' i := by
    intro q
    have e := congrArg ((f ^ n' q)⁻¹ • ·) (hrep' q)
    simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul, Finset.smul_sum] at e
    exact e
  have hvR : ∀ p q, ∃ v, IsValueAt D.y (R p q) z v := by
    intro q i
    obtain ⟨w, hw⟩ := exists_value_of_pow_mul_mem hz hyc hzc ⟨uf, huf, huf0⟩ (ha i q).choose_spec
    exact ⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow (hvf l) (n i))
      (pow_ne_zero _ hl)) hw⟩
  have hvR' : ∀ p q, ∃ v, IsValueAt D.y (R' p q) z v := by
    intro i q
    obtain ⟨w, hw⟩ := exists_value_of_pow_mul_mem hz hyc hzc hflu (ha' q i).choose_spec
    exact ⟨_, LineFlag.isValueAt_mul (LineFlag.isValueAt_inv hz (LineFlag.isValueAt_pow huf (n' q))
      (pow_ne_zero _ huf0)) hw⟩
  obtain ⟨Rz, hRz⟩ : ∃ Rz : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R p q) z (Rz p q) :=
    ⟨fun p q => (hvR p q).choose, fun p q => (hvR p q).choose_spec⟩
  obtain ⟨R'z, hR'z⟩ : ∃ R'z : Matrix (Fin D.N) (Fin D.N) ℂ, ∀ p q, IsValueAt D.y (R' p q) z (R'z p q) :=
    ⟨fun p q => (hvR' p q).choose, fun p q => (hvR' p q).choose_spec⟩
  have hRR' : R * R' = 1 := by
    ext p q
    have hcomb : ∑ p, ((R * R') p q - (1 : Matrix (Fin D.N) (Fin D.N) Ω) p q) • bfr p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul]
      have e1 : ∑ p, ∑ i, (R p i * R' i q) • bfr p = bfr q := by
        rw [Finset.sum_comm, hR' q]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hR i, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [smul_smul, mul_comm]
      simp [e1, Matrix.one_apply, ite_smul]
    have := Fintype.linearIndependent_iff.1 hli _ hcomb p
    exact sub_eq_zero.1 this
  refine ⟨b', R, R', Rz, R'z, hli', hspan, hR, hR', hRz, hR'z, ?_⟩
  ext p r
  have hv := LineFlag.isValueAt_sum _ _ fun q => LineFlag.isValueAt_mul (hRz p q) (hR'z q r)
  have e : ∑ q, R p q * R' q r = (1 : Matrix (Fin D.N) (Fin D.N) Ω) p r := by
    rw [← Matrix.mul_apply, hRR']
  rw [e, Matrix.one_apply] at hv
  rw [Matrix.mul_apply, Matrix.one_apply]
  split_ifs at hv ⊢
  · exact isValueAt_one hz hv
  · exact isValueAt_zero hz hv

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerExpand
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace PlueckerExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_finsetSum {α : Type} (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (s : Finset α)
    (f : α → Ω) (v : α → ℂ) (h : ∀ i, IsValueAt y (f i) z (v i)) :
    IsValueAt y (∑ i ∈ s, f i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LineFlag.isValueAt_zero' y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact LineFlag.isValueAt_add (h a) ih

theorem isValueAt_finsetProd {α : Type} (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (s : Finset α)
    (f : α → Ω) (v : α → ℂ) (h : ∀ i, IsValueAt y (f i) z (v i)) :
    IsValueAt y (∏ i ∈ s, f i) z (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_one_self y z
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact LineFlag.isValueAt_mul (h a) ih

end PlueckerExpand

theorem PlueckerExpand.proof : PlueckerExpand.Statement := by
  intro K _ ι _ Ω _ E _ _ y c b N r φ bfr z V A Az hz hV hA
  choose v0 hv0 hVeq using fun q => (hV q).2
  set P : ℂ := ∏ k, z ⟨k, c k⟩ ^ b k with hP
  refine ⟨fun q hq => ?_, fun q σ => ?_, ?_⟩
  · have h0 : φ (bfr ∘ q) = 0 := φ.map_eq_zero_of_not_injective _ fun hinj => hq fun a a' h => hinj (by simp [h])
    have hval : IsValueAt y (φ (bfr ∘ q) * twistFactor y c b) z 0 := by
      rw [h0, zero_mul]; exact LineFlag.isValueAt_zero' y z
    rw [hVeq q, LineFlag.isValueAt_unique hz (hv0 q) hval, zero_mul]
  · have hperm : φ (bfr ∘ (q ∘ σ)) * twistFactor y c b =
        ((Equiv.Perm.sign σ : ℤ) : Ω) * (φ (bfr ∘ q) * twistFactor y c b) := by
      rw [show bfr ∘ (q ∘ σ) = (bfr ∘ q) ∘ σ from rfl, φ.map_perm, Units.smul_def, zsmul_eq_mul, mul_assoc]
    have hval := LineFlag.isValueAt_mul (PlueckerExpand.isValueAt_intCast y z (Equiv.Perm.sign σ : ℤ)) (hv0 q)
    rw [← hperm] at hval
    rw [hVeq (q ∘ σ), hVeq q, LineFlag.isValueAt_unique hz (hv0 (q ∘ σ)) hval, mul_assoc]
  · refine ⟨∑ q, (∏ a, Az (q a) a) * v0 q, ?_, ?_⟩
    · have hexp : φ (fun a => ∑ q, A q a • bfr q) = ∑ q : Fin r → Fin N, (∏ a, A (q a) a) * φ (bfr ∘ q) := by
        have := φ.toMultilinearMap.map_sum (fun a q => A q a • bfr q)
        simp only [AlternatingMap.coe_multilinearMap] at this
        rw [this]
        refine Finset.sum_congr rfl fun q _ => ?_
        have h2 := φ.toMultilinearMap.map_smul_univ (fun a => A (q a) a) (fun a => bfr (q a))
        simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
        exact h2
      rw [hexp, Finset.sum_mul]
      refine PlueckerExpand.isValueAt_finsetSum y z _ _ _ fun q => ?_
      rw [mul_assoc]
      exact LineFlag.isValueAt_mul
        (PlueckerExpand.isValueAt_finsetProd y z _ _ _ fun a => hA (q a) a) (hv0 q)
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hVeq q]; ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSameSpanAltDet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem SameSpanAltDet.proof : SameSpanAltDet.Statement := by
  intro Ω _ E _ _ r u u' hu hu' hspan
  let S := Submodule.span Ω (Set.range u')
  let B' : Module.Basis (Fin r) Ω S := Module.Basis.span hu'
  have hmem : ∀ a, u a ∈ S := fun a => by
    change u a ∈ Submodule.span Ω (Set.range u')
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  let v : Fin r → S := fun a => ⟨u a, hmem a⟩
  have hv : LinearIndependent Ω v := LinearIndependent.of_comp S.subtype hu
  have : FiniteDimensional Ω S := Module.Finite.of_basis B'
  have hcard : Fintype.card (Fin r) = Module.finrank Ω S := (Module.finrank_eq_card_basis B').symm
  let B : Module.Basis (Fin r) Ω S := basisOfLinearIndependentOfCardEqFinrank' v hv hcard
  have hB : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hv hcard
  refine ⟨B'.det v, ?_, ?_⟩
  · rw [← hB]
    exact (B'.isUnit_det B).ne_zero
  · intro φ
    have key := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det B' (φ.compLinearMap S.subtype))
    have hB' : (fun i => S.subtype (B' i)) = u' := funext fun a => Module.Basis.coe_span_apply hu' a
    have hv' : (fun i => S.subtype (v i)) = u := rfl
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at key
    rw [hB', hv'] at key
    rw [key, mul_comm]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagRatioTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagRatioTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n : ℕ),
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n))) =
      ((Fintype.card Ψ * flagDim n : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFnFieldTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FnFieldTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (d : ℕ), Birational y → IsArithVar (mCoordIdeal y) (d + 1) → Algebra.trdeg ℤ Ω = d

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGenLeadMinorNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinorNeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (a : Fin (n - 1)), leadMinor (genMatFr F Ψ n τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagMinorTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelChartUnit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def IsMuLocalDatum {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) (c : (k : K) → ι k) (f : Ω)
    (b : ∀ τ, Fin D.N → E τ) (u : Ω) : Prop :=
  (∀ τ, IsAdaptedFrame D.y (D.W τ) (H.F τ) D.j_le_N c f (b τ)) ∧ IsUnitOn D.y c f u ∧
    H.Λ = (u * chartMono D.y c H.aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (H.F τ) D.j_le_N (b τ)

open Classical in

def MuModelChartUnit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    ∀ (c₀ : (k : K) → ι k) (f₀ : Ω) (b₀ : ∀ τ, Fin D.N → E τ) (u₀ : Ω), IsMuLocalDatum H c₀ f₀ b₀ u₀ →
    ∀ W : Ideal (MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ), W.IsPrime →
      (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ W →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
      ∃ (dp dq : MuBlocks D → ℕ) (p q : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ),
        GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog p dp ∧
        GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog q dq ∧ p ∉ W ∧ q ∉ W ∧
        (∀ k, (dp k : ℤ) - dq k = muDeg D k - Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ) k) ∧
        aeval (muPointOf P b₀) p = (u₀⁻¹ * chartMono D.y c₀ (-H.aMu)) * aeval (muPointOf P b₀) q

def PlueckerFrameGen.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ) (i : Fin D.N)
    (c : (k : K) → ι k) (f : Ω) (b : Fin D.N → E τ), IsFrameOver D.y (D.W τ) c f b →
    (∀ m, ∃ n : ℕ, f ^ n * (P.gen τ i m (b ∘ Fin.castLE i.isLt) * twistFactor D.y c P.b) ∈
      chartRing ℤ (segreCoord D.y) c) ∧
    ∃ (M : ℕ) (a : Fin (P.M τ i) → Ω), (∀ m, a m ∈ chartRing ℤ (segreCoord D.y) c) ∧
      f ^ M = ∑ m, a m * (P.gen τ i m (b ∘ Fin.castLE i.isLt) * twistFactor D.y c P.b)

def WedgeTransition.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (F : ∀ τ, Submodule Ω (E τ)) (N j r s : ℕ) (hj : j ≤ N) (hr : r ≤ N) (hs : s ≤ N),
    r = j → s = N → ∀ b b' : ∀ τ, Fin N → E τ,
    (∀ τ, LinearIndependent Ω (b τ) ∧ Submodule.span Ω (Set.range (b τ)) = ⊤ ∧
      Submodule.span Ω (Set.range (b τ ∘ Fin.castLE hr)) = F τ) →
    (∀ τ, LinearIndependent Ω (b' τ) ∧ Submodule.span Ω (Set.range (b' τ)) = ⊤ ∧
      Submodule.span Ω (Set.range (b' τ ∘ Fin.castLE hr)) = F τ) →
    ∀ (φ : ∀ τ, E τ [⋀^Fin s]→ₗ[Ω] Ω) (ψ : ∀ τ, E τ [⋀^Fin r]→ₗ[Ω] Ω) (κ κ' : Ω),
      κ • PiTensorProduct.tprod Ω (fun τ => quotWedge (F τ) hj (b τ)) =
        κ' • PiTensorProduct.tprod Ω (fun τ => quotWedge (F τ) hj (b' τ)) →
      κ * ∏ τ, (φ τ (b τ ∘ Fin.castLE hs) * ψ τ (b' τ ∘ Fin.castLE hr)) =
        κ' * ∏ τ, (φ τ (b' τ ∘ Fin.castLE hs) * ψ τ (b τ ∘ Fin.castLE hr))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PivotMinorFlag.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n), (a : ℕ) ≤ b →
    ∃ S : PluckerBlocks n n a, pivotMinor M a b = flagMinor M a S

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerRatioFieldEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PlueckerRatioFieldEq.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (c : ∀ k, Pl.ιY k), (∀ k, Pl.yY ⟨k, c k⟩ ≠ 0) →
    IntermediateField.adjoin Ω (coneRatios Pl.yY c) =
      IntermediateField.adjoin Ω (Set.range (flagMinorRatio Ω Ψ D.N))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

