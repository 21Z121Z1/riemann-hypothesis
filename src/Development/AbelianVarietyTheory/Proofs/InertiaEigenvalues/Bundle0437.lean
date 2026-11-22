import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EnvLevel

theorem mem_smul_top_of_mem_map_C {R : Type} [CommRing R] (I : Ideal R) (p : MvPolynomial ℕ R)
    (hp : p ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial ℕ R) I) :
    p ∈ I • (⊤ : Submodule R (MvPolynomial ℕ R)) := by
  rw [MvPolynomial.mem_map_C_iff] at hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun s _ => ?_
  have : MvPolynomial.monomial s (p.coeff s) = p.coeff s • MvPolynomial.monomial s (1 : R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hp s) Submodule.mem_top

theorem tri_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (l i : ℕ) (v : Aˣ)
    (a b : MvPolynomial ℕ A)
    (ha : a ∈ MvPolynomial.supported A (Set.Iio i)) (hb : b ∈ MvPolynomial.supported A (Set.Iio i)) :
    ∃ (v' : Rˣ) (a' b' : MvPolynomial ℕ R), a' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      b' ∈ MvPolynomial.supported R (Set.Iio i) ∧
      MvPolynomial.map f (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) =
        MvPolynomial.C (v' : R) * MvPolynomial.X i ^ l + a' * MvPolynomial.X i + b' := by
  refine ⟨Units.map f.toMonoidHom v, MvPolynomial.map f a, MvPolynomial.map f b, ?_, ?_, ?_⟩
  · rw [MvPolynomial.mem_supported] at ha ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map a f)).trans ha
  · rw [MvPolynomial.mem_supported] at hb ⊢
    exact (Finset.coe_subset.mpr (MvPolynomial.vars_map b f)).trans hb
  · simp [map_add, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]

end GlobalTheory.EnvLevel

theorem GlobalTheory.digitMonomials_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  intro l _ A _ J r hr n
  classical
  let π : MvPolynomial ℕ A →+* MvPolynomial ℕ (A ⧸ J ^ n) := MvPolynomial.map (Ideal.Quotient.mk (J ^ n))
  have hπs : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    simp only [π]; rw [MvPolynomial.ker_map, Ideal.mk_ker]
  let I : Ideal (A ⧸ J ^ n) := J.map (Ideal.Quotient.mk (J ^ n))
  have hIn : I ^ n = ⊥ := by
    simp only [I]; rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  choose v a b ha hb hrab using hr
  let t : ℕ → MvPolynomial ℕ (A ⧸ J ^ n) := fun i =>
    π (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)
  have ht := fun i => GlobalTheory.EnvLevel.tri_map (Ideal.Quotient.mk (J ^ n)) l i (v i) (a i) (b i) (ha i) (hb i)
  obtain ⟨htli, htsp⟩ := GlobalTheory.T.triangular_system_monomial_products_basis l (A ⧸ J ^ n) t ht
  let B : Digits l × (ℕ →₀ ℕ) → MvPolynomial ℕ (A ⧸ J ^ n) := fun x =>
    MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => π (r i) ^ m
  have hK : ∀ i, π (r i) - t i ∈ Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I := by
    intro i
    have h1 : π (r i) - t i = π (r i - (MvPolynomial.C (v i : A) * MvPolynomial.X i ^ l + a i * MvPolynomial.X i + b i)) := by
      simp only [t, map_sub]
    have h2 : Ideal.map (MvPolynomial.C : (A ⧸ J ^ n) →+* MvPolynomial ℕ (A ⧸ J ^ n)) I =
        Ideal.map π (J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) := by
      simp only [I, π]
      rw [Ideal.map_map, Ideal.map_map, MvPolynomial.map_comp_C]
    rw [h1, h2]
    exact Ideal.mem_map_of_mem _ (hrab i)
  have hBK : ∀ x, B x - (MvPolynomial.monomial x.1.1 (1 : A ⧸ J ^ n) * x.2.prod fun i m => t i ^ m) ∈
      I • (⊤ : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n))) := by
    intro x
    apply GlobalTheory.EnvLevel.mem_smul_top_of_mem_map_C
    rw [← Ideal.Quotient.eq]
    simp only [B, map_mul, Finsupp.prod, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq.mpr (hK i)]
  obtain ⟨hBli, hBsp⟩ := GlobalTheory.T.basis_of_congr_basis_mod_nilpotent_ideal (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) (Digits l × (ℕ →₀ ℕ))
    _ B I n hIn htli htsp hBK
  have hBmem : ∀ k : Digits l × (ℕ →₀ ℕ), k.2 ≠ 0 → B k ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
    intro k hk
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk
    apply Ideal.mul_mem_left
    have hd : π (r i) ^ k.2 i ∣ k.2.prod fun i m => π (r i) ^ m :=
      Finset.dvd_prod_of_mem (fun i => π (r i) ^ k.2 i) hi
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    apply Ideal.mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self (f := ⇑π ∘ r) i)) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  let S : Submodule (A ⧸ J ^ n) (MvPolynomial ℕ (A ⧸ J ^ n)) :=
    Submodule.span (A ⧸ J ^ n) (B '' {x | x.2 ≠ 0})
  have hmulS : ∀ i (p : MvPolynomial ℕ (A ⧸ J ^ n)), p * π (r i) ∈ S := by
    intro i p
    have hp : p ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have : B k * π (r i) = B (k.1, k.2 + Finsupp.single i 1) := by
        simp only [B]
        rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
          Finsupp.prod_single_index (by simp)]
        simp only [pow_one, mul_assoc]
      rw [this]
      refine Submodule.subset_span ⟨(k.1, k.2 + Finsupp.single i 1), ?_, rfl⟩
      intro h
      have := DFunLike.congr_fun h i
      simp at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hspanS : ∀ x ∈ Ideal.span (Set.range (⇑π ∘ r)), ∀ p, p * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact fun p => hmulS i p
    | zero => intro p; simp
    | add y z _ _ hy hz => intro p; rw [mul_add]; exact S.add_mem (hy p) (hz p)
    | smul c y _ hy => intro p; rw [smul_eq_mul, ← mul_assoc]; exact hy (p * c)
  refine ⟨?_, ?_⟩
  · intro x
    have hx : π x ∈ Submodule.span (A ⧸ J ^ n) (Set.range B) := by rw [hBsp]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let f0 := f.filter fun k => k.2 = 0
    let f1 := f.filter fun k => ¬ k.2 = 0
    let g : Digits l →₀ (A ⧸ J ^ n) := f0.mapDomain Prod.fst
    have hsplit : π x = (f0.sum fun k a => a • B k) + (f1.sum fun k a => a • B k) := by
      rw [← hf, ← Finsupp.sum_add_index' (h := fun k a => a • B k) (fun _ => zero_smul _ _)
        (fun _ _ _ => add_smul _ _ _)]
      simp only [f0, f1]
      rw [Finsupp.filter_add_filter_not]
    have h0sum : (f0.sum fun k a => a • B k) = g.sum fun α a => MvPolynomial.monomial α.1 a := by
      simp only [g]
      rw [Finsupp.sum_mapDomain_index (h := fun (α : Digits l) (a : A ⧸ J ^ n) => MvPolynomial.monomial α.1 a)
        (fun (α : Digits l) => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_zero)
        (fun (α : Digits l) _ _ => (MvPolynomial.monomial (R := A ⧸ J ^ n) α.1).map_add _ _)]
      refine Finsupp.sum_congr fun k hk => ?_
      have hk2 : k.2 = 0 := by
        simp only [f0] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      simp only [B, hk2, Finsupp.prod_zero_index, mul_one, MvPolynomial.smul_monomial, smul_eq_mul]
    have h1mem : (f1.sum fun k a => a • B k) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      unfold Finsupp.sum
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk2 : k.2 ≠ 0 := by
        simp only [f1] at hk
        rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
      show f1 k • B k ∈ _
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ (hBmem k hk2)
    let sec : (A ⧸ J ^ n) → A := fun y =>
      if y = 0 then 0 else Function.surjInv (Ideal.Quotient.mk_surjective (I := J ^ n)) y
    have hsec0 : sec 0 = 0 := by simp [sec]
    have hsec : ∀ y, Ideal.Quotient.mk (J ^ n) (sec y) = y := by
      intro y
      by_cases h : y = 0
      · simp [sec, h]
      · simp only [sec, h, if_false]; exact Function.surjInv_eq _ y
    refine ⟨g.mapRange sec hsec0, ?_⟩
    have hmap : π ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) =
        g.sum fun α a => MvPolynomial.monomial α.1 a := by
      rw [map_finsuppSum, Finsupp.sum_mapRange_index (h := fun (α : Digits l) (a : A) => π (MvPolynomial.monomial α.1 a))
        (fun _ => by simp)]
      simp only [π, MvPolynomial.map_monomial, hsec]
    have hmem : x - ((g.mapRange sec hsec0).sum fun α a => MvPolynomial.monomial α.1 a) ∈
        Ideal.comap π (Ideal.map π (Ideal.span (Set.range r))) := by
      rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, map_sub, hmap, hsplit, ← h0sum,
        add_sub_cancel_left]
      exact h1mem
    rwa [Ideal.comap_map_of_surjective _ hπs, ← RingHom.ker_eq_comap_bot, hker] at hmem
  · intro c hc α
    have h1 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range (⇑π ∘ r)) := by
      have := Ideal.mem_map_of_mem π hc
      rwa [Ideal.map_sup, ← hker, (Ideal.map_eq_bot_iff_le_ker π).mpr le_rfl, sup_bot_eq, Ideal.map_span,
        ← Set.range_comp] at this
    have h2 : π (c.sum fun α a => MvPolynomial.monomial α.1 a) ∈ S := by
      simpa using hspanS _ h1 1
    have hinj : Function.Injective (fun α : Digits l => (α, (0 : ℕ →₀ ℕ))) :=
      fun _ _ h => congrArg Prod.fst h
    let g' : Digits l × (ℕ →₀ ℕ) →₀ (A ⧸ J ^ n) :=
      Finsupp.mapDomain (fun α => (α, (0 : ℕ →₀ ℕ))) (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _))
    have hg' : Finsupp.linearCombination (A ⧸ J ^ n) B g' = π (c.sum fun α a => MvPolynomial.monomial α.1 a) := by
      rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • (B ∘ fun α => (α, (0 : ℕ →₀ ℕ))) i)
          (fun _ => zero_smul _ _), map_finsuppSum]
      refine Finsupp.sum_congr fun β _ => ?_
      simp [B, π, MvPolynomial.smul_monomial]
    obtain ⟨l', hl', hl'eq⟩ := (Finsupp.mem_span_image_iff_linearCombination (A ⧸ J ^ n)).mp h2
    have hl : l' = g' := hBli (hl'eq.trans hg'.symm)
    have h3 : g' (α, 0) = 0 := by
      rw [← hl]; exact (Finsupp.mem_supported' (A ⧸ J ^ n) l').mp hl' _ (by simp)
    have h4 : g' (α, 0) = Ideal.Quotient.mk (J ^ n) (c α) :=
      Finsupp.mapDomain_apply hinj (c.mapRange (Ideal.Quotient.mk (J ^ n)) (map_zero _)) α
    rw [h4] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormula
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualSelmerClassFromCoeffsKilledByMulStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualSelmerClass_from_coeffsKilledBy_mul : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  first | exact @GlobalTheory.DualSub.dualSel_of_smul_cob | exact GlobalTheory.DualSub.dualSel_of_smul_cob | (intros; apply GlobalTheory.DualSub.dualSel_of_smul_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  first | exact @GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | exact GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c | (intros; apply GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowDvdOfBdRPlusDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_pow_dvd_of_bdRPlus_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧ ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  first | exact @GlobalTheory.BSP.DivTransfer.div_transfer | exact GlobalTheory.BSP.DivTransfer.div_transfer | (intros; apply GlobalTheory.BSP.DivTransfer.div_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrTopOfSpanEqTop
section
open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallLetterTypeFunctional
section
noncomputable section

open Polynomial Module

namespace GlobalTheory.LetterSep

theorem eq_zero_of_forall_letterHom {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D]
    (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F]
    [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D]
    (hm : ∀ (c : U) (x : D), c • x = m c x)
    (hk : ∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) (x : D)
    (hx : ∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F),
      f x = 0) :
    x = 0 := by
  classical
  let sm : L → D →ₗ[U] D := fun a =>
    { toFun := fun x => a • x, map_add' := smul_add a
      map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }
  let r : L →+* Module.End F (D →ₗ[U] F) :=
    { toFun := fun a =>
        { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp [sm]
      map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm]
      map_zero' := by ext f x; simp [sm]
      map_add' := fun a b => by ext f x; simp [sm, add_smul] }
  have hr : ∀ a f y, r a f y = f (a • y) := fun _ _ _ => rfl
  have hrk : ∀ c : k, r (algebraMap k L c) =
      algebraMap F (Module.End F (D →ₗ[U] F)) (algebraMap k F c) := fun c => by
    ext f y
    rw [hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, smul_eq_mul]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q := fun a => by
    have : a ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  have hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F)) := fun q => by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    exact RingHom.ext hrk
  have hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α) := fun s => by
    refine le_antisymm (iInf_le _ α) (le_iInf fun a y hy => ?_)
    obtain ⟨q, rfl⟩ := hpoly a
    rw [End.mem_eigenspace_iff] at hy ⊢
    rw [hev, End.aeval_apply_of_mem_apply_eq_smul hy, eval_map_algebraMap, aeval_algHom_apply]
  have h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0 := by
    rw [← hev, minpoly.aeval, map_zero]
  have hss : (r α).IsSemisimple := End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0
  have htop : ⊤ ≤ ⨆ s : L →ₐ[k] F, ⨅ a, (r a).eigenspace (s a) := by
    rw [← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun μ y hy => ?_
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_mem _
    have h1 := End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F))
      (End.mem_eigenspace_iff.mp hy)
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hy0, eval_map_algebraMap] at h1
    have h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]
      exact ⟨minpoly.ne_zero hint, h1⟩
    obtain ⟨s, rfl⟩ := h2
    exact Submodule.mem_iSup_of_mem s (by rw [hE s]; exact hy)
  by_contra hx0
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual U D, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff U x).mp h)
  let f : D →ₗ[U] F := (Algebra.linearMap U F) ∘ₗ φ
  have hf : f x ≠ 0 := by
    simp only [f, LinearMap.comp_apply, Algebra.linearMap_apply]
    exact (_root_.map_ne_zero _).mpr hφ
  apply hf
  refine Submodule.iSup_induction (motive := fun g : D →ₗ[U] F => g x = 0) _ (htop (Submodule.mem_top (x := f)))
    (fun s g hg => ?_) rfl (fun g h hg hh => by simp [hg, hh])
  have h1 : ∀ a y, g (a • y) = s a * g y := by
    intro a y
    have := (Submodule.mem_iInf _).mp hg a
    rw [End.mem_eigenspace_iff] at this
    have := LinearMap.congr_fun this y
    simpa [hr] using this
  have h2 : ∀ c y, g (m c y) = algebraMap U F c * g y := by
    intro c y
    rw [← hm, g.map_smul, Algebra.smul_def]
  exact hx s g.toAddMonoidHom ⟨h1, h2⟩

end GlobalTheory.LetterSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancelStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equal_gaussNorm_teichmuller_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧ gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  first | exact @GlobalTheory.GaussCancel.equal_gauss_cancel | exact GlobalTheory.GaussCancel.equal_gauss_cancel | (intros; apply GlobalTheory.GaussCancel.equal_gauss_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisPhiPowEigenvectorDoubleSeriesStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_acris_phi_pow_eigenvector_double_series : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.exists_acris_Lam | exact GlobalTheory.PSer.exists_acris_Lam | (intros; apply GlobalTheory.PSer.exists_acris_Lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AinfRetraction

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  refine ⟨TB.c TB.i₀, TB.c_mul TB.i₀, ?_⟩
  rw [← TB.b_i₀]
  exact TB.c_self TB.i₀

end GlobalTheory.BKLim.AinfRetraction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_root_eisenstein_away_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ), ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧ bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  first | exact @GlobalTheory.BSP.BK.exists_approx_root | exact GlobalTheory.BSP.BK.exists_approx_root | (intros; apply GlobalTheory.BSP.BK.exists_approx_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockActionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_action_of_decomposition : ∀ {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (π : X) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Submodule.span O (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O), (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) = (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧ ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  first | exact @GlobalTheory.SpanBlockAction.exists_block_action | exact GlobalTheory.SpanBlockAction.exists_block_action | (intros; apply GlobalTheory.SpanBlockAction.exists_block_action <;> assumption)
end

