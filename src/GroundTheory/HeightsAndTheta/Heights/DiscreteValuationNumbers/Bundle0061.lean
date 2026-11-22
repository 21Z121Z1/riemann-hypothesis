import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section CycEval

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_congr_support {n n' Z : Ideal (MRing ι R) → ℤ} (h : ∀ W, Z W ≠ 0 → n W = n' W) :
    cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]

theorem cycEval_mul_left (c : ℤ) (n Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => c * n W) Z = c * cycEval n Z := by
  rw [cycEval_eq_sum hZ, cycEval_eq_sum hZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycEval_finset_sum {α : Type*} (S : Finset α) (F : α → Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => ∑ a ∈ S, F a W) Z = ∑ a ∈ S, cycEval (F a) Z := by
  rw [cycEval_eq_sum hZ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cycEval_eq_sum hZ]

theorem cycEval_sub_cycle (n Z₁ Z₂ : Ideal (MRing ι R) → ℤ) (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) :
    cycEval n Z₁ - cycEval n Z₂ = cycEval n (Z₁ - Z₂) := by
  have h₃ : (Function.support (Z₁ - Z₂)).Finite :=
    (h₁.union h₂).subset (Function.support_sub Z₁ Z₂)
  let S := h₁.toFinset ∪ h₂.toFinset
  have e : ∀ Z : Ideal (MRing ι R) → ℤ, Function.support Z ⊆ S → cycEval n Z = ∑ W ∈ S, Z W * n W := by
    intro Z hZS
    unfold cycEval
    refine finsum_eq_sum_of_support_subset _ fun W hW => hZS (Function.support_mul_subset_left _ _ hW)
  have s₁ : Function.support Z₁ ⊆ S := fun W hW => by simp [S, hW]
  have s₂ : Function.support Z₂ ⊆ S := fun W hW => by simp [S, hW]
  rw [e Z₁ s₁, e Z₂ s₂, e (Z₁ - Z₂) ((Function.support_sub Z₁ Z₂).trans (Set.union_subset s₁ s₂)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [Pi.sub_apply]
  ring

end CycEval

section Additivity

theorem vNumL_add_of_divCycle_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1))
    {c : K → ℕ} {s : MRing ι O} (hs : IsMultiHomog s c) {W : Ideal (MRing ι O)}
    (hW : divCycle P s W ≠ 0) (hϖW : (C ϖ : MRing ι O) ∈ W) (a₁ a₂ : K → ℤ) (l : List (K → ℤ))
    (hl : e ≤ l.length) :
    vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold divCycle at hW
  split_ifs at hW with hW''
  swap
  · exact absurd rfl hW
  have hWm : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P s c hPmh hs) hW''.1
  have hWp : W.IsPrime := hW''.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW''.1.1.2
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
    refine lt_of_lt_of_le (lt_natCast_of_add_one_le hdrop) ?_
    exact_mod_cast (by omega : e + 1 + 1 + Fintype.card K ≤ l.length + 2 + Fintype.card K)
  have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W)
    (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
    hdim a₁ a₂ l.get
  have e' : ∀ c, vNumL W (c :: l) =
      intNum (IsLocalRing.ResidueField O) (specialIdeal W) (Matrix.vecCons c l.get) := by
    intro c
    change _ = vNum W (Matrix.vecCons c l.get)
    rw [vNum_vecCons_eq, List.ofFn_get]
  rw [e', e', e', key]

end Additivity

section Cut

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

theorem cut_list (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g) {c : K → ℕ} {s : MRing ι O}
    (hs : IsMultiHomog s c) (hsP : s ∉ P)
    (hgen : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g)
    (l : List (K → ℤ)) (hP : IsModelOver P (l.length + 1)) :
    cycEval (fun G => vNumL G ((fun k => (c k : ℤ)) :: l)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W (b :: l)
        else cycEval (fun G => vNumL G l) (ratDiv W f g)) (divCycle P s) := by
  have h := hC3 O ϖ hϖ K ι P l.length hP b f g hD c s hs hsP hgen l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

open Classical in

theorem cut_list_ratDiv (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {b : K → ℤ} {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    {cs ch : K → ℕ} {s h : MRing ι O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hsP : s ∉ P)
    (hhP : h ∉ P)
    (hgen : ∀ H, (divCycle P s H ≠ 0 ∨ divCycle P h H ≠ 0) → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g)
    (l : List (K → ℤ)) (hP : IsModelOver P (l.length + 1)) :
    cycEval (fun G => vNumL G ((fun k => (cs k : ℤ) - ch k) :: l)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W (b :: l)
        else cycEval (fun G => vNumL G l) (ratDiv W f g)) (ratDiv P s h) := by
  have e1 := cut_list hC3 hϖ hD hs hsP (fun H hH => hgen H (Or.inl hH)) l hP
  have e2 := cut_list hC3 hϖ hD hh hhP (fun H hH => hgen H (Or.inr hH)) l hP
  have hr : ratDiv P s h = divCycle P s - divCycle P h := rfl
  have hfg := ratDiv_finite_support P f g
  rw [hr, ← cycEval_sub_cycle _ _ _ (divCycle_finite_support P s) (divCycle_finite_support P h), ← e1, ← e2,
    cycEval_eq_sum hfg, cycEval_eq_sum hfg, cycEval_eq_sum hfg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hG' : ratDiv P f g G ≠ 0 := by simpa using hG
  have hadd := vNumL_add_of_ratDiv_ne_zero hϖ hP hD hG' (fun k => (cs k : ℤ) - ch k)
    (fun k => (ch k : ℤ)) l le_rfl
  have e : ((fun k => (cs k : ℤ) - ch k) + fun k => (ch k : ℤ)) = fun k => (cs k : ℤ) := by
    funext k
    simp
  rw [e] at hadd
  rw [hadd]
  ring

open Classical in

theorem pairNum_cut_section (hC3 : CutByEffectiveDivisor.Statement.{0}) (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1)) {r : ℕ} (z z' : Fin r → K → ℤ)
    (fs gs : Fin r → MRing ι O) (hD : ∀ i, IsVerticalDivisor P ϖ (z i - z' i) (fs i) (gs i))
    {cs ch : K → ℕ} {s h : MRing ι O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hsP : s ∉ P)
    (hhP : h ∉ P)
    (hgen : ∀ H, (divCycle P s H ≠ 0 ∨ divCycle P h H ≠ 0) → (C ϖ : MRing ι O) ∉ H →
      ∀ i, IsVerticalDivisor H ϖ (z i - z' i) (fs i) (gs i))
    {m : ℕ} (hm : 1 ≤ m) {A : MvPolynomial (Fin r) ℤ} {Bs : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ}
    (hBs : IsPairExpansion m A Bs) (Q : List (K → ℤ)) (hQ : Q.length + m = e + 1) :
    pairNum P z z' fs gs Bs ((fun k => (cs k : ℤ) - ch k) :: Q) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then classNum z A Q W - classNum z' A Q W
        else pairNum W z z' fs gs Bs Q) (ratDiv P s h) := by
  set c : K → ℤ := fun k => (cs k : ℤ) - ch k with hc
  set cl : Fin r ⊕ Fin r → K → ℤ := Sum.elim z z' with hcl
  have hsh := ratDiv_finite_support P s h
  have hlen : ∀ i, ∀ μ ∈ (Bs i).support, (classList cl μ ++ Q).length = e := by
    intro i μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hBs.homogeneous i) hμ]
    omega

  have step : ∀ i, ∀ μ ∈ (Bs i).support,
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) =
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q))
          else cycEval (fun G => vNumL G (classList cl μ ++ Q)) (ratDiv W (fs i) (gs i))) (ratDiv P s h) := by
    intro i μ hμ
    refine cut_list_ratDiv hC3 hϖ (hD i) hs hh hsP hhP (fun H hH hϖH => hgen H hH hϖH i) _ ?_
    rw [hlen i μ hμ]
    exact hP

  have hL : pairNum P z z' fs gs Bs (c :: Q) = ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) := by
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (fun W : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) (c :: Q) W) =
        fun W : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W (c :: (classList cl μ ++ Q)) := by
      funext W
      unfold classNum
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [vNumL_perm W List.perm_middle]
    rw [e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support P (fs i) (gs i))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [cycEval_mul_left _ _ _ (ratDiv_finite_support P (fs i) (gs i))]
  rw [hL]
  have hR : ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
      cycEval (fun G => vNumL G (c :: (classList cl μ ++ Q))) (ratDiv P (fs i) (gs i)) =
      cycEval (fun W => ∑ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ *
        (if (C ϖ : MRing ι O) ∈ W then vNumL W ((z i - z' i) :: (classList cl μ ++ Q))
          else cycEval (fun G => vNumL G (classList cl μ ++ Q)) (ratDiv W (fs i) (gs i)))) (ratDiv P s h) := by
    rw [cycEval_finset_sum _ _ _ hsh]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cycEval_finset_sum _ _ _ hsh]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [cycEval_mul_left _ _ _ hsh, step i μ hμ]
  rw [hR]
  refine cycEval_congr_support fun W hW => ?_
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · simp only [if_pos hϖW]

    have hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
        vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l) := by
      intro a₁ a₂ l hl
      by_cases h1 : divCycle P s W = 0
      · have h2 : divCycle P h W ≠ 0 := by
          intro h2
          apply hW
          simp [ratDiv, h1, h2]
        exact vNumL_add_of_divCycle_ne_zero hϖ hP hh h2 hϖW a₁ a₂ l hl
      · exact vNumL_add_of_divCycle_ne_zero hϖ hP hs h1 hϖW a₁ a₂ l hl
    have ht : e ≤ (m - 1) + Q.length := by omega
    have e2 : ∀ i, ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL W ((z i - z' i) :: (classList cl μ ++ Q)) =
        classNum cl (pairDiff i * Bs i) Q W := fun i =>
      (classNum_pairDiff_mul hadd z z' i (hBs.homogeneous i) Q ht).symm
    simp only [e2]
    have e3 := map_sum (classNumAddHom cl Q W) (fun i => pairDiff i * Bs i) Finset.univ
    simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e3
    rw [← e3]
    have e4 : ∑ i, pairDiff i * Bs i = rename Sum.inl A - rename Sum.inr A := by
      rw [hBs.expansion]
      rfl
    rw [e4]
    have e5 := map_sub (classNumAddHom cl Q W) (rename Sum.inl A) (rename Sum.inr A)
    simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at e5
    rw [e5, classNum_rename_vars, classNum_rename_vars]
    rfl
  · simp only [if_neg hϖW]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (fun G : Ideal (MRing ι O) => classNum (Sum.elim z z') (Bs i) Q G) =
        fun G : Ideal (MRing ι O) => ∑ μ ∈ (Bs i).support, (Bs i).coeff μ * vNumL G (classList cl μ ++ Q) := rfl
    rw [e1, cycEval_finset_sum _ _ _ (ratDiv_finite_support W (fs i) (gs i))]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [cycEval_mul_left _ _ _ (ratDiv_finite_support W (fs i) (gs i))]

end Cut

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagProjSpecialDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem comap_C_pointIdeal {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by
  ext a
  simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
    MvPolynomial.algebraMap_apply, C_eq_zero, Submodule.mem_bot]
  exact ⟨fun ha => h (by rw [ha, map_zero]), fun ha => by rw [ha, map_zero]⟩

theorem specialIdeal_dim_add_one_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by
  set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  have e1 := (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 := (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P
    (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) := h0
    rw [hPC, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle

theorem relDim_specialIdeal_lt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} (P : Ideal (MRing ι O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MRing ι O) = ⊥) (n : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim (specialIdeal P) < ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have h := (specialIdeal_dim_add_one_le hϖ P hPC).trans hdim
  unfold FieldNumbers.relDim specialIdeal
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
    P.map (MvPolynomial.map (IsLocalRing.residue O))) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n + Fintype.card K := by exact_mod_cast h'
      have hlt : (m : ℤ) - Fintype.card K < n := by omega
      change (((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) < (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact_mod_cast hlt

theorem SegreFlagProjSpecialDim.proof (hDim : PrimeDimLeTrdeg.Statement) (hTr : FlagProjTrdegLe.Statement) :
    SegreFlagProjSpecialDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _
    e t ht k hk
  obtain ⟨h1, h2⟩ := hTr O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk

  have hVt : (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat = ((d + Fintype.card K : ℕ) : ℕ∞) := by
    have h := DvrConeDimTrdeg.proof O K ι _ hV.multiProj hV.noTorsion
    rw [hV.dim] at h
    have h0 : ((d + 1 + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      exact_mod_cast h
    have h' : ((d + Fintype.card K : ℕ) : ℕ∞) + 1 = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      rw [← h0]; push_cast; ring
    exact (WithTop.add_right_cancel ENat.one_ne_top h').symm

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      simp [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, ha]
    rwa [hV.noTorsion, Ideal.mem_bot] at hmem
  have hOΦ : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    exact (algebraMap Ω Φ).injective.comp hOΩ

  have key : ∀ {K' : Type} [Fintype K'] [DecidableEq K'] (j : K' ↪ Option (Option K)), Fintype.card K' = Fintype.card K + 1 →
      Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
          pointIdeal O (flagProjPt j y w e φ φ' t k)) ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt j y w e φ φ' t k))) <
        ((d + k : ℕ) : WithBot (WithTop ℤ)) := by
    intro K' _ _ j hcard hle
    have hP : (pointIdeal O (flagProjPt j y w e φ φ' t k)).IsPrime := by
      unfold pointIdeal
      exact RingHom.ker_isPrime _
    have hPC := comap_C_pointIdeal hOΦ (flagProjPt j y w e φ φ' t k)
    refine relDim_specialIdeal_lt hϖ _ hPC (d + k) ((hDim O K' _ _ hP hPC).trans ?_)
    have ht : Cardinal.toENat _ ≤ Cardinal.toENat _ := OrderHomClass.mono Cardinal.toENat hle
    simp only [map_add, map_natCast, hVt] at ht
    have : ((Algebra.trdeg O (MRing (fun o => bundleIdx (bundleIdx ι M) M' (j o)) O ⧸
        pointIdeal O (flagProjPt j y w e φ φ' t k))).toENat + 1 : ℕ∞) ≤ ((d + k + Fintype.card K' : ℕ) : ℕ∞) := by
      rw [hcard]
      calc _ ≤ ((d + Fintype.card K : ℕ) : ℕ∞) + (k : ℕ∞) + 1 := by gcongr
        _ = _ := by push_cast; ring
    exact_mod_cast this
  exact ⟨key Function.Embedding.some (by simp) h1, key secondFactorBlocks (by simp) h2⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPairValueIndependence

theorem polyNum_congr {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F κ)) (n : ℕ)
    {m : ℕ} {deg₁ deg₂ : Fin m → K → ℤ} (P : MvPolynomial (Fin m) ℤ)
    (h : ∀ s ∈ P.vars, deg₁ s = deg₂ s) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₁ P = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₂ P := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hm : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₁ μ = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₂ μ := by
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
    congr 1
    funext s
    by_cases hs : μ s = 0
    · simp [hs]
    · rw [h s ((mem_vars_iff_mem_support s).mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hs⟩)]
  exact congrArg (fun l : List (K → ℤ) => P.coeff μ * if h : l.length = n then
    I W n (fun j => l.get (Fin.cast h.symm j)) else 0) hm

theorem not_mem_vars_divDiff_castAdd {N r : ℕ} (i : Fin N) (j : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    Fin.natAdd (N + r) (Fin.natAdd N j) ∉ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
      (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)).vars := by
  classical
  intro hs
  obtain ⟨μ, hμ, hsμ⟩ := (mem_vars_iff_mem_support _).mp hs
  have he : Function.Injective
      (finSumFinEquiv.symm : Fin ((N + r) + (N + r)) → Fin (N + r) ⊕ Fin (N + r)) :=
    finSumFinEquiv.symm.injective
  have h1 : Finsupp.mapDomain finSumFinEquiv.symm μ ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).support := by
    rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ hμ
  have h2 : finSumFinEquiv.symm (Fin.natAdd (N + r) (Fin.natAdd N j)) ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).vars := by
    refine (mem_vars_iff_mem_support _).mpr ⟨_, h1, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply he]
    exact Finsupp.mem_support_iff.mp hsμ
  rw [finSumFinEquiv_symm_apply_natAdd, plainPolynomialPairNumber.rename_divDiff_castAdd_mul] at h2
  rcases Finset.mem_union.mp (vars_mul _ _ h2) with h3 | h3
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    rcases t with t | t
    · exact Sum.inl_ne_inr ht
    · simp only [Sum.map_inr, Sum.inr.injEq] at ht
      have := congrArg Fin.val ht
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    exact Sum.inl_ne_inr ht

theorem proof (hPlain : FlagPlainValueIndependence.Statement)
    (hFur : flagFurtherTerm_independent.Statement) : FlagPairValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ
  classical
  have hz : ∀ J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (IsLocalRing.ResidueField O) ι) → ℤ,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J 0 = 0 := fun J => Finsupp.sum_zero_index
  have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 :=
    sub_self _
  have split : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E',
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ.deg y) (Fin.append φ.deg' y') (Fin.append φ.f f) (Fin.append φ.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                  (Fin.append φ.deg y) (Fin.append φ.deg' y) (Fin.append φ.f fun _ => 1)
                                  (Fin.append φ.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) +
          ∑ l : Fin r, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
            (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
              (Fin.append (Fin.append φ.deg y) (Fin.append φ.deg' y'))
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) := by
    intro φ
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, h0, hz, Finset.sum_const_zero, add_zero]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    refine congrArg (fun J => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J _) (funext fun W => ?_)
    refine polyNum_congr I W d _ fun s hs => ?_
    induction s using Fin.addCases with
    | left a => simp only [Fin.append_left]
    | right b =>
      induction b using Fin.addCases with
      | left a => simp only [Fin.append_right, Fin.append_left]
      | right j => exact absurd hs (not_mem_vars_divDiff_castAdd i j G Q)
  rw [split φ₁, split φ₂, hPlain O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y c Q hc hGc hQ]
  congr 1
  exact Finset.sum_congr rfl fun l _ =>
    hFur O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ l

end FlagPairValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

