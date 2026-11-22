import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPrimeQuasiFiniteSheets
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace PrimeQuasiFiniteSheets

variable {n d : ℕ}

theorem eval_pullback (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (g : MvPolynomial (Fin d) ℂ) :
    eval x (ComplexSets.pullback A g) = eval (A.mulVec x) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem sheets_of_not_injective (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hinj : ¬ Function.Injective (ComplexSets.projHom Q A)) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y c ≠ 0 →
      ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
        IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
        ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
          Function.Injective (fun j => s j y') ∧
          ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by
  rw [injective_iff_map_eq_zero] at hinj
  push Not at hinj
  obtain ⟨g, hg, hg0⟩ := hinj
  have hQ : ComplexSets.pullback A g ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp hg
  have hempty : ∀ y' : Fin d → ℂ, eval y' g ≠ 0 → ComplexSets.fibre Q A y' = ∅ := by
    intro y' hy'
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, rfl⟩
    exact hy' (by rw [← eval_pullback]; exact hx _ hQ)
  refine ⟨g, hg0, fun y hy => ⟨{w | eval w g ≠ 0}, 0, fun j => j.elim0,
    isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const, hy, fun j => j.elim0,
    fun y' hy' => ⟨fun j => j.elim0, fun i => i.elim0, ?_⟩⟩⟩
  rw [hempty y' hy']
  exact Set.empty_subset _

theorem differentiableOn_polyEval (P : Polynomial (MvPolynomial (Fin d) ℂ)) {ψ : (Fin d → ℂ) → ℂ}
    {U : Set (Fin d → ℂ)} (hψ : DifferentiableOn ℂ ψ U) :
    DifferentiableOn ℂ (fun w => (P.map (eval w)).eval (ψ w)) U := by
  have h : (fun w => (P.map (eval w)).eval (ψ w)) =
      fun w => ∑ i ∈ Finset.range (P.natDegree + 1), eval w (P.coeff i) * ψ w ^ i := by
    funext w
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [h]
  exact DifferentiableOn.fun_sum fun i _ =>
    ((AnalyticOnNhd.eval_mvPolynomial (P.coeff i)).differentiableOn.mono (Set.subset_univ _)).mul
      (hψ.pow i)

theorem card_roots_toFinset {p : Polynomial ℂ} (hp : p.Separable) : p.roots.toFinset.card = p.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hp), IsAlgClosed.card_roots_eq_natDegree]

theorem sheets_of_parametrisation (hSR : ComplexSets.SimpleRootBranch.Statement)
    {Q : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
    (S : Fin n → Polynomial (MvPolynomial (Fin d) ℂ))
    (hP : ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
      (m.map (eval y)).natDegree = m.natDegree ∧ (m.map (eval y)).Separable ∧
      (∀ x ∈ ComplexSets.fibre Q A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
        ∀ j, eval y Δ * x j = ((S j).map (eval y)).eval (∑ k, c k * x k)) ∧
      ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ ComplexSets.fibre Q A y, ∑ j, c j * x j = τ)
    (y : Fin d → ℂ) (hy : eval y Δ ≠ 0) :
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
        Function.Injective (fun j => s j y') ∧
        ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by
  have hcnt : ∀ w : Fin d → ℂ, eval w Δ ≠ 0 → (m.map (eval w)).roots.toFinset.card = m.natDegree := by
    intro w hw
    obtain ⟨hd, hs, -, -⟩ := hP w hw
    rw [card_roots_toFinset hs, hd]
  obtain ⟨-, hsep, -, -⟩ := hP y hy
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (eval y)).roots.toFinset := ⟨_, rfl⟩
  let τ : Fin R.card → ℂ := fun j => (R.equivFin.symm j : ℂ)
  have hRroot : ∀ z ∈ R, (m.map (eval y)).IsRoot z := by
    intro z hz
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots'] at hz
    exact hz.2
  have hτroot : ∀ j, (m.map (eval y)).IsRoot (τ j) := fun j => hRroot _ (R.equivFin.symm j).2
  have hτinj : Function.Injective τ := fun i j h => R.equivFin.symm.injective (Subtype.ext h)
  have hder : ∀ j, (m.map (eval y)).derivative.eval (τ j) ≠ 0 := by
    intro j
    have h := hsep.aeval_derivative_ne_zero (x := τ j) (by
      rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]; exact hτroot j)
    rwa [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at h
  choose U B ψ hU hyU hBo hτB hψd hψy hψ using fun j => hSR d m y (τ j) (hτroot j) (hder j)
  let W : Fin R.card → Fin R.card → Set (Fin d → ℂ) :=
    fun j k => U j ∩ U k ∩ {w | j ≠ k → ψ j w ≠ ψ k w}
  have hWo : ∀ j k, IsOpen (W j k) := by
    intro j k
    by_cases hjk : j = k
    · have : W j k = U j ∩ U k := by
        ext w
        simp [W, hjk]
      rw [this]
      exact (hU j).inter (hU k)
    · have : W j k = (U j ∩ U k) ∩ (fun w => ψ j w - ψ k w) ⁻¹' {0}ᶜ := by
        ext w
        simp [W, hjk, sub_eq_zero]
      rw [this]
      exact ContinuousOn.isOpen_inter_preimage
        (((hψd j).mono Set.inter_subset_left).sub ((hψd k).mono Set.inter_subset_right)).continuousOn
        ((hU j).inter (hU k)) isOpen_compl_singleton
  let V : Set (Fin d → ℂ) := {w | eval w Δ ≠ 0} ∩ ⋂ j, ⋂ k, W j k
  have hVo : IsOpen V := (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const).inter
    (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => hWo j k)
  have hyV : y ∈ V := by
    refine ⟨hy, Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun k => ⟨⟨hyU j, hyU k⟩, fun hjk => ?_⟩⟩
    rw [hψy j, hψy k]
    exact fun h => hjk (hτinj h)
  have hVU : ∀ w ∈ V, ∀ j, w ∈ U j := fun w hw j => (Set.mem_iInter.1 (Set.mem_iInter.1 hw.2 j) j).1.1
  have hVd : ∀ w ∈ V, ∀ j k, j ≠ k → ψ j w ≠ ψ k w :=
    fun w hw j k => (Set.mem_iInter.1 (Set.mem_iInter.1 hw.2 j) k).2
  let s : Fin R.card → (Fin d → ℂ) → Fin n → ℂ :=
    fun j w i => ((S i).map (eval w)).eval (ψ j w) * (eval w Δ)⁻¹
  refine ⟨V, R.card, s, hVo, hyV, fun j => ?_, fun y' hy' => ?_⟩
  · rw [differentiableOn_pi]
    intro i
    have hΔd : DifferentiableOn ℂ (fun w : Fin d → ℂ => eval w Δ) V :=
      (AnalyticOnNhd.eval_mvPolynomial Δ).differentiableOn.mono (Set.subset_univ _)
    exact (differentiableOn_polyEval (S i) ((hψd j).mono fun w hw => hVU w hw j)).mul
      (hΔd.inv fun w (hw : w ∈ V) => hw.1)
  obtain ⟨-, hsep', hfib', hroot'⟩ := hP y' hy'.1
  have hψroot : ∀ j, (m.map (eval y')).IsRoot (ψ j y') := fun j =>
    ((hψ j y' (hVU y' hy' j)).2 _ (hψ j y' (hVU y' hy' j)).1).2 rfl
  have hrec : ∀ x ∈ ComplexSets.fibre Q A y', ∀ j, ∑ k, c k * x k = ψ j y' → s j y' = x := by
    intro x hx j hj
    funext i
    simp only [s]
    rw [← hj, ← (hfib' x hx).2 i, mul_comm, inv_mul_cancel_left₀ hy'.1]
  have hmem : ∀ j, ∃ x ∈ ComplexSets.fibre Q A y', ∑ k, c k * x k = ψ j y' ∧ s j y' = x := by
    intro j
    obtain ⟨x, hx, hxl⟩ := hroot' _ (hψroot j)
    exact ⟨x, hx, hxl, hrec x hx j hxl⟩
  refine ⟨fun j => ?_, fun j k hjk => ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, -, hsx⟩ := hmem j
    rw [hsx]
    exact hx
  · obtain ⟨x, hx, hxl, hsx⟩ := hmem j
    obtain ⟨x', hx', hxl', hsx'⟩ := hmem k
    by_contra hne
    apply hVd y' hy' j k hne
    have hxx : x = x' := by
      rw [← hsx, ← hsx']
      exact hjk
    rw [← hxl, ← hxl', hxx]
  · have hinjψ : Function.Injective (fun j => ψ j y') := fun j k h =>
      by_contra fun hne => hVd y' hy' j k hne h
    have hsub : Finset.univ.image (fun j => ψ j y') ⊆ (m.map (eval y')).roots.toFinset := by
      intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hsep'.ne_zero, hψroot j⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injective _ hinjψ, Finset.card_univ, Fintype.card_fin, hcnt y' hy'.1,
        hR, hcnt y hy])
    have hl : ∑ k, c k * x k ∈ (m.map (eval y')).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hsep'.ne_zero, (hfib' x hx).1⟩
    rw [← heq] at hl
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hl
    exact ⟨j, hrec x hx j hj.symm⟩

end PrimeQuasiFiniteSheets

theorem PrimeQuasiFiniteSheets.proof (hFF : FiniteFibresDimLe.Statement)
    (hDP : DominantPrimitiveFibres.Statement) (hSR : ComplexSets.SimpleRootBranch.Statement) :
    PrimeQuasiFiniteSheets.Statement := by
  intro n d Q A hQ hfin
  by_cases hinj : Function.Injective (ComplexSets.projHom Q A)
  · obtain ⟨c, m, Δ, S, hΔ, hP⟩ := hDP n d Q A hQ (hFF n d Q A hQ hfin) hinj
    exact ⟨Δ, hΔ, PrimeQuasiFiniteSheets.sheets_of_parametrisation hSR c m Δ S hP⟩
  · exact PrimeQuasiFiniteSheets.sheets_of_not_injective Q A hinj

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughTwoPointsTrdeg.proof (hT : TrdegAdjoinLe.Statement) : ThroughTwoPointsTrdeg.Statement := by
  intro K Ω _ _ n k _ _ _ hinj x c hcx y j hyj hprop hy
  let u : Fin k × Fin n → Ω := fun im => algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (X im)
  let z : Fin n → Ω := fun m => y m * (y j)⁻¹
  let x' : Fin n → Ω := fun m => algebraMap K Ω (x m)
  let c' : Fin n → Ω := fun m => algebraMap K Ω (c m)
  let s : Fin k → Ω := fun i => ∑ l, u (i, l) * x' l
  have hC : ∀ a : K, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (C a) = algebraMap K Ω a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k × Fin n) K) Ω, MvPolynomial.algebraMap_eq]

  have heq : ∀ i, ∑ m, u (i, m) * z m = s i * ∑ m, c' m * z m := by
    intro i
    have h := hy i
    simp only [genSubst, map_sub, map_mul, map_sum, hC] at h
    have h' : ∑ m, u (i, m) * y m = s i * ∑ m, c' m * y m := by
      rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [u, s, x', c']
      ring
    simp only [z, ← mul_assoc, ← Finset.sum_mul]
    rw [h']

  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcx
  have hx'p : x' p ≠ 0 := by simpa [x'] using hp
  obtain ⟨q, hD⟩ : ∃ q, x' p * z q - x' q * z p ≠ 0 := by
    by_contra h
    push Not at h
    apply hprop (y j * (z p * (x' p)⁻¹))
    funext m
    have hm := h m
    simp only [z, x'] at hm hx'p ⊢
    have hm2 : (algebraMap K Ω (x p) * y m - algebraMap K Ω (x m) * y p) * (y j)⁻¹ = 0 := by
      rw [← hm]; ring
    have hm3 := (mul_eq_zero.1 hm2).resolve_right (inv_ne_zero hyj)
    have e : y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        y p * algebraMap K Ω (x m) * (algebraMap K Ω (x p))⁻¹ := by
      rw [show y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        (y j * (y j)⁻¹) * (y p * algebraMap K Ω (x m)) * (algebraMap K Ω (x p))⁻¹ by ring,
        mul_inv_cancel₀ hyj, one_mul]
    rw [e, eq_mul_inv_iff_mul_eq₀ hx'p]
    linear_combination hm3
  set D := x' p * z q - x' q * z p with hDdef
  have hqp : q ≠ p := by
    rintro rfl
    exact hD (by simp [D])
  let E := (Finset.univ.erase p).erase q
  have hqE : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨hqp, Finset.mem_univ q⟩
  have hsplit : ∀ g : Fin n → Ω, ∑ m, g m = g p + g q + ∑ m ∈ E, g m := fun g => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hqE, add_assoc]

  let t : Fin k ⊕ (Fin k × E) → Ω := fun a => Sum.elim s (fun b => u (b.1, b.2.1)) a
  let B := Algebra.adjoin K (Set.range z ∪ Set.range t)
  have hzB : ∀ m, z m ∈ B := fun m => Algebra.subset_adjoin (Or.inl ⟨m, rfl⟩)
  have hsB : ∀ i, s i ∈ B := fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)
  have huB : ∀ i, ∀ m ∈ E, u (i, m) ∈ B := fun i m hm =>
    Algebra.subset_adjoin (Or.inr ⟨Sum.inr (i, ⟨m, hm⟩), rfl⟩)
  have hKB : ∀ a : K, algebraMap K Ω a ∈ B := fun a => B.algebraMap_mem a
  have hczB : ∑ m, c' m * z m ∈ B := B.sum_mem fun m _ => B.mul_mem (hKB _) (hzB m)
  have hDB : D ∈ B := B.sub_mem (B.mul_mem (hKB _) (hzB q)) (B.mul_mem (hKB _) (hzB p))
  have halg : ∀ v, D * v ∈ B → IsAlgebraic B v := fun v hv =>
    IsAlgebraic.of_mul (y := D) (mem_nonZeroDivisors_of_ne_zero hD)
      (isAlgebraic_algebraMap (⟨D, hDB⟩ : B)) (isAlgebraic_algebraMap (⟨D * v, hv⟩ : B))
  have hw : ∀ im, IsAlgebraic B (u im) := by
    rintro ⟨i, m⟩
    have hSx : ∑ m ∈ E, u (i, m) * x' m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hKB _)
    have hSz : ∑ m ∈ E, u (i, m) * z m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hzB m)
    have e1 := hsplit (fun m => u (i, m) * x' m)
    have e2 := hsplit (fun m => u (i, m) * z m)
    rw [heq i] at e2
    change s i = _ at e1
    by_cases hmp : m = p
    · subst hmp
      refine halg _ ?_
      have : D * u (i, m) = z q * (s i - ∑ m ∈ E, u (i, m) * x' m) -
          x' q * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) := by
        rw [hDdef]; linear_combination -z q * e1 + x' q * e2
      rw [this]
      exact B.sub_mem (B.mul_mem (hzB q) (B.sub_mem (hsB i) hSx))
        (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
    by_cases hmq : m = q
    · subst hmq
      refine halg _ ?_
      have : D * u (i, m) = x' p * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) -
          z p * (s i - ∑ m ∈ E, u (i, m) * x' m) := by
        rw [hDdef]; linear_combination -x' p * e2 + z p * e1
      rw [this]
      exact B.sub_mem (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
        (B.mul_mem (hzB p) (B.sub_mem (hsB i) hSx))
    exact isAlgebraic_algebraMap
      (⟨u (i, m), huB i m (Finset.mem_erase.2 ⟨hmq, Finset.mem_erase.2 ⟨hmp, Finset.mem_univ m⟩⟩)⟩ : B)
  have hle := hT K Ω (Set.range z) (Fin k ⊕ (Fin k × E)) t (Fin k × Fin n) u hw

  have hadj : Algebra.adjoin K (Set.range u) = (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω).range := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hinj' : Function.Injective (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω) := hinj
  have htr : Algebra.trdeg K (Algebra.adjoin K (Set.range u)) = ((k * n : ℕ) : Cardinal) := by
    rw [hadj, ← (AlgEquiv.ofInjective _ hinj').trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have hcard : Fintype.card (Fin k ⊕ (Fin k × E)) = k + k * (n - 2) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hqE, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [htr, hcard] at hle
  have hn : 2 ≤ n := by
    have := Fin.val_ne_of_ne hqp
    omega
  rcases lt_or_ge (Algebra.trdeg K (Algebra.adjoin K (Set.range z))) Cardinal.aleph0 with hfin | hinf
  · obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hd] at hle ⊢
    norm_cast at hle ⊢
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left] at hle
    nlinarith
  · exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans hinf

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibreAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def matGauss {m n : ℕ} (π : Fin m → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2))

def ConeFibreAverage.Statement : Prop :=
  ∀ n m : ℕ, ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
    ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J →
      (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
        ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
          K * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J}

theorem ConeFibreAverage.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w ≠ ⊤ := by
  obtain ⟨hJ, hfib⟩ := ConeMassOfFibre.hypotheses_inhabited
  refine ⟨hJ, ?_⟩
  filter_upwards [hfib] with π hπ
  filter_upwards [hπ] with w hw
  rw [hw]
  exact ENat.natCast_ne_top 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaIntegral.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
    ∀ h : EuclideanSpace ℂ (Fin n) → ℝ≥0∞,
      ∫⁻ y in graphPt e F '' A, h y ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ x in A, h (graphPt e F x) * ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionCycleReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, linForm u ∉ P) →
      fundCycle (J ⊔ Ideal.span {linForm u}) = ∑ P ∈ (fundCycle J).support, divCycle P u

end GroundTheory.Heights₂.Heights
end

