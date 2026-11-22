import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ _
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLastZeroInclusion
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

open GlobalTheory.Branching.AddColumn in

theorem exists_eq_incl_of_last_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  intro K _ _ n ν hν x hx
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢
  obtain ⟨x', rfl⟩ := exists_rename_eq_of_vars_subset_range x _ hinj (by
    rintro ⟨a, s⟩ hv
    induction s using Fin.lastCases with
    | cast s => exact ⟨(a, s), rfl⟩
    | last =>
      exfalso
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h := congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)
      rw [hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff] at h
      have h2 := h _ hvd
      simp [colW] at h2
      exact Finsupp.mem_support_iff.1 hvd h2)
  refine ⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩
  · rw [← coeff_rename_mapDomain _ hinj] at hu
    funext i
    rw [← (weight_mapDomain (n + 1) n u).1, hx.1 hu]
  · have h := hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)
    rw [colAddGen_rename_castSucc] at h
    apply rename_injective _ (Option.map_injective hinj)
    rw [h, rename_rename, rename_rename]
    rfl

end GlobalTheory.BrCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs, hs, map_add, rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylOrthonormalBasisValuesAtUnitarySumSqLeOn
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DualWeyl.EvBound

theorem sum_sq_norm_evalAt_onBasis_eq_one (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (g : UN n) :
    ∑ i, ‖evalAt g.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := GlobalTheory.DualWeyl.Repro.exists_repr la
  have h1 := GlobalTheory.DualWeyl.Repro.normSq_repr hla hk
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  let u : UN n := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
  rw [← h1, ← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← he, inner_toSpace, GlobalTheory.DualWeyl.Repro.form_rhoU_repr hk]
  rfl

theorem sum_sq_norm_evalAt_onBasis_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n,
    ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 :=
  fun n la hla u => (sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le

end GlobalTheory.DualWeyl.EvBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSpannedByInterlacing
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCompare.Surj

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

variable {K : Type} [Field K]

theorem rowAct_initMinor_mem {r m s : ℕ} (g : Matrix (Fin r) (Fin r) K) (I : Fin s → Fin r) (hs : s ≤ m) :
    rowAct K g (initMinor K I hs) ∈ Submodule.span K (Set.range fun J : Fin s → Fin r => initMinor K J hs) := by
  classical
  have h1 : rowAct K g (initMinor K I hs) =
      (Matrix.detRowAlternating (n := Fin s) (R := MvPolynomial (Fin r × Fin m) K)).toMultilinearMap
        (fun p => ∑ b : Fin r, (C (g (I p) b) : MvPolynomial (Fin r × Fin m) K) •
          fun q : Fin s => (X (b, Fin.castLE hs q) : MvPolynomial (Fin r × Fin m) K)) := by
    unfold initMinor
    rw [AlgHom.map_det]
    change Matrix.det _ = Matrix.det _
    congr 1
    ext p q : 2
    simp [rowAct, Finset.sum_apply]
  rw [h1, MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun J _ => ?_
  rw [MultilinearMap.map_smul_univ, ← map_prod, smul_eq_mul, ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)

theorem prod_mem_span_range {A ι : Type} [CommRing A] [Algebra K A] [Fintype ι] {J : ι → Type}
    (f : ∀ i, J i → A) (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (Set.range (f i))) :
    ∏ i, x i ∈ Submodule.span K (Set.range fun t : ∀ i, J i => ∏ i, f i (t i)) := by
  classical
  refine Submodule.span_mono ?_ (GlobalTheory.OrbitSpan.prod_mem_span_prod Finset.univ _ x hx)
  intro y hy
  rw [Set.mem_fintype_prod] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  choose t ht using hz
  exact ⟨t, Finset.prod_congr rfl fun i _ => ht i⟩

theorem rowAct_piGen_mem {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) (g : Matrix (Fin n) (Fin n) K)
    (t : Gen lam sg) : rowAct K g (piGen K lam sg t) ∈ Submodule.span K (Set.range (piGen K lam sg)) := by
  unfold piGen
  simp only [map_mul, map_prod]
  have h1 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (aNum lam sg i) => rowAct_initMinor_mem g (t.1 i k) (Nat.succ_le_of_lt i.isLt)
  have h2 := prod_mem_span_range (K := K) _ _ fun i : Fin n => prod_mem_span_range _ _
    fun k : Fin (bNum lam sg i) => rowAct_initMinor_mem g (t.2 i k) i.isLt.le
  have h3 := Submodule.mul_mem_mul h1 h2
  rw [Submodule.span_mul_span] at h3
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩
  exact ⟨(u, v), rfl⟩

theorem prod_shift {A : Type} [CommMonoid A] {n : ℕ} (D : ℕ → A) (h0 : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    have h1 : nuNext b (Fin.last m) = 0 := by simp [nuNext]
    rw [h1, pow_zero, mul_one, Fin.val_zero, h0, one_pow, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 : nuNext b i.castSucc = b i.succ := by
      unfold nuNext
      rw [dif_pos (by simp)]
      rfl
    rw [h2]
    rfl

theorem aNum_add_bNext {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) (i : Fin n) :
    aNum lam sg i + nuNext (bNum lam sg) i = sg.natW i - nuNext sg.natW i := by
  have hn : 0 < n := Fin.pos i
  unfold nuNext
  simp only [aNum, bNum, DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have h1 := (h i).1
  split_ifs with hi
  · have h2 := (h ⟨i.val + 1, hi⟩).2
    have h3 : (⟨i.val + 1, hi⟩ : Fin n).castSucc = i.succ := rfl
    have h4 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, hi⟩ := sg.anti (by simp [Fin.le_def]; omega)
    rw [h3] at h2 ⊢
    omega
  · have h2 := he i (by omega)
    have h3 : i.succ = Fin.last n := Fin.ext (by simp; omega)
    have h4 : (⟨n - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [h3, h4]
    omega

theorem hw_eq_piGen {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n} (h : Interlace lam sg)
    (he : EqualLast lam sg) :
    hw K le_rfl sg.natW = piGen K lam sg
      (fun i _ => Fin.castLE (Nat.succ_le_of_lt i.isLt), fun i _ => Fin.castLE i.isLt.le) := by
  let D : ℕ → MvPolynomial (Fin n × Fin n) K := fun k => if hk : k ≤ n then lpMinor K k hk hk else 1
  have hD : ∀ k (hk : k ≤ n), initMinor K (Fin.castLE hk) hk = D k := fun k hk => by
    simp only [D, dif_pos hk]; rfl
  have hD' : ∀ k (hk : k ≤ n), lpMinor K k hk hk = D k := hD
  have h0 : D 0 = 1 := by
    rw [← hD' 0 (Nat.zero_le _)]; simp [lpMinor]
  unfold piGen hw
  simp only [hD, hD', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_shift D h0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, aNum_add_bNext h he]

theorem dualWeyl_le_span_piGen (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1))
    (sg : DomWeight n) (h : Interlace lam sg) (he : EqualLast lam sg) :
    dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (piGen K lam sg)) := by
  refine (GlobalTheory.OrbitSpan.dualWeyl_le_span_orbit K le_rfl sg.natW (Formalism.L2.Col.natW_anti sg)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  beta_reduce
  rw [hw_eq_piGen h he]
  exact rowAct_piGen_mem lam sg _ _

end GlobalTheory.BrCompare.Surj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKronecker
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem evalAt_mul_intVec {n : ℕ} (la : Fin n → ℕ) {K S : Type} [Field K] [CharZero K] [CommRing S] (φ : K →+* S)
    (g : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) S) (j : Idx la) :
    GlobalTheory.DualWeyl.evalAt (g.map φ * y) (map (Int.castRingHom S) (intVec la j)) =
      ∑ i, φ (rhoMat la g i j) * GlobalTheory.DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  have h1 : (rho la K gᵀ (basis la K j) : Pol n K) = ∑ i, rhoMat la g i j • (basis la K i : Pol n K) := by
    have h := (basis la K).sum_repr (rho la K gᵀ (basis la K j))
    conv_lhs => rw [← h]
    simp only [Submodule.coe_sum, Submodule.coe_smul, rhoMat, LinearMap.toMatrix_apply]
  have hmap : ∀ i, map φ (basis la K i : Pol n K) = map (Int.castRingHom S) (intVec la i) := by
    intro i
    rw [coe_basis, map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom S)]
  rw [coe_rho, Matrix.transpose_transpose] at h1
  rw [← hmap j, ← evalAt_rowAct, ← GlobalTheory.NabStab.map_rowAct, coe_basis, ← coe_basis, h1]
  simp only [map_sum, map_smul, smul_eq_C_mul, map_mul, map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmap i]
  simp [GlobalTheory.DualWeyl.evalAt]

theorem tval_translate : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  intro T _ _ N la K S _ _ _ φ x g y
  unfold tval
  simp only [evalAt_mul_intVec, Finset.prod_univ_sum]
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  first | (exact @GlobalTheory.HomFixUniv.eq_of_proport) | (exact GlobalTheory.HomFixUniv.eq_of_proport) | (intros; apply GlobalTheory.HomFixUniv.eq_of_proport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTvalInvertible
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoordVanish

theorem coeff_eq_zero_of_evalAt {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] (c : Idx la → K)
    (h : ∀ y : Matrix (Fin n) (Fin n) K, y.det ≠ 0 →
      ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) = 0) : c = 0 := by
  classical
  set Q : Pol n K := ∑ i, c i • map (Int.castRingHom K) (intVec la i) with hQ
  have hQe : ∀ y : Matrix (Fin n) (Fin n) K,
      DualWeyl.evalAt y Q = ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) := by
    intro y
    simp [hQ, map_sum, smul_eq_mul]
  set D : Pol n K := (Matrix.of fun a b : Fin n => (X (a, b) : Pol n K)).det with hD
  have hDe : ∀ y : Matrix (Fin n) (Fin n) K, DualWeyl.evalAt y D = y.det := by
    intro y
    rw [hD, AlgHom.map_det]
    congr 1
    ext a b
    simp
  have hev : ∀ (v : Fin n × Fin n → K) (p : Pol n K),
      eval v p = DualWeyl.evalAt (Matrix.of fun a b => v (a, b)) p := by
    intro v p
    simp [DualWeyl.evalAt, aeval_eq_eval]
  have hQD : Q * D = 0 := by
    refine MvPolynomial.funext fun v => ?_
    rw [hev, map_mul, hDe, map_zero]
    by_cases hd : (Matrix.of fun a b => v (a, b)).det = 0
    · rw [hd, mul_zero]
    · rw [hQe, h _ hd, zero_mul]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hDe 1
    rw [h0, map_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hQD).resolve_right hD0
  funext i
  exact Fintype.linearIndependent_iff.mp (intVec_spec la K).1 c hQ0 i

theorem eq_zero_of_prod {T : Type} [Fintype T] [DecidableEq T] {ι : T → Type} [∀ t, Fintype (ι t)]
    {A : T → Type} {K : Type} [Field K] (g : ∀ t, ι t → A t → K) (a0 : ∀ t, A t)
    (H : ∀ t (c : ι t → K), (∀ b : A t, ∑ i, c i * g t i b = 0) → c = 0)
    (x : (∀ t, ι t) → K) (hx : ∀ a : ∀ t, A t, ∑ I, x I * ∏ t, g t (I t) (a t) = 0) : x = 0 := by
  classical
  have key : ∀ S : Finset T, ∀ x : (∀ t, ι t) → K,
      (∀ a : ∀ t, A t, ∑ I, x I * ∏ t ∈ S, g t (I t) (a t) = 0) →
      ∀ I : ∀ t, ι t, ∑ I' ∈ Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ S, I' t = I t), x I' = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx I
      simpa using hx a0
    | insert s S hs IH =>
      intro x hx I
      have step : ∀ i : ι s, ∀ a : ∀ t, A t,
          ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t) = 0 := by
        intro i a
        have hc := H s (fun i => ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t)) (fun b => by
          have h1 := hx (Function.update a s b)
          have h2 : ∀ I' : ∀ t, ι t, ∏ t ∈ S, g t (I' t) (Function.update a s b t) = ∏ t ∈ S, g t (I' t) (a t) := by
            intro I'
            refine Finset.prod_congr rfl fun t ht => ?_
            have : t ≠ s := fun h => hs (h ▸ ht)
            rw [Function.update_of_ne this]
          simp only [Finset.prod_insert hs, Function.update_self, h2] at h1
          refine Eq.trans ?_ h1
          simp only [Finset.sum_mul, ite_mul, zero_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => ?_
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          ring)
        exact congrFun hc i
      have h3 := IH _ (step (I s)) I
      rw [Finset.sum_filter] at h3
      rw [Finset.sum_filter]
      refine Eq.trans (Finset.sum_congr rfl fun I' _ => ?_) h3
      simp only [Finset.forall_mem_insert]
      by_cases h4 : I' s = I s <;> by_cases h5 : ∀ t ∈ S, I' t = I t <;> simp [h4, h5]
  funext I
  have h := key Finset.univ x (by simpa using hx) I
  have h6 : Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ (Finset.univ : Finset T), I' t = I t) = {I} := by
    ext I'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, forall_const]
    exact ⟨fun h => funext h, fun h t => h ▸ rfl⟩
  rw [h6, Finset.sum_singleton] at h
  exact h

theorem eq_zero_of_tval_invertible : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ)
    (K : Type) [Field K] [CharZero K] (x : TIdx la → K),
    (∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → tval la x y = 0) → x = 0 := by
  intro T _ _ N la K _ _ x hx
  exact eq_zero_of_prod (ι := fun t => Idx (la t))
    (A := fun t => {M : Matrix (Fin (N t)) (Fin (N t)) K // M.det ≠ 0})
    (fun t i M => DualWeyl.evalAt M.1 (map (Int.castRingHom K) (intVec (la t) i))) (fun t => ⟨1, by simp⟩)
    (fun t c hc => coeff_eq_zero_of_evalAt (la t) K c fun y hy => hc ⟨y, hy⟩) x
    (fun a => hx (fun t => (a t).1) fun t => (a t).2)

end GlobalTheory.CoordVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisStableTorsionFamilyKerStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisStable_torsion_family_ker : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (T : ι → ℂ), Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 ∧ Fintype.card ι = 2 * (N - 1) ∧ Stable L F T ∧ ∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice := by
  first | exact @GlobalTheory.CMModel.exists_stable_family_ker | exact GlobalTheory.CMModel.exists_stable_family_ker | (intros; apply GlobalTheory.CMModel.exists_stable_family_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharactersStatement
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rapid_superposition_characters' : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  first | exact @GlobalTheory.JSW.exists_rapid_superposition_characters | exact GlobalTheory.JSW.exists_rapid_superposition_characters | (intros; apply GlobalTheory.JSW.exists_rapid_superposition_characters <;> assumption)
end

