import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0506
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BranchingRankTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltration
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR.CmpFil

theorem amulG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ∀ o o', ι' (o * o') = ι' o * ι' o') (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (x y : OD l O) (v : V ⊗[ℚ_[l]] R) : A (x * y) v = A x (A y v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [add_mul, map_add, AddMonoidHom.add_apply, hx, hx']
    | tmul o b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | add y y' hy hy' => simp only [mul_add, map_add, AddMonoidHom.add_apply, hy, hy']
      | tmul o' b' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hA, hA, hA, map_mul, mul_assoc, h1, mul_smul]

theorem aoneG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ι' 1 = 1) (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (v : V ⊗[ℚ_[l]] R) : A 1 v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c => rw [Algebra.TensorProduct.one_def, hA, map_one, one_mul, h1, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem amulL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (x y : OD l ↥(OL LL)) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A (x * y) v = A x (A y v) :=
  amulG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) (fun _ _ => rfl) (GlobalTheory.BKGal.JumpDR.cD Td) A hA x y v

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem aoneL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A 1 v = v :=
  aoneG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) rfl (GlobalTheory.BKGal.JumpDR.cD Td) A hA v

set_option maxHeartbeats 1000000 in
theorem coreG {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {W : Type} [AddCommGroup W] (A : OD l O →+ (W →+ W)) (Fil : ℤ → W → Prop)
    (amul : ∀ x y v, A (x * y) v = A x (A y v)) (aone : ∀ v, A 1 v = v)
    (hbij : Function.Bijective (A (ϖ.iD t K (fun _ => Ehat O K l e))))
    (hS : ∀ (y : W) (j : ℤ), Fil j y ↔ Fil (j + 1) (A (ϖ.iD t K (fun _ => Ehat O K l e)) y))
    (gB : ι → W) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (f : ι → W) (hf1 : ∀ i, A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i) = ∑ j, A (ϖ.iD t K (fun τ => y τ j i)) (gB j))
    (hspan : ∀ v, Fil 0 v ↔ ∃ d : ι → OD l O, v = ∑ i, A (d i) (f i))
    (hind : ∀ d : ι → OD l O, ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0)
    {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (g : Fin n → W)
    (hC : ∀ (s' : Fin n → ZMod a → Ahat O K l e) (c : ZMod a → ι → Ahat O K l e), (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD t K (s' k)) (g k) = ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j))
    (hE1 : ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i)
    (j : ℤ) :
    GlobalTheory.BKGal.JumpDR.InEhat O K l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ Fil j (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
  classical
  have hbijN : ∀ N : ℕ, Function.Bijective (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) := by
    intro N
    induction N with
    | zero =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ 0)) = id := funext fun v => by rw [pow_zero]; exact aone v
      rw [h0]; exact Function.bijective_id
    | succ N ih =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1))) = ⇑(A (ϖ.iD t K (fun _ => Ehat O K l e))) ∘ ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) :=
        funext fun v => by rw [pow_succ', amul]; rfl
      rw [h0]; exact hbij.comp ih
  have hSh : ∀ (N : ℕ) (y : W) (j : ℤ), Fil j y ↔ Fil (j + N) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by
    intro N
    induction N with
    | zero => intro y j; rw [pow_zero, aone, Nat.cast_zero, add_zero]
    | succ N ih =>
      intro y j
      have e1 : (j + ((N + 1 : ℕ) : ℤ)) = (j + N) + 1 := by push_cast; ring
      have e2 : A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1)) y = A (ϖ.iD t K (fun _ => Ehat O K l e)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by rw [pow_succ', amul]
      rw [e1, e2]
      exact (ih y j).trans (hS _ _)
  have Fb : ∀ (d : ι → OD l O) (kk : ℕ), Fil kk (∑ i, A (d i) (f i)) ↔ ∀ i, d i ∈ Ideal.span {(ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk} := by
    intro d kk
    constructor
    · intro hd
      obtain ⟨v', hv'⟩ := (hbijN kk).2 (∑ i, A (d i) (f i))
      have h0 : Fil 0 v' := (hSh kk v' 0).2 (by rw [hv', zero_add]; exact hd)
      obtain ⟨z, rfl⟩ := (hspan v').1 h0
      have h4 : ∑ i, A (d i - (ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk * z i) (f i) = 0 := by
        simp only [map_sub, AddMonoidHom.sub_apply, Finset.sum_sub_distrib, amul]
        rw [← map_sum, hv', sub_self]
      intro i
      have h5 := hind _ h4 i
      rw [sub_eq_zero] at h5
      rw [h5]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hd
      choose z hz using fun i => Ideal.mem_span_singleton'.1 (hd i)
      have h6 : ∑ i, A (d i) (f i) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk) (∑ i, A (z i) (f i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hz i, mul_comm, amul]
      have h7 := (hSh kk _ 0).1 ((hspan _).2 ⟨z, rfl⟩)
      rw [zero_add] at h7
      rw [h6]; exact h7
  have key : ∀ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), (∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
      A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) (∑ k, A (ϖ.iD t K (s k)) (g k)) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i) := by
    intro N x hx
    let s' : Fin n → ZMod a → Ahat O K l e := fun k => (fun _ => Ehat O K l e) ^ (N + β) * s k
    let c : ZMod a → ι → Ahat O K l e := fun τ j => ∑ i, y τ j i * x τ i
    have hw : ∀ τ i, GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N + β) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i
      simp only [GlobalTheory.BKGal.JumpDR.hsum, s', Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, Finset.mul_sum, mul_assoc]
    have hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i := by
      intro τ j
      simp only [c, map_sum, map_mul, hy, hx, hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hC' := hC s' c hc
    have h1 : ∑ k, A (ϖ.iD t K (s' k)) (g k) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + β)) (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [s', map_mul, map_pow]
      rw [amul]
    have h2' : ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) := by
      have h3 : ∀ j, (fun τ => c τ j) = ∑ i, (fun τ => x τ i) * (fun τ => y τ j i) := by
        intro j; funext τ; simp only [c, Finset.sum_apply, Pi.mul_apply, mul_comm]
      simp only [h3, map_sum, AddMonoidHom.finset_sum_apply, map_mul, amul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf1 i, map_sum]
    rw [h1, h2'] at hC'
    have h3 : ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← amul, ← amul, mul_comm]
    rw [h3, pow_add, mul_comm, amul] at hC'
    exact (hbijN β).1 hC'
  constructor
  · rintro ⟨N, hN, hx⟩
    choose x' hx' using hx
    have hkj : (((j + N).toNat : ℕ) : ℤ) = j + N := Int.toNat_of_nonneg hN
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ (j + N).toNat * x' τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; rw [← map_pow]; exact hx' τ i
    have hK := key N x hxx
    have hmem : Fil (((j + N).toNat : ℕ) : ℤ) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      refine (Fb _ _).2 fun i => ?_
      have h8 : (fun τ => x τ i) = (fun _ => Ehat O K l e) ^ (j + N).toNat * fun τ => x' τ i := by
        funext τ; simp only [x, Pi.mul_apply, Pi.pow_apply]
      rw [h8, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hK, hkj] at hmem
    exact (hSh N _ j).2 hmem
  · intro hF
    obtain ⟨N₁, x₁, hx₁⟩ := hE1
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ j.natAbs * x₁ τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N₁ + j.natAbs) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; simp only [x, map_mul, map_pow, hx₁, pow_add]; ring
    have hK := key _ x hxx
    have hN : 0 ≤ j + ((N₁ + j.natAbs : ℕ) : ℤ) := by push_cast; have := neg_abs_le j; omega
    have hkj : (((j + ((N₁ + j.natAbs : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j + ((N₁ + j.natAbs : ℕ) : ℤ) := Int.toNat_of_nonneg hN
    have h1 := (hSh (N₁ + j.natAbs) _ j).1 hF
    rw [hK, ← hkj] at h1
    have h2 := (Fb _ _).1 h1
    refine ⟨N₁ + j.natAbs, hN, fun τ i => ?_⟩
    obtain ⟨z, hz⟩ := PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ _ _ (h2 i)
    refine ⟨z τ, ?_⟩
    have h9 := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h9
    rw [← h9, map_pow]
    exact hxx τ i

end GlobalTheory.BKGal.JumpDR.CmpFil

open GlobalTheory.BKGal.JumpDR.CmpFil in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BKGal.JumpDR.inEhat_iff_filV : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  intro hFont l _ a e _ _ ϖ LL _ _ h2 ι _ _ P T I jB Pl AI Td hcmp X hX A hA n s m j
  obtain ⟨hbij, hS⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td A hA
  obtain ⟨β, y, hy⟩ := GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat l a e ϖ LL ι P
  obtain ⟨f, hf1, hspan, hind⟩ := GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus hFont l a e ϖ LL h2 ι P T I jB Pl AI Td hcmp X hX A hA β y hy
  exact coreG (thetaW a LL) ϖ P A (fun j y => y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    (amulL A hA) (aoneL A hA) hbij hS (fun j => X (jB (Pi.single j 1))) β y hy f hf1 hspan hind s m
    (fun k => X (jB (toBcris (thetaW a LL) ϖ P (m k))))
    (fun s' c h => GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates hFont l a e ϖ LL h2 ι P T jB Pl AI Td X hX A hA n s' m c h)
    (GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral l a e ϖ LL ι P n s m) j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyOperatorMapsIntoCompletion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalENM

theorem EN_mem_Man : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH m hm
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin _ _ l e a ι P
  have hv := hn m hm
  obtain ⟨jD, hjD⟩ := GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice l a e _ _ (thetaW a LL) ϖ ι P T I
  let w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e := fun τ i =>
    toHat _ _ l e ⟨(E ↥LL.1 l e ^ n • P.EN m) τ i, mem_tot.1 hv τ i⟩
  have hw : ∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) =
      hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i) := fun τ i => (hat_coe_Rpi l e _).symm
  clear_value w
  have h3 := GlobalTheory.T.monodromy_image_mem_BdRplus_lattice hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH jD hjD m hm n hv w hw
  choose y hy using fun i => GlobalTheory.T.ideal_power_membership_divisible l a e _ _ (thetaW a LL) ϖ n (fun τ => w τ i) (h3 i)
  have hE : P.EN m ∈ P.Mext (RpiE ↥(OL LL) ↥LL.1 l e) := P.mem_Mext_invE_of_mem_divE hv
  rw [← P.hatTot_mem_Mhat_iff hE, P.mem_Mhat]
  intro τ i
  refine ⟨y i τ, ?_⟩
  have h1 := congrFun (hy i) τ
  have h2 := hw τ i
  have h4 := hat_E_pow_mul (O := ↥(OL LL)) l e n (mem_tot.1 hE τ i)

  have h1' : w τ i = Ehat ↥(OL LL) ↥LL.1 l e ^ n * y i τ := by rw [h1]; rfl
  have h5 : (E ↥LL.1 l e ^ n • P.EN m) τ i = E ↥LL.1 l e ^ n * P.EN m τ i := rfl
  have h7 := ((congrArg (algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e)) h1').symm.trans h2).trans
    ((congrArg (hat ↥(OL LL) l e) h5).trans h4)
  have h8 := (map_mul (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)) _ _).symm.trans h7
  have hu : IsUnit (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (Ehat ↥(OL LL) ↥LL.1 l e)).pow n
  exact hu.mul_left_cancel h8

end GlobalTheory.NgalENM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDetectedSubgroupTowerRat_proof : NoTowerQ := by
  first | exact @GlobalTheory.PMon.Ram.noTowerQ_holds | exact GlobalTheory.PMon.Ram.noTowerQ_holds | (intros; apply GlobalTheory.PMon.Ram.noTowerQ_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem exists_embU_one (τ : E →+* ℂ) (z : ℂ) (hz : ‖z‖ = 1) : ∃ x ∈ embU 1 τ, cEmb τ x 0 0 = z := by
  classical
  let z' : ℂ := if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z
  have hz' : star z' * z' = 1 := by
    have h : ‖z'‖ = 1 := by
      simp only [z']
      split_ifs <;> simp [hz]
    rw [mul_comm]
    change z' * starRingEnd ℂ z' = 1
    rw [Complex.mul_conj', h]
    simp
  let c : Cinf E := Function.update 1 (InfinitePlace.mk τ) z'
  have hc : star c * c = 1 := by
    funext w
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      simpa [c] using hz'
    · simp [c, h]
  let y : GL (Fin 1) (Cinf E) := GeneralLinearGroup.scalar (Fin 1) ⟨c, star c, by rw [mul_comm, hc], hc⟩
  have hy : y.val 0 0 = c := by simp [y]
  have hU : infGL E 1 y ∈ UA E 1 := infGL_mem_UA y (by
    ext1 i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [Matrix.mul_apply, hy, hc])
  have he : ∀ τ' : E →+* ℂ, cEmb τ' ⟨_, hU⟩ 0 0 = coord τ' c := fun τ' => by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E 1 y)) 0 0 = _
    rw [pInf_infGL, ← hy]
    rfl
  refine ⟨⟨_, hU⟩, ⟨pFin_infGL y, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    refine (he τ').trans ?_
    unfold coord
    split_ifs <;> simp [c, h]
  · rw [he]
    unfold coord
    split_ifs with h <;> simp [c, z', h]

theorem weight_eq_zero_of_const (τ : E →+* ℂ) (lam : DomWeight 1)
    (h : HasWeightAt (Submodule.span ℂ {(fun _ => 1 : UA E 1 → ℂ)}) τ lam) : lam.w 0 = 0 := by
  obtain ⟨-, f, h0, h1, h2⟩ := h
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
  by_contra hl
  have hl' : (lam.w 0 : ℂ) ≠ 0 := by exact_mod_cast hl
  obtain ⟨x, hx, e⟩ := exists_embU_one τ _ (Complex.norm_exp_ofReal_mul_I (Real.pi / lam.w 0))
  have h3 := h2 ⟨x, hx⟩ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h1 v)
  have h4 : RU E 1 x (f v) = f v := by rw [← hc]; rfl
  rw [GlobalTheory.Branching.RankTwo.small_act, map_smul] at h3
  change (cEmb τ x 0 0) ^ lam.w 0 • f v = RU E 1 x (f v) at h3
  rw [e, h4, ← Complex.exp_int_mul, show (lam.w 0 : ℂ) * (((Real.pi / lam.w 0 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
    push_cast; field_simp, Complex.exp_pi_mul_I] at h3
  have h5 : (2 : ℂ) • f v = 0 := by linear_combination (norm := module) -h3
  exact hv ((smul_eq_zero.1 h5).resolve_left two_ne_zero)

theorem isCompAlong_const {n : ℕ} (Gv : Subgroup (UA E n)) {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
    (p : Gv →* H) {σ : Representation ℂ H W} (φ : (Representation.trivial ℂ H ℂ).Equiv σ) :
    IsCompAlong (Submodule.span ℂ {(fun _ => 1 : UA E n → ℂ)}) Gv p σ := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ
    ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩),
    (LinearMap.toSpanSingleton ℂ _ fun _ => 1).comp φ.symm.toLinearMap, fun h => ?_,
    fun v => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun x v => ?_⟩
  · have := congrFun (LinearMap.congr_fun h (φ 1)) 1
    simp at this
  · have : φ.symm (σ (p x) v) = φ.symm v := LinearMap.congr_fun (φ.symm.isIntertwining' (p x)) v
    funext g
    change φ.symm (σ (p x) v) • (1 : ℂ) = φ.symm v • (1 : ℂ)
    rw [this]

theorem hasWeightAt_const (τ : E →+* ℂ) :
    HasWeightAt (Submodule.span ℂ {(fun _ => 1 : UA E 1 → ℂ)}) τ ⟨0, antitone_const⟩ := by
  let lam : DomWeight 1 := ⟨0, antitone_const⟩
  have h0 : GlobalTheory.Branching.RankTwo.one' lam ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  refine isCompAlong_const _ _ (.mk (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ _ (GlobalTheory.Branching.RankTwo.one' lam))
    ⟨smul_left_injective ℂ h0, fun f => ⟨_, (GlobalTheory.Branching.RankTwo.eq_smul_one lam f).symm⟩⟩) fun g => ?_)
  refine LinearMap.ext fun c => ?_
  refine Eq.trans ?_ (GlobalTheory.Branching.RankTwo.small_act lam g _).symm
  simp [lam]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
omit [IsCMField E] in

theorem nonempty_equiv_locProd_triv {n : ℕ} (h : ∑ _ : Fin 1, n = n) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ).Equiv
      (locProd h w fun _ => SmIrr.triv _)) :=
  GlobalTheory.LocGL.nonempty_equiv_multiProd_one (SmIrr.triv _).smooth _ fun a i => Fin.ext (by
    rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp)

end GlobalTheory.UnitaryBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
section
open MeasureTheory

namespace GlobalTheory.SplitWeil

theorem nabs_map_of_homeomorph : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → ∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' x
  haveI : SecondCountableTopology k := (Model.secondCountable_and_t2_local_field (k := k)).1
  haveI : T2Space k := (Model.secondCountable_and_t2_local_field (k := k)).2
  haveI : SecondCountableTopology k' := (Model.secondCountable_and_t2_local_field (k := k')).1
  haveI : T2Space k' := (Model.secondCountable_and_t2_local_field (k := k')).2
  let e : k ≃ₜ+ k' :=
    { i.toAddEquiv with
      continuous_toFun := hi
      continuous_invFun := hi' }
  unfold nabs
  congr 1
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e x (Units.map i.toRingHom.toMonoidHom x) (fun y => by
    change i ((x : k) * y) = i x * i y
    exact map_mul i _ _)

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CocycleInt

theorem TWincl_comp_toB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] {T : LocLat (Gl l) ℚ_[l] K O} (z : TW (OA l O) T) :
    TWincl (toOB l O) T (TWincl (toOCr l O) T z) = TWincl (toB l O) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x => rfl

theorem TWincl_smul' {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

end GlobalTheory.BKGal.CocycleInt

open GlobalTheory.BKGal.CocycleInt in

theorem GlobalTheory.BKGal.potential_cocycle_mem_lpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R hηH hl y hyY c hc b hb g hg hex
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hval, rfl⟩ := hb
  have hl2 : l ≠ 2 := by omega
  obtain ⟨z, hz⟩ := GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image l a e O K t ϖ hl2 ι η H D T R σ c (by rw [hconn]; exact hc) g hg
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower R.jB R.cmp ε hε z
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice l a e O K t ϖ ι η H D T R y hyY hy m₀ b₀ hm₀ hval ε hε
  obtain ⟨z₁, hz₁⟩ := GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl l O K T g ε hε (H + 2 * η) b₀ z₀ hz₀
  obtain ⟨n, x, hx⟩ := hex
  set jσ := R.jB (toBcris t ϖ D.toPhiMod σ)
  refine GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound l O K T hl2 ε hε (H + 2 * η) n c (by omega) _ x
    (toOCr l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) • w₁ - (l : O) ^ c • TWincl (toOCr l O) T z₁) hx ?_
  have hsplit : actB (sQ l) T g (jσ - b₀) - (jσ - b₀) = (actB (sQ l) T g jσ - jσ) - (actB (sQ l) T g b₀ - b₀) := by
    rw [map_sub]; abel
  have hmu : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η) : OA l O) =
      ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ η) := by
    rw [show H + 2 * η = (H + η) + η by ring, pow_add]
  rw [hsplit, map_sub, TWincl_smul', map_smul, TWincl_comp_toB, ← hz₁, smul_sub, hz, ← hw₁]
  rw [smul_sub, hmu, map_mul, mul_smul, hw₁, smul_comm ((l : O) ^ c) (toB l O _ * toB l O _ : OB l O)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsCommStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_adelicRationalPoints_comm : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι → Ad E) × (κ → Ad E) → ℂ), Per ((ratV E ι).prod (ratV E κ)) Φ → avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) = avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_comm | exact GlobalTheory.CuspGeneric.avg_comm | (intros; apply GlobalTheory.CuspGeneric.avg_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageSumIndexFubiniStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_sum_index_fubini : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ → avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_sum_index | exact GlobalTheory.CuspGeneric.avg_sum_index | (intros; apply GlobalTheory.CuspGeneric.avg_sum_index <;> assumption)
end

