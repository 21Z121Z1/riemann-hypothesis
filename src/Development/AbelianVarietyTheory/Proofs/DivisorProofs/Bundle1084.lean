import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatProductFormula

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixing
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem support_cxF_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  intro p _ G v wt Kf f _ K' f' _ β x t hx hfin a
  by_cases hpos : 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re
  · refine (hfin (LeftCosets.rep _ _ a.1) _ hpos).subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    unfold cxF at hy
    split_ifs at hy with hc
    · exact ⟨hc.2, left_ne_zero_of_mul hy⟩
    · exact absurd rfl hy
  · convert Set.finite_empty
    ext y
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    unfold cxF
    rw [if_neg (fun hc => hpos hc.1)]

end GlobalTheory.CxUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem mvPolynomial_submodule_eq_top {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) (h1 : (1 : MvPolynomial σ ℂ) ∈ S)
    (hX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • (1 : MvPolynomial σ ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [this]; exact S.smul_mem a h1
  | add p q hp hq => exact S.add_mem (hp trivial) (hq trivial)
  | mul_X p n hp => rw [mul_comm]; exact hX n p (hp trivial)

theorem tensor_submodule_eq_top : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)),
    PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N →
    (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  intro ι σ _ _ N h1 hX
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial σ ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun _ => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial σ ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial σ ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [atPl_tprod] at this
        simpa using this
      have htop := mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.FibreProj

variable {ι : Type} [Fintype ι]

open Classical in

def pol (φ : (ι → ℤ) → ℝ) : ℝ := ∑ S : Finset ι, (-1 : ℝ) ^ S.card * φ fun i => if i ∈ S then -1 else 0

theorem pol_eq_multiDiff [DecidableEq ι] (φ : (ι → ℤ) → ℝ) :
    pol φ = multiDiff (fun i => (Pi.single i 1 : ι → ℤ)) φ 0 := by
  rw [pol, multiDiff_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  congr 2
  funext i
  simp only [zero_sub, Pi.neg_apply, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  split_ifs <;> simp

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in

theorem _root_.GlobalTheory.FibreProj.pol_sum {J : Type} (T : Finset J)
    (φ : J → (ι → ℤ) → ℝ) :
    _root_.GlobalTheory.FibreProj.pol (fun n => ∑ j ∈ T, φ j n) =
      ∑ j ∈ T, _root_.GlobalTheory.FibreProj.pol (φ j) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem pol_sub (φ ψ : (ι → ℤ) → ℝ) : pol (fun n => φ n - ψ n) = pol φ - pol ψ := by
  simp only [pol, mul_sub, Finset.sum_sub_distrib]

theorem pol_const_mul (a : ℝ) (φ : (ι → ℤ) → ℝ) : pol (fun n => a * φ n) = a * pol φ := by
  simp only [pol, Finset.mul_sum, mul_left_comm]

theorem pol_mul_const (a : ℝ) (φ : (ι → ℤ) → ℝ) : pol (fun n => φ n * a) = pol φ * a := by
  simp only [pol, Finset.sum_mul, mul_assoc]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
private theorem sum_pow_eq_sum_words_prod {R : Type} [CommRing R] (c : ι → R) (D : ℕ) :
    (∑ i, c i) ^ D = ∑ f : Fin D → ι, ∏ k, c (f k) := by
  rw [← Fin.prod_const, Fintype.prod_sum]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_range_subset_eq_ite_surjective {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (f : Fin D → ι) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  have hr : ∀ t : Finset ι, (∏ i ∈ t, (-1 : R)) *
      ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) =
        (-1) ^ t.card * (if ∀ k, f k ∈ t then 1 else 0) := by
    intro t
    rw [Finset.prod_const, Finset.prod_ite_zero, Finset.prod_const_one]
    have hiff : (∀ i ∈ Finset.univ \ t, i ∉ Set.range f) ↔ ∀ k, f k ∈ t := by
      constructor
      · intro h k
        by_contra hk
        exact h (f k) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hk⟩) ⟨k, rfl⟩
      · rintro h i hi ⟨k, rfl⟩
        exact (Finset.mem_sdiff.1 hi).2 (h k)
    simp only [hiff]
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)
      = ∑ t ∈ (Finset.univ : Finset ι).powerset, (∏ i ∈ t, (-1 : R)) *
          ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun t _ => (hr t).symm
    _ = ∏ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) := (Finset.prod_add _ _ _).symm
    _ = _ := by
        split_ifs with hs
        · have h1 : ∀ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) = -1 := fun i => by
            rw [if_neg (show ¬(i ∉ Set.range f) from not_not.2 (hs i)), add_zero]
          simp only [h1, Finset.prod_const, Finset.card_univ, hD]
        · simp only [Function.Surjective, not_forall] at hs
          obtain ⟨i, hi⟩ := hs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos (show i ∉ Set.range f from fun h => hi h)]; ring)

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_surjective_words_prod_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ f : Fin D → ι, (∏ k, w (f k)) * (if Function.Surjective f then (-1 : R) ^ D else 0) =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  have hbij : ∀ f : Fin D → ι, Function.Surjective f → Function.Bijective f := fun f hf =>
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, by rw [Fintype.card_fin, hD]⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hprod : ∀ f ∈ Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f),
      (∏ k, w (f k)) * (-1 : R) ^ D = (∏ i, w i) * (-1) ^ D := by
    intro f hf
    rw [← Equiv.prod_comp (Equiv.ofBijective f (hbij f (Finset.mem_filter.1 hf).2)) w]
    rfl
  have e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hD).symm
  have hcard : (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card =
      D.factorial := by
    calc (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card
        = (Finset.univ.map ⟨fun σ : Fin D ≃ ι => (σ : Fin D → ι),
            DFunLike.coe_injective⟩).card := by
          congr 1
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          constructor
          · intro hf
            exact ⟨Equiv.ofBijective f (hbij f hf), rfl⟩
          · rintro ⟨σ, rfl⟩
            exact σ.surjective
      _ = Fintype.card (Fin D ≃ ι) := by rw [Finset.card_map, Finset.card_univ]
      _ = D.factorial := by rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D
      = ∑ S : Finset ι, ∑ f : Fin D → ι,
          (∏ k, w (f k)) * ((-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_pow_eq_sum_words_prod, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.prod_ite_zero]
        simp only [Finset.mem_univ, true_implies]
        split_ifs <;> ring
    _ = ∑ f : Fin D → ι, (∏ k, w (f k)) *
          (if Function.Surjective f then (-1 : R) ^ D else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.mul_sum, sum_neg_one_pow_card_range_subset_eq_ite_surjective hD f]
    _ = _ := sum_surjective_words_prod_eq_factorial_prod hD w

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in

theorem _root_.GlobalTheory.FibreProj.pol_pow {R : Type} [CommRing R]
    [Algebra ℝ R] (z : ι → R) (Φ : R →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    _root_.GlobalTheory.FibreProj.pol (fun n => Φ ((∑ i, (n i : ℝ) • z i) ^ D)) =
      D.factorial * Φ (∏ i, z i) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  have hsum : ∀ S : Finset ι, (∑ i, (((if i ∈ S then -1 else 0 : ℤ) : ℝ)) • z i) =
      ∑ i, if i ∈ S then -z i else 0 := by
    intro S
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [hsum]
  have hterm : ∀ (k : ℕ) (x : R), Φ ((-1 : R) ^ k * x) = (-1 : ℝ) ^ k * Φ x := by
    intro k x
    rw [← smul_eq_mul ((-1 : ℝ) ^ k), ← map_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  have h1 : ((-1 : R) ^ D) * (-1) ^ D = 1 := by rw [← mul_pow]; simp
  have hfinal : Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) = D.factorial * Φ (∏ i, z i) := by
    rw [Finset.prod_neg, Finset.card_univ, hD]
    calc Φ ((-1) ^ D * D.factorial * ((-1) ^ D * ∏ i, z i))
        = Φ ((D.factorial : ℝ) • ∏ i, z i) := by
          congr 1
          rw [Algebra.smul_def, map_natCast]
          linear_combination (↑D.factorial * ∏ i, z i) * h1
      _ = _ := by rw [map_smul, smul_eq_mul]
  calc ∑ S : Finset ι, (-1 : ℝ) ^ S.card * Φ ((∑ i, if i ∈ S then -z i else 0) ^ D)
      = Φ (∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then -z i else 0) ^ D) := by
        rw [map_sum]
        simp only [hterm]
    _ = Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) :=
        congrArg Φ (sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod hD fun i => -z i)
    _ = _ := hfinal

theorem pol_lin_pow (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    pol (fun n : ι → ℤ => Φ (lin (fun i => (n i : ℝ)) ^ D)) = D.factorial * Φ (∏ i, X i) := by
  simpa only [lin, smul_eq_C_mul] using pol_pow (fun i => (X i : MvPolynomial ι ℝ)) Φ hD

theorem pol_mix (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    pol (fun n : ι → ℤ => Φ (X none * rename some (lin fun i => (n i : ℝ)) ^ D)) =
      D.factorial * Φ (∏ o, X o) := by
  have := pol_lin_pow (Φ ∘ₗ LinearMap.mulLeft ℝ (X none) ∘ₗ
    (rename some : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (Option ι) ℝ).toLinearMap) hD
  simpa [Fintype.prod_option] using this

end GlobalTheory.FibreProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenter
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem pow_indep_tensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n →
    ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F),
      ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  intro p _ G γ hn v c hc

  let ψ : (Fin G.n → G.F) →ₗ[ℚ] G.C :=
    { toFun := fun f => ∑ i, f i • γ ^ (i : ℕ)
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc] }
  have li : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hn] at this
    exact this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    exact funext ((Fintype.linearIndependent_iff.mp li) f hf)
  have hinj : Function.Injective (ψ.lTensor (Qv v)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  let e := TensorProduct.piRight ℚ ℚ (Qv v) (fun _ : Fin G.n => G.F)
  have key : ∀ t : Qv v ⊗[ℚ] (Fin G.n → G.F),
      ∑ i, iotaF G v (e t i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = ψ.lTensor (Qv v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, ← hx, ← hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, map_add, add_mul]
    | tmul q f =>
      rw [LinearMap.lTensor_tmul]
      have : ∀ i, e (q ⊗ₜ[ℚ] f) i = q ⊗ₜ[ℚ] f i := fun i => rfl
      simp only [this, iotaF_tmul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum, Algebra.smul_def]

  have h0 : ψ.lTensor (Qv v) (e.symm c) = 0 := by
    rw [← key, LinearEquiv.apply_symm_apply]; exact hc
  have : e.symm c = 0 := hinj (by rw [h0, map_zero])
  rw [← e.apply_symm_apply c, this, map_zero]

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  first | exact @GlobalTheory.SchwartzBox.boxFun_mem_schA | exact GlobalTheory.SchwartzBox.boxFun_mem_schA | (intros; apply GlobalTheory.SchwartzBox.boxFun_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphicStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G), Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  first | (exact @GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (exact GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (intros; apply GlobalTheory.LKCx.Form.mk_eq_iff_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleFrameExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

namespace GlobalTheory.VB.CokerFrame

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem isFrame_of_injective_of_local {e : ι → Γ(F, U)}
    (inj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)))
    (loc : ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ ∃ a : ι → Γ(X, W),
        Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i)) a = resM F h' s) :
    VB.IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← VB.resM_linearCombination e ((hW x).trans h), ← VB.resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [VB.resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

theorem sum_eq_sum_last {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, (j : ℕ) < l → g j = 0) :
    ∑ j, g j = ∑ k : Fin (N - l), g ⟨l + k, by omega⟩ := by
  symm
  refine Finset.sum_of_injOn (fun k : Fin (N - l) => (⟨l + k, by omega⟩ : Fin N))
    (fun a _ b _ hab => ?_) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_)
    (fun _ _ => rfl)
  · have := congrArg Fin.val hab
    simp only at this
    exact Fin.ext (by omega)
  · refine hg j (Nat.lt_of_not_le fun hlj => hj ⟨⟨j - l, by omega⟩, by simp, Fin.ext ?_⟩)
    simp only
    omega

end GlobalTheory.VB.CokerFrame

open GlobalTheory.VB.CokerFrame in

theorem GlobalTheory.VB.exists_isFrame_cokernel_of_frame :
    ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)),
      VB.IsFrame c → ∀ (l : ℕ), l ≤ N →
      (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
        (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) →
      ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  intro X F U N P c hc l hl hP
  set π := cokernel.π P.incl

  have hlow (V : X.Opens) (h : V ≤ U) (j : Fin N) (hj : (j : ℕ) < l) :
      π.app V (resM F h (c j)) = 0 := by
    classical
    rw [VB.Sub.cokernel_π_app_eq_zero_iff]
    have := (hP V h (Pi.single j 1)).2 fun j' hj' => by
      rw [Pi.single_apply, if_neg (fun e => by subst e; omega)]
    simpa [Pi.single_apply] using this
  refine ⟨fun k => π.app U (c ⟨l + k, by omega⟩), isFrame_of_injective_of_local ?_ ?_⟩
  · intro V h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    classical
    let b : Fin N → Γ(X, V) := fun j => if hj : l ≤ (j : ℕ) then a ⟨j - l, by omega⟩ else 0
    have hsum : (∑ j, b j • resM F h (c j)) =
        ∑ k : Fin (N - l), a k • resM F h (c ⟨l + k, by omega⟩) := by
      rw [sum_eq_sum_last hl]
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [b, dif_pos (Nat.le_add_right l k)]
        congr 2
        ext
        simp
      · intro j hj
        simp only [b, dif_neg (by omega : ¬ l ≤ (j : ℕ)), zero_smul]
    have hmem : (∑ j, b j • resM F h (c j)) ∈ P.sec V := by
      rw [hsum, ← VB.Sub.cokernel_π_app_eq_zero_iff]
      rw [Fintype.linearCombination_apply] at ha
      rw [map_sum]
      simpa only [Scheme.Modules.Hom.app_smul, app_resM] using ha
    have hb := (hP V h b).1 hmem
    funext k
    have := hb ⟨l + k, by omega⟩ (Nat.le_add_right l k)
    simpa [b] using this
  · intro V h t x hx
    obtain ⟨W, h', hxW, s, hs⟩ := VB.exists_app_eq_of_epi π t hx
    obtain ⟨β, hβ⟩ := (hc W (h'.trans h)).2 s
    refine ⟨W, h', hxW, fun k => β ⟨l + k, by omega⟩, ?_⟩
    rw [← hs, ← hβ, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum,
      sum_eq_sum_last hl]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.Hom.app_smul, app_resM]
    · intro j hj
      rw [Scheme.Modules.Hom.app_smul, hlow W (h'.trans h) j hj, smul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_elements_bounded_padic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (h₂ : Gr G 1), ∃ (B : ℝ) (e : ℕ), ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) ∧ ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.FixBound.bounded_of_support) | (exact GlobalTheory.FixBound.bounded_of_support) | (intros; apply GlobalTheory.FixBound.bounded_of_support <;> assumption)
end

