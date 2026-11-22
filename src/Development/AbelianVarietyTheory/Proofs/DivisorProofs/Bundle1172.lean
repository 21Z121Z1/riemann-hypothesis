import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorsNonzeroTerms
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKBound

theorem integral_of_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), IsSimple G → 0 < r → IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ N : ℕ, 0 < N ∧ ∀ P : Pair G, (∃ μ, P.Mark μ) → P.term L.K.toSubgroup f r K φ ≠ 0 → IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f r K φ hG hr hf hφ
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)
  obtain ⟨k, hk⟩ := GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ
  have hp := (Fact.out : p.Prime)
  refine ⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩
  intro P _ hP

  have fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β →
      ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w ((y0⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ →
          ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ i, ∃ kk : ℕ, ∃ a : ℤ, ((D * p ^ kk : ℕ) : ℚ) * (LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.coeff i = a) →
      IsIntegral ℤ (((D * p ^ (2 * k * Module.finrank ℚ G.C) : ℕ) : ℤ) • (y0 : G.C)) := by
    intro y0 c0 hy0 hc hc' hu hu' hAf
    have hroots := GlobalTheory.T.bounded_eigenvalues_classes p G hG P.β y0 c0 hy0 _ hc hc' hu hu'
    have hroots' : ∀ μ : PadicAlgCl p,
        ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
        ‖μ‖ ≤ (p : ℝ) ^ (2 * k) := fun μ hμ => by
      rw [show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ
    have h6 := GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'
    rw [LinearMap.charpoly_natDegree] at h6
    apply GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C
    intro i
    obtain ⟨kk, hkk⟩ := hAf i
    exact GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk

  rw [Pair.term] at hP
  split_ifs at hP with h
  swap
  · exact absurd rfl hP
  rw [Pair.termAt, pointSum] at hP
  obtain ⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by
    by_contra hc
    push_neg at hc
    exact hP (by rw [finsum_congr hc]; exact finsum_zero)
  have hq2 := (mul_ne_zero_iff.1 hq).2
  have hfq := (mul_ne_zero_iff.1 hq2).1
  have hφq := (mul_ne_zero_iff.1 hq2).2
  set x := P.trivAf.choose with hxdef
  set o := Quotient.out q with hodef
  have hgΩ := hΩ _ hfq
  have hnrm := h.choose_spec
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq
  set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg
  have hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
      ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ *
        ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹ := by
    show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) *
      (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _
    group
  set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x
  have hA := hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)
  have hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹ := Or.inr (by simpa using hgΩ)
  have hA' := hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by
    show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _
    rw [hg1]; simp [mul_assoc])
  have hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _
    simp
  have hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _
    simp
  have hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w (P.γ : G.C) := fun w => rfl
  have hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C) := fun w => rfl
  have hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β := (P.cent.inv_mem P.self.2).2
  refine ⟨fin P.γ P.c P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ))
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA,
    fin P.γ⁻¹ P.c⁻¹ hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1)
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ))
      (fun w μ hμ => hk3 w μ (by rw [hw1, ← inv_inv P.γ]; exact hμ)) hA'⟩

end GlobalTheory.LKBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliCoeffDualWeylEqCoeffProd
section
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finset_sum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finset_sum_coeff, coeff_monomial, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirSectionSumIdentity
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

noncomputable section

namespace GlobalTheory.SteepMult.CasDom

variable {R S : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem position_section (k : ℕ) (i : Fin k) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (Z : Mat R S) (L : Module.End ℂ W)
    (Ψ : (Fin k → NC R S) → W) :
    ∑ g, formT 1 B (factorOp 1 0 Z (section1 Ψ i g)) (fun h => L (section1 Ψ i g h)) =
      (Fintype.card (NC R S) : ℂ) * formT k B (factorOp k i Z Ψ) (fun g => L (Ψ g)) := by
  classical
  set s : (Fin k → NC R S) → ℂ := fun g' => B (factorOp k i Z Ψ g') (L (Ψ g')) with hs
  have h1 : ∀ g (h : Fin 1 → NC R S), B (factorOp 1 0 Z (section1 Ψ i g) h) (L (section1 Ψ i g h)) =
      s (Function.update g i (h 0)) := by
    intro g h
    simp [hs, factorOp, section1]
  have h2 : ∀ g, ∑ h : Fin 1 → NC R S, s (Function.update g i (h 0)) = ∑ y, s (Function.update g i y) := by
    intro g
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ (fun h => rfl)
  simp only [formT_apply, h1, h2]
  have := sum_update_swap i (fun (_ g' : Fin k → NC R S) => s g')
  rw [this]
  simp [Finset.sum_const, Finset.mul_sum, hs]

theorem adCoeff_casimir (z w : NC R S) :
    ∑ a, ∑ b, (if sameBlock a b then
      ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) =
      if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  exact GlobalTheory.T.adjoint_block_orthogonality R S z w

lemma sum4' {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    ∑ i, ∑ g, ∑ a, ∑ b, f i g a b = ∑ a, ∑ b, ∑ i, ∑ g, f i g a b := by
  calc _ = ∑ i, ∑ a, ∑ b, ∑ g, f i g a b := Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem position_cas_of (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x : (Fin 1 → NC R S) → W)
    (hC : ∀ z w : NC R S, ∑ a, ∑ b, (if sameBlock a b then
      ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) =
      if z = w then ((R + S : ℕ) : ℂ) else 0) :
    ∑ a, ∑ b, (if sameBlock a b then formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x) else 0) =
      ((R + S : ℕ) : ℂ) * formT 1 B x x := by
  classical
  set X : NC R S → W := fun z => x (fun _ => z) with hX
  have hu : ∀ (h : Fin 1 → NC R S) z, Function.update h (0 : Fin 1) z = fun _ => z := by
    intro h z; funext j; rw [Subsingleton.elim j 0]; simp
  have hx : ∀ h : Fin 1 → NC R S, x h = X (h 0) := by
    intro h; simp only [hX]; congr 1; funext j; rw [Subsingleton.elim j 0]
  have hsum : ∀ F : NC R S → ℂ, ∑ h : Fin 1 → NC R S, F (h 0) = ∑ y, F y := fun F =>
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ (fun h => rfl)
  have hform : ∀ Z : Mat R S, formT 1 B (factorOp 1 0 Z x) (factorOp 1 0 Z x) =
      ∑ z, ∑ w, (∑ y, (starRingEnd ℂ) (adP Z y z) * adP Z y w) * B (X z) (X w) := by
    intro Z
    have e : ∀ h : Fin 1 → NC R S, factorOp 1 0 Z x h = ∑ z, adP Z (h 0) z • X z := by
      intro h; simp [factorOp, hu, hX]
    simp only [formT_apply, e]
    rw [hsum (fun y => B (∑ z, adP Z y z • X z) (∑ w, adP Z y w • X w))]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [RingHom.id_apply]
    ring
  have hr : formT 1 B x x = ∑ y, B (X y) (X y) := by
    simp only [formT_apply, hx]
    exact hsum (fun y => B (X y) (X y))
  calc _ = ∑ a, ∑ b, ∑ z, ∑ w, (if sameBlock a b then
        ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) * B (X z) (X w) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : sameBlock a b
        · simp only [if_pos h, hform]
        · simp [h]
    _ = ∑ z, ∑ w, ∑ a, ∑ b, (if sameBlock a b then
        ∑ y, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0) * B (X z) (X w) := sum4' _
    _ = ∑ z, ∑ w, (if z = w then ((R + S : ℕ) : ℂ) else 0) * B (X z) (X w) := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        rw [← hC z w, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
    _ = _ := by
        rw [hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp [ite_mul]

theorem position_cas (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x : (Fin 1 → NC R S) → W) :
    ∑ a, ∑ b, (if sameBlock a b then formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x) else 0) =
      ((R + S : ℕ) : ℂ) * formT 1 B x x :=
  position_cas_of B x adCoeff_casimir

lemma same_symm' {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

lemma tAct_split (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) :
    tAct k actW Z Ψ = (fun g => actW Z (Ψ g)) + (∑ i, factorOp k i Z) Ψ := by
  ext g
  simp [tAct_apply, factorOp, LinearMap.sum_apply, Finset.sum_apply]

lemma formT_herm (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ Φ : (Fin k → NC R S) → W) : (formT k B Φ Ψ).re = (formT k B Ψ Φ).re := by
  rw [formT_apply, formT_apply, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← hU.1 (Ψ g) (Φ g)]
  simp

lemma formT_nonneg (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) : 0 ≤ (formT k B Ψ Ψ).re := by
  rw [formT_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun g _ => ?_
  by_cases h : Ψ g = 0
  · simp [h]
  · exact (hU.2.1 _ h).le

lemma tAct_adj (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) {a b : Ix R S} (hab : sameBlock a b) (Ψ Φ : (Fin k → NC R S) → W) :
    formT k B (tAct k actW (Eab a b) Ψ) Φ = formT k B Ψ (tAct k actW (Eab b a) Φ) :=
  (isUnitary_tAct R S k W actW B hU).2.2 a b hab Ψ Φ

lemma casK_form (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ) = ∑ a, ∑ b, (if sameBlock a b then
      formT k B (tAct k actW (Eab b a) Ψ) (tAct k actW (Eab b a) Ψ) else 0) := by
  simp only [GlobalTheory.BlockReps.casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [GlobalTheory.BlockReps.unitK, if_pos h, if_pos (same_symm' h)]
    exact (tAct_adj k hU (same_symm' h) _ _).symm
  · simp [GlobalTheory.BlockReps.unitK, h]

lemma casK_pt (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g)) = ∑ a, ∑ b, (if sameBlock a b then
      formT k B (fun g => actW (Eab b a) (Ψ g)) (fun g => actW (Eab b a) (Ψ g)) else 0) := by
  simp only [formT_apply, GlobalTheory.BlockReps.casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [GlobalTheory.BlockReps.unitK, if_pos h, if_pos (same_symm' h)]
    exact Finset.sum_congr rfl fun g _ => (hU.2.2 b a (same_symm' h) _ _).symm
  · simp [GlobalTheory.BlockReps.unitK, h]

lemma diff_eq (k : ℕ) {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    (formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re - (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re =
      ∑ a, ∑ b, (if sameBlock a b then
        (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) ((∑ i, factorOp k i (Eab b a)) Ψ)).re +
        2 * (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))).re else 0) := by
  rw [casK_form k hU, casK_pt k hU, Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : sameBlock a b
  · simp only [if_pos h, tAct_split, map_add, LinearMap.add_apply, Complex.add_re]
    rw [formT_herm k hU ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))]
    ring
  · simp [h]

lemma bracket_eq {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}
    (hU : IsUnitary actW B) (x : (Fin 1 → NC R S) → W) :
    (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 actW) x)).re - ((R + S : ℕ) : ℝ) * (formT 1 B x x).re -
        (formT 1 B x (fun h => GlobalTheory.BlockReps.casK actW (x h))).re =
      ∑ a, ∑ b, (if sameBlock a b then
        2 * (formT 1 B (factorOp 1 0 (Eab b a) x) (fun h => actW (Eab b a) (x h))).re else 0) := by
  have h2 : ∑ a, ∑ b, (if sameBlock a b then
      (formT 1 B (factorOp 1 0 (Eab b a) x) (factorOp 1 0 (Eab b a) x)).re else 0) =
      ((R + S : ℕ) : ℝ) * (formT 1 B x x).re := by
    have := congrArg Complex.re (position_cas B x)
    simpa [Complex.re_sum, apply_ite Complex.re] using this
  have h1 := diff_eq 1 hU x
  simp only [Fin.sum_univ_one] at h1
  rw [sub_right_comm, h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

theorem casDom (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hU : IsUnitary actW B) (Ψ : (Fin k → NC R S) → W) :
    ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) ≤
      (Fintype.card (NC R S) : ℝ) * ((formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re -
        (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re) := by
  have hL : ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) =
      (Fintype.card (NC R S) : ℝ) * ∑ a, ∑ b, (if sameBlock a b then
        2 * (formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g))).re else 0) := by
    simp only [bracket_eq hU]
    rw [sum4', Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : sameBlock a b
    · simp only [if_pos h]
      have e : ∑ i, ∑ g, formT 1 B (factorOp 1 0 (Eab b a) (section1 Ψ i g))
            (fun h => actW (Eab b a) (section1 Ψ i g h)) =
          ((Fintype.card (NC R S) : ℝ) : ℂ) *
            formT k B ((∑ i, factorOp k i (Eab b a)) Ψ) (fun g => actW (Eab b a) (Ψ g)) := by
        simp only [position_section, ← Finset.mul_sum, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
        push_cast
        rfl
      have e2 := congrArg Complex.re e
      rw [Complex.re_ofReal_mul, Complex.re_sum] at e2
      simp only [Complex.re_sum] at e2
      simp only [← Finset.mul_sum, e2]
      ring
    · simp [h]
  rw [hL, diff_eq k hU Ψ]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (Nat.cast_nonneg _)
  split_ifs
  · linarith [formT_nonneg k hU ((∑ i, factorOp k i (Eab b a)) Ψ)]
  · exact le_rfl

end GlobalTheory.SteepMult.CasDom

end
end

