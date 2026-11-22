import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralEqGenericIntersection
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegralStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_unit_log_integral : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) → ∀ j : K → FlBlock Ψ N, IsChain j → ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEvalStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_polynomial_eval : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3FromLocal
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

noncomputable section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [divCycle, h]

theorem C_not_mem {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : O} (ha : a ≠ 0) :
    (C a : MRing ι O) ∉ P := by
  intro h
  have h' : a ∈ P.comap (C : O →+* MRing ι O) := h
  rw [hP.noTorsion] at h'
  exact ha (by simpa using h')

theorem laNum_eq (P : Ideal (MRing ι O)) (a : O) {r : ℕ} (x : Fin r → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) :
    ((laNum P a x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum (divCycle P (C a)) x (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1)) Q := by
  have h := (cycNum_int_and_comb O K ι (Fin r) x Q).1 (divCycle P (C a))
    (divCycle_support_finite P (C a)) (psum (Fin r) ℤ (k - 1))
  have e : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ (k - 1)) =
      ∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1) := by
    simp [psum, map_sum]
  rw [e] at h
  rw [h, laNum]
  push_cast
  rfl

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]

theorem liePs_inl (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inl τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j => (τ, Fin.castAdd j' i))
        (∑ i : Fin j, (X i : MvPolynomial (Fin j) ℝ) ^ m) := by
  simp only [liePs, map_sum, map_pow, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem liePs_inr (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inr τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j' => (τ, Fin.natAdd j i))
        (∑ i : Fin j', (-(X i : MvPolynomial (Fin j') ℝ)) ^ m) := by
  simp only [liePs, map_sum, map_pow, map_neg, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ x : Fin j, ¬ j ≤ (x : ℕ) := fun x => not_le.2 x.2
  simp [h0]

theorem cycNum_neg {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d)
    {a : O} (ha : a ≠ 0) {r : ℕ} (cls : Fin r → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (hQ : m + Q.length = d) :
    cycNum (divCycle P (C a)) (fun i => -cls i) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) Q =
      cycNum (divCycle P (C a)) cls (∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m) Q := by
  have hC : IsMultiHomog (C a : MRing ι O) (0 : K → ℕ) := isWeightedHomogeneous_C _ a
  have hH : (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m).IsHomogeneous m :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X ℝ i).pow m
  have h := (GlobalTheory.T.divisor_cycle_substitution O ϖ hϖ K ι P d hP 0 0 (C a) (C a) hC hC (C_not_mem hP ha) (C_not_mem hP ha)
    (Fin r) (Fin r) cls (fun t i => if t = i then -1 else 0) _ m hH Q hQ).2
  have e1 : (fun t : Fin r => ∑ i, (if t = i then (-1 : ℤ) else 0) • cls i) = fun i => -cls i := by
    funext t
    simp
  have e2 : aeval (fun t : Fin r => ∑ i, (C (((if t = i then (-1 : ℤ) else 0 : ℤ)) : ℝ) * X i :
      MvPolynomial (Fin r) ℝ)) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) =
      ∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m := by
    simp [map_sum, apply_ite]
  rw [e1, e2] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

namespace GlobalTheory.CompanionTheory.Ar.Num

open GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3 in

theorem flag_m3_of_local_m3 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p hp Ψ _ _ j j' φ T lie om hl ho hr hM τ k hk Q hQ
  set Z := divCycle P (C (p : O)) with hZ
  have hm : k - 1 + Q.length = d := by omega

  have hlab : ∀ τ' : Ψ ⊕ Ψ, ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum Z T.x (liePs j (k - 1) τ') Q := by
    rintro (t | t)
    · have e : (lie (Sum.inl t)).x = fun i : Fin j => T.x (t, Fin.castAdd j' i) := by
        rw [hl t]; rfl
      have e' : ((laNum P (p : O) (lie (Sum.inl t)).x k Q : ℤ) : ℝ) =
          ((laNum P (p : O) (fun i : Fin j => T.x (t, Fin.castAdd j' i)) k Q : ℤ) : ℝ) :=
        congrArg (fun y : Fin j → K → ℤ => ((laNum P (p : O) y k Q : ℤ) : ℝ)) e
      rw [e', laNum_eq, liePs_inl, (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
    · rw [hr t k Q hQ, laNum_eq, cycNum_neg hϖ hP hp _ _ Q hm, liePs_inr,
        (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
  have hL := hM k hk Q hQ (Sum.inl τ)
  have e1 : (lie (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j) => L.ck P k Q) (hl τ)
  have e2 : (om (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j') => L.ck P k Q) (ho τ)
  have hadd := GlobalTheory.T.local_pair_split_sum O K ι j j' (T.comp fun i : Fin (j + j') => (τ, i)) P k Q
  have hlin := GlobalTheory.T.cycle_number_linear O K ι (Ψ × Fin (j + j')) Z T.x Q
  rw [e1, e2] at hL
  have hleft : (((T.comp fun i : Fin (j + j') => (τ, i)).ck P k Q : ℤ) : ℝ) =
      (((T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q : ℤ) : ℝ) +
      (((T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q : ℤ) : ℝ) := by
    rw [hadd]
    push_cast
    rfl
  rw [hleft, hL, bracket]
  rw [hlin.2.1, hlin.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  rw [hlin.2.1, hlab τ']
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricFamilyIntersectionEq
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.TopLink

section Cyc

variable {K : Type} [DecidableEq K] {ι : K → Type}

theorem intNumL_perm (F : Type) [Field F] (V : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ) := ⟨fun a b g => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cycList_perm (Z : Ideal (MRing ι O) → ℤ) {l l' : List (K → ℤ)} (h : l.Perm l') :
    cycList Z l = cycList Z l' := by
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm (IsLocalRing.ResidueField O) (specialIdeal W) h

omit [DecidableEq K] in

theorem divCycle_mul_finite {R : Type} [CommRing R] [IsNoetherianRing (MRing ι R)] (P : Ideal (MRing ι R))
    (f : MRing ι R) (n : Ideal (MRing ι R) → ℤ) :
    (Function.support fun W => divCycle P f W * n W).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp only [divCycle]
  rw [dif_neg (fun h' => h h'.1), zero_mul]

theorem cycList_ratDiv [Fintype K] [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (f g : MRing ι O)
    (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  unfold cycList cycEval ratDiv
  simp only [sub_mul]
  exact finsum_sub_distrib (divCycle_mul_finite P f _) (divCycle_mul_finite P g _)

end Cyc

theorem link_monomial {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {σ : Type} {S : Finset Nat.Primes} {T : LocPair ι ℤ σ} (hT : T.IsVertOff P S)
    {A A' : σ → HermLine ι} (hA : ∀ i, IsSmoothHerm (A i)) (hA' : ∀ i, IsSmoothHerm (A' i))
    (hiso : T.IsIsometric P A A') (i : σ) (μ : σ ⊕ σ →₀ ℕ) (hμ : μ.toMultiset.card = D) :
    arList I P (((μ + Finsupp.single (Sum.inl i) 1).toMultiset.map (Sum.elim A A')).toList) -
      arList I P (((μ + Finsupp.single (Sum.inr i) 1).toMultiset.map (Sum.elim A A')).toList) =
    ∑ p ∈ S, Real.log (p : ℕ) *
      (cycList (ratDiv (extTo (ZP p) P) (MvPolynomial.map (Int.castRingHom (ZP p)) (T.f i))
        (MvPolynomial.map (Int.castRingHom (ZP p)) (T.g i))) (classList (Sum.elim T.x T.x') μ ++ []) : ℝ) := by
  classical
  set m := μ.toMultiset.toList with hm
  have hlen : m.length = D := by rw [hm, Multiset.length_toList, hμ]
  subst hlen
  let L : Fin m.length → HermLine ι := fun j => Sum.elim A A' (m.get j)
  have hB : ∀ s, IsSmoothHerm (Sum.elim A A' s) := by
    rintro (s | s)
    · exact hA s
    · exact hA' s
  have hL : ∀ j, IsSmoothHerm (L j) := fun j => hB _
  have hofL : List.ofFn L = m.map (Sum.elim A A') := by
    conv_rhs => rw [← List.ofFn_get m]
    rw [List.map_ofFn]
    rfl
  have key : ∀ s, arList I P (((μ + Finsupp.single s 1).toMultiset.map (Sum.elim A A')).toList) =
      I P (m.length + 1) (Fin.snoc L (Sum.elim A A' s)) := by
    intro s
    apply arList_eq_of_perm hP hI
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; exact hB s
      · rw [Fin.snoc_castSucc]; exact hL j
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [show (List.ofFn fun j => L j) = m.map (Sum.elim A A') from hofL, ← Multiset.coe_eq_coe,
        Multiset.coe_toList, List.concat_eq_append, ← Multiset.coe_add, ← Multiset.map_coe, hm,
        Multiset.coe_toList, map_add, Finsupp.toMultiset_single, Multiset.map_add]
      simp
  have hdeg : (List.ofFn fun j => (L j).a).Perm (classList (Sum.elim T.x T.x') μ ++ []) := by
    have h1 : (List.ofFn fun j => (L j).a) = m.map (Sum.elim T.x T.x') := by
      conv_rhs => rw [← List.ofFn_get m]
      rw [List.map_ofFn]
      congr 1
      funext j
      simp only [L, Function.comp]
      rcases m.get j with s | s
      · exact (hiso s).1
      · exact (hiso s).2.1
    rw [h1, List.append_nil, classList, ← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, hm,
      Multiset.coe_toList]
  rw [key, key]
  have step := GlobalTheory.T.isometric_vertical_intersection_eq K ι P m.length hP I hI S (T.comp fun _ : Unit => i) (fun _ => hT i)
    (A i) (A' i) (hA i) (hA' i) (fun _ => hiso i) L hL
  refine step.trans (Finset.sum_congr rfl fun p _ => ?_)
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -⟩ := hT i
  have e1 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bf (T.f i) hf hfP (List.ofFn fun j => (L j).a) (by simp)
  have e2 := GlobalTheory.T.vertical_number_local_cycle K ι P m.length hP p bg (T.g i) hg hgP (List.ofFn fun j => (L j).a) (by simp)
  rw [← cycList_perm _ hdeg, cycList_ratDiv, ← e1, ← e2]
  push_cast
  rfl

theorem arNum_eq_sum_log_val : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (σ : Type) [Fintype σ] (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff P S → ∀ A A' : σ → HermLine ι, (∀ i, IsSmoothHerm (A i)) → (∀ i, IsSmoothHerm (A' i)) → T.IsIsometric P A A' → ∀ (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ), IsMixExpansion D V Gs → arNum I P (Sum.elim A A') V = ∑ p ∈ S, Real.log (p : ℕ) * (T.map (Int.castRingHom (ZP p))).val (extTo (ZP p) P) Gs := by
  intro K _ _ ι _ P D hP I hI σ _ S T hT A A' hA hA' hiso V Gs hV
  classical
  obtain ⟨rfl, hG⟩ := hV
  rw [arNum_sum']
  simp only [LocPair.val, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cycNum, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [(Gs i).as_sum, Finset.mul_sum, arNum_sum']
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hcard : μ.toMultiset.card = D := by
    have h := hG i (MvPolynomial.mem_support_iff.1 hμ)
    rw [Finsupp.card_toMultiset, ← h, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hpoly : (X (Sum.inl i) - X (Sum.inr i)) * monomial μ (coeff μ (Gs i)) =
      monomial (μ + Finsupp.single (Sum.inl i) 1) (coeff μ (Gs i)) +
        monomial (μ + Finsupp.single (Sum.inr i) 1) (-coeff μ (Gs i)) := by
    rw [monomial_add_single, monomial_add_single, map_neg]
    ring
  have hmono := link_monomial hP hI hT hA hA' hiso i μ hcard
  rw [hpoly, arNum_add', arNum_monomial', arNum_monomial', neg_mul, ← sub_eq_add_neg, ← mul_sub, hmono,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [LocPair.map]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.TopLink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_model_over_place : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], pointIdeal O y = (pointIdeal A y).map (MvPolynomial.map (algebraMap A O)) ∧ IsModelOver (pointIdeal O y) D ∧ ∀ (ϖ : O), Irreducible ϖ → ∀ (σ : Type) (S : Finset Nat.Primes) (T : LocPair ι ℤ σ), T.IsVertOff (mCoordIdeal y) S → (T.map (Int.castRingHom O)).IsVert (pointIdeal O y) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.pl_model | exact GlobalTheory.CompanionTheory.Ar.Num.pl_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.pl_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralEqGenericIntersectionStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_integral_eq_generic_intersection : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) = (intNum ℚ (extTo ℚ P) (fun j => (L j).a) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_one_eq_intNum | exact GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_one_eq_intNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ptsIntegral_one_eq_intNum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem ht_combLine_integral_multiple : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  intro II hII Ψ _ N M t lam s q n W hn hW
  have hpos : 0 < degC W := GroundTheory.Heights₂.Heights.LowerBoundFree.degC_pos_of_isArithVar_one hW.1
  refine ⟨hpos, ?_⟩
  have hl : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hupd : ∀ B : HermLine M.ι, Function.update (![M.A] : Fin 1 → HermLine M.ι) 0 B = ![B] := by
    intro B
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp
  have hL : ∀ i, IsSmoothHerm ((![M.A] : Fin 1 → HermLine M.ι) i) := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact M.A_smooth
  have h := GlobalTheory.T.arith_intersection_multilinear II hII M.K M.ι W 1 ![M.A] 0 (Option (Ψ × Fin N)) (M.line t) n hW.1 hL hl
  simp only [hupd] at h
  have hd : (degC W : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h, RootModel.ht, mul_assoc, div_mul_cancel₀ _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hn j, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Top
end

