import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
import Formalism.CyclotomicNorms.Bundle0001
import Formalism.PairingDivisors.StatementN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinates
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_isHomogeneous_poly_coords :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
      ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
        ∀ x : L, Algebra.norm K x =
          MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first
  | exact @_root_.GlobalTheory.IdealPowerMembership.main
  | exact _root_.GlobalTheory.IdealPowerMembership.main
  | (apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerMembership.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPow
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

variable {L : Type} [Field L] (v : Valuation L ℝ≥0) {p : ℕ} {θ : ℝ≥0}

theorem approxRoot_pow_le (hθ : θ ≤ 1) {u w : L} (h : v (u - w ^ p) ≤ θ * v u) :
    v (w ^ p) ≤ v u := by
  have e : w ^ p = u - (u - w ^ p) := by ring
  rw [e]
  refine (Valuation.map_sub v _ _).trans (max_le le_rfl (h.trans ?_))
  simpa using mul_le_mul' hθ (le_refl (v u))

theorem approxRoot_mul (hθ : θ ≤ 1) {u u' w w' : L} (h : v (u - w ^ p) ≤ θ * v u)
    (h' : v (u' - w' ^ p) ≤ θ * v u') : v (u * u' - (w * w') ^ p) ≤ θ * v (u * u') := by
  have e : u * u' - (w * w') ^ p = u * (u' - w' ^ p) + w' ^ p * (u - w ^ p) := by ring
  rw [e, map_mul]
  refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v u * v (u' - w' ^ p) ≤ v u * (θ * v u') := mul_le_mul' le_rfl h'
      _ = θ * (v u * v u') := by ring
  · rw [map_mul]
    calc v (w' ^ p) * v (u - w ^ p) ≤ v u' * (θ * v u) :=
          mul_le_mul' (approxRoot_pow_le v hθ h') h
      _ = θ * (v u * v u') := by ring

theorem approxRoot_inv (hθ : θ < 1) {u w : L} (hu : u ≠ 0) (h : v (u - w ^ p) ≤ θ * v u) :
    v (u⁻¹ - (w⁻¹) ^ p) ≤ θ * v u⁻¹ := by
  have hvu : 0 < v u := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff v).mpr hu
  have hlt : v (w ^ p - u) < v u := by
    rw [Valuation.map_sub_swap]
    exact h.trans_lt (by simpa using mul_lt_mul_of_pos_right hθ hvu)
  have heq : v (w ^ p) = v u := Valuation.map_eq_of_sub_lt v hlt
  have hw : w ^ p ≠ 0 := by
    intro h0; rw [h0, map_zero] at heq; exact hvu.ne' heq.symm
  have e : u⁻¹ - (w⁻¹) ^ p = (w ^ p - u) * (u⁻¹ * (w ^ p)⁻¹) := by
    rw [inv_pow]; field_simp
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, heq, Valuation.map_sub_swap]
  calc v (u - w ^ p) * ((v u)⁻¹ * (v u)⁻¹) ≤ θ * v u * ((v u)⁻¹ * (v u)⁻¹) :=
        mul_le_mul' h le_rfl
    _ = θ * (v u)⁻¹ := by field_simp

theorem approxRoot_closed : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  intro L _ v p F θ hθ u u' ⟨w, hwF, hw⟩ ⟨w', hw'F, hw'⟩
  have hθ1 : θ ≤ 1 := hθ.le
  refine ⟨⟨w * w', F.mul_mem hwF hw'F, approxRoot_mul v hθ1 hw hw'⟩, fun hu' => ?_, fun k => ?_⟩
  · refine ⟨w * w'⁻¹, F.mul_mem hwF (F.inv_mem hw'F), ?_⟩
    rw [div_eq_mul_inv]
    exact approxRoot_mul v hθ1 hw (approxRoot_inv v hθ hu' hw')
  · induction k with
    | zero => exact ⟨1, F.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨x, hxF, hx⟩ := ih
      refine ⟨x * w, F.mul_mem hxF hwF, ?_⟩
      rw [pow_succ]
      exact approxRoot_mul v hθ1 hx hw

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniform
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem isClosed_setOf_algEquiv_apply_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (a b : L) : IsClosed {g : L ≃ₐ[K] L | g a = b} := by
  by_cases h : ∃ g₀ : L ≃ₐ[K] L, g₀ a = b
  · obtain ⟨g₀, hg₀⟩ := h
    have hc : IsClosed ((MulAction.stabilizer (L ≃ₐ[K] L) a : Subgroup _) : Set (L ≃ₐ[K] L)) :=
      Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral a)
    have hp := hc.preimage (continuous_const_mul g₀⁻¹)
    convert hp using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      mul_smul, inv_smul_eq_iff]
    simp only [AlgEquiv.smul_def, hg₀]
  · have : {g : L ≃ₐ[K] L | g a = b} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => h ⟨g, hg⟩
    rw [this]
    exact isClosed_empty

theorem exists_primitive_for_finset (k : Type) {Ω : Type} [Field k] [CharZero k] [Field Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (u : Finset Ω) : ∃ x : Ω, ∀ {L : Type} [Field L] (φ ψ : Ω →+* L),
      φ.comp (algebraMap k Ω) = ψ.comp (algebraMap k Ω) → φ x = ψ x →
      ∀ y ∈ u, φ y = ψ y := by
  let F : IntermediateField k Ω := IntermediateField.adjoin k (u : Set Ω)
  haveI : FiniteDimensional k F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k F
  refine ⟨α, fun {L} _ φ ψ hk hx y hy => ?_⟩
  have key : ∀ z : F, z ∈ IntermediateField.adjoin k {α} → φ z = ψ z := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx' =>
      rw [Set.mem_singleton_iff.mp hx']
      exact hx
    | algebraMap q =>
      exact DFunLike.congr_fun hk q
    | add x y _ _ hx hy => simp [hx, hy]
    | inv x _ hx => simp [hx]
    | mul x y _ _ hx hy => simp [hx, hy]
  exact key ⟨y, IntermediateField.subset_adjoin k _ hy⟩ (by rw [hα]; trivial)

theorem exists_algEquiv_inducing_of_forall_conj :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L]
      [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L)
      (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) →
      ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s h
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K L := {}
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hne := (isCompact_univ (X := L ≃ₐ[K] L)).inter_iInter_nonempty
    (fun x : Ω => {g : L ≃ₐ[K] L | g (j x) = j (s x)})
    (fun x => isClosed_setOf_algEquiv_apply_eq _ _)
    (fun u => by
      obtain ⟨x, hx⟩ := exists_primitive_for_finset ℚ u
      obtain ⟨g, hg⟩ := h x
      refine ⟨g, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro y hy
      exact hx ((g : L →+* L).comp j) (j.comp (s : Ω →+* Ω)) (RingHom.ext_rat _ _) hg y hy)
  obtain ⟨g, -, hg⟩ := hne
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hg
  exact ⟨g, hg⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwise
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem exists_algEquiv_apply_eq_of_fixes_preimage_base :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s hs x
  classical
  haveI : IsAlgClosure K L := ⟨‹_›, ‹_›⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral K (j x) := Algebra.IsIntegral.isIntegral _
  have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  have hcomp : j.comp (algebraMap ℚ Ω) = (algebraMap K L).comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  set Q : Polynomial Ω := (minpoly ℚ x).map (algebraMap ℚ Ω) with hQ
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hxint)
  have hQj : Q.map j = ((minpoly ℚ x).map (algebraMap ℚ K)).map (algebraMap K L) := by
    rw [hQ, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hdvd : minpoly K (j x) ∣ (minpoly ℚ x).map (algebraMap ℚ K) := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, ← hQj, eval_map, eval₂_at_apply, hQ, eval_map, ← aeval_def,
      minpoly.aeval, map_zero]
  set P : L[X] := (minpoly K (j x)).map (algebraMap K L) with hP
  have hPm : P.Monic := (minpoly.monic hint).map _
  have hPQ : P ∣ Q.map j := by
    rw [hQj]; exact Polynomial.map_dvd _ hdvd
  have hroots : ∀ r ∈ P.roots, r ∈ Set.range j := by
    intro r hr
    have h1 : r ∈ (Q.map j).roots :=
      Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hQ0) hPQ) hr
    rw [(IsAlgClosed.splits Q).roots_map j] at h1
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h1
    exact ⟨a, ha⟩
  have hlift : P ∈ lifts j := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨a, rfl⟩ := hroots r hr
    exact (mem_lifts _).2 ⟨X - C a, by simp⟩
  obtain ⟨M, hM⟩ := (mem_lifts _).1 hlift
  have hMs : M.map (s : Ω →+* Ω) = M := by
    ext n
    rw [coeff_map]
    refine hs _ ⟨(minpoly K (j x)).coeff n, ?_⟩
    rw [← coeff_map, ← coeff_map, hM]
  have hMx : M.eval x = 0 := by
    apply j.injective
    rw [← eval₂_at_apply, ← eval_map, hM, hP, eval_map, ← aeval_def, minpoly.aeval, map_zero]
  have hMsx : M.eval (s x) = 0 := by
    have h := eval₂_at_apply (p := M) (s : Ω →+* Ω) x
    rw [← eval_map, hMs, hMx, map_zero] at h
    exact h
  have hroot : aeval (j (s x)) (minpoly K (j x)) = 0 := by
    rw [aeval_def, ← eval_map, ← hP, ← hM, eval_map, eval₂_at_apply, hMsx, map_zero]
  exact (isConjRoot_of_aeval_eq_zero hint hroot).symm.exists_algEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

open MvPolynomial

theorem is_c1_of_finite_of_tsen_lang_systems : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  intro F K _ _ _ _ hF n d f hf hd hdn
  set m := Module.finrank F K with hm
  have hm0 : 0 < m := Module.finrank_pos
  let b : Module.Basis (Fin m) F K := Module.finBasis F K
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let g : Fin n → MvPolynomial (Fin (n * m)) K := fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))
  have hg : ∀ i, (g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  let G : MvPolynomial (Fin (n * m)) K := aeval g f
  have hG : G.IsHomogeneous d := by
    have h1 := hf.aeval g hg
    rwa [one_mul] at h1
  let P : Fin m → MvPolynomial (Fin (n * m)) F := fun l =>
    ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)
  have hP : ∀ l, (P l).IsHomogeneous d := fun l =>
    IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hs)))
  have hlt : m * d < n * m := by
    rw [mul_comm n m]; exact Nat.mul_lt_mul_of_pos_left hdn hm0
  obtain ⟨y, hy0, hy⟩ := hF (n * m) m d P hP hd hlt
  let x : Fin n → K := fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply hy0
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hxi : ∑ j, y (e (i, j)) • b j = 0 := by
      have := congrFun hx i
      simpa [x, Algebra.smul_def] using this
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j
  · have key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G := by
      rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
      show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)
      rw [MvPolynomial.aeval_bind₁]
      have hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i) := by
        funext i
        simp [g, x, mul_comm]
      rw [hxe]
      rfl
    have key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G
        = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l := by
      simp only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
      rw [Finset.sum_comm, MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      conv_lhs => rw [← b.sum_repr (G.coeff s)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [Finsupp.prod, map_prod, map_pow, Algebra.smul_def]
      ring
    rw [key, key2]
    exact Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
section
namespace GlobalTheory.ZModDual

theorem stdAddChar_comp_bijective (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun φ : Module.Dual (ZMod n) A =>
      ((ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom : AddChar A ℂ) := by
  first
  | exact @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | (apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar ..)

theorem card_dual_eq (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A]
    [Finite A] : Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_eq_of_bijective _ (stdAddChar_comp_bijective n A),
    Nat.card_eq_fintype_card (α := AddChar A ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

end GlobalTheory.ZModDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPowEqOneLeOfIsCyclicUnits
section
namespace GlobalTheory

private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn

theorem card_pow_eq_one_le_index_mul {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    [IsCyclic H] {d : ℕ} (hd : 0 < d) : Nat.card {x : G // x ^ d = 1} ≤ H.index * d := by
  classical

  set K : Subgroup G := (powMonoidHom d : G →* G).ker with hKdef
  have hK : Nat.card {x : G // x ^ d = 1} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hKdef]))
  have hsplit := (H.subgroupOf K).card_mul_index
  have hidx : (H.subgroupOf K).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := K))
  have hsmall : Nat.card (H.subgroupOf K) ≤ d := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : H.subgroupOf K => (⟨⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩ :
        {h : H // h ^ d = 1})) ?_) (card_pow_eq_one_le_of_isCyclic hd)
    · apply Subtype.ext
      have hx : (x.1 : G) ^ d = 1 := x.1.2
      simpa using hx
    · intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg (fun z : {h : H // h ^ d = 1} => ((z.1 : H) : G)) hxy
  rw [hK, ← hsplit]
  calc Nat.card (H.subgroupOf K) * (H.subgroupOf K).index ≤ d * H.index :=
        Nat.mul_le_mul hsmall hidx
    _ = H.index * d := Nat.mul_comm _ _

theorem card_pow_eq_one_le_units {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨Units.ofPowEqOne x.1 d x.2 hd.ne', Units.pow_ofPowEqOne _ _⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {u : Mˣ // u ^ d = 1} => ((z.1 : Mˣ) : M)) hxy
  simpa using this

theorem card_pow_eq_one_le_of_isCyclic_units (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d :=
  (card_pow_eq_one_le_units hd).trans (card_pow_eq_one_le_of_isCyclic hd)

theorem card_pow_eq_one_two_pow_le (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain _ | _ | n := w
  · omega
  ·
    have : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by norm_num)
    exact (card_pow_eq_one_le_of_isCyclic_units _ hd).trans (by omega)
  ·
    let u : (ZMod (2 ^ (n + 2)))ˣ :=
      ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))
    have hu : orderOf u = 2 ^ n := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
    have hG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
    have hidx : (Subgroup.zpowers u).index = 2 := by
      have h := (Subgroup.zpowers u).card_mul_index
      rw [Nat.card_zpowers, hu, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    calc Nat.card {x : ZMod (2 ^ (n + 2)) // x ^ d = 1}
        ≤ Nat.card {x : (ZMod (2 ^ (n + 2)))ˣ // x ^ d = 1} := card_pow_eq_one_le_units hd
      _ ≤ (Subgroup.zpowers u).index * d := card_pow_eq_one_le_index_mul _ hd
      _ = 2 * d := by rw [hidx]

theorem rootsOfUnityCount : Formalism.CyclotomicNorms.RootsOfUnityCount := by
  intro ℓ w d hℓ hw hd
  have : NeZero (ℓ ^ w) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact ⟨fun h => absurd rfl h, card_pow_eq_one_two_pow_le w hw hd⟩
  ·
    have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ h2 w
    have h := card_pow_eq_one_le_of_isCyclic_units (ℓ ^ w) (d := d) hd
    exact ⟨fun _ => h.trans (Nat.le_mul_of_pos_right _ (pow_pos hℓ.pos _)), h.trans (by omega)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CauchyParallelogramUpperHalfPlaneStatement
section
open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_segment_eq_parallelogram_sides : ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  first | exact @GlobalTheory.cauchy_parallelogram_upper_half_plane | exact GlobalTheory.cauchy_parallelogram_upper_half_plane | (intros; apply GlobalTheory.cauchy_parallelogram_upper_half_plane <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBound
section
namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance

theorem exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)

theorem cmValues_minPadicVal_bound : MinVal := by
  intro l n hl hn2 hne
  haveI := Fact.mk hl
  have hn0 : n ≠ 0 := by omega
  unfold mE
  by_cases h2 : l = 2
  · subst h2
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    have h := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne
    have h4 : padicValNat 2 (3 + 1) = 2 := by
      norm_num
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2' : padicValNat 2 (3 - 1) = 1 := by norm_num
    rw [h4, h2'] at h
    simp only [if_true]
    omega
  · simp only [h2, if_false]
    have hodd : Odd l := hl.odd_of_ne_two h2
    by_cases hd : (l - 1) ∣ n
    · simp only [hd, if_true]
      refine ⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩
      · first
          | exact (Nat.coprime_succ_self l)
          | exact (Nat.coprime_self_succ l)
          | simp
      · have h := padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega)
          (by simp) (by
            intro hdv
            have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).mp hdv
            exact hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0
        rw [one_pow] at h
        rw [h, show l + 1 - 1 = l by omega, padicValNat_self]
    · simp only [hd, if_false]
      obtain ⟨a, ha2, hac, hnd⟩ := exists_pow_ne_one_mod l n hl hd
      exact ⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApproxStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  first | exact @GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | exact GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | (intros; apply GlobalTheory.UniformCoboundary.coboundary_of_padic_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimensionStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_finiteType_ideal_codimension : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧ (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ → Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) → I = J) := by
  first | exact @GlobalTheory.DedekindCodim.dedekind_finiteType_codim | exact GlobalTheory.DedekindCodim.dedekind_finiteType_codim | (intros; apply GlobalTheory.DedekindCodim.dedekind_finiteType_codim <;> assumption)
end

