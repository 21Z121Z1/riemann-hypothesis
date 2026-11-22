import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDlogCoef
section
open GlobalTheory.K5 Polynomial

noncomputable section
namespace GlobalTheory.K5.DlogCoef

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem smul_mk (J : Ideal (On p n)) (a b : On p n) :
    a • (Ideal.Quotient.mk J b) = Ideal.Quotient.mk J (a * b) := by
  first
  | rfl
  | exact (Submodule.Quotient.mk_smul _ _ _).symm
  | simp [Algebra.smul_def]

theorem deriv_pow (J : Ideal (On p n)) (D : Derivation (O0 p) (On p n) (On p n ⧸ J))
    (r c : On p n) (h : D r = Ideal.Quotient.mk J (c * r)) (i : ℕ) :
    D (r ^ i) = Ideal.Quotient.mk J ((i : On p n) * c * r ^ i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, h, smul_mk, smul_mk, ← map_add]
    congr 1
    push_cast
    ring

end GlobalTheory.K5.DlogCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsZeroAtFinsetSum
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isZeroAt_zero_fun (c : OnePoint ℝ) (k : ℤ) : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  simpa using! Filter.zero_zeroAtFilter _

theorem isZeroAt_finset_sum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isZeroAt_zero_fun c k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_cuspForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hinv : ∀ γ ∈ GlobalTheory.Hk.lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ =>
    SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := GlobalTheory.Hk.uOp q ⇑f
            slash_action_eq' := fun A hA => by
              obtain ⟨A, hA, rfl⟩ := hA
              exact hU A hA
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq.pos (CuspFormClass.holo f)).1
            zero_at_cusps' := fun {c} hc => by
              rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq.pos]
              exact isZeroAt_finset_sum _ c k _ fun j _ =>
                GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.pos) f c hc }, rfl⟩

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
section
namespace GlobalTheory.IwahoriEigenObj

theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymEqOfModEqFourMul
section
namespace GlobalTheory

theorem jacobiSym_eq_of_modEq_four_mul (a q q' : ℕ) (hq : Odd q) (hq' : Odd q')
    (h : q ≡ q' [MOD 4 * a]) : jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) q' := by
  rw [jacobiSym.mod_right' a hq, jacobiSym.mod_right' a hq']
  unfold Nat.ModEq at h
  rw [h]

theorem jacobiSym_const_on_class : Formalism.HermitianLattices.GL2a2.ClassConst := by
  intro m₀ d q q' h8 hd hsq hq hq' hqq
  have h4 : 4 ∣ m₀ := Dvd.dvd.trans (by norm_num) h8
  have key : ∀ e : ℕ, Odd e → e ∣ m₀ → jacobiSym (e : ℤ) q = jacobiSym (e : ℤ) q' := by
    intro e he hem
    have hc : Nat.Coprime 4 e := by
      have h2 : Nat.Coprime 2 e := Nat.coprime_two_left.mpr he
      simpa using Nat.Coprime.pow_left 2 h2
    exact jacobiSym_eq_of_modEq_four_mul e q q' hq hq'
      (hqq.of_dvd (hc.mul_dvd_of_dvd_of_dvd h4 hem))
  rcases Nat.even_or_odd d with hev | hodd
  · obtain ⟨e, rfl⟩ := hev.two_dvd
    have he : Odd e := by
      rcases Nat.even_or_odd e with h | h
      · obtain ⟨f, rfl⟩ := h.two_dvd
        have : IsUnit (2 : ℕ) := hsq 2 ⟨f, by ring⟩
        simp at this
      · exact h
    have h2 := jacobiSym_eq_of_modEq_four_mul 2 q q' hq hq' (hqq.of_dvd h8)
    have he' := key e he (Dvd.dvd.trans (Dvd.intro_left 2 rfl) hd)
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left, h2, he']
  · exact key d hodd hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymNegEqOfThreeModFour
section
namespace GlobalTheory

theorem jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.neg _ hn]
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hq h]
    ring

theorem kronOdd_holds : Formalism.HermitianLattices.GL2a2.KronOdd :=
  fun q n hq hn => jacobiSym_neg_eq_of_three_mod_four q n hq hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JointHarmonicOfHookNorm
section
noncomputable section

namespace GlobalTheory.JointHarm

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials

section Minors

variable {R : Type*} [CommRing R]

variable {n l : ℕ}

end Minors

variable {n p q : ℕ}

section Killed

end Killed

section Fock

open Formalism.E

theorem fock_add_left {σ : Type} (P P' Q : MvPolynomial σ ℂ) :
    fock (P + P') Q = fock P Q + fock P' Q := by
  classical
  have key : ∀ (F : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)), F.support ⊆ s →
      fock F Q = ∑ m ∈ s, F.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
    intro F s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
  rw [key _ _ support_add, key P _ Finset.subset_union_left, key P' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

theorem fock_monomial_left {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by
  classical
  unfold fock
  rw [support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp

variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem mapDomain_add_inj (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by
  constructor
  · ext x
    have := DFunLike.congr_fun h (f x)
    have hx : f x ∉ Set.range g := fun ⟨y, hy⟩ => hfg x y hy.symm
    simpa [Finsupp.mapDomain_apply hf, Finsupp.mapDomain_notin_range _ _ hx] using this
  · ext y
    have := DFunLike.congr_fun h (g y)
    have hy : g y ∉ Set.range f := fun ⟨x, hx⟩ => hfg x y hx
    simpa [Finsupp.mapDomain_apply hg, Finsupp.mapDomain_notin_range _ _ hy] using this

theorem coeff_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    coeff (α.mapDomain f + β.mapDomain g) (rename f P * rename g Q) = coeff α P * coeff β Q := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [map_add, add_mul, coeff_add, h, h']
  | monomial α' x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add, mul_add, coeff_add, h, h']
    | monomial β' y =>
      rw [rename_monomial, rename_monomial, monomial_mul, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases h : α'.mapDomain f + β'.mapDomain g = α.mapDomain f + β.mapDomain g
      · obtain ⟨rfl, rfl⟩ := mapDomain_add_inj hf hg hfg h
        simp
      · rw [if_neg h]
        split_ifs with h1 h2
        · exact absurd (by rw [h1, h2]) h
        all_goals simp

theorem mfact_mapDomain_add (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) :
    Formalism.A.mfact (α.mapDomain f + β.mapDomain g) = Formalism.A.mfact α * Formalism.A.mfact β := by
  classical
  unfold Formalism.A.mfact
  rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_mapDomain_index_inj hf,
    Finsupp.prod_mapDomain_index_inj hg]
  rw [Finsupp.mapDomain_support_of_injective hf, Finsupp.mapDomain_support_of_injective hg,
    Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
  exact hfg x y hy.symm

theorem fock_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (P P' : MvPolynomial σ₁ ℂ) (Q Q' : MvPolynomial σ₂ ℂ) :
    fock (rename f P * rename g Q) (rename f P' * rename g Q') = fock P P' * fock Q Q' := by
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h h' => simp only [map_add, add_mul, fock_add_left, h, h']
  | monomial α x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q₁ Q₂ h h' => simp only [map_add, mul_add, fock_add_left, h, h']
    | monomial β y =>
      rw [rename_monomial, rename_monomial, monomial_mul, fock_monomial_left, fock_monomial_left,
        fock_monomial_left, coeff_rename_mul hf hg hfg, mfact_mapDomain_add hf hg hfg, star_mul']
      push_cast
      ring

end Fock

end GlobalTheory.JointHarm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerDRootTwist
section
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem kaehlerD_root_twist (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ζ : Sˣ) (r : S)
    (N a : ℕ) (hN : 1 ≤ N) (hζ : (ζ : S) ^ N = 1) :
    ((ζ : S) ^ a * r) ^ (N - 1) • KaehlerDifferential.D R S ((ζ : S) ^ a * r) =
      r ^ (N - 1) • KaehlerDifferential.D R S r +
        ((a : S) * r ^ N * ((ζ⁻¹ : Sˣ) : S)) • KaehlerDifferential.D R S (ζ : S) ∧
    (N : S) • (r ^ (N - 1) • KaehlerDifferential.D R S r) = KaehlerDifferential.D R S (r ^ N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hzi : (ζ : S) * ((ζ⁻¹ : Sˣ) : S) = 1 := Units.mul_inv ζ
  constructor
  · rw [Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]
    simp only [smul_add, smul_smul]
    congr 2
    · have hw : ((ζ : S) ^ a) ^ (M + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
      rw [mul_pow]
      linear_combination r ^ M * hw
    · rcases a with _ | b
      · simp
      · have hw : ((ζ : S) ^ (b + 1)) ^ (M + 1) = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        linear_combination ((b : S) + 1) * r ^ (M + 1) *
          (((ζ⁻¹ : Sˣ) : S) * hw - ((ζ : S) ^ (b + 1)) ^ M * (ζ : S) ^ b * hzi)
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, Nat.add_sub_cancel]

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegralStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt p x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt p (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  first | exact @GlobalTheory.KumDlog.kaehler_rel_isInt | exact GlobalTheory.KumDlog.kaehler_rel_isInt | (intros; apply GlobalTheory.KumDlog.kaehler_rel_isInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClass
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kum_eq_of_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} (hN : 0 < N) {ζ θ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) (g : Ω ≃ₐ[K] Ω) (i : ZMod N) (hg : g θ = ζ ^ i.val * θ) :
    kum ζ θ g = i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hex : ∃ j : ZMod N, g θ = ζ ^ j.val * θ := ⟨i, hg⟩
  unfold kum
  rw [dif_pos hex]
  have h1 := hex.choose_spec
  have h2 : ζ ^ i.val = ζ ^ hex.choose.val := mul_right_cancel₀ hθ (hg.symm.trans h1)
  have h3 := (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)) h2
  exact (ZMod.val_injective N h3).symm

theorem eta_kummer_galoisInvariant : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix a b α β ha hb hα hβ η hη hcob
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  set E := IntermediateField.adjoin K ({α, β} : Set Ω) with hE
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hα; exact ha ((map_eq_zero _).mp hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hβ; exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨-, hαapp, hαmul, hαker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨-, hβapp, hβmul, hβker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  let x : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ α g)) (fun g h => by simp [hαmul, ofAdd_add])
  let y : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ β g)) (fun g h => by simp [hβmul, ofAdd_add])
  obtain ⟨-, hconj, hhom⟩ := GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary (Ω ≃ₐ[K] Ω) N x y η (fun g h => hcob g h)

  have memH : ∀ g : Ω ≃ₐ[K] Ω, g ∈ E.fixingSubgroup ↔ g α = α ∧ g β = β := by
    intro g
    constructor
    · intro hg
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg α
          (IntermediateField.subset_adjoin K _ (by simp)),
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg β
          (IntermediateField.subset_adjoin K _ (by simp))⟩
    · rintro ⟨h1, h2⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      | algebraMap r => exact g.commutes r
      | add u v _ _ hu hv => rw [map_add, hu, hv]
      | inv u _ hu => rw [map_inv₀, hu]
      | mul u v _ _ hu hv => rw [map_mul, hu, hv]
  have kα0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ α g = 0 := fun g hg => (hαker g).2 ((memH g).1 hg).1
  have kβ0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ β g = 0 := fun g hg => (hβker g).2 ((memH g).1 hg).2
  have hηhom : ∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, η (g * h) = η g + η h :=
    fun g hg h _ => hhom g h (kα0 g hg)
  obtain ⟨θ, hθ0, hθE, hθapp⟩ := GlobalTheory.T.exists_kummer_generator_of_locallyConstant_hom K Ω N ζ hN hζ hfix E η hη hηhom
  have hkθ : ∀ g ∈ E.fixingSubgroup, η g = kum ζ θ g := fun g hg =>
    (kum_eq_of_apply hN hζ hθ0 g (η g) (hθapp g hg)).symm
  refine ⟨θ, hθ0, hθE, hkθ, fun s => ?_⟩

  have hconjH : ∀ m ∈ E.fixingSubgroup, s⁻¹ * m * s ∈ E.fixingSubgroup ∧ η (s⁻¹ * m * s) = η m := by
    intro m hm
    obtain ⟨hmα, hmβ⟩ := (memH m).1 hm
    have hsα : m (s α) = s α := by
      rw [hαapp s, map_mul, map_pow, hfix m, hmα]
    have hsβ : m (s β) = s β := by
      rw [hβapp s, map_mul, map_pow, hfix m, hmβ]
    refine ⟨(memH _).2 ⟨?_, ?_⟩, ?_⟩
    · show s⁻¹ (m (s α)) = α
      rw [hsα]; exact s.symm_apply_apply α
    · show s⁻¹ (m (s β)) = β
      rw [hsβ]; exact s.symm_apply_apply β
    · have := hconj s⁻¹ m
      rw [inv_inv] at this
      rw [this]
      simp [x, y, kα0 m hm, kβ0 m hm]
  set u := s θ / θ with hu
  have hsθ0 : s θ ≠ 0 := by simpa using hθ0
  have hu0 : u ≠ 0 := div_ne_zero hsθ0 hθ0
  refine ⟨u, ?_, hu0, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro m hm
    obtain ⟨hmem, hηeq⟩ := hconjH m hm
    have h1 : m θ = ζ ^ (η m).val * θ := hθapp m hm
    have h2 : (s⁻¹ * m * s) θ = ζ ^ (η m).val * θ := by rw [← hηeq]; exact hθapp _ hmem
    have h3 : m (s θ) = ζ ^ (η m).val * s θ := by
      have : s ((s⁻¹ * m * s) θ) = m (s θ) := by
        show s (s⁻¹ (m (s θ))) = m (s θ)
        exact s.apply_symm_apply _
      rw [← this, h2, map_mul, map_pow, hfix s]
    have hz : ζ ^ (η m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [hu, map_div₀, h1, h3, mul_div_mul_left _ _ hz]
  · rw [map_pow, hu, div_pow, mul_div_cancel₀ _ (pow_ne_zero N hθ0)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombinationStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination : ∀ (p : ℕ) [Fact p.Prime] (f : Lau p), ∃ (g : Fin p → Lau p) (h : Lau p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  first | exact @GlobalTheory.K5.LauZ.exists_pow_comb | exact GlobalTheory.K5.LauZ.exists_pow_comb | (intros; apply GlobalTheory.K5.LauZ.exists_pow_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineFunctionalEqPeriodMulStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_functional_eq_period_mul_alt : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  first | exact @GlobalTheory.line_functional_eq_period_mul | exact GlobalTheory.line_functional_eq_period_mul | (intros; apply GlobalTheory.line_functional_eq_period_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
end

