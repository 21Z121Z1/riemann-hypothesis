import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetractionStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_fittingDatum_retraction : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (exact GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_basicOpen_fibres_preirreducible :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B →
    ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) →
    PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) →
    ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧
      (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧
      ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) →
        IsPreirreducible {r : PrimeSpectrum B |
          r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  intro A B _ _ _ hsm q Ω _ _ _ hq hΩ
  obtain ⟨b, hbq, n, _, hST, hSE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q.asIdeal)
  have hΩb := GlobalTheory.T.preirreducible_tensor_localization_away A B b Ω hΩ
  obtain ⟨a, I, haΩ, hIΩ, hall⟩ := GlobalTheory.T.preirreducible_fibre_standardEtale_spreads A (Localization.Away b) n hSE Ω hΩb
  have memq : ∀ x : A, algebraMap A B x ∈ q.asIdeal ↔ algebraMap A Ω x = 0 := by
    intro x
    have := congrArg (x ∈ ·) hq
    simpa [Ideal.mem_comap, RingHom.mem_ker] using this
  refine ⟨b, a, I, hbq, fun h => haΩ ((memq a).1 h), fun c hc => (memq c).2 (hIΩ c hc), ?_⟩
  intro t hat hIt
  let k := AlgebraicClosure t.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap A k) = t.asIdeal := by
    rw [IsScalarTower.algebraMap_eq A t.asIdeal.ResidueField k, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap t.asIdeal.ResidueField k).injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  have hmem : ∀ x : A, algebraMap A k x = 0 ↔ x ∈ t.asIdeal := by
    intro x; rw [← RingHom.mem_ker, hker]
  have hk := hall k (fun h => hat ((hmem a).1 h)) (fun c hc => (hmem c).2 (hIt c hc))
  have himg := (PreirreducibleSpace.isPreirreducible_univ (X := PrimeSpectrum (k ⊗[A] Localization.Away b))).image
    (PrimeSpectrum.comap ((Algebra.TensorProduct.includeRight :
      Localization.Away b →ₐ[A] k ⊗[A] Localization.Away b).toRingHom.comp
        (algebraMap B (Localization.Away b))))
    (PrimeSpectrum.continuous_comap _).continuousOn
  convert himg using 1
  rw [Set.image_univ, PrimeSpectrum.comap_comp, Set.range_comp,
    GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker, hker]
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hr, hbr⟩
    have : r ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]; exact hbr
    obtain ⟨r', rfl⟩ := this
    refine ⟨r', ?_, rfl⟩
    rw [← hr, IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
    rfl
  · rintro ⟨r', hr', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hr', IsScalarTower.algebraMap_eq A B (Localization.Away b), ← Ideal.comap_comap]
      rfl
    · have : PrimeSpectrum.comap (algebraMap B (Localization.Away b)) r' ∈
          Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := ⟨r', rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b) b] at this
      exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperators
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ.Shuf

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

theorem bop_id (n m : ℕ) : bop (𝟙 (SimplexCategory.mk n)) (𝟙 (SimplexCategory.mk m)) = 𝟙 (bo n m) := rfl

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    dsimp only
    split_ifs with hji
    · dsimp only
      rw [fc_comp_fc n i j hji (by omega), ← add_smul]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show i' + 1 - 1 = i' by omega, pow_succ]
      ring_nf
      simp
    · dsimp only
      rw [fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]
      ring_nf
      simp
  · rintro ⟨i, j⟩ _ _
    dsimp only
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    split_ifs <;> simp only <;> omega
  · rintro ⟨i, j⟩ _
    by_cases h : j < i
    · simp only [h, if_true]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega
    · simp only [h, if_false]
      rw [if_pos (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega

theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  subst hk
  have hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d =
      ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) +
        ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d) := by
    intro x
    simp only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]
    rw [add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  have hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  rw [Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]
  · dsimp only
    by_cases h : a = c + 1 ∧ b = d + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [dH_comp_dV c d, ← add_smul, pow_succ]
      simp
    · have e1 : dH a b c (d + 1) = 0 := by unfold dH; rw [if_neg h]
      have e2 : dV a b (c + 1) d = 0 := by unfold dV; rw [if_neg h]
      rw [e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dH x1 x2 c d = 0 := by
      unfold dH; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dV x1 x2 c d = 0 := by
      unfold dV; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]

noncomputable def shufRec (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n : ℕ) :
    ∀ a b : ℕ, bo a b ⟶ bo n n :=
  Nat.rec (motive := fun n => ∀ a b : ℕ, bo a b ⟶ bo n n) (fun a b => idO a b 0 0)
    (fun n g a b => if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ g x.1 x.2) else 0) n

theorem shufRec_zero (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (a b : ℕ) :
    shufRec cone 0 a b = idO a b 0 0 := rfl

theorem shufRec_succ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n a b : ℕ) :
    shufRec cone (n + 1) a b = if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ shufRec cone n x.1 x.2) else 0 := rfl

theorem exists_shuffle : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧
    ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  obtain ⟨cone, ε, hε, h0, hs⟩ := GlobalTheory.T.cone_contracting_homotopy
  have hid : shufRec cone 0 0 0 = 𝟙 (bo 0 0) := by
    rw [shufRec_zero]
    rw [idO, if_pos ⟨rfl, rfl⟩, idc_self]
    exact bop_id 0 0
  refine ⟨fun a b n => shufRec cone n a b, hid, ?_⟩
  intro a b n
  induction n generalizing a b with
  | zero =>
    intro hab
    dsimp only
    rw [shufRec_succ, if_pos hab, h0]
    have hr : ε a b (∑ x ∈ Finset.HasAntidiagonal.antidiagonal 0, dT a b x.1 x.2 ≫ shufRec cone 0 x.1 x.2) = 0 := by
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      dsimp only
      rw [hid, Category.comp_id]
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
    rw [hr, zero_smul, sub_zero]
  | succ n ih =>
    intro hab
    dsimp only at ih ⊢
    rw [shufRec_succ, if_pos hab, hs]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
        (dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n =
          ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, (dT a b x.1 x.2 ≫ dT x.1 x.2 y.1 y.2) ≫
            shufRec cone n y.1 y.2 := by
      intro x hx
      rw [Category.assoc, ih x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
      simp only [Category.assoc]
    have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫
        dD (n + 1) n = 0 := by
      rw [Preadditive.sum_comp, Finset.sum_congr rfl step, Finset.sum_comm]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [← Preadditive.sum_comp, dT_comp_dT a b y.1 y.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), zero_comp]
    rw [hz, map_zero, sub_zero]

end GlobalTheory.EZ.Shuf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureBaseChangeMapsAndRetractionStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closureBaseChange_maps_and_retraction : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [Algebra A₁ R₁] (f : A →+* A₁), Function.Injective f →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (S : Type) [CommRing S] [Algebra R₁ S],
    letI := closureAlg A R DA
    letI : Algebra R S := ((algebraMap R₁ S).comp κ).toAlgebra
    letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
    ∃ (φ : S ⊗[R] closure A R DA →ₐ[S] S ⊗[R₁] BC β DA)
      (ψ : S ⊗[R₁] BC β DA →ₐ[S] Localization (Algebra.algebraMapSubmonoid (S ⊗[R] closure A R DA)
          ((nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁))))),
      ψ.comp φ = IsScalarTower.toAlgHom S _ _ ∧
      (∀ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        IsUnit (algebraMap S (S ⊗[R₁] BC β DA) m)) ∧
      ∀ x : S ⊗[R₁] BC β DA, ∃ m ∈ (nonZeroDivisors A₁).map ((algebraMap R₁ S).comp (algebraMap A₁ R₁)),
        x * algebraMap S _ m ∈ φ.range := by
  first | (exact @GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (exact GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps) | (intros; apply GlobalTheory.KeyOriginBCMaps.exists_bc_closure_maps  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalk
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cofiltered_limit_affine_etale_of_isStalk : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  intro S O _ s hs
  obtain ⟨_, A, _, _, j, hj, hind, rfl⟩ := hs
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hind
  let G : Jᵒᵖ ⥤ Over S :=
    { obj := fun k => Over.mk (Spec.map (D.obj k.unop).hom ≫ j)
      map := fun {k l} f => Over.homMk (Spec.map (D.map f.unop).right) (by
        dsimp
        rw [← Category.assoc, ← Spec.map_comp, Under.w])
      map_id := fun k => by ext1; simp
      map_comp := fun f g => by ext1; simp [Spec.map_comp] }
  let π : (Functor.const Jᵒᵖ).obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j)) ⟶ G :=
    { app := fun k => Over.homMk (Spec.map (ι.app k.unop).right) (by
        dsimp [G]
        rw [← Category.assoc, ← Spec.map_comp, Under.w (ι.app k.unop)]
        rfl)
      naturality := fun k l f => by
        ext1
        change (𝟙 _ ≫ Spec.map (ι.app l.unop).right) = Spec.map (ι.app k.unop).right ≫ Spec.map (D.map f.unop).right
        rw [Category.id_comp, ← Spec.map_comp]
        congr 1
        have := congrArg (fun m => Under.Hom.right m) (ι.naturality f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Under.comp_right] at this
        exact this.symm }
  haveI : IsConnected J := IsFiltered.isConnected J
  haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G, π, ⟨?_⟩, fun k => ⟨?_, ?_⟩⟩
  · apply isLimitOfReflects (Over.forget S)
    have h1 := isColimitOfPreserves (Under.forget (CommRingCat.of A)) hc
    have h2 := isLimitOfPreserves Scheme.Spec h1.op
    exact h2
  · dsimp [G]; infer_instance
  · dsimp [G]
    have : Etale (Spec.map (D.obj k.unop).hom) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (het k.unop)
    infer_instance

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem exists_eisensteinCombination_of_isModularForm {w : ℕ} {F : ℍ → ℂ}
    (hF : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (w : ℤ) F) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  obtain ⟨f, hf⟩ := hF
  have hmem := _root_.ReciprocityTheory.PGsh.coe_mem_monoSpanF w f
  unfold _root_.ReciprocityTheory.PGsh.monoSpanF at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  classical
  refine ⟨(_root_.ReciprocityTheory.PGsh.monoIdx w).image fun a => (a, _root_.ReciprocityTheory.PGsh.monoB w a),
    fun p => if hp : p.1 ∈ _root_.ReciprocityTheory.PGsh.monoIdx w then c ⟨p.1, hp⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact _root_.ReciprocityTheory.PGsh.monoIdx_wt ha
  · intro τ
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h), ← hf τ, ← hc]
    rw [Finset.sum_apply, ← Finset.sum_attach (_root_.ReciprocityTheory.PGsh.monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, a.2, dif_pos]
    rw [_root_.ReciprocityTheory.PGsh.coe_monoW a.2]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem qConj_eisensteinCombination (g : ℂ ≃+* ℂ) {N : ℕ}
    (hN : 0 < N) {ι : Type} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ) :
    _root_.GlobalTheory.QFam.QConj g N (fun τ => ∑ i ∈ s, c i * (E₄ τ ^ u i * E₆ τ ^ v i))
      (fun τ => ∑ i ∈ s, g (c i) * (E₄ τ ^ u i * E₆ τ ^ v i)) := by
  refine _root_.GlobalTheory.QFam.QConj.sum s fun i _ => ?_
  have h₄ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inl rfl) g
  have h₆ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
  exact (_root_.GlobalTheory.QFam.QConj.const g N (c i)).mul hN
    ((h₄.pow hN (u i)).mul hN (h₆.pow hN (v i)))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in

theorem _root_.GlobalTheory.QFam.levelPoly_conj : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ),
    0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → _root_.GlobalTheory.QFam.QConj g N F F' →
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧
      ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro g w N F F' hN hinv hconj
  obtain ⟨a, ha, ha'⟩ := hconj
  obtain ⟨s, c, hw, hF⟩ := exists_eisensteinCombination_of_isModularForm
    (_root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha)
  refine ⟨s, c, hw, hF, ?_⟩
  obtain ⟨b, hb, hb'⟩ :=
    qConj_eisensteinCombination g hN s c Prod.fst Prod.snd
  have hFeq : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
  rw [← hFeq] at hb
  have hab : a = b := ha.coeff_unique hN hb
  subst hab
  intro τ
  exact congrFun (ha'.fun_unique hb') τ

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoublingJetSuccOfLiftStatement
section
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  first | exact @GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | exact GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift | (intros; apply GlobalTheory.Nef.PathJet.exists_jet_succ_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrimeStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_factorization_of_isIndEtale : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  first | exact @GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | exact GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | (intros; apply GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime <;> assumption)
end

