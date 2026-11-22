import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalization
section
namespace GlobalTheory

theorem etale_away_quotient_eq_localization :
    ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D]
      (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → f ∈ P → ∀ (Q : Ideal D), Q.IsPrime →
      Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) →
      ∃ g : D, (∀ a : Localization.Away g, ∃ b : B,
          a - algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f}) ∧
        ∀ b : B, algebraMap B (Localization.Away g) b ∈
            Ideal.span {algebraMap B (Localization.Away g) f} ↔
          ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  intro B D _ _ _ _ _ f hf P hP hfP Q hQ hQP hres

  have hQmax : Q.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h1 => ?_, fun J x hQJ hx hxJ => ?_⟩
    · have : (1 : B) ∈ Q.comap (algebraMap B D) := by simpa using h1
      rw [hQP] at this
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
    · obtain ⟨b, hb⟩ := hres x
      have hbP : b ∉ P := by
        intro hbP
        apply hx
        have : algebraMap B D b ∈ Q := by
          rw [← Ideal.mem_comap, hQP]; exact hbP
        simpa using Q.add_mem hb this
      obtain ⟨c, hc⟩ : ∃ c : B, c * b - 1 ∈ P := by
        obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbP
        refine ⟨c, ?_⟩
        have : c * b - 1 = -i := by rw [← hci]; ring
        rw [this]; exact P.neg_mem hi
      have h1 : algebraMap B D (c * b - 1) ∈ Q := by
        rw [← Ideal.mem_comap, hQP]; exact hc
      have h2 : algebraMap B D c * x - 1 ∈ Q := by
        have : algebraMap B D c * x - 1 =
            algebraMap B D c * (x - algebraMap B D b) + algebraMap B D (c * b - 1) := by
          simp only [map_sub, map_mul, map_one]; ring
        rw [this]
        exact Q.add_mem (Q.mul_mem_left _ hb) h1
      have h3 : algebraMap B D c * x ∈ J := J.mul_mem_left _ hxJ
      have : (1 : D) = algebraMap B D c * x - (algebraMap B D c * x - 1) := by ring
      rw [this]
      exact J.sub_mem h3 (hQJ h2)
  obtain ⟨g, hgQ, hQ'⟩ := GlobalTheory.T.isolate_maximal_among_primes_containing_etale B D f hf Q hQmax
  refine ⟨g, ?_⟩
  haveI : Algebra.Etale D (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale B (Localization.Away g) := Algebra.Etale.comp B D (Localization.Away g)
  have hφ : ∀ b : B, algebraMap B (Localization.Away g) b =
      algebraMap D (Localization.Away g) (algebraMap B D b) := fun b =>
    IsScalarTower.algebraMap_apply B D (Localization.Away g) b

  have hunit := GlobalTheory.T.localization_inverse_mod_f B D f P Q g hQP hQ'

  have hker : ∀ b : B, (∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) →
      algebraMap B (Localization.Away g) b ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
    rintro b ⟨s, hs, hsb⟩
    obtain ⟨t, ht⟩ := hunit s hs
    have h1 : algebraMap B (Localization.Away g) (s * b) ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.mem_span_singleton] at hsb ⊢
      obtain ⟨c, hc⟩ := hsb
      exact ⟨algebraMap B _ c, by rw [hc, map_mul]⟩
    have : algebraMap B (Localization.Away g) b = algebraMap B _ (s * b) * t -
        (algebraMap B _ s * t - 1) * algebraMap B (Localization.Away g) b := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ ht)
  refine ⟨?_, fun b => ⟨fun hb => ?_, hker b⟩⟩
  ·
    obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
    have hPN : (P ^ N).map (algebraMap B (Localization.Away g)) ≤
        Ideal.span {algebraMap B (Localization.Away g) f} := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      exact hker b (hN b hb)
    have hfib : ∀ Q' : Ideal (Localization.Away g), Q'.IsPrime →
        P.map (algebraMap B (Localization.Away g)) ≤ Q' →
        Q' = Q.map (algebraMap D (Localization.Away g)) := by
      intro Q' hQ'p hPQ'
      have hc : Q'.comap (algebraMap D (Localization.Away g)) = Q := by
        apply hQ' _ (Ideal.comap_isPrime _ _)
        · rw [Ideal.mem_comap, ← hφ]
          exact hPQ' (Ideal.mem_map_of_mem _ hfP)
        · intro hg
          rw [Ideal.mem_comap] at hg
          exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hg
            (IsLocalization.Away.algebraMap_isUnit g))
      rw [← hc]
      exact (IsLocalization.map_comap (Submonoid.powers g) (Localization.Away g) Q').symm
    have hle := GlobalTheory.T.etale_unique_prime_le_map_maximal B (Localization.Away g) P hP
      (Q.map (algebraMap D (Localization.Away g))) hfib
    have hres' := GlobalTheory.T.localization_residue_approximation B D P hP Q g hgQ hQP hres
    refine GlobalTheory.T.nilpotent_approximation_surjective B (Localization.Away g) P _ N (fun a => ?_) hPN
    obtain ⟨b, hb⟩ := hres' a
    exact ⟨b, Ideal.mem_sup_left (hle hb)⟩
  ·
    have hgu : IsUnit (algebraMap D (Localization.AtPrime Q) g) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
    let ρ : Localization.Away g →+* Localization.AtPrime Q := IsLocalization.Away.lift g hgu
    have hρ : ∀ d : D, ρ (algebraMap D (Localization.Away g) d) =
        algebraMap D (Localization.AtPrime Q) d :=
      fun d => IsLocalization.Away.lift_eq g hgu d
    have e : ∀ x : B, algebraMap B (Localization.AtPrime Q) x =
        ρ (algebraMap B (Localization.Away g) x) := by
      intro x
      rw [hφ, hρ, IsScalarTower.algebraMap_apply B D (Localization.AtPrime Q)]
    have hloc : algebraMap B (Localization.AtPrime Q) b ∈
        Ideal.span {algebraMap B (Localization.AtPrime Q) f} := by
      rw [Ideal.mem_span_singleton] at hb ⊢
      obtain ⟨c, hc⟩ := hb
      exact ⟨ρ c, by rw [e, e, hc, map_mul]⟩
    obtain ⟨s, hs, hsb⟩ := GlobalTheory.T.flat_localization_membership B D Q f b hloc
    rw [hQP] at hs
    exact ⟨s, hs, hsb⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOverDirectedUnionEssEtaleLocal
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleOverDirectedUnion

theorem localRing_of_etale_over_essEtale : ∀ (R S' E : Type) [CommRing R] [CommRing S'] [CommRing E] [Algebra R S'] [Algebra S' E] [Algebra R E] [IsScalarTower R S' E] [Algebra.Etale S' E], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] S')) → ∀ (P : Ideal E) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S' E _ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨ψ⟩⟩ P hP
  letI : Algebra (Localization.AtPrime q) S' := ψ.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime q) E := ((algebraMap S' E).comp ψ.toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime q) S' E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale (Localization.AtPrime q) S' :=
    Algebra.Etale.of_equiv (R := Localization.AtPrime q)
      ({ ψ.toRingEquiv with commutes' := fun _ => rfl } : Localization.AtPrime q ≃ₐ[Localization.AtPrime q] S')
  haveI : Algebra.Etale (Localization.AtPrime q) E := Algebra.Etale.comp (Localization.AtPrime q) S' E
  haveI : IsScalarTower R (Localization.AtPrime q) E := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R E r = algebraMap S' E (ψ (algebraMap R _ r))
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply])
  exact GlobalTheory.T.etale_local_ring_of_localization R A E q P

theorem span_one_tmul_eq_top (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (A₀ B₀ : Type)
    [CommRing A₀] [CommRing B₀] [Algebra A₀ S] [Algebra A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) :
    Submodule.span S (Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← e.symm_apply_apply y]
  induction e y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul s b =>
    have : s ⊗ₜ[A₀] b = s • ((1 : S) ⊗ₜ[A₀] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | add x z hx hz => rw [map_add]; exact add_mem hx hz

theorem fg_le_member {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (A₀ : Subalgebra R S) (h : A₀.FG) :
    ∃ i, A₀ ≤ Si i := by
  classical
  obtain ⟨t, rfl⟩ := h
  choose f hf using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image f)
  exact ⟨M, Algebra.adjoin_le fun s hs => hmono (hM _ (Finset.mem_image_of_mem f hs)) (hf s)⟩

theorem construct : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [Algebra.Etale S B], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (C : ι → Subalgebra R B), Monotone C ∧ (∀ b : B, ∃ i, b ∈ C i) ∧ ∀ i (P : Ideal (C i)) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S B _ _ _ _ _ _ _ _ ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩
  obtain ⟨A₀, B₀, _, _, hfg, hét, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R S B
  obtain ⟨i₀, hi₀⟩ := fg_le_member Si hmono hcov A₀ hfg
  let g : B₀ → B := fun b => e.symm (1 ⊗ₜ b)
  let C : {j // i₀ ≤ j} → Subalgebra R B := fun j =>
    Algebra.adjoin R ((algebraMap S B) '' (Si j.1 : Set S) ∪ Set.range g)
  have hdir : IsDirected {j // i₀ ≤ j} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  have hCmono : Monotone C := fun a b hab =>
    Algebra.adjoin_mono (Set.union_subset_union_left _ (Set.image_mono (hmono hab)))
  refine ⟨{j // i₀ ≤ j}, inferInstance, hdir, ⟨⟨i₀, le_rfl⟩⟩, C, hCmono, ?_, ?_⟩
  · intro b
    have hb : b ∈ Submodule.span S (Set.range g) := by
      rw [span_one_tmul_eq_top S B A₀ B₀ e]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx => exact ⟨⟨i₀, le_rfl⟩, Algebra.subset_adjoin (Or.inr hx)⟩
    | zero => exact ⟨⟨i₀, le_rfl⟩, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a b
      exact ⟨k, add_mem (hCmono hak ha) (hCmono hbk hb)⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨j, hj⟩ := hcov s
      obtain ⟨k, hak, hjk⟩ := directed_of (· ≤ ·) a.1 j
      refine ⟨⟨k, a.2.trans hak⟩, ?_⟩
      rw [Algebra.smul_def]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, hmono hjk hj, rfl⟩)) (hCmono hak ha)
  · intro j P hP
    obtain ⟨_, _, _⟩ := GlobalTheory.T.etale_adjoin_baseChange_image' R S B A₀ B₀ e (Si j.1) (hi₀.trans (hmono j.2))
    exact localRing_of_etale_over_essEtale R (Si j.1) (C j) (hloc j.1) P hP

end GlobalTheory.EtaleOverDirectedUnion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjective
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge

open Polynomial

theorem prod_X_sub_C_dvd_of_eval_zero {O S : Type} [CommRing O] [IsDomain O] [Fintype S]
    (b : S → O) (hb : Function.Injective b) (g : O[X]) (hg : ∀ s, g.eval (b s) = 0) :
    (∏ s, (X - C (b s))) ∣ g := by
  by_cases h0 : g = 0
  · simp [h0]
  have hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]
  rw [Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]
  intro t ht
  obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 ht
  exact (mem_roots h0).2 (hg s)

theorem evalVec_injective_of_injective (C : Type) [Field C] (w : Valuation C ℝ≥0)
    (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring)
    (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) :
    Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  intro ha
  have hinj : Function.Injective (liftA hv a) := by
    intro s t hst
    apply ha
    apply Subtype.ext
    have := congrArg (fun u : Int0 v => (u : C)) hst
    exact this
  have key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0 := by
    intro x hx
    funext i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    rw [Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]
    apply prod_X_sub_C_dvd_of_eval_zero _ hinj
    intro s
    have h1 := congrFun (congrFun hx s) i
    simp only [evalVec, Pi.zero_apply, ← hg] at h1
    apply Subtype.ext
    rw [show ((0 : Int0 v) : C) = 0 from rfl, ← h1]
    congr 1
  intro x y hxy
  have := key (x - y) (by rw [evalVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

end GlobalTheory.HerbrandBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleIsUnitDetLocalInvolution
section
open Matrix

namespace GlobalTheory.LocalLift

def invEquiv {O : Type} [CommRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃+* O :=
  { c with invFun := c, left_inv := hc, right_inv := hc }

noncomputable def resInv {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.ResidueField.mapEquiv (invEquiv c hc)).toRingHom

theorem resInv_residue {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O)
    (hc : ∀ x, c (c x) = x) (x : O) :
    resInv c hc (IsLocalRing.residue O x) = IsLocalRing.residue O (c x) := by
  simp only [resInv, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem lift_of_field
    (hF : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
      ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
      ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
        Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
        ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro O _ _ c hc h2 n S hS hSc A B C D hdet hU
  set π := IsLocalRing.residue O with hπ
  set cb := resInv c hc with hcbdef
  have hcb : ∀ x, cb (π x) = π (c x) := resInv_residue c hc
  have hcbM : ∀ M : Matrix (Fin n) (Fin n) O, (M.map c).map π = (M.map π).map cb := by
    intro M; ext i j; simp [hcb]
  have hcbb : ∀ x, cb (cb x) = x := by
    intro x; obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    show cb (cb (π y)) = π y
    rw [hcb, hcb, hc]
  have h2k : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (h2.map π).ne_zero; rwa [map_ofNat] at this
  have hSk : IsUnit (S.map π).det := by
    have := hS.map π; rwa [RingHom.map_det] at this
  have hSck : (S.map π)ᵀ = -(S.map π).map cb := by
    rw [← hcbM, ← Matrix.transpose_map, hSc]; ext i j; simp
  have h11 : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply] at hU
    have := (Matrix.fromBlocks_inj.1 hU).1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at this
    rw [add_comm]; simpa [Matrix.mul_assoc] using this
  have hinj : ∀ u, (A.map π) *ᵥ u = 0 → (C.map π) *ᵥ u = 0 → u = 0 := by
    intro u hA hC
    have hd : ((fromBlocks A B C D).map π).det ≠ 0 := by
      have := (hdet.map π).ne_zero; rwa [RingHom.map_det] at this
    have := Matrix.eq_zero_of_mulVec_eq_zero hd (v := Sum.elim u 0) (by
      rw [fromBlocks_map, fromBlocks_mulVec]; ext (i | i) <;> simp [hA, hC])
    funext i; simpa using congrFun this (Sum.inl i)
  have hiso : (A.map π)ᵀ * S.map π * (C.map π).map cb + (C.map π)ᵀ * S.map π * (A.map π).map cb = 0 := by
    have : (Aᵀ * S * C.map c + Cᵀ * S * A.map c).map π = 0 := by rw [h11]; ext; simp
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.transpose_map, hcbM, hcbM] at this
    exact this
  obtain ⟨Xb, hXadm, hXunit⟩ := hF cb hcbb h2k (S.map π) hSk hSck (A.map π) (C.map π) hinj hiso

  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin n) (Fin n) O, X0.map π = Xb :=
    ⟨Xb.map (fun x => (IsLocalRing.residue_surjective x).choose), by
      ext i j; exact (IsLocalRing.residue_surjective (Xb i j)).choose_spec⟩
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hch : c h = h := by
    have h' : c 2 * c h = 1 := by rw [← map_mul, hh, map_one]
    rw [map_ofNat] at h'
    calc c h = (h * 2) * c h := by rw [mul_comm h 2, hh, one_mul]
      _ = h * (2 * c h) := by ring
      _ = h := by rw [h', mul_one]
  set Z0 := X0ᵀ * S with hZ0
  set Z := h • (Z0 + (Z0.map c)ᵀ) with hZ
  have hZh : (Z.map c)ᵀ = Z := by
    ext i j; simp only [hZ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, map_mul, map_add, hch, hc]; ring
  set X := (Z * S⁻¹)ᵀ with hX
  have hSt : (S.map c)ᵀ = -S := by
    have : S.map c = -Sᵀ := by rw [hSc, neg_neg]
    rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
  have hSinv : S * (S⁻¹.map c)ᵀ = -1 := by
    have h1 : (S⁻¹.map c) * (S.map c) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul S hS]; exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2' := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one, hSt, Matrix.neg_mul] at h2'
    rw [← neg_neg (S * _), h2']
  have hXS : Xᵀ * S = Z := by
    rw [hX, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
  have hXc : X.map c = (S⁻¹.map c)ᵀ * Z := by
    rw [hX, Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hZh]
  refine ⟨X, ?_, ?_⟩
  · rw [hXS, hXc, ← Matrix.mul_assoc, hSinv, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
  · have hSbt : ((S.map π).map cb)ᵀ = -S.map π := by
      have : (S.map π).map cb = -(S.map π)ᵀ := by rw [hSck, neg_neg]
      rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
    have hZb : ((Xbᵀ * S.map π).map cb)ᵀ = Xbᵀ * S.map π := by
      rw [Matrix.map_mul, Matrix.transpose_mul, hSbt, ← Matrix.transpose_map, Matrix.transpose_transpose,
        Matrix.neg_mul]
      exact (eq_neg_of_add_eq_zero_left hXadm).symm
    have hZ0b : Z0.map π = Xbᵀ * S.map π := by
      rw [hZ0, Matrix.map_mul, Matrix.transpose_map, hX0]
    have hZm : Z.map π = π h • (Z0.map π + ((Z0.map c).map π)ᵀ) := by
      ext i j
      simp only [hZ, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
        smul_eq_mul, map_mul, map_add]
    have hZπ : Z.map π = Xbᵀ * S.map π := by
      have h2h : π h * 2 = 1 := by rw [← map_ofNat π 2, ← map_mul, mul_comm, hh, map_one]
      rw [hZm, hcbM, hZ0b, hZb, ← two_smul (IsLocalRing.ResidueField O) (Xbᵀ * S.map π), smul_smul, h2h,
        one_smul]
    have hXπ : X.map π = Xb := by
      have hmm : (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul]
      have e : (X.map π)ᵀ * S.map π = Xbᵀ * S.map π := by
        calc (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := hmm
          _ = Z.map π := by rw [hXS]
          _ = Xbᵀ * S.map π := hZπ
      have e' := congrArg (· * (S.map π)⁻¹) e
      simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hSk] at e'
      exact Matrix.transpose_inj.1 e'
    apply isUnit_of_map_unit π
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add π), Matrix.map_mul, hXπ]
    exact hXunit

theorem exists_admissible_isUnit_det :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det :=
  lift_of_field GlobalTheory.T.exists_admissible_lagrangian_transverse_field

end GlobalTheory.LocalLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverIdealRepresents
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

noncomputable section

namespace GlobalTheory.PtClosed

theorem represents_away (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
    (V : S.Opens) (hV : IsAffineOpen V) (a : Γ(S, V)) (J : Ideal Γ(S, S.basicOpen a))
    (hJ : Represents (ptQ P (S.basicOpen a) (hV.basicOpen a)) J) :
    ∃ J' : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J' := by
  let ρ := (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
  letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra
  haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a
  let e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)
  refine ⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩
  intro R' _ h
  have hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) =
      (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    have := e.symm.commutes x
    rw [← this]
    rfl
  have hs : ∀ g : Γ(S, S.basicOpen a) →+* R',
      spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec := by
    intro g
    rw [← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]
    simp only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap _ ≫ hV.fromSpec) ↔ _
  rw [hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem affine_local_represents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  intro S P hcov V hV
  let T : Set Γ(S, V) := {a | ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}
  have hT : Ideal.span T = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro z hzV
    obtain ⟨U, hU, hzU, K, hK⟩ := hcov z
    obtain ⟨a, b, hab, hz⟩ := exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩
    have hle : S.basicOpen a ≤ U := hab ▸ S.basicOpen_le b
    have hJ := represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK
    have haT : a ∈ T := represents_away S P V hV a _ hJ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 hT
  exact ⟨s, hs, fun a ha ↦ hsT ha⟩

end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegralStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  first | (exact @GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (exact GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (intros; apply GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicGeneratorsSeparableMinStatement
section
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclic_generators_separable_min : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type) [AddCommGroup G] [Module κ G]
    [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X]) (_ : h.Monic) (_ : h.Separable)
    (_ : aeval T h = 0) (N : ℕ) (_ : LinearMap.charpoly T = h ^ N),
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  first | exact @GlobalTheory.semisimple_charpoly_pow_generators | exact GlobalTheory.semisimple_charpoly_pow_generators | (intros; apply GlobalTheory.semisimple_charpoly_pow_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  first | exact @GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | exact GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | (intros; apply GlobalTheory.exists_valuationSubring_extend_of_formallyEtale <;> assumption)
end

