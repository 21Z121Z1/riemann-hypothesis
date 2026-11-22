import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamily
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ClopenIdealSheaf

theorem map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring

theorem map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

end GlobalTheory.ClopenIdealSheaf

namespace GlobalTheory.ClopenIdealSheaf

theorem exists_idealSheafData_of_isClopen : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W →
    ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  intro Z W hW F hF
  let W' : Z.Opens := ⟨W, hW.isOpen⟩
  let Wc : Z.Opens := ⟨Wᶜ, hW.isClosed.isOpen_compl⟩
  have hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W') := by
    intro U
    obtain ⟨e, -, he, -⟩ := GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z)
      (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc)
      (by
        rw [← inf_sup_left]
        have : W' ⊔ Wc = ⊤ := by
          ext x; simp [W', Wc, em]
        rw [this, inf_top_eq])
      (by
        refine Disjoint.mono inf_le_right inf_le_right ?_
        rw [disjoint_iff]; ext x; simp [W', Wc])
    rw [← he]; exact U.2.basicOpen e
  let V : Z.affineOpens → Z.affineOpens := fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩
  have hVU : ∀ U, (V U : Z.Opens) ≤ U := fun U => inf_le_left
  have hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W := fun U => Set.inter_subset_right
  let I : ∀ U : Z.affineOpens, Ideal Γ(Z, U) := fun U =>
    (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom
  refine ⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩
  · intro U f
    have hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) =
        V (Z.affineBasicOpen f) := by
      apply Subtype.ext
      change Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'
      rw [Scheme.basicOpen_res]
      have := Z.basicOpen_le f
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
      · exact le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left
    exact map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))
  · intro U hU
    have key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A,
        (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A := by
      rintro A B rfl hle
      have : homOfLE hle = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
      exact Ideal.comap_id _
    exact key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)
  · intro x hx
    by_contra hxW
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl
    replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    have hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥ := by
      ext y
      simp only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
        Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun h => hUW h.1 h.2
    haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    have htop : F (V ⟨U, hU⟩) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]
      exact zero_mem _
    have hI : I ⟨U, hU⟩ = ⊤ := by
      simp only [I, htop, Ideal.comap_top]
    change x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx
    rw [hI, Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)

end GlobalTheory.ClopenIdealSheaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHeckeEigensystemDeligneSerre
section
open Matrix

namespace GlobalTheory.DeligneSerre

theorem eq_top_of_isUnit_det (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by
  set f := (σ p).charpoly with hf
  have hq : Polynomial.aeval p f ∈ m := by
    apply hker
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
  have h0 : algebraMap O R (f.coeff 0) ∈ m := by
    have h := hq
    rw [← Polynomial.X_mul_divX_add f, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (Submodule.add_mem_iff_right m (m.mul_mem_right _ hp)).1 h
  have hc : IsUnit (f.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hu
    exact isUnit_of_mul_isUnit_right hu
  exact Ideal.eq_top_of_isUnit_mem m h0 (hc.map _)

theorem eigen_ringHom (R : Type) [CommRing R] (K : Type) [Field K] (n : ℕ)
    (τ : R →+* Matrix (Fin n) (Fin n) K) (c : Fin n → K) (hc : c ≠ 0)
    (h : ∀ p, ∃ μ : K, τ p *ᵥ c = μ • c) : ∃ χ : R →+* K, ∀ p, τ p *ᵥ c = χ p • c := by
  choose μ hμ using h
  have inj : ∀ a b : K, a • c = b • c → a = b := fun a b h => smul_left_injective K hc h
  refine ⟨{ toFun := μ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hμ⟩
  · apply inj; rw [← hμ, map_one, one_mulVec, one_smul]
  · intro a b; apply inj
    rw [← hμ, map_mul, ← mulVec_mulVec, hμ b, mulVec_smul, hμ a, smul_smul, mul_comm (μ b)]
  · apply inj; rw [← hμ, map_zero, zero_mulVec, zero_smul]
  · intro a b; apply inj; rw [← hμ, map_add, add_mulVec, hμ a, hμ b, add_smul]

theorem norm_det_eq_one (K : Type) [NormedField K] [IsAlgClosed K] (n : ℕ)
    (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ μ : K, (∃ c : Fin n → K, c ≠ 0 ∧ N *ᵥ c = μ • c) → ‖μ‖ = 1) : ‖N.det‖ = 1 := by
  have hroot : ∀ μ ∈ N.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    apply h
    have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
    have hr := (Polynomial.mem_roots hne).1 hμ
    rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hr
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  rw [Matrix.det_eq_prod_roots_charpoly]
  revert hroot
  generalize N.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    rw [Multiset.prod_cons, norm_mul, hs a (Multiset.mem_cons_self a s),
      ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem norm_eigen_le_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by
  first
  | (rename_i h_1 h_3; revert l h_1 O h_3 emb hle n N c μ hc hN; exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one)
  | exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one ..)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem unitBall_prime (R : Type) [CommRing R] (l : ℕ) [Fact l.Prime] (χ : R →+* PadicAlgCl l)
    (h : ∀ p, ‖χ p‖ ≤ 1) : ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 := by
  refine ⟨{ carrier := {p | ‖χ p‖ < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_,
    fun p => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  · simp
  · intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖χ c‖ * ‖χ x‖ ≤ 1 * ‖χ x‖ := by gcongr; exact h c
      _ < 1 := by simpa using hx
  · refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ ‖χ 1‖ < 1
      simp
    · intro a b hab
      show ‖χ a‖ < 1 ∨ ‖χ b‖ < 1
      have hab' : ‖χ a‖ * ‖χ b‖ < 1 := by
        have : ‖χ (a * b)‖ < 1 := hab
        simpa [map_mul, norm_mul] using this
      by_contra hno
      push_neg at hno
      have : 1 * 1 ≤ ‖χ a‖ * ‖χ b‖ := mul_le_mul hno.1 hno.2 zero_le_one (norm_nonneg _)
      linarith

theorem core (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a)
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal R) (hm : m.IsMaximal) (hker : ∀ p, σ p = 0 → p ∈ m) :
    ∃ χ : R →+* PadicAlgCl l, (∀ p, ‖χ p‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖χ p‖ < 1) ∧
      (∀ a, χ (algebraMap O R a) = emb a) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, (σ p).map emb *ᵥ c = χ p • c := by
  classical
  let τ : R →+* Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
    (emb.mapMatrix).comp (σ : R →+* Matrix (Fin n) (Fin n) O)
  have hτ : ∀ p, τ p = (σ p).map emb := fun p => rfl
  have hcomm : ∀ p q, Commute (τ p) (τ q) := fun p q => by
    show τ p * τ q = τ q * τ p
    rw [← map_mul, ← map_mul, mul_comm]
  let X : Set (R →+* PadicAlgCl l) :=
    {χ | ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, τ p *ᵥ c = χ p • c}
  have hXfin : X.Finite := by
    have h := GlobalTheory.T.finite_joint_eigenvalues_of_commute (PadicAlgCl l) n R τ hcomm
    refine Set.Finite.of_finite_image (f := fun χ : R →+* PadicAlgCl l => (χ : R → PadicAlgCl l))
      (h.subset ?_) DFunLike.coe_injective.injOn
    rintro _ ⟨χ, ⟨c, hc, hχ⟩, rfl⟩
    exact ⟨c, hc, hχ⟩
  have hXle : ∀ χ ∈ X, ∀ p, ‖χ p‖ ≤ 1 := by
    rintro χ ⟨c, hc, hχ⟩ p
    exact norm_eigen_le_one l O emb hle n (σ p) c (χ p) hc (hχ p)
  have hP : ∀ χ ∈ X, ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 :=
    fun χ hχ => unitBall_prime R l χ (hXle χ hχ)
  choose! P hPprime hPmem using hP
  have key : ∃ χ ∈ X, m ≤ P χ := by
    by_contra hno
    push_neg at hno
    obtain ⟨p, hpm, hpX⟩ : ∃ p ∈ m, ∀ χ ∈ X, ¬ ‖χ p‖ < 1 := by
      rcases X.eq_empty_or_nonempty with hX | ⟨χ0, hχ0⟩
      · exact ⟨0, m.zero_mem, by simp [hX]⟩
      · have hns : ¬ ((m : Set R) ⊆ ⋃ χ ∈ X, (P χ : Set R)) := by
          rw [Ideal.subset_union_prime_finite hXfin χ0 χ0 (fun χ hχ _ _ => hPprime χ hχ)]
          rintro ⟨χ, hχ, hle'⟩
          exact hno χ hχ hle'
        rw [Set.not_subset] at hns
        obtain ⟨p, hpm, hp⟩ := hns
        refine ⟨p, hpm, fun χ hχ hlt => hp ?_⟩
        exact Set.mem_biUnion hχ ((hPmem χ hχ p).2 hlt)
    have hdet : ‖(τ p).det‖ = 1 := by
      apply norm_det_eq_one (PadicAlgCl l) n (τ p)
      rintro μ ⟨c, hc, hcμ⟩
      let E : Submodule (PadicAlgCl l) (Fin n → PadicAlgCl l) :=
        { carrier := {v | τ p *ᵥ v = μ • v}
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_add, ha, hb, smul_add]
          zero_mem' := by simp
          smul_mem' := by
            intro a v hv
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_smul, hv, smul_comm] }
      have hcE : c ∈ E := hcμ
      have hE : E ≠ ⊥ := fun h => hc ((Submodule.mem_bot _).1 (h ▸ hcE))
      have hstab : ∀ A ∈ Set.range τ, ∀ v ∈ E, A *ᵥ v ∈ E := by
        rintro _ ⟨q, rfl⟩ v hv
        have hv' : τ p *ᵥ v = μ • v := hv
        show τ p *ᵥ (τ q *ᵥ v) = μ • (τ q *ᵥ v)
        rw [mulVec_mulVec, (hcomm p q).eq, ← mulVec_mulVec, hv', mulVec_smul]
      obtain ⟨v, hvE, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_mem_of_commute (PadicAlgCl l) n (Set.range τ)
        (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hcomm a b) E hE hstab
      obtain ⟨χ, hχ⟩ := eigen_ringHom R (PadicAlgCl l) n τ v hv0 (fun q => hv (τ q) ⟨q, rfl⟩)
      have hχX : χ ∈ X := ⟨v, hv0, hχ⟩
      have hμ : χ p = μ := by
        have h1 : τ p *ᵥ v = μ • v := hvE
        exact smul_left_injective (PadicAlgCl l) hv0 ((hχ p).symm.trans h1)
      rw [← hμ]
      exact le_antisymm (hXle χ hχX p) (not_lt.1 (hpX χ hχX))
    have hdet' : ‖emb (σ p).det‖ = 1 := by
      rw [RingHom.map_det]
      exact hdet
    exact hm.ne_top (eq_top_of_isUnit_det O R n σ m hker p hpm (hunit _ hdet'))
  obtain ⟨χ, hχX, hmP⟩ := key
  have hmeq : m = P χ := hm.eq_of_le (hPprime χ hχX).ne_top hmP
  obtain ⟨c, hc, hχc⟩ := id hχX
  refine ⟨χ, hXle χ hχX, fun p => by rw [hmeq]; exact hPmem χ hχX p, ?_, c, hc, hχc⟩
  intro a
  have h1 := hχc (algebraMap O R a)
  have h2 : τ (algebraMap O R a) *ᵥ c = emb a • c := by
    rw [hτ, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero emb)]
    ext i
    simp [mulVec_diagonal]
  exact smul_left_injective (PadicAlgCl l) hc (h1.symm.trans h2)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem exists_integral_eigensystem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  intro l _ O _ _ _ emb hinj hL I M _ _ _ _ hfin htf V _ _ j Tq hli hcomp m hm hann
  obtain ⟨L, _, hL⟩ := hL
  have hmemL : ∀ a, emb a ∈ L ∧ ‖emb a‖ ≤ 1 := by
    intro a
    have h : emb a ∈ Set.range emb := ⟨a, rfl⟩
    rw [hL] at h
    exact h
  have hle : ∀ a, ‖emb a‖ ≤ 1 := fun a => (hmemL a).2
  have hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a := by
    intro a ha
    have hne : emb a ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (emb a)⁻¹ ∈ Set.range emb := by
      rw [hL]
      refine ⟨L.inv_mem (hmemL a).1, ?_⟩
      rw [norm_inv, ha, inv_one]
    obtain ⟨b, hb⟩ := hinv
    have hab : a * b = 1 := hinj (by rw [map_mul, hb, map_one, mul_inv_cancel₀ hne])
    exact IsUnit.of_mul_eq_one b hab
  obtain ⟨n, σ, e, hσ, he_inj, he_span, he_T⟩ :=
    GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt l O emb I M hfin htf V j Tq hli hcomp
  obtain ⟨χ, hχle, hχm, hχalg, c, hc, hχc⟩ :=
    core l O emb hle hunit (MvPolynomial I O) n σ m hm (fun p hp => hann p (hσ p hp))
  set θ : I → PadicAlgCl l := fun i => χ (MvPolynomial.X i) with hθ
  have hext : MvPolynomial.eval₂Hom emb θ = χ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, hχalg]
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
  have heval : ∀ p, MvPolynomial.eval₂ emb θ p = χ p := fun p =>
    congrArg (fun f : MvPolynomial I O →+* PadicAlgCl l => f p) hext
  refine ⟨θ, fun i => hχle _, fun p => by rw [heval]; exact hχm p, e c, he_span c, ?_, ?_⟩
  · intro h
    exact hc (he_inj (by rw [h, map_zero]))
  · intro i
    rw [he_T, hχc, map_smul]

end GlobalTheory.DeligneSerre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixOfIntertwiner
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem exists_isMat_of_equivariant (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) :
    IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  intro he he' hX
  let L' : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin N → RL p O Λ) :=
    e'.symm.toLinearMap ∘ₗ (Matrix.mulVecLin X) ∘ₗ e.toLinearMap
  have hL' : ∀ w, e' (L' w) = X *ᵥ e w := by
    intro w; simp [L']
  have hl : ∀ (l : Λ) w, L' (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • L' w := by
    intro l w
    apply e'.injective
    rw [hL', he, he', hL', Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec]
  have hs : ∀ (r : RL p O Λ) w, L' (r • w) = r • L' w := by
    intro r w
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      have : (a ⊗ₜ[ℤ_[p]] l : RL p O Λ) = algebraMap (Ainf p O) (RL p O Λ) a * ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul, L'.map_smul, hl]
    | add x y hx hy => rw [add_smul, add_smul, L'.map_add, hx, hy]
  let L : (Fin N → RL p O Λ) →ₗ[RL p O Λ] (Fin N → RL p O Λ) :=
    { toFun := L'
      map_add' := L'.map_add
      map_smul' := hs }
  refine ⟨LinearMap.toMatrix' L, fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact (hL' w).symm

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibre
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q hQp hQ
  set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef
  set f := algebraMap T[X] E with hfdef
  obtain ⟨y, hy, hQy⟩ := Ideal.exists_le_maximal Q hQp.ne_top
  have hPy : P ≤ y.comap f := hQ ▸ Ideal.comap_mono hQy

  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  have eP := Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩
  have hPnf : ¬ P.IsMaximal := by
    intro hm
    have hf : IsField (T[X] ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm
    exact Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)

  let φ : T[X] ⧸ P →+* E ⧸ y := Ideal.quotientMap y f hPy
  have hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f := Ideal.quotientMap_comp_mk hPy
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)
    rw [hcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Field (E ⧸ y) := Ideal.Quotient.field y
  letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra
  haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft
  haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _
  have hker : (RingHom.ker φ).IsMaximal := by
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))
    rwa [← RingHom.ker_eq_comap_bot] at this
  have hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hymax : (y.comap f).IsMaximal := by
    rw [hyc]; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩
  have hle : maximalIdeal T ≤ (y.comap f).comap C := by
    intro a ha
    exact hPy (Ideal.mem_map_of_mem _ ha)
  have hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤ := (Ideal.comap_isPrime C (y.comap f)).ne_top
  exact ((maximalIdeal.isMaximal T).eq_of_le hne hle).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqMulSqOfFaithfullyFlatHeightOneStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_eq_mul_sq_of_faithfullyFlat_height_one : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  first | exact @GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | exact GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime | (intros; apply GlobalTheory.Mum.exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairingsStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
end

