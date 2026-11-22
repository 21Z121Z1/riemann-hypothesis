import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.LeviFlag

private theorem cT_mul_lemma {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (P : Matrix (Fin a) (Fin b) A)
    (Q : Matrix (Fin b) (Fin c) A) : Formalism.UG.cT s (P * Q) = Formalism.UG.cT s Q * Formalism.UG.cT s P := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_cT_of_involutive {A : Type} [CommRing A] (s : A →+* A) (hs : ∀ x, s (s x) = x) {a b : ℕ}
    (P : Matrix (Fin a) (Fin b) A) : Formalism.UG.cT s (Formalism.UG.cT s P) = P := by
  unfold Formalism.UG.cT
  ext i j
  simp [hs]

private theorem cT_one_divisor {A : Type} [CommRing A] (s : A →+* A) {a : ℕ} :
    Formalism.UG.cT s (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

private theorem cT_Y_J_X_eq_one_and_complement_eq_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (hσ : ∀ x, σ (σ x) = x) {X Y : Matrix (Fin n) (Fin r) E}
    (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0) (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 ∧
      Formalism.UG.cT (σ : E →+* E) Y * J * J⁻¹ * Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Y * J) = 0 := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => hσ x
  have hJJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    unfold Formalism.UG.cT
    ext i j
    simp [hJ.1 i j]
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  constructor
  · have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [cT_mul_lemma, cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, cT_one_divisor, ← Matrix.mul_assoc] at e
    exact e
  · rw [cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, Matrix.mul_nonsing_inv_cancel_right _ _ hdet, ← Matrix.mul_assoc]
    exact hyy

private theorem exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) (p : GAd σ J) (hp : p ∈ parFlag σ J X d) :
    ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hm : ∀ a b, adjA σ J (a * b) = adjA σ J b * adjA σ J a := adjA_mul hJ
  have hi : ∀ a, adjA σ J (adjA σ J a) = a := adjA_adjA hJ hσ
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  have h1 : adjA σ J 1 = 1 := by
    have e := hm (adjA σ J 1) 1
    simp only [mul_one, hi] at e
    exact e.symm
  have hτ : ∀ a, adjA σ J (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) =
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) (Option.map Sum.swap a) := by
    rintro (_ | j | j)
    · show adjA σ J (1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j) =
        1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j
      rw [map_sub, h1, map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hi]
      rw [add_comm]
    · rfl
    · exact hi _
  have hw : ∀ a, wt d (∑ i, d i + 1) (Option.map Sum.swap a) = - wt d (∑ i, d i + 1) a := by
    rintro (_ | j | j) <;> simp [wt]
  have hττ : ∀ a : Option (Fin r ⊕ Fin r), Option.map Sum.swap (Option.map Sum.swap a) = a := by
    rintro (_ | j | j) <;> rfl
  have hxy1 : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := by
    rw [map_inv]
    exact Units.mul_inv _
  have hyx1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [map_inv]
    exact Units.inv_mul _
  obtain ⟨m, m', hmm', hm'm, hstm, hmd, hm'd, hraise, hsub⟩ :=
    GlobalTheory.T.exists_weightPreservingPart_nonLowering_unit (adjA σ J) (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)))
      (wt d (∑ i, d i + 1)) (Option.map Sum.swap) hm hi hε hτ hw hττ _ _ hxy1 hyx1 (adjA_mat hJ p)
      (GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p hp)
      (GlobalTheory.T.isotropicFlagStabilizer_not_lower_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p⁻¹ (inv_mem hp))
  let U : GL (Fin n) (AF F ⊗[F] E) := ⟨m, m', hmm', hm'm⟩
  have hU : U ∈ HR (AF F) σ J := (adjA_mul_self_iff hJ U).1 (by
    show adjA σ J m * m = 1
    rw [hstm, hm'm])
  let g : GAd σ J := (⟨U, hU⟩ : HR (AF F) σ J)
  have hg1 : (matHom _ σ J g).1 = m := rfl
  have hg2 : (matHom _ σ J g⁻¹).1 = m' := by
    rw [map_inv]
    rfl
  have hgl : g ∈ leviFlag σ J X Y d :=
    GlobalTheory.T.mem_isotropicFlagLevi_of_keeps_weights F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (by rw [hg1]; exact hmd) (by rw [hg2]; exact hm'd)
  refine ⟨p * g⁻¹, ?_, g, hgl, (inv_mul_cancel_right p g).symm, ?_⟩
  · rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM, map_mul, Units.val_mul, hg2]
    exact hraise
  · intro hpr
    rw [← range_ratEmb σ J] at hpr
    obtain ⟨γ, hγ⟩ := hpr
    have : Nontrivial (AF F) := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      exact (evInf F w).toRingHom.domain_nontrivial
    have hinj : Function.Injective (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E) :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap F (AF F)))
    have hφ : Function.Injective ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix :
        Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := Matrix.map_injective hinj
    have hu : ∀ j, idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range :=
      fun j => ⟨_, rfl⟩
    have hsu : ∀ j, adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j) ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      intro j
      show adjA σ J ((X * Matrix.single j j (1 : E) * (Formalism.UG.cT (σ : E →+* E) Y * J)).map
        (inclR (F := F) (AF F))) ∈ _
      rw [adjA_map]
      exact ⟨_, rfl⟩
    have hε0 : ∀ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rintro (_ | j | j)
      · exact Subring.sub_mem _ (Subring.one_mem _) (Subring.sum_mem _ fun j _ => by
          rcases j with j | j
          exacts [hu j, hsu j])
      · exact hu j
      · exact hsu j
    have hx0 : (matHom _ σ J p).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ]
      exact ⟨_, rfl⟩
    have hy0 : (matHom _ σ J p⁻¹).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ, ← map_inv]
      exact ⟨_, rfl⟩
    obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := hsub _ hε0 hx0 hy0
    have hkk' : k * k' = 1 := hφ (by rw [map_mul, map_one, hk, hk', hmm'])
    have hk'k : k' * k = 1 := hφ (by rw [map_mul, map_one, hk, hk', hm'm])
    have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
    have hadj : J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J = k' := hφ (by
      show (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J).map (inclR (F := F) (AF F)) = _
      rw [← adjA_map, hk', ← hstm, ← hk]
      rfl)
    have hUJ : Formalism.UG.cT (σ : E →+* E) k * J * k = J := by
      calc Formalism.UG.cT (σ : E →+* E) k * J * k = J * (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J) * k := by
            rw [← mul_assoc J, ← mul_assoc J, Matrix.mul_nonsing_inv _ hdet, one_mul]
        _ = J := by rw [hadj, mul_assoc, hk'k, mul_one]
    let K : GL (Fin n) E := ⟨k, k', hkk', hk'k⟩
    have hK : K ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      show Formalism.UG.cT (σ : E →+* E) k * J * k = J
      exact hUJ
    rw [← range_ratEmb σ J]
    refine ⟨⟨K, hK⟩, matHom_injective _ σ J (Units.ext ?_)⟩
    show (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix k = m
    exact hk

private theorem unipFlag_inf_leviFlag_eq_bot (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hu, hl⟩ := Subgroup.mem_inf.1 hg
  have hl' : g ∈ parFlag σ J X d ⊓ parFlag σ J Y d := hl
  rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM] at hu
  have hu' : ∀ a b, wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b + ((0 : ℕ) : ℤ) →
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
        fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := hu
  have hY := GlobalTheory.T.oppositeIsotropicFlagStabilizer_not_raise_weight F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (Subgroup.mem_inf.1 hl').2
  have hz : ∀ a b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
    intro a b
    by_cases hab : wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b
    · exact hu' a b (by simpa using hab)
    · rw [not_le] at hab
      have hne : a ≠ b := by
        rintro rfl
        exact lt_irrefl _ hab
      rw [mul_sub, sub_mul, hY a b hab, mul_one, hε.ortho hne, sub_zero]
  have h0 : (matHom _ σ J g).1 - 1 = 0 := by
    rw [show (matHom _ σ J g).1 - 1 =
        (∑ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) * ((matHom _ σ J g).1 - 1) *
          (∑ b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b) by
        rw [hε.complete, one_mul, mul_one]]
    simp only [Finset.sum_mul, Finset.mul_sum, hz, Finset.sum_const_zero]
  apply matHom_injective _ σ J
  rw [map_one]
  exact Units.ext (sub_eq_zero.1 h0)

theorem levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → (∀ p ∈ parFlag σ J X d, ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J)) ∧ unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ ∧ leftGrp σ J X d = unipFlag σ J X d ⊔ (ratPts σ J ⊓ leviFlag σ J X Y d) ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d hxx hyy hxy
  refine ⟨fun p hp => exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hp,
    unipFlag_inf_leviFlag_eq_bot F E σ h n J hJ r X Y d hxx hyy hxy, ?_,
    fun t a ht hta => GlobalTheory.T.splitTorusElement_mem_isotropicFlagLevi F E σ h n J hJ r X Y d hxx hyy hxy t a ht hta⟩
  apply le_antisymm
  · show unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d) ≤ _
    refine sup_le le_sup_left ?_
    intro p hp
    obtain ⟨hpr, hpp⟩ := Subgroup.mem_inf.1 hp
    obtain ⟨u, hu, m, hm, hpe, hrat⟩ := exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hpp
    rw [hpe]
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_inf.2 ⟨hrat hpr, hm⟩)
  · show _ ≤ unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d)
    exact sup_le_sup_left (inf_le_inf_left _ (inf_le_left : parFlag σ J X d ⊓ parFlag σ J Y d ≤ _)) _

end GlobalTheory.LeviFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementPreservesWittColumnSpan
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem levi_mulVec_col : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) →
    ∀ {g : GAd σ J}, g ∈ levi σ J X Y S → ∀ k ∈ S,
    (matHom _ σ J g).1 *ᵥ (fun i => adMat F X i k) =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k • (fun i => adMat F X i k) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS g hg k hk
  classical
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) := fun Z => rfl
  have mem : ∀ {h' : GAd σ J}, h' ∈ levi σ J X Y S → ∀ k ∈ S,
      h' ∈ frameStab σ J (initCols X k) ⊤ ∧ h' ∈ frameStab σ J (initCols Y k) ⊤ := fun hh k hk =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh k) hk)

  have fr : ∀ (C : Matrix (Fin n) (Fin r) E) (h' : GAd σ J) (k : Fin r), h' ∈ frameStab σ J (initCols C k) ⊤ →
      ∃ c : Fin r → AF F ⊗[F] E, (∀ j, k < j → c j = 0) ∧
        ∀ i, ((matHom _ σ J h').1 * adMat F C) i k = (adMat F C *ᵥ c) i := by
    rintro C h' k ⟨B, -, e⟩
    let P : Matrix (Fin r) (Fin (k.val + 1)) (AF F ⊗[F] E) :=
      (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)).submatrix id (Fin.castLE k.2)
    have hP : adMat F (initCols C k) = adMat F C * P := by
      ext i j; simp [P, initCols, Matrix.mul_apply, Matrix.one_apply]
    refine ⟨fun j => (P * B.1) j ⟨k, Nat.lt_succ_self _⟩, fun j hj => ?_, fun i => ?_⟩
    · simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id]
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [Matrix.one_apply_ne, zero_mul]
      intro hjj
      rw [show j = _ from hjj] at hj
      exact absurd hj (not_lt.2 (Nat.le_of_lt_succ j'.2))
    · have e2 : ((matHom _ σ J h').1 * adMat F C) i k =
          ((matHom _ σ J h').1 * adMat F (initCols C k)) i ⟨k, Nat.lt_succ_self _⟩ := by
        simp [Matrix.mul_apply, initCols]
      rw [e2, e, hP, Matrix.mul_assoc]
      rfl
  set M := (matHom _ σ J g).1 with hMdef
  obtain ⟨hX, -⟩ := mem hg k hk
  obtain ⟨c, hc0, hcM⟩ := fr X g k hX
  have hYX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : ∀ j, (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k = c j := by
    intro j
    have : (fun i => (M * adMat F X) i k) = adMat F X *ᵥ c := funext hcM
    calc (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k
        = (adMat F (cT (σ : E →+* E) Y * J) *ᵥ fun i => (M * adMat F X) i k) j := by
          rw [Matrix.mul_assoc]; rfl
      _ = c j := by rw [this, mulVec_mulVec, hYX, one_mulVec]
  have hone : cT (sigR (AF F) σ) (adMat F Y) * adMat F J * adMat F X = 1 := by
    rw [c1, ← Matrix.map_mul, ← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hlt : ∀ j, j < k → c j = 0 := by
    intro j hjk
    obtain ⟨-, hY⟩ := mem (inv_mem hg) j (hS k hk j hjk.le)
    obtain ⟨c', hc'0, hc'M⟩ := fr Y g⁻¹ j hY
    set Mi := (matHom _ σ J g⁻¹).1 with hMidef
    have hMMi : M * Mi = 1 := by
      rw [hMdef, hMidef, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have hu : cT (sigR (AF F) σ) M * adMat F J * M = adMat F J := g.2
    have hJM : adMat F J * M = cT (sigR (AF F) σ) Mi * adMat F J := by
      conv_rhs => rw [← hu]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
    set W : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun (m : Fin r) (_ : Fin r) => c' m with hWdef
    have hD : ∀ l, (Mi * adMat F Y) l j = (adMat F Y * W) l j := by
      intro l; rw [hc'M l]; rfl
    have e0 : adMat F (cT (σ : E →+* E) Y * J) = adMat F (cT (σ : E →+* E) Y) * adMat F J := Matrix.map_mul
    have e1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT (sigR (AF F) σ) (Mi * adMat F Y) * adMat F J := by
      rw [e0, ← c1, Matrix.mul_assoc, hJM, Formalism.UG.cT_mul, Matrix.mul_assoc]
    have key : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k =
        (cT (sigR (AF F) σ) (adMat F Y * W) * adMat F J * adMat F X) j k := by
      rw [e1]
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hD]
    rw [← hG j, key, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (adMat F Y)), hone,
      Matrix.mul_one]
    show sigR (AF F) σ (c' k) = 0
    rw [hc'0 k hjk, map_zero]
  have hc : c = Pi.single k (c k) := by
    funext j
    rcases lt_trichotomy j k with hj | rfl | hj
    · rw [hlt j hj]; simp [Pi.single_apply, hj.ne]
    · simp
    · rw [hc0 j hj]; simp [Pi.single_apply, hj.ne']
  funext i
  calc (M *ᵥ fun i => adMat F X i k) i = (M * adMat F X) i k := rfl
    _ = (adMat F X *ᵥ c) i := hcM i
    _ = _ := by
      rw [hc, hG k]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

end GlobalTheory.IdTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingProjection
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.LeviAt

theorem embAt_projAt_mem_parab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (V : HSpace E) (W : Submodule E V.V) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : GAd hc.sig V.gram) (ht : t ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V (AF F) W) :
    embAt hc.sig V.gram S (projAt hc.sig V.gram S t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V (AF F) W := by
  have h := mem_atPts.1 (embAt_mem hc.sig V.gram S (projAt hc.sig V.gram S t))
  refine mem_parab_of_adelic (fun w => ?_) fun v => ?_
  · rw [mem_finPts_iff_forall.1 h.1 w]; exact one_mem _
  · by_cases hv : v ∈ S
    · rw [proj_embAt hc.sig V.gram S _ ⟨v, hv⟩]
      exact mapH_mem_parab (evFin F v) ht
    · rw [h.2 v hv]; exact one_mem _

theorem embAt_projAt_mem_levi : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : GAd D.sp.cm.sig V.gram), t ∈ Φ.levi D.sp.cm (AF D.host.F) P → embAt D.sp.cm.sig V.gram S (projAt D.sp.cm.sig V.gram S t) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  intro D V Φ P S t ht
  simp only [WittFrame.levi, Subgroup.mem_iInf, Subgroup.mem_inf] at ht ⊢
  exact fun u hu => ⟨embAt_projAt_mem_parab _ _ _ S t (ht u hu).1, embAt_projAt_mem_parab _ _ _ S t (ht u hu).2⟩

end GlobalTheory.LeviAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSubgroupLeGradedIsotropicFlagLevi
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem submatrix_mul_right' {R : Type} [CommRing R] {m n o p : ℕ} (P : Matrix (Fin m) (Fin n) R)
    (Q : Matrix (Fin n) (Fin o) R) (e : Fin p → Fin o) : (P * Q).submatrix id e = P * Q.submatrix id e := by
  ext i j; simp [Matrix.mul_apply]

theorem submatrix_eq_mul_one {R : Type} [CommRing R] {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Fin p → Fin n) : A.submatrix id e = A * (1 : Matrix (Fin n) (Fin n) R).submatrix id e := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem flag_mat {R : Type} [CommRing R] {n r : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (A' : Matrix (Fin r) (Fin n) R) (hA : A' * A = 1) (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    (d : Fin s → ℕ) (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card)
    (hM : ∀ k ∈ S, ∃ Bk : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) R,
      M * A.submatrix id (Fin.castLE k.2) = A.submatrix id (Fin.castLE k.2) * Bk) :
    ∃ B : Matrix (Fin s) (Fin s) R, B.BlockTriangular d ∧
      M * A.submatrix id (Fin.castLE hs) = A.submatrix id (Fin.castLE hs) * B := by
  have key : ∀ k ∈ S, ∀ j : Fin r, j ≤ k →
      (∀ l : Fin r, k < l → (A' * M * A) l j = 0) ∧ ∀ a, (M * A) a j = (A * (A' * M * A)) a j := by
    intro k hk j hj
    obtain ⟨Bk, hB⟩ := hM k hk
    have hAk : A' * A.submatrix id (Fin.castLE k.2) = (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) := by
      rw [← submatrix_mul_right', hA]
    have hTk : (A' * M * A).submatrix id (Fin.castLE k.2) =
        (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) * Bk := by
      rw [Matrix.mul_assoc, submatrix_mul_right', submatrix_mul_right', hB, ← Matrix.mul_assoc, hAk]
    have hjk : j.val < k.val + 1 := Nat.lt_succ_of_le hj
    have hj' : Fin.castLE k.2 (⟨j.val, hjk⟩ : Fin (k.val + 1)) = j := Fin.ext rfl
    refine ⟨fun l hl => ?_, fun a => ?_⟩
    · have := congrFun (congrFun hTk l) ⟨j.val, hjk⟩
      rw [Matrix.submatrix_apply, hj'] at this
      change (A' * M * A) l j = _ at this
      rw [this, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l' _ => ?_
      have hne : l ≠ Fin.castLE k.2 l' := by
        intro h; have := congrArg Fin.val h; simp at this; have := l'.2; have := Fin.lt_def.1 hl; omega
      simp [Matrix.one_apply, hne]
    · have e1 : M * A.submatrix id (Fin.castLE k.2) = (A * (A' * M * A)).submatrix id (Fin.castLE k.2) := by
        rw [hB, submatrix_mul_right', hTk, ← Matrix.mul_assoc, ← submatrix_eq_mul_one]
      have := congrFun (congrFun e1 a) ⟨j.val, hjk⟩
      rw [← submatrix_mul_right', Matrix.submatrix_apply, Matrix.submatrix_apply, hj'] at this
      exact this
  have hsmall : ∀ j : Fin r, j.val < s → ∀ l : Fin r, s ≤ l.val → (A' * M * A) l j = 0 := by
    intro j hj l hl
    obtain ⟨k, hk, hjk⟩ := (hS j).1 hj
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    exact (key k hk j hjk).1 l (Fin.lt_def.2 (by omega))
  refine ⟨(A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, ?_⟩
  · obtain ⟨k, hk, h1, h2⟩ := (depth_lt_iff S s hs d hd i j).1 hij
    exact (key k hk _ h1).1 _ h2
  · ext a j
    have hj : (Fin.castLE hs j).val < s := j.2
    obtain ⟨k, hk, hjk⟩ := (hS _).1 hj
    have e := (key k hk _ hjk).2 a
    rw [← submatrix_mul_right']
    change (M * A) a (Fin.castLE hs j) = _
    rw [e, Matrix.mul_apply, Matrix.mul_apply]
    symm
    rw [show (∑ x : Fin s, A.submatrix id (Fin.castLE hs) a x * (A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs) x j) =
        ∑ l ∈ Finset.univ.map (Fin.castLEEmb hs), A a l * (A' * M * A) l (Fin.castLE hs j) from by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have : s ≤ l.val := by
      by_contra h; push_neg at h
      exact hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hsmall _ hj l this, mul_zero]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

open GlobalTheory.StdPar in

theorem levi_le_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.StdPar.levi σ J X Y S ≤
      GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have side : ∀ Z W : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) W * J * Z = 1 →
      ∀ g : GAd σ J, (∀ k ∈ S, g ∈ frameStab σ J (initCols Z k) ⊤) →
      ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
        (matHom _ σ J g).1 * adMat F (Z.submatrix id (Fin.castLE hs)) =
          adMat F (Z.submatrix id (Fin.castLE hs)) * B := by
    intro Z W hWZ g hg
    have hA : adMat F (Formalism.UG.cT (σ : E →+* E) W * J) * adMat F Z = 1 := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact flag_mat (adMat F Z) _ hA _ S s hs hS d hd fun k hk => by
      obtain ⟨B, -, e⟩ := hg k hk
      exact ⟨B.1, e⟩
  have mem : ∀ g ∈ levi σ J X Y S, ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ⊤ ∧ g ∈ frameStab σ J (initCols Y k) ⊤ := fun g hg k hk => by
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg
    exact hg k hk
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := yx h hJ hW
  intro g hg
  have hgi := inv_mem hg
  exact Subgroup.mem_inf.2
    ⟨⟨side X Y hyx g fun k hk => (mem g hg k hk).1, side X Y hyx g⁻¹ fun k hk => (mem _ hgi k hk).1⟩,
      ⟨side Y X hW.xy g fun k hk => (mem g hg k hk).2, side Y X hW.xy g⁻¹ fun k hk => (mem _ hgi k hk).2⟩⟩

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  first | exact @GlobalTheory.LBReductions.lbIso_of_reductions | exact GlobalTheory.LBReductions.lbIso_of_reductions | (intros; apply GlobalTheory.LBReductions.lbIso_of_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 → z ∈ closure (GlobalTheory.HeckeSplitGen.grpHF σ N : Set (AF F ⊗[F] E)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | exact GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one <;> assumption)
end

