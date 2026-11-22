import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPa
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanEx

open scoped ComplexOrder

private lemma map_star_mul' {l m k : Type} [Fintype m] (X : Matrix l m ℂ) (Y : Matrix m k ℂ) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private lemma map_star_star {l m : Type} (X : Matrix l m ℂ) : (X.map star).map star = X := by
  ext i j; simp

private lemma map_star_one {m : Type} [DecidableEq m] : (1 : Matrix m m ℂ).map star = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma star_mulVec_map {l m : Type} [Fintype m] (X : Matrix l m ℂ) (v : m → ℂ) :
    star (X *ᵥ v) = X.map star *ᵥ star v := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  intro n M r s ⟨hn, A, hA⟩
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by simp [hD, Matrix.fromBlocks_multiply]
  have hDT : Dᵀ = D := by simp [hD, Matrix.fromBlocks_transpose]
  have hDs : D.map star = D := by
    simp only [hD, Matrix.fromBlocks_map]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  clear_value D
  set L := D * Aᵀ * M with hLdef
  clear_value L
  have hL : L * A.map star = 1 := by
    rw [hLdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, hDD]
  have e : Fin n ≃ Fin r ⊕ Fin s := (finSumFinEquiv.trans (finCongr hn)).symm
  have hR : A.map star * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hL
  have hR' : A * L.map star = 1 := by
    have := congrArg (fun X => Matrix.map X star) hR
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  have hL' : L.map star * A = 1 := by
    have := congrArg (fun X => Matrix.map X star) hL
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  refine ⟨A * D * L.map star, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L.map star) A, hL', Matrix.one_mul, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul, hR']
  · have hDL : D * L = Aᵀ * M := by
      rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    calc (A * D * L.map star)ᵀ * M * (A * D * L.map star).map star
        = (L.map star)ᵀ * D * (Aᵀ * M * A.map star) * (D * L) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul', map_star_mul', map_star_star, hDs, hDT]
          simp only [Matrix.mul_assoc]
      _ = (A * L.map star)ᵀ * M := by
          rw [hA, hDL, Matrix.mul_assoc (L.map star)ᵀ D D, hDD, Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M := by rw [hR', Matrix.transpose_one, Matrix.one_mul]
  · intro x hx
    set a := L.map star *ᵥ x with ha_def
    have hxa : x = A *ᵥ a := by rw [ha_def, Matrix.mulVec_mulVec, hR', Matrix.one_mulVec]
    have ha : a ≠ 0 := by
      intro h; apply hx; rw [hxa, h, Matrix.mulVec_zero]
    have hθx : (A * D * L.map star) *ᵥ x = A *ᵥ (D *ᵥ a) := by
      rw [ha_def, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have key : ∀ b c : Fin r ⊕ Fin s → ℂ, (A *ᵥ b) ⬝ᵥ M *ᵥ (A.map star *ᵥ c) = b ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ c := by
      intro b c
      rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
    have hval : ((A * D * L.map star) *ᵥ x) ⬝ᵥ M *ᵥ star x = a ⬝ᵥ star a := by
      rw [hθx]
      conv_lhs => rw [hxa, star_mulVec_map]
      rw [key, hA, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hDT, hDD, Matrix.vecMul_one]
    rw [hval]
    exact (Complex.pos_iff.mp (Matrix.dotProduct_self_star_pos_iff.mpr ha)).1

end GlobalTheory.CartanEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoatomOfFiniteLength
section
open GlobalTheory.WeilM GlobalTheory.HoweAdelic

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HoweAdelic.TrivSup

theorem trivial_irr (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
  · rcases eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

theorem trivial_adm (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  have : {g : G | Representation.trivial ℂ G ℂ g v = v} = Set.univ := by ext; simp
  rw [this]; exact isOpen_univ

theorem exists_coatom_of_finiteLength {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (hf : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule) (S : Subrepresentation Θ) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation Θ, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hf
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ H) Θ.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

end GlobalTheory.HoweAdelic.TrivSup

namespace GlobalTheory.HoweAdelic

open TrivSup in

theorem sup_ne_SB_of_howeDuality : ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    ∀ N N', IsLocSub om N → IsLocSub om N' → N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hHD hom N N' hN hN' hNe hN'e hsup
  obtain ⟨⟨T, _, _, Θ, p, ⟨hpair, hsurj, hker⟩, -, hfl, huniq⟩, -⟩ :=
    hHD ℂ (Representation.trivial ℂ G ℂ) (trivial_irr G) (trivial_adm G)
  let q : SB Y →ₗ[ℂ] T := (TensorProduct.lid ℂ T).toLinearMap ∘ₗ p
  have hqsurj : Function.Surjective q := (TensorProduct.lid ℂ T).surjective.comp hsurj
  have hq : ∀ (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (1, h) φ → q φ₁ = Θ h (q φ) := by
    intro h φ φ₁ e
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hpair 1 h φ φ₁ e]
    induction p φ using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkerq : ∀ x : SB Y, q x = 0 → (x : Y → ℂ) ∈ locAug om := by
    intro x hx
    have hp : p x = 0 := by simpa [q] using hx
    by_contra hnot
    let L : Submodule ℂ (SB Y) := (locAug om).comap (SB Y).subtype
    have hxL : L.mkQ x ≠ 0 := by
      rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hnot
    obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ (SB Y ⧸ L), l (L.mkQ x) ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hxL ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
    have hf : GlobalTheory.Published.IsLeftHom om (Representation.trivial ℂ G ℂ) (l ∘ₗ L.mkQ) := by
      intro g φ φ₁ e
      have hmem : φ₁ - φ ∈ L := by
        show ((φ₁ - φ : SB Y) : Y → ℂ) ∈ locAug om
        rw [Submodule.coe_sub, e]
        exact Submodule.subset_span ⟨g, φ, φ.2, rfl⟩
      have h0 : L.mkQ (φ₁ - φ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
      rw [map_sub] at h0
      simp only [LinearMap.comp_apply, Representation.trivial, MonoidHom.one_apply, Module.End.one_apply]
      rw [sub_eq_zero.1 h0]
    exact hl ((hker x).1 hp _ hf)
  have key : ∀ M, IsLocSub om M → M ≠ SB Y →
      ∃ C : Subrepresentation Θ, IsCoatom C ∧ ∀ φ : SB Y, (φ : Y → ℂ) ∈ M → q φ ∈ C.toSubmodule := by
    intro M hM hMne
    obtain ⟨S, hSdef⟩ : ∃ S : Subrepresentation Θ, S.toSubmodule = (M.comap (SB Y).subtype).map q :=
      ⟨⟨(M.comap (SB Y).subtype).map q, by
        rintro h _ ⟨φ, hφ, rfl⟩
        exact ⟨⟨om (1, h) φ, hom _ φ φ.2⟩, hM.2.2 h φ hφ, hq h φ _ rfl⟩⟩, rfl⟩
    have hS : S ≠ ⊤ := by
      intro hS
      apply hMne
      refine le_antisymm hM.2.1 (fun φ hφ => ?_)
      have h1 : q ⟨φ, hφ⟩ ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      rw [hSdef] at h1
      obtain ⟨ψ, hψ, e⟩ := h1
      have hd := hkerq (⟨φ, hφ⟩ - ψ) (by rw [map_sub, e, sub_self])
      have h2 : φ = (((⟨φ, hφ⟩ : SB Y) - ψ : SB Y) : Y → ℂ) + ψ := by simp
      rw [h2]; exact M.add_mem (hM.1 hd) hψ
    obtain ⟨C, hC, hle⟩ := exists_coatom_of_finiteLength Θ hfl S hS
    refine ⟨C, hC, fun φ hφ => hle (show q φ ∈ S.toSubmodule from ?_)⟩
    rw [hSdef]; exact ⟨φ, hφ, rfl⟩
  obtain ⟨C, hC, hCN⟩ := key N hN hNe
  obtain ⟨C', hC', hCN'⟩ := key N' hN' hN'e
  obtain rfl := huniq C C' hC hC'
  apply hC.1
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨φ, rfl⟩ := hqsurj t
  have hφ : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [hsup]; exact φ.2
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hφ
  have h3 : φ = ⟨a, hN.2.1 ha⟩ + ⟨b, hN'.2.1 hb⟩ := Subtype.ext (by simp [e])
  rw [h3, map_add]
  exact C.toSubmodule.add_mem (hCN _ ha) (hCN' _ hb)

end GlobalTheory.HoweAdelic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroups
section
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.FinAdeleNbhd

theorem exists_prod_openCompact_subset :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (V : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    V ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (N v : Set (v.adicCompletion F))) ∧ (∀ v, IsCompact (N v : Set (v.adicCompletion F))) ∧
      (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) ∧
      {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v} ⊆ V := by
  intro F _ _ κ _ V hV
  classical

  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨J, s, hs, hJs⟩ := hV
  set W : Set (FiniteAdeleRing (𝓞 F) F) := ⋂ i, s i with hWdef
  have hW : W ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 hs
  have hWV : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, y i ∈ W) → y ∈ V := fun y hy =>
    hJs fun i _ => Set.mem_iInter.1 (hy i) i

  let R : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Type := fun v => v.adicCompletion F
  let A : ∀ v, Set (R v) := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let e := RestrictedProduct.structureMap R A Filter.cofinite
  have he : Continuous e := (RestrictedProduct.isEmbedding_structureMap).continuous
  let p : ∀ v, A v := fun v => ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  have hep : (e p : FiniteAdeleRing (𝓞 F) F) = 0 := rfl
  have hpre : e ⁻¹' W ∈ 𝓝 p := he.continuousAt.preimage_mem_nhds (by rw [hep]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hpre
  obtain ⟨I, t, ht, hIt⟩ := hpre
  have hu : ∀ v, ∃ u ∈ 𝓝 (0 : R v), Subtype.val ⁻¹' u ⊆ t v := fun v =>
    (mem_nhds_subtype (A v) (p v) (t v)).1 (ht v)
  choose u hu0 hut using hu

  have hG : ∀ v, ∃ G : OpenAddSubgroup (R v), (G : Set (R v)) ⊆ u v := fun v =>
    NonarchimedeanAddGroup.is_nonarchimedean _ (hu0 v)
  choose G hGu using hG
  let O : ∀ v, AddSubgroup (R v) := fun v => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hOset : ∀ v, ((O v : AddSubgroup (R v)) : Set (R v)) = A v := fun v => rfl
  have hOopen : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hOcpt : ∀ v, IsCompact (A v) := fun v =>
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let N : ∀ v, AddSubgroup (R v) := fun v => if v ∈ I then (G v).toAddSubgroup ⊓ O v else O v
  have hNO : ∀ v, ∀ x ∈ N v, x ∈ A v := by
    intro v x hx
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true] at hx; exact hx.2
    · simp only [N, hv, if_false] at hx; exact hx
  have hNG : ∀ v ∈ I, ∀ x ∈ N v, x ∈ (G v : Set (R v)) := by
    intro v hv x hx
    simp only [N, hv, if_true] at hx; exact hx.1
  have hNopen : ∀ v, IsOpen (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (G v).isOpen.inter (hOopen v)
    · simp only [N, hv, if_false]; exact hOopen v
  have hNcpt : ∀ v, IsCompact (N v : Set (R v)) := by
    intro v
    by_cases hv : v ∈ I
    · simp only [N, hv, if_true, AddSubgroup.coe_inf]
      exact (hOcpt v).inter_left (G v).isClosed
    · simp only [N, hv, if_false]; exact hOcpt v
  refine ⟨N, hNopen, hNcpt, ?_, ?_, ?_⟩
  · filter_upwards [I.eventually_cofinite_notMem] with v hv
    simp only [N, hv, if_false]; rfl
  ·
    let P : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ N v}
    have hPeq : P = {a : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ I → a v ∈ A v} ∩ ⋂ v ∈ I, (fun a : FiniteAdeleRing (𝓞 F) F => a v) ⁻¹' (N v : Set (R v)) := by
      ext a
      simp only [P, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h; exact ⟨fun v _ => hNO v _ (h v), fun v _ => h v⟩
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ I
        · exact h2 v hv
        · have := h1 v hv
          simp only [N, hv, if_false]; exact this
    have hPopen : IsOpen P := by
      rw [hPeq]
      refine IsOpen.inter (RestrictedProduct.isOpen_forall_imp_mem hOopen) ?_
      exact isOpen_biInter_finset fun v _ => (hNopen v).preimage (RestrictedProduct.continuous_eval v)
    have hP0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ P := fun v => (N v).zero_mem
    have : (Set.univ : Set κ).pi (fun _ => P) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      set_pi_mem_nhds Set.finite_univ fun i _ => hPopen.mem_nhds hP0
    refine Filter.mem_of_superset this ?_
    intro y hy i v
    exact hy i (Set.mem_univ i) v
  ·
    intro y hy
    apply hWV
    intro i
    have hyi : ∀ v, (y i) v ∈ N v := fun v => hy i v
    let x : ∀ v, A v := fun v => ⟨(y i) v, hNO v _ (hyi v)⟩
    have hex : (e x : FiniteAdeleRing (𝓞 F) F) = y i := rfl
    have hxI : x ∈ (I : Set _).pi t := by
      intro v hv
      apply hut v
      show (y i) v ∈ u v
      exact hGu v (hNG v hv _ (hyi v))
    have h := hIt hxI
    have h' : (e x : FiniteAdeleRing (𝓞 F) F) ∈ W := h
    rw [hex] at h'
    exact h'

end GlobalTheory.FinAdeleNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitaryStatement
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | exact GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | (intros; apply GlobalTheory.ColAction.exists_symplectic_hom_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormSemiLocalWhittakerSpaceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  first | exact @GlobalTheory.JSW.MirSemi.whitSpace_exists | exact GlobalTheory.JSW.MirSemi.whitSpace_exists | (intros; apply GlobalTheory.JSW.MirSemi.whitSpace_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFramesStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  first | exact @GlobalTheory.HolRead.TorusExt.exists_extension | exact GlobalTheory.HolRead.TorusExt.exists_extension | (intros; apply GlobalTheory.HolRead.TorusExt.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistAcyclicSpectrumPolynomialOfIsAlgClosedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  first | (exact @GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (exact GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed) | (intros; apply GlobalTheory.EtC.acyc_polynomial_of_isAlgClosed  <;> assumption)
end

