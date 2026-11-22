import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDecompositionLevi
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactIwasawa
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SiegelAssemble

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (F E) in

abbrev phiInf : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

variable (F E) in

abbrev phiFin : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

omit [NumberField E] in

theorem tens_ext {z z' : AF F ⊗[F] E} (h₁ : phiInf F E z = phiInf F E z') (h₂ : phiFin F E z = phiFin F E z') :
    z = z' := by
  obtain ⟨y, hy⟩ : ∃ y : AF F ⊗[F] E, y = z - z' + 1 := ⟨_, rfl⟩
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiInf F E y = 1
      rw [hy, map_add, map_sub, h₁, sub_self, zero_add, map_one])
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      change phiFin F E y = 1
      rw [hy, map_add, map_sub, h₂, sub_self, zero_add, map_one])
  have h3 : z - z' + 1 = 1 := hy.symm.trans (congrFun (congrFun this 0) 0)
  exact sub_eq_zero.1 (add_right_cancel (h3.trans (zero_add 1).symm))

omit [NumberField E] in
theorem matrix_tens_ext {a b : Type} {P Q : Matrix a b (AF F ⊗[F] E)} (h₁ : P.map (phiInf F E) = Q.map (phiInf F E))
    (h₂ : P.map (phiFin F E) = Q.map (phiFin F E)) : P = Q :=
  Matrix.ext fun i j => tens_ext (congrFun (congrFun h₁ i) j) (congrFun (congrFun h₂ i) j)

omit [NumberField E] in
theorem mat_projInf (g : GAd σ J) : (matHom _ σ J (projInf σ J g)).1 = (matHom _ σ J g).1.map (phiInf F E) := rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = (matHom _ σ J g).1.map (phiFin F E) := rfl

theorem mem_minPar_of_parts {p q : GAd σ J} (hp : p ∈ minPar σ J X) (h₁ : projInf σ J q = projInf σ J p)
    (h₂ : projFin σ J q = 1) : q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  let e₀ : AF F ⊗[F] E := (((1 : Ainf F), (0 : Af F)) : AF F) ⊗ₜ[F] (1 : E)
  have e₁ : phiInf F E e₀ = 1 := rfl
  have e₂ : phiFin F E e₀ = 0 := TensorProduct.zero_tmul _ _
  let B' : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
    Matrix.of fun i j => (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j +
      e₀ * (B i j - (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) i j)
  have b₁ : B'.map (phiInf F E) = B.map (phiInf F E) := Matrix.ext fun i j => by
    simp [B', e₁]
  have b₂ : B'.map (phiFin F E) = 1 := Matrix.ext fun i j => by
    by_cases hij : i = j
    · subst hij; simp [B', e₂]
    · simp [B', e₂, Matrix.one_apply_ne hij]
  refine ⟨B', fun i j hij => ?_, matrix_tens_ext ?_ ?_⟩
  · have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    simp [B', hB hij, Matrix.one_apply_ne hne]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projInf, h₁, mat_projInf, b₁, ← Matrix.map_mul, e, Matrix.map_mul]
  · rw [Matrix.map_mul, Matrix.map_mul, ← mat_projFin, h₂, b₂]
    simp

theorem commute_of_mem {a b : GAd σ J} (ha : a ∈ infPts σ J) (hb : b ∈ finPts σ J) : Commute a b := by
  have ha' : a ∈ (ofInf σ J).range := by rw [range_ofInf]; exact ha
  have hb' : b ∈ (ofFin σ J).range := by rw [range_ofFin]; exact hb
  obtain ⟨x, rfl⟩ := ha'
  obtain ⟨y, rfl⟩ := hb'
  exact commute_ofInf_ofFin σ J x y

theorem mul_mem_leviMin {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

def prodSub (K₁ K₂ : Subgroup (GAd σ J)) (h₁ : K₁ ≤ infPts σ J) (h₂ : K₂ ≤ finPts σ J) : Subgroup (GAd σ J) where
  carrier := (K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))
  one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
    have c : b * a' = a' * b := ((commute_of_mem (h₁ ha') (h₂ hb)).eq).symm
    change a * a' * (b * b') = a * b * (a' * b')
    rw [mul_assoc a b, ← mul_assoc b, c, mul_assoc a', mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
    change a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact ((commute_of_mem (h₁ (K₁.inv_mem ha)) (h₂ (K₂.inv_mem hb))).eq)

end GlobalTheory.CompanionTheory.SiegelAssemble

open GlobalTheory.CompanionTheory.SiegelAssemble in

theorem GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K₁ K₂ : Subgroup (GAd σ J), K₁ ≤ infPts σ J → K₂ ≤ finPts σ J → IsCompact (K₁ : Set (GAd σ J)) → IsCompact (K₂ : Set (GAd σ J)) → (∀ g ∈ infPts σ J, ∃ p ∈ minPar σ J X, p ∈ infPts σ J ∧ ∃ k ∈ K₁, g = p * k) → (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K₂, g = p * k) → (∀ p ∈ minPar σ J X, p ∈ K₁ → p ∈ leviMin σ J X Y) → GoodPosition σ J X Y K₂ → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂ iw₁ iw₂ hlev hgood
  refine ⟨prodSub K₁ K₂ h₁ h₂, (show IsCompact ((K₁ : Set (GAd σ J)) * (K₂ : Set (GAd σ J))) from c₁.mul c₂), fun g => ?_, ?_⟩
  · obtain ⟨p₁, hp₁, hp₁', k₁, hk₁, e₁⟩ := iw₁ (ofInf σ J (projInf σ J g)) (mem_infPts.2 (by simp))
    obtain ⟨p₂, hp₂, hp₂', k₂, hk₂, e₂⟩ := iw₂ (ofFin σ J (projFin σ J g)) (mem_finPts.2 (by simp))
    refine ⟨p₁ * p₂, mul_mem_minimal_parabolic hp₁ hp₂, k₁ * k₂, ⟨k₁, hk₁, k₂, hk₂, rfl⟩, ?_⟩
    have c : k₁ * p₂ = p₂ * k₁ := (commute_of_mem (h₁ hk₁) hp₂').eq
    calc g = ofInf σ J (projInf σ J g) * ofFin σ J (projFin σ J g) := (ofInf_projInf_mul_ofFin_projFin σ J g).symm
      _ = p₁ * (k₁ * p₂) * k₂ := by rw [e₁, e₂]; simp only [mul_assoc]
      _ = p₁ * p₂ * (k₁ * k₂) := by rw [c]; simp only [mul_assoc]
  · rintro _ hp ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have i₁ : projFin σ J k₁ = 1 := mem_infPts.1 (h₁ hk₁)
    have i₂ : projInf σ J k₂ = 1 := mem_finPts.1 (h₂ hk₂)
    have m₁ : k₁ ∈ minPar σ J X := mem_minPar_of_parts hp (by simp [i₂]) i₁
    have m₂ : k₂ ∈ minPar σ J X := by
      have := mul_mem_minimal_parabolic (inv_mem_minimal_parabolic h hJ hW m₁) hp
      simpa using this
    obtain ⟨m, hm, hmK, u, hu, huK, rfl⟩ := hgood k₂ m₂ hk₂
    exact ⟨k₁ * m, mul_mem_leviMin (hlev k₁ m₁ hk₁) hm, ⟨k₁, hk₁, m, hmK, rfl⟩, u, hu,
      ⟨1, K₁.one_mem, u, huK, one_mul u⟩, by simp only [mul_assoc]⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupSmallAnnihilator
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta GlobalTheory.CompanionTheory.BZOnto GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto.PerpSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (m : ℕ) (s : kˣ) : AddSubgroup (Fin m → k) where
  carrier := {l | ∀ j, l j ∈ cball s}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' _ := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_box {m : ℕ} {s : kˣ} {l : Fin m → k} : l ∈ box m s ↔ ∀ j, l j ∈ cball s := by
  exact Iff.rfl

theorem coe_box (m : ℕ) (s : kˣ) :
    (box m s : Set (Fin m → k)) = Set.univ.pi fun _ => cball s := by
  ext l
  simp only [SetLike.mem_coe, mem_box, Set.mem_univ_pi]

theorem isCompact_box (m : ℕ) (s : kˣ) : IsCompact (box m s : Set (Fin m → k)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s

theorem box_mem_nhds (m : ℕ) (s : kˣ) : (box m s : Set (Fin m → k)) ∈ 𝓝 (0 : Fin m → k) := by
  rw [coe_box]
  exact set_pi_mem_nhds Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.cball_mem_nhds s

theorem exists_box_subset {m : ℕ} {Ω : Set (Fin m → k)} (hΩ : Ω ∈ 𝓝 (0 : Fin m → k)) :
    ∃ r : kˣ, (box m r : Set (Fin m → k)) ⊆ Ω := by
  rw [nhds_pi, Filter.mem_pi'] at hΩ
  obtain ⟨I, t, ht, hsub⟩ := hΩ
  choose s hs using fun i => GlobalTheory.SplitWeil.exists_cball_subset (by simpa using ht i)
  by_cases hm : Nonempty (Fin m)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ValuativeRel.valuation k (s i : k))
      Finset.univ_nonempty
    refine ⟨s i₀, fun l hl => hsub fun i _ => hs i ?_⟩
    exact le_trans (show ValuativeRel.valuation k (l i) ≤ _ from (mem_box.1 hl) i) (hi₀ i (Finset.mem_univ _))
  · exact ⟨1, fun l _ => hsub fun i _ => (hm ⟨i⟩).elim⟩

theorem dotProduct_mem_cball {m : ℕ} {r s : kˣ} {b l : Fin m → k} (hb : b ∈ box m (r * s⁻¹))
    (hl : l ∈ box m s) : b ⬝ᵥ l ∈ cball r := by
  unfold dotProduct
  refine Finset.sum_induction _ (· ∈ cball r) (fun a b ha hb => add_mem_cball ha hb) ?_ ?_
  · simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k 0 ≤ _
    simp
  · intro j _
    have h1 := (mem_box.1 hb) j
    have h2 := (mem_box.1 hl) j
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k (b j * l j) ≤ ValuativeRel.valuation k (r : k)
    rw [map_mul]
    calc ValuativeRel.valuation k (b j) * ValuativeRel.valuation k (l j)
        ≤ ValuativeRel.valuation k ((r * s⁻¹ : kˣ) : k) * ValuativeRel.valuation k (s : k) := mul_le_mul' h1 h2
      _ = ValuativeRel.valuation k (r : k) := by
        rw [← map_mul]
        congr 1
        simp

end GlobalTheory.CompanionTheory.BZOnto.PerpSmall
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
section
noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.LocalThetaTranslation

theorem phi_transpose (n : ℕ) (R : Type) [CommRing R] :
    (GlobalTheory.Tw.Phi n R)ᵀ = ((-1 : R) ^ (n + 1)) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · have h' : (j : ℕ) + i + 1 = n := by omega
    rw [if_pos h, if_pos h', ← pow_add]
    have e : n + 1 + (i : ℕ) = j + 2 * ((i : ℕ) + 1) := by omega
    rw [e, pow_add, pow_mul]
    simp
  · have h' : ¬ (j : ℕ) + i + 1 = n := by omega
    rw [if_neg h, if_neg h']
    simp

theorem phi_map (n : ℕ) {R : Type} [CommRing R] (c : R →+* R) : (GlobalTheory.Tw.Phi n R).map c = GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (n : ℕ) (R : Type) [CommRing R] :
    GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h := Phi_mul_transpose n R
  rw [phi_transpose, Matrix.mul_smul] at h
  have e : ((-1 : R) ^ (n + 1)) * ((-1 : R) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; simp
  rw [← h, smul_smul, e, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_conj_eq_sign (n : ℕ) : ∃ s : E, s ≠ 0 ∧ conjE E s = (-1 : E) ^ (n + 1) * s := by
  rcases neg_one_pow_eq_or E (n + 1) with h | h
  · exact ⟨1, one_ne_zero, by rw [h, map_one, one_mul]⟩
  · have hx : ∃ x : E, conjE E x ≠ x := by
      by_contra hc
      push Not at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    have hcc : conjE E (conjE E x) = x := IsCMField.complexConj_apply_apply E x
    refine ⟨x - conjE E x, sub_ne_zero.2 hx.symm, ?_⟩
    rw [h, map_sub, hcc]
    ring

omit [NumberField E] [IsCMField E] in

theorem scalar_val {n : ℕ} (t : Eˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h]

omit [NumberField E] [IsCMField E] in

theorem scalar_commute {n : ℕ} (t : Eˣ) (g : GL (Fin n) E) :
    GeneralLinearGroup.scalar (Fin n) t * g = g * GeneralLinearGroup.scalar (Fin n) t := by
  apply Units.ext
  simp only [Units.val_mul, scalar_val]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem thetaE_phiU (n : ℕ) : (thetaE E n (PhiU n E)).val = GlobalTheory.Tw.Phi n E := by
  change ((((PhiU n E)⁻¹).val).map (conjE E))ᵀ = _
  rw [phiU_inv_val, Matrix.transpose_map, Matrix.transpose_transpose, phi_map]

theorem thetaE_scalar {n : ℕ} (t : Eˣ) :
    (thetaE E n (GeneralLinearGroup.scalar (Fin n) t)).val =
      (conjE E (t : E))⁻¹ • (1 : Matrix (Fin n) (Fin n) E) := by
  change ((((GeneralLinearGroup.scalar (Fin n) t)⁻¹).val).map (conjE E))ᵀ = _
  rw [← map_inv, scalar_val]
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem translEx : TranslEx := by
  intro E _ _ _ n
  obtain ⟨s, hs, hc⟩ := exists_conj_eq_sign (E := E) n
  have hcs : conjE E s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hs
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E, ?_, ?_⟩
  · intro g
    have h1 : thE E n g = PhiU n E * thetaE E n g * (PhiU n E)⁻¹ := thetaGL_eq n E _ g
    rw [h1]
    have h2 := scalar_commute (Units.mk0 s hs) (PhiU n E * thetaE E n g * (PhiU n E)⁻¹)
    have h3 : GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E * thetaE E n g *
        (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * (PhiU n E * thetaE E n g * (PhiU n E)⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs))⁻¹ := by
      group
    rw [h3, h2, mul_inv_cancel_right]
  · apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_mul, Units.val_mul, thetaE_phiU, thetaE_scalar, scalar_val, phiU_val]
    simp only [Units.val_mk0, Units.val_one]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      phi_mul_self, smul_smul, smul_smul, hc]
    have hp : ((-1 : E) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have : s * (((-1 : E) ^ (n + 1)) * s)⁻¹ * ((-1 : E) ^ (n + 1)) = 1 := by
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.LocalThetaTranslation
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
section
open Matrix Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticTwist

theorem exists_eigenbasis {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hs : N.charpoly.Separable) :
    ∃ (h : GL (Fin n) ℂ) (γ : Fin n → ℂ), Function.Injective γ ∧ (∀ i, N.charpoly.IsRoot (γ i)) ∧
      N * h.val = h.val * diagonal γ := by
  have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
  have hcard : N.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := Finset.equivFinOfCardEq hcard
  let γ : Fin n → ℂ := fun i => (e.symm i).1
  have hinj : Function.Injective γ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hroot : ∀ i, N.charpoly.IsRoot (γ i) := fun i =>
    (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0 := fun i =>
    exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)
  choose v hv0 hv using hev
  have hNv : ∀ i, N *ᵥ v i = γ i • v i := fun i => by
    have h1 := hv i
    rw [sub_mulVec, sub_eq_zero] at h1
    rw [← h1]
    ext k
    simp [scalar_apply, mulVec_diagonal]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v
      (fun i => Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)
  have hu : IsUnit (Matrix.of v)ᵀ := linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨h, hh⟩ := hu
  refine ⟨h, γ, hinj, hroot, ?_⟩
  have hh' : h.val = (Matrix.of v)ᵀ := hh
  rw [hh']
  ext i j
  have h2 := congrFun (hNv j) i
  rw [mul_diagonal]
  simpa [mul_apply, mulVec, dotProduct, mul_comm] using h2

variable {n : ℕ}

theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR (starRingEnd ℂ) n g).val = (g⁻¹).valᴴ := by
  ext i j
  simp [thetaR_val, conjTranspose_apply]

theorem theta_inv_val (g : GL (Fin n) ℂ) :
    ((thetaR (starRingEnd ℂ) n g)⁻¹).val = g.valᴴ := by
  rw [← map_inv, theta_val, inv_inv]

theorem theta_theta (g : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
  Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])

theorem offDiag_eq_zero (D : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ = 1)
    (hinj : Function.Injective γ) (hD : D = diagonal γ * Dᴴ) {i j : Fin n} (hij : i ≠ j) : D i j = 0 := by
  have h2 : Dᴴ = D * diagonal (star γ) := by
    conv_lhs => rw [hD]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have h3 : D i j = γ i * (D i j * star (γ j)) := by
    conv_lhs => rw [hD, h2]
    rw [diagonal_mul, mul_diagonal]
    rfl
  by_contra hne
  have h4 : γ i * star (γ j) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination -h3
  have h5 : star (γ j) * γ j = 1 := by
    have := Complex.conj_mul' (γ j)
    rw [hγ j] at this
    simpa using this
  apply hij
  apply hinj
  linear_combination -γ i * h5 + γ j * h4

theorem ellDiag : EllDiag := by
  intro n d hd
  obtain ⟨hs, hn⟩ := hd
  obtain ⟨h, γ, hinj, hroot, hN⟩ := exists_eigenbasis _ hs
  have hγ : ∀ i, ‖γ i‖ = 1 := fun i => hn _ (hroot i)
  set θ := thetaR (starRingEnd ℂ) n with hθ
  let d₁ : GL (Fin n) ℂ := twConj θ h d
  have hnorm : (d₁ * θ d₁).val = diagonal γ := by
    have h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h := by
      simp [d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]
    simp
  have hD : d₁.val = diagonal γ * d₁.valᴴ := by
    rw [← hnorm, ← theta_inv_val, ← Units.val_mul]
    simp [hθ]
  let b : Fin n → ℂ := fun i => d₁.val i i
  have hdiag : d₁.val = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [b]
    · rw [offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i hi
    have h0 : d₁.val.det = 0 := by
      rw [hdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i) := by
    intro i
    have h1 := congrFun (congrFun hD i) i
    rw [diagonal_mul] at h1
    simpa [conjTranspose_apply] using h1
  let s : Fin n → ℂ := fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)
  have hnb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb0 i)
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'
  have hss : ∀ i, s i * s i = (‖b i‖ : ℂ) := fun i => by
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩
  have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
  have htθ : (θ t).val = diagonal fun i => (s i)⁻¹ := by
    rw [hθ, theta_val, htinv, diagonal_conjTranspose]
    congr 1
    ext i
    simp [s]
  let z : Fin n → ℂ := fun i => b i / (‖b i‖ : ℂ)
  have hz2 : ∀ i, z i ^ 2 = γ i := by
    intro i
    have hne : (‖b i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hnb i).ne'
    have h1 := Complex.mul_conj' (b i)
    simp only [z]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]
    conv_lhs => rw [sq]; enter [1]; rw [hbγ i]
    ring
  refine ⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩
  · change (t⁻¹ * d₁ * θ t).val = _
    rw [Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    have := hss i
    have h0 := hs0 i
    simp only [z]
    rw [← this]
    field_simp
  · intro i
    simp only [z]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']
  · intro i j hij
    apply hinj
    have := hz2 i
    have := hz2 j
    simp only at hij
    rw [← hz2 i, ← hz2 j, hij]
  · simp [twConj, d₁, map_mul, map_inv, mul_assoc]

end GlobalTheory.CompanionTheory.EllipticTwist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDecompositionLeviStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_decomposition_levi : PositivityTheory.RgBcC.RealD.HCdecLv := by
  first | exact @GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | exact GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | (intros; apply GlobalTheory.CompanionTheory.RealHCLv.hcdecLv <;> assumption)
end

