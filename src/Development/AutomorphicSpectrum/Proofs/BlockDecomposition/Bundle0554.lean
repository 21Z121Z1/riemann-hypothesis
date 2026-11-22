import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExists
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.KCurve

section
open scoped Matrix.Norms.L2Operator

theorem exists_exp_eq_of_unitary {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ)
    (hu : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp Y = k := by
  haveI : IsStarNormal k :=
    ⟨(Unitary.star_mul_self_of_mem hu).trans (Unitary.mul_star_self_of_mem hu).symm⟩
  have hfin := Matrix.finite_spectrum k
  have hunit : IsUnit k := (Unitary.toUnits ⟨k, hu⟩).isUnit
  have hne : ∀ x ∈ spectrum ℂ k, x ≠ 0 := fun x hx h0 =>
    (spectrum.zero_notMem_iff ℂ).mpr hunit (h0 ▸ hx)
  refine ⟨cfc Complex.log k, ?_⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (p := IsStarNormal) (a := cfc Complex.log k),
    ← cfc_comp (R := ℂ) (p := IsStarNormal) NormedSpace.exp Complex.log k
      (hg := (hfin.image _).continuousOn _) (hf := hfin.continuousOn _)]
  have hc : cfc (NormedSpace.exp ∘ Complex.log) k = cfc (id : ℂ → ℂ) k := by
    refine cfc_congr fun x hx => ?_
    simp only [Function.comp, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log (hne x hx)]
  rw [hc, cfc_id ℂ k]

end

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def atPlace (w : InfinitePlace E) :
    Matrix (Fin a) (Fin a) (Cinf E) →+* Matrix (Fin a) (Fin a) ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix

theorem atPlace_apply (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) :
    atPlace w x i j = x i j w := rfl

theorem continuous_atPlace (w : InfinitePlace E) :
    Continuous (atPlace (a := a) w) :=
  continuous_id.matrix_map (continuous_apply w)

theorem atPlace_star (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) :
    atPlace w (star x) = star (atPlace w x) := by
  ext i j
  rfl

theorem exists_exp_eq (k : Kinf E a) :
    ∃ M : Matrix (Fin a) (Fin a) (Cinf E), NormedSpace.exp M = k.1 := by
  have hk : ∀ w, atPlace w k.1 ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := fun w =>
    Unitary.mem_iff.mpr
      ⟨by rw [← atPlace_star, ← map_mul, Unitary.star_mul_self_of_mem k.2, map_one],
       by rw [← atPlace_star, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]⟩
  choose Y hY using fun w => exists_exp_eq_of_unitary (atPlace w k.1) (hk w)
  refine ⟨Matrix.of fun i j w => Y w i j, Matrix.ext fun i j => ?_⟩
  funext w
  have h1 := congrArg (fun m => m i j)
    (NormedSpace.map_exp (atPlace w) (continuous_atPlace w) (Matrix.of fun i j w => Y w i j))
  have hM : atPlace w (Matrix.of fun i j w => Y w i j) = Y w := by
    ext i' j'
    rfl
  simp only [atPlace_apply, hM] at h1
  exact h1.trans ((congrArg (fun m => m i j) (hY w)).trans (atPlace_apply w k.1 i j))

theorem exists_curve : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  intro E _ _ _ a k
  obtain ⟨M, hM⟩ := exists_exp_eq k
  have htoL : ∀ N : Matrix (Fin a) (Fin a) (Cinf E), toL N = GlobalTheory.CompanionTheory.LieCurve.toLieL E a N := fun N => by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
  have hof : Matrix.of (GlobalTheory.CompanionTheory.LieCurve.toLieL E a M) = M := by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
    rfl
  refine ⟨GlobalTheory.CompanionTheory.LieCurve.expUnit E a M, GlobalTheory.CompanionTheory.LieCurve.toLieL E a M,
    GlobalTheory.CompanionTheory.LieCurve.expUnit_zero E a M, ?_, fun s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, one_smul, hM]
    rfl
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, hof, htoL]
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s
      (GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a M s)
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_inv_val, hof, htoL]
    have h1 := GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a (-M) s
    have e1 : (fun t : ℝ => NormedSpace.exp (t • -M)) = fun t : ℝ => NormedSpace.exp (-t • M) := by
      funext t
      rw [neg_smul, smul_neg]
    have e2 : NormedSpace.exp (s • -M) * -M = -(M * NormedSpace.exp (-s • M)) := by
      rw [smul_neg, ← neg_smul, mul_neg, ((Commute.refl M).smul_right (-s)).exp_right.eq]
    rw [e1, e2] at h1
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s h1

end GlobalTheory.CompanionTheory.SmoothRep.KCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitaryWitt

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem conj_mem_UJ_one_iff (σ : L →+* L) {J : Matrix (Fin n) (Fin n) L} (b g : GL (Fin n) L)
    (hb : cT σ b.val * b.val = J) : b * g * b⁻¹ ∈ UJ σ 1 ↔ g ∈ UJ σ J := by
  have hbi : b.val * (b⁻¹ : GL (Fin n) L).val = 1 := by rw [← Units.val_mul]; simp
  have hib : (b⁻¹ : GL (Fin n) L).val * b.val = 1 := by rw [← Units.val_mul]; simp
  change cT σ (b * g * b⁻¹).val * 1 * (b * g * b⁻¹).val = 1 ↔ cT σ g.val * J * g.val = J
  simp only [Units.val_mul, Matrix.mul_one]
  have hc : cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val = 1 := by
    rw [← cT_mul, hbi, cT_one]
  have key : cT σ (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) * (b.val * g.val * (b⁻¹ : GL (Fin n) L).val)
      = cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val := by
    rw [← hb]
    simp only [cT_mul, Matrix.mul_assoc]
  rw [key]
  constructor
  · intro h
    have h2 : cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val
        = cT σ b.val * 1 * b.val := by rw [h]
    have hc' : cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val = 1 := by
      rw [← cT_mul, hib, cT_one]
    calc cT σ g.val * J * g.val
        = (cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val) * (cT σ g.val * J * g.val) * ((b⁻¹ : GL (Fin n) L).val * b.val) := by
          rw [hc', hib, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.mul_one, hb]
  · intro h
    rw [h, ← hb]
    calc cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ b.val * b.val) * (b⁻¹ : GL (Fin n) L).val
        = (cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val) * (b.val * (b⁻¹ : GL (Fin n) L).val) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hbi, Matrix.one_mul]

theorem diagT_mem_UJ_antiJ_iff (σ : L →+* L) (u : Fin n → Lˣ) :
    GlobalTheory.SmGL.diagT L (Fin n) u ∈ UJ σ (antiJ L n) ↔ ∀ i, σ (u i) * u (Fin.rev i) = 1 := by
  have hent : ∀ i j, (cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val) i j
      = σ (u i) * antiJ L n i j * u j := by
    intro i j
    have hd : cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val = Matrix.diagonal fun i => σ (u i) := by
      rw [GlobalTheory.SmGL.val_diagT]
      ext a c
      by_cases h : a = c
      · subst h; simp [cT]
      · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rw [hd, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrev : ∀ i : Fin n, antiJ L n i (Fin.rev i) = 1 := by
    intro i
    have : i.val + (Fin.rev i).val + 1 = n := by
      rw [Fin.val_rev]; omega
    exact if_pos this
  change cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val = antiJ L n ↔ _
  constructor
  · intro h i
    have := congrFun (congrFun h i) (Fin.rev i)
    rw [hent, hrev, mul_one] at this
    exact this
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = Fin.rev i := by
        apply Fin.ext; rw [Fin.val_rev]; omega
      subst hj
      rw [hrev, mul_one, h i]
    · have : antiJ L n i j = 0 := by simp [antiJ, hij]
      rw [this]; simp

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem UL_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) : UL n w = UJ (cj w) 1 := if_neg hw

theorem mem_iwU_iff (n : ℕ) (w : Pl E) (b : GLw n w) (γ : UL n w) :
    γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w := by
  rw [iwU, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have e' : b * x * b⁻¹ = γ.1 := e
    rw [← e']
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    change b * (b⁻¹ * γ.1 * b) * b⁻¹ = γ.1
    group

theorem isClosed_UJ_one {w : Pl E} (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Set (GLw n w)) := by
  have hv : Continuous fun g : GLw n w => (g.val : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GLw n w => cT (cj w) g.val * 1 * g.val := by
    refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
    exact (hv.matrix_map hc).matrix_transpose
  exact isClosed_eq hm continuous_const

theorem isCompact_iwU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hc : Continuous (cj w)) :
    IsCompact (iwU n w b : Set (UL n w)) := by
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [UL_eq_of_not_split hw]; exact isClosed_UJ_one n hc
  have hK : IsCompact ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n)).image (by fun_prop)
  have hP := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have e : (iwU n w b : Set (UL n w)) = Subtype.val ⁻¹'
      ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) := by
    ext γ
    simp only [SetLike.mem_coe, mem_iwU_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨_, h, by group⟩
    · rintro ⟨x, hx, e⟩
      rw [← e]
      simpa [mul_assoc] using hx
  rw [e]
  exact hP

theorem unitary_hyperbolic_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  intro E _ _ _ hU w hw n b hb
  refine ⟨fun g => ?_, mem_iwU_iff n w b, isCompact_iwU hw n b (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1,
    diagT_mem_UJ_antiJ_iff (cj w)⟩
  rw [UL_eq_of_not_split hw]
  exact conj_mem_UJ_one_iff (cj w) b g hb.2

end GlobalTheory.CompanionTheory.UnitaryWitt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFinite
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Mahler

open GlobalTheory.CompanionTheory.RedCov.Bridge

def pointsHomeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GAd (conj F E).toAlgHom J ≃ₜ unitaryPoints F E J 𝔸[F] where
  toFun g := ⟨matHom _ _ J g, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).1 g.2⟩
  invFun u := ⟨u.1, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

theorem exists_isCompact_of_le_hgt : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  intro hM F E _ _ _ _ _ σ hσ n J hJ t ht
  obtain ⟨hF, hE', h2, hc⟩ := hσ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let e := pointsHomeo (F := F) (E := E) J
  obtain ⟨Ω, hΩ, hcov⟩ := hM F E n J hu
    (e '' {g | ∀ v : Fin n → E, v ≠ 0 → t ≤ hgt _ J g v}) t ht (by
      rintro _ ⟨g, hg, rfl⟩ x hx
      obtain ⟨v, rfl⟩ := cvec_surjective (F := F) (E := E) (n := n) x
      have hv : v ≠ 0 := by
        rintro rfl
        apply hx
        funext p
        simp [cvec]
      have := hg v hv
      rw [hgt_eq] at this
      exact this)
  refine ⟨e ⁻¹' Ω, e.isCompact_preimage.2 hΩ, fun g hg => ?_⟩
  obtain ⟨θ, hθ, hθΩ⟩ := hcov (e g) ⟨g, hg, rfl⟩
  rw [← CompanionTheory.SWFin.HFin_eq, Subgroup.mem_subgroupOf] at hθ
  refine ⟨e.symm θ, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 hθ
  · exact hθΩ

end GlobalTheory.CompanionTheory.RedCov.Mahler
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.Wexp

theorem cone_strictAnti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) : StrictAnti l := by
  have key : ∀ (d : ℕ) (i j : Fin m), (j : ℕ) = i + d + 1 → l j < l i := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have := hl.1 i j (by omega)
      omega
    | succ d ih =>
      intro i j hij
      have hk : (i : ℕ) + d + 1 < m := by have := j.isLt; omega
      have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
      have h2 := hl.1 ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
      omega
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  exact key ((j : ℕ) - i - 1) i j (by omega)

theorem wexp_of_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    wexp n l i = l ⟨i, h⟩ := by
  simp only [wexp, dif_pos h]

theorem wexp_of_rev_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h' : n - 1 - (i : ℕ) < n / 2) :
    wexp n l i = -l ⟨n - 1 - i, h'⟩ := by
  have h : ¬ (i : ℕ) < n / 2 := by have := i.isLt; omega
  simp only [wexp, dif_neg h, dif_pos h']

theorem wexp_of_middle {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : ¬ (i : ℕ) < n / 2)
    (h' : ¬ n - 1 - (i : ℕ) < n / 2) : wexp n l i = 0 := by
  simp only [wexp, dif_neg h, dif_neg h']

theorem wexp_strictAnti_rev : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l →
    StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  intro n l hl
  have hs := cone_strictAnti hl
  have hp := hl.2
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.isLt
    by_cases h1 : (i : ℕ) < n / 2
    · rw [wexp_of_lt l i h1]
      have a := hp ⟨i, h1⟩
      by_cases h2 : (j : ℕ) < n / 2
      · rw [wexp_of_lt l j h2]
        exact hs (Fin.mk_lt_mk.mpr hij')
      · by_cases h3 : n - 1 - (j : ℕ) < n / 2
        · rw [wexp_of_rev_lt l j h3]
          have b := hp ⟨_, h3⟩
          omega
        · rw [wexp_of_middle l j h2 h3]
          omega
    · have h3 : n - 1 - (j : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l j h3]
      have b := hp ⟨_, h3⟩
      by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · rw [wexp_of_rev_lt l i h2]
        have : l ⟨n - 1 - i, h2⟩ < l ⟨n - 1 - j, h3⟩ := hs (Fin.mk_lt_mk.mpr (by omega))
        omega
      · rw [wexp_of_middle l i h1 h2]
        omega
  · intro i
    have hi := i.isLt
    have hr : ((Fin.rev i : Fin n) : ℕ) = n - 1 - i := by
      rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < n / 2
    · have h' : n - 1 - ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l _ h', wexp_of_lt l i h1]
      congr 2
      apply Fin.ext
      simp only
      omega
    · by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · have h' : ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
        rw [wexp_of_lt l _ h', wexp_of_rev_lt l i h2, neg_neg]
        congr 1
        exact Fin.ext hr
      · rw [wexp_of_middle l i h1 h2, wexp_of_middle l _ (by omega) (by omega), neg_zero]

end GlobalTheory.CompanionTheory.Wexp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCorrespond
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO

namespace GlobalTheory.CompanionTheory.AgreeO.Read

def BaseChars : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle),
    IsTriple W W₁ X α β → ∀ (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w)
      (τ : InfinitePlace D.host.F → D.what₂.Tau), Function.Bijective τ → (∀ w x, (emb w).1 x = conj (tauE D (τ w) x)) →
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E),
      Bs.ψ = ψ ∧ Bs.emb = emb ∧ Xc.α = α ∧ Xc.β = β ∧ Bs.IsGood D.sp.cm.sig ∧ Xc.IsGood Bs W.rank W₁.rank ∧
        ∀ w, ((W.rank + W₁.rank : ℕ) : ℤ) < Bs.mα w - Bs.mβ w

def SkewSpace : Prop :=
  ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (τ : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (Bs.emb w).1 x = conj (tauE D (τ w) x)) → ∀ (X : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
      (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ) (q d : ℕ) (e : Fin X.rank ≃ Fin d), IsSelfDualC X Λ →
      (∀ τ', IsCartanInv (gramAt D X τ') (s τ')) → (∀ τ', Formalism.UG.HasSignature (gramAt D X τ') (X.rank - q) q) → q ≤ X.rank →
      ∃ Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d, Z.J = skewJ X e ∧ (∀ w, Z.θ w = (reindex e e (s (τ w))).map conj) ∧
        Z.IsSkew D.sp.cm.sig Bs (d - q) q

def ConjDomain : Prop :=
  ∀ (D : D7) (M : HSp D) (J : Matrix (Fin M.rank) (Fin M.rank) D.host.E) (c : D.host.E) (h : J = c • M.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D M)) (𝓕 : Set (GA D M)), IsHaarFD M ν 𝓕 →
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h))

def ThetaBij : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.ψ = ψ →
    Bs.IsGood D.sp.cm.sig → ∀ (ε : Bool) (M X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      Y.IsHerm D.sp.cm.sig Bs r s → Z.IsSkew D.sp.cm.sig Bs r' s' →
      Y.J = (if ε then (1 : D.host.E) else -1) • M.gram → Z.J = skewJ X e →
      ∀ Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z, Mo.IsGood ψ →
      (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), IsThetaFunO ψ (sgn ε M) X (thetaOf (ε := ε) e Mo ψ Φ)) ∧
      (∀ f, IsThetaFunO ψ (sgn ε M) X f → ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), thetaOf (ε := ε) e Mo ψ Φ = f) ∧
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d), ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
        thetaOf (ε := ε) e Mo ψ Φ = thetaOf (ε := ε) e Mo ψ Φ' → Φ = Φ'

def WeilCorrespond : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.ψ = ψ →
    Bs.IsGood D.sp.cm.sig → ∀ (ε : Bool) (M X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      0 < M.rank → 0 < d → Y.IsHerm D.sp.cm.sig Bs r s → Z.IsSkew D.sp.cm.sig Bs r' s' →
      ∀ (c : D.host.E) (hc : c = if ε then (1 : D.host.E) else -1) (hY : Y.J = c • M.gram) (hZ : Z.J = skewJ X e)
        (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z), Mo.IsGood ψ →
      ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z),
        IsWeil ψ ε M X χ χ' ω → Mo.IsWeil ψ χ χ' om →
        ∀ g h, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin d),
          thetaOf (ε := ε) e Mo ψ (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c hY g, skewU X e hZ h) Φ) = ω (g, h) (thetaOf (ε := ε) e Mo ψ Φ)

end GlobalTheory.CompanionTheory.AgreeO.Read

end
end

