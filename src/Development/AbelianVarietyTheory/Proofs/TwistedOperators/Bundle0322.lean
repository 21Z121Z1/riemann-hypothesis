import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem isURepOn_K (h : IsAdmRep ε ρ) : IsURepOn (Kset ε) ρ :=
  ⟨⟨h.1.1, fun a ha b hb => h.1.2 a (mem_UJset_of_mem_Kset ha) b (mem_UJset_of_mem_Kset hb)⟩, h.2.2.1,
    fun v => (h.2.1 v).mono fun _ hk => mem_UJset_of_mem_Kset hk⟩

theorem finiteDimensional_kIso (h : IsAdmRep ε ρ) (Λ : Fin n → ℝ) : FiniteDimensional ℂ (kIso ε ρ Λ) := by
  have e : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S} = {S | IsKTypeOf ε ρ Λ S} := by
    ext S; simp
  unfold kIso
  rw [← e]
  exact h.2.2.2 Λ

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

theorem finset_sup_le (s : Finset (Fin n → ℝ)) : s.sup (kIso ε ρ) ≤ kFinVec ε ρ :=
  Finset.sup_le fun Λ _ => kIso_le Λ

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

theorem ext_types (hUρ : IsURepOn (Kset ε) ρ) (hUπ : IsURepOn (Kset ε) π)
    (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) {T : H →ₗ[ℂ] V}
    (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) (s : Finset (Fin n → ℝ)) {a : H} {w : V}
    (ha : a ∈ s.sup (kIso ε ρ)) (hw : w ∈ s.sup (kIso ε π))
    (hs : ∀ Λ ∈ s, ∀ y ∈ kIso ε ρ Λ, ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) :
    ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  intro y hy
  refine Submodule.iSup_induction (kIso ε ρ) (motive := fun y => ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) (hd y hy)
    (fun Λ y hyΛ => ?_) (by simp) (fun y₁ y₂ h₁ h₂ => by simp [inner_add_right, h₁, h₂])
  by_cases hΛ : Λ ∈ s
  · exact hs Λ hΛ y hyΛ
  · rw [finset_orth hUρ s hΛ a ha y hyΛ,
      finset_orth hUπ s hΛ w hw (T y) (map_kIso_le hT Λ (Submodule.mem_map_of_mem hyΛ))]

end

theorem kFinite_riesz : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → ∀ T : H →ₗ[ℂ] V, (kFinVec ε ρ).map T = kFinVec ε π → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ a : H, IsKFin ε ρ a → (∀ y, IsKFin ε ρ y → T y = 0 → ⟪a, y⟫_ℂ = 0) → ∃ w, IsKFin ε π w ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) ∧ ∀ w : V, IsKFin ε π w → ∃ a, IsKFin ε ρ a ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hπ T hmap hT
  have hUρ := isURepOn_K hρ
  have hUπ := isURepOn_K hπ
  have hdρ : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ :=
    decomp n ε H ρ hUρ (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hρ.1 hρ.2.1 hρ.2.2.1).1
  have hdπ : ∀ v, IsKFin ε π v → v ∈ ⨆ Λ, kIso ε π Λ :=
    decomp n ε V π hUπ (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε V π hπ.1 hπ.2.1 hπ.2.2.1).1
  haveI : ∀ Λ, FiniteDimensional ℂ (kIso ε ρ Λ) := finiteDimensional_kIso hρ
  haveI : ∀ Λ, FiniteDimensional ℂ (kIso ε π Λ) := finiteDimensional_kIso hπ
  refine ⟨fun a ha hker => ?_, fun w hw => ?_⟩
  · obtain ⟨s, hs⟩ := exists_finset hdρ a ha
    set U := s.sup (kIso ε π) with hUdef
    let Y : Submodule ℂ H := U.comap T ⊓ kFinVec ε ρ
    let T' : Y →ₗ[ℂ] U := (T ∘ₗ Y.subtype).codRestrict U (fun y => y.2.1)
    have hsurj : LinearMap.range T' = ⊤ := by
      rw [eq_top_iff]
      rintro u -
      have hu : (u : V) ∈ kFinVec ε π := finset_sup_le s u.2
      rw [← hmap] at hu
      obtain ⟨y, hy, hyu⟩ := hu
      exact ⟨⟨y, ⟨show T y ∈ U from hyu ▸ u.2, hy⟩⟩, Subtype.ext hyu⟩
    obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective T' hsurj
    let φ : Y →ₗ[ℂ] ℂ := (innerₛₗ ℂ a) ∘ₗ Y.subtype
    let g : U →ₗ[ℂ] ℂ := φ ∘ₗ r
    have hg : ∀ y : Y, g (T' y) = φ y := by
      intro y
      have h1 : T' (r (T' y)) = T' y := by rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
      have h2 : T ((r (T' y) : H) - y) = 0 := by
        have := congrArg Subtype.val h1
        rw [map_sub, sub_eq_zero]
        exact this
      have h3 := hker ((r (T' y) : H) - y) ((kFinVec ε ρ).sub_mem (r (T' y)).2.2 y.2.2) h2
      simp only [g, φ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
      rw [inner_sub_right, sub_eq_zero] at h3
      exact h3
    let w : U := (InnerProductSpace.toDual ℂ U).symm (LinearMap.toContinuousLinearMap g)
    refine ⟨w, finset_sup_le s w.2, ext_types hUρ hUπ hdρ hT s hs w.2 ?_⟩
    intro Λ hΛ y hy
    have hyK : IsKFin ε ρ y := kIso_le Λ hy
    have hTy : T y ∈ U := Finset.le_sup (f := kIso ε π) hΛ (map_kIso_le hT Λ (Submodule.mem_map_of_mem hy))
    have h6 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := U) (x := ⟨T y, hTy⟩)
      (y := LinearMap.toContinuousLinearMap g)
    rw [Submodule.coe_inner] at h6
    have h4 := hg ⟨y, hTy, hyK⟩
    have h5 : T' ⟨y, hTy, hyK⟩ = ⟨T y, hTy⟩ := rfl
    rw [h5] at h4
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply] at h4
    rw [h6, LinearMap.coe_toContinuousLinearMap', h4]
  · obtain ⟨s, hs⟩ := exists_finset hdπ w hw
    set A := s.sup (kIso ε ρ) with hAdef
    let g : A →ₗ[ℂ] ℂ := (innerₛₗ ℂ w) ∘ₗ T ∘ₗ A.subtype
    let a : A := (InnerProductSpace.toDual ℂ A).symm (LinearMap.toContinuousLinearMap g)
    refine ⟨a, finset_sup_le s a.2, ext_types hUρ hUπ hdρ hT s a.2 hs ?_⟩
    intro Λ hΛ y hy
    have hyA : y ∈ A := Finset.le_sup (f := kIso ε ρ) hΛ hy
    have h6 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := A) (x := ⟨y, hyA⟩)
      (y := LinearMap.toContinuousLinearMap g)
    rw [Submodule.coe_inner] at h6
    rw [h6]
    simp [g]

end GlobalTheory.KFinDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
open GlobalTheory.Grid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

theorem absNorm_mem_idS (I : Ideal (𝓞 D.host.E)) :
    ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
  have : oToS D.host.F D.host.E ((Ideal.absNorm I : ℕ) : 𝓞 D.host.E) ∈ idS D.host.F I :=
    Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  simpa using this

theorem mk_eq_of_eq_add {A : Type} [CommRing A] {R : Subring A} (J : Ideal R) {x y w : A} (hx : x ∈ R) (hy : y ∈ R)
    (hw : w ∈ R) {n : ℕ} (hn : (n : R) ∈ J) (h : x = y + n * w) :
    Ideal.Quotient.mk J ⟨x, hx⟩ = Ideal.Quotient.mk J ⟨y, hy⟩ := by
  rw [Ideal.Quotient.eq]
  have e : (⟨x, hx⟩ - ⟨y, hy⟩ : R) = (n : R) * ⟨w, hw⟩ := by
    apply Subtype.ext
    change x - y = ((n : R) : A) * w
    rw [h]
    push_cast
    ring
  rw [e]
  exact J.mul_mem_right _ hn

open Classical in

theorem isFinVec_of_isCosetVec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ}
    (hv : GlobalTheory.Grid.IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    (hI : I ≠ ⊥) (hc : GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f) : GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  let φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ := fun y =>
    if (∀ i j, ∃ h : y i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Ideal.Quotient.mk (idS D.host.F I) ⟨y i j, h⟩ = cmpS D.host.F I (c i j)) then 1 else 0
  have hfun : cosetInd S T e I c = fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0 := by
    funext x
    unfold cosetInd
    by_cases hx : IsHalf e x
    · rw [if_pos hx]
      by_cases hx' : InCosetOf S T I c x
      · rw [if_pos ⟨hx, hx'⟩]
        exact (if_pos hx').symm
      · rw [if_neg fun h => hx' h.2]
        exact (if_neg hx').symm
    · rw [if_neg hx, if_neg fun h => hx h.1]
  have hS' := GlobalTheory.FlipPath.isSelfDualC_sgn ε hS
  refine GlobalTheory.FlipPath.isFinVec_of_own hv hS hT he (φ := φ) ⟨?_, ?_⟩
  · rw [← hfun]
    obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := sgn ε S.V) hS'.1.fg hT.1.fg S.β T.β
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := sgn ε S.V) hS'.1 hT.1 S.β T.β
    have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
    have hKN : ((K * Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (absNorm_mem_idS I)
    refine ⟨fun t ht => ?_, K * (Ideal.absNorm I * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu hh t => ?_,
      fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg fun h' => h h'.1)
    · have hH : IsHalf e (t + (K * (Ideal.absNorm I * M)) • u) ↔ IsHalf e t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have e1 : (t + (K * (Ideal.absNorm I * M)) • u) i j = t i j + ((K * (Ideal.absNorm I * M) : ℕ) : AE D) * u i j := by
          change t i j + (K * (Ideal.absNorm I * M)) • u i j = _
          rw [nsmul_eq_mul]
        rw [e1, mul_add, mul_left_comm, hh i j]
        constructor
        · intro h; exact add_right_cancel h
        · intro h; rw [h]
      have hadd : ∀ i j, frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j =
          frMapO S.V T.V S.β T.β t i j +
            ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) := by
        intro i j
        rw [GlobalTheory.PlaceDatum.frMapO_add, show K * (Ideal.absNorm I * M) = K * Ideal.absNorm I * M from (mul_assoc _ _ _).symm,
          Nat.cast_mul (K * Ideal.absNorm I) M, mul_assoc]
      have hC' : InCosetOf S T I c (t + (K * (Ideal.absNorm I * M)) • u) ↔ InCosetOf S T I c t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have hz : (M : EAf D) * frMapO S.V T.V S.β T.β u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hB u hu i j
        have hw : ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) ∈
            Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem (natCast_mem _ _) hz
        have hmem : frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
            frMapO S.V T.V S.β T.β t i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hadd]; exact add_mem_cancel_right hw
        constructor
        · rintro ⟨h1, h⟩
          exact ⟨hmem.1 h1, (mk_eq_of_eq_add _ h1 (hmem.1 h1) hz hKN (hadd i j)).symm.trans h⟩
        · rintro ⟨h2, h⟩
          exact ⟨hmem.2 h2, (mk_eq_of_eq_add _ (hmem.2 h2) h2 hz hKN (hadd i j)).trans h⟩
      unfold cosetInd
      by_cases ht : IsHalf e t ∧ InCosetOf S T I c t
      · rw [if_pos ⟨hH.2 ht.1, hC'.2 ht.2⟩, if_pos ht]
      · rw [if_neg fun h => ht ⟨hH.1 h.1, hC'.1 h.2⟩, if_neg ht]
    · have h : IsHalf e t ∧ InCosetOf S T I c t := by
        by_contra h
        exact ht (if_neg h)
      have hK' := hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf h.1) fun i j => (h.2 i j).1
      rw [mul_nsmul]
      exact nsmul_mem hK' _
  · rw [← hfun]
    exact hc

end GlobalTheory.Grid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HSAbs

theorem coeFn_finsum {X : Type} [MeasurableSpace X] {ν : Measure X} {κ : Type} (s : Finset κ)
    (f : κ → Lp ℂ 2 ν) : (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[ν] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 ν
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

theorem pointwise {X : Type} [MeasurableSpace X] {ν : Measure X}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∀ᵐ x ∂ν, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ≤ C ^ 2 := by
  classical

  let w : (s → ℂ) → H := fun c => ∑ j : s, c j • e j
  have hon : Orthonormal ℂ (fun j : s => e j) := he.comp _ Subtype.val_injective
  have hw2 : ∀ c, ‖w c‖ ^ 2 = ∑ j : s, ‖c j‖ ^ 2 := by
    intro c
    have h := hon.inner_sum c c Finset.univ
    rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (s → ℂ)
  have hD : ∀ c ∈ D, ∀ᵐ x ∂ν, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    intro c _
    have hlin : T (w c) = ∑ j : s, c j • T (e j) := by
      simp only [w, map_sum, map_smul]
    have hsm : ∀ᵐ x ∂ν, ∀ j : s, (c j • T (e j) : Lp ℂ 2 ν) x = c j * T (e j) x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (T (e j))] with x hx
      rw [hx]; rfl
    filter_upwards [hT (w c), coeFn_finsum (ν := ν) Finset.univ (fun j : s => c j • T (e j)), hsm]
      with x hx hsum hj
    rw [hlin, hsum] at hx
    simpa only [hj] using hx
  filter_upwards [(ae_ball_iff hDc).2 hD] with x hx

  have hall : ∀ c : s → ℂ, ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖ := by
    have hcl : IsClosed {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure D ⊆ {c : s → ℂ | ‖∑ j : s, c j * T (e j) x‖ ≤ C * ‖w c‖} :=
      hcl.closure_subset_iff.2 fun c hc => hx c hc
    intro c
    exact hsub (hDd.closure_eq ▸ Set.mem_univ c)

  set S := ∑ j : s, ‖T (e j) x‖ ^ 2 with hS
  have key := hall fun j => (starRingEnd ℂ) (T (e j) x)
  have hL : ‖∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x‖ = S := by
    have : ∑ j : s, (starRingEnd ℂ) (T (e j) x) * T (e j) x = ((S : ℝ) : ℂ) := by
      rw [hS]; push_cast
      exact Finset.sum_congr rfl fun j _ => RCLike.conj_mul _
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR : ‖w (fun j => (starRingEnd ℂ) (T (e j) x))‖ ^ 2 = S := by
    rw [hw2]
    exact Finset.sum_congr rfl fun j _ => by rw [RCLike.norm_conj]
  rw [hL] at key
  have hnn := norm_nonneg (w fun j => (starRingEnd ℂ) (T (e j) x))
  have hfin : S ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - ‖w fun j => (starRingEnd ℂ) (T (e j) x)‖)]
  rw [← Finset.sum_coe_sort s (fun i => ‖T (e i) x‖ ^ 2)]
  exact hfin

theorem sum_le {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ)
    (hT : ∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) (s : Finset ι) :
    ∑ i ∈ s, ‖T (e i)‖ ^ 2 ≤ C ^ 2 * ν.real univ := by
  have hn : ∀ f : Lp ℂ 2 ν, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    intro f
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hint : ∀ f : Lp ℂ 2 ν, Integrable (fun x => ‖f x‖ ^ 2) ν := by
    intro f
    have hm : MemLp f ((2 : ℕ) : ENNReal) ν := by simpa using Lp.memLp f
    exact hm.integrable_norm_pow (by norm_num)
  calc ∑ i ∈ s, ‖T (e i)‖ ^ 2 = ∫ x, ∑ i ∈ s, ‖T (e i) x‖ ^ 2 ∂ν := by
        rw [integral_finset_sum s fun i _ => hint (T (e i))]
        exact Finset.sum_congr rfl fun i _ => hn _
    _ ≤ ∫ _x, C ^ 2 ∂ν :=
        integral_mono_ae (integrable_finset_sum s fun i _ => hint (T (e i)))
          (integrable_const _) (pointwise e he T C hT s)
    _ = C ^ 2 * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

end GlobalTheory.HSAbs

open GlobalTheory.HSAbs in

theorem GlobalTheory.isHilbertSchmidt_of_ae_bounded : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  intro X _ ν _ H _ _ _ T C hT
  unfold GlobalTheory.OpTrace.IsHilbertSchmidt
  refine summable_of_sum_le (c := C ^ 2 * ν.real univ) (fun i => sq_nonneg _) fun u => ?_
  exact GlobalTheory.HSAbs.sum_le _ (GlobalTheory.OpTrace.stdBasis H).orthonormal T C hT u
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSum_longVectors_decayWeight_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  first | exact @GlobalTheory.SepPer.latSum_le | exact GlobalTheory.SepPer.latSum_le | (intros; apply GlobalTheory.SepPer.latSum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelVector_finiteDatum_isTheta_vacuum_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  first | exact @GlobalTheory.FinZeta.levVec_vacFin | exact GlobalTheory.FinZeta.levVec_vacFin | (intros; apply GlobalTheory.FinZeta.levVec_vacFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_bound_real_unipotent_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  first | exact @GlobalTheory.RealMove.lip_move_real | exact GlobalTheory.RealMove.lip_move_real | (intros; apply GlobalTheory.RealMove.lip_move_real <;> assumption)
end

