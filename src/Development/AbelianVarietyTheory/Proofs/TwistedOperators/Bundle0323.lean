import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoDualChars

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' := by
  simp only [isoPart, Matrix.add_mul]

theorem isoPart_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C 0 = 0 := by
  simp only [isoPart, Matrix.zero_mul]

theorem midPart_zero (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B 0 = 0 := by
  simp only [midPart, Matrix.zero_mul]

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous fun y : Mx D W.rank r => isoPart V W C y := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem symplO_smul_left' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T (c • x) y = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_left, mul_add]

theorem symplO_smul_right' (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.SplitScalar.symplOH_add_self,
    GlobalTheory.FinTranslate.symplOH_smul_right, mul_add]

theorem trace_incA' (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem exists_pair_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (c : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hc : c ≠ 0) :
    ∃ w : WO S T, ψ (symplO S T (c.map (incA D)) w) ≠ 1 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (Matrix.ext h)
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  set s : AF D.host.F := x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (s • c.map (incA D)) i j (c i j)⁻¹
  refine ⟨s • γ, ?_⟩
  have h1 : symplO S T (c.map (incA D)) (s • γ) = x₀ := by
    rw [symplO_smul_right', ← symplO_smul_left', hγ, Matrix.smul_apply, Matrix.map_apply, mul_smul_comm,
      map_smul, ← map_mul, inv_mul_cancel₀ hij, trace_incA', smul_eq_mul, ← hq, mul_assoc, ← map_mul,
      inv_mul_cancel₀ hq0, map_one, mul_one]
  rw [h1]
  exact hx₀

end GlobalTheory.IsoDualChars

namespace GlobalTheory.IsoDualChars

open GlobalTheory.LatVac in

theorem chars : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨oII, oIM, oDM, oDD⟩ := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hs C' h1 h2 h3
  have hdual : ∀ t, isoPart V W C' t = e (t, 0, 0) := fun t => by
    rw [he, isoPart_zero, midPart_zero, add_zero, add_zero]
  have hiso : ∀ y, isoPart V W C y = e (0, y, 0) := fun y => by
    rw [he, isoPart_zero, midPart_zero, add_zero, zero_add]
  have hmapr : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, a.map (incA D) ∈ ratMx D W.rank r := fun a => ⟨a, rfl⟩
  refine ⟨fun a => ?_, fun a t s => ?_, fun a b t => ?_, fun t => ?_, fun a ha => ?_⟩
  · exact hψ.1.1.comp (GlobalTheory.SplitScalar.continuous_symplO V W (continuous_isoPart V W C') continuous_const)
  · rw [isoPart_add, symplO_add_left, AddChar.map_add_eq_mul]
  · rw [Matrix.map_add _ (map_add (incA D)), isoPart_add, symplO_add_right, AddChar.map_add_eq_mul]
  · constructor
    · intro h
      have hmem : isoPart V W C' t ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun γ hγ => ?_
        obtain ⟨⟨t₀, y₀, x₀⟩, rfl⟩ := e.surjective γ
        obtain ⟨-, ⟨a₀, rfl⟩, -⟩ := (hrat t₀ _ x₀).1 hγ
        rw [he, symplO_add_right, symplO_add_right, oDD, oDM, zero_add, add_zero]
        exact h a₀
      rw [hdual] at hmem
      exact ((hrat t 0 0).1 hmem).1
    · intro ht a
      have hx : isoPart V W C' t ∈ ratL W V := by
        rw [hdual]; exact (hrat t 0 0).2 ⟨ht, zero_mem _, zero_mem _⟩
      have hy : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
        rw [hiso]; exact (hrat 0 _ 0).2 ⟨zero_mem _, hmapr a, zero_mem _⟩
      exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hx _ hy
  · set z := isoPart V W C (a.map (incA D)) with hz
    have hall : ∀ w : WO V W, ψ (symplO V W z w) = 1 := fun w => by
      obtain ⟨⟨t, y, x⟩, rfl⟩ := e.surjective w
      have hskew : symplO V W z (e (t, y, x)) = -symplO V W (e (t, y, x)) z := by
        exact GlobalTheory.SplitScalar.symplO_skew V W _ _
      rw [hskew, he, symplO_add_left, symplO_add_left, hz, oII, GlobalTheory.SplitScalar.symplO_skew V W _ (midPart V V' W B x),
        oIM, neg_zero, add_zero, add_zero, AddChar.map_neg_eq_inv, ha t, inv_one]
    have hzc : z = (a * (adj D C * V.gram)).map (incA D) := by
      simp only [hz, isoPart, Matrix.map_mul]
    by_contra ha0
    have hc : a * (adj D C * V.gram) ≠ 0 := by
      intro h0
      apply ha0
      calc a = a * (adj D C * V.gram * C') := by rw [h1, Matrix.mul_one]
        _ = a * (adj D C * V.gram) * C' := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by rw [h0, Matrix.zero_mul]
    obtain ⟨w, hw⟩ := exists_pair_ne_one ψ hψ V W _ hc
    rw [← hzc] at hw
    exact hw (hall w)

end GlobalTheory.IsoDualChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KPerp

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inner_map_map_of_norm {A : H →L[ℂ] H} (hA : ∀ v, ‖A v‖ = ‖v‖) (u v : H) :
    ⟪A u, A v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (A : H →ₗ[ℂ] H), norm_map' := hA }
  exact L.inner_map_map u v

theorem isKStableOn_orthogonal (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {T : Submodule ℂ H}
    [FiniteDimensional ℂ T] (hT : IsKStableOn ε ρ T) : IsKStableOn ε ρ Tᗮ := by
  intro k hk x hx
  rw [Submodule.mem_orthogonal]
  intro t ht
  let f : T →ₗ[ℂ] T := ((ρ k : H →ₗ[ℂ] H).restrict fun v hv => hT k hk v hv)
  have hinj : Function.Injective f := by
    intro a b hab
    have : ρ k ((a : H) - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val hab)
    have h0 : ‖((a : H) - b)‖ = 0 := by rw [← hK k hk, this, norm_zero]
    exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h0))
  obtain ⟨t', ht'⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨t, ht⟩
  have ht'' : ρ k (t' : H) = t := congrArg Subtype.val ht'
  rw [← ht'', inner_map_map_of_norm (hK k hk)]
  exact (Submodule.mem_orthogonal _ _).1 hx t' t'.2

theorem le_of_forall_irred (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) (M : Submodule ℂ H) :
    ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F = d → IsKStableOn ε ρ F →
      (∀ T : Submodule ℂ H, T ≤ F → T ≠ ⊥ → FiniteDimensional ℂ T → IsKStableOn ε ρ T →
        (∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) → T ≤ M) → F ≤ M := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hF hd hFK hM
  by_cases hF0 : F = ⊥
  · rw [hF0]; exact bot_le

  have hex : ∃ m, ∃ T : Submodule ℂ H, T ≤ F ∧ T ≠ ⊥ ∧ IsKStableOn ε ρ T ∧ Module.finrank ℂ T = m :=
    ⟨_, F, le_rfl, hF0, hFK, rfl⟩
  classical
  obtain ⟨T, hTF, hT0, hTK, hTm⟩ := Nat.find_spec hex
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTF
  have hTirr : ∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T := by
    intro S' hS' hS'K
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
    have hle : Module.finrank ℂ T ≤ Module.finrank ℂ S' := by
      rw [hTm]; exact Nat.find_min' hex ⟨S', hS'.trans hTF, h0, hS'K, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hS' hle
  have hTM : T ≤ M := hM T hTF hT0 inferInstance hTK hTirr

  set F' := Tᗮ ⊓ F with hF'
  have hF'K : IsKStableOn ε ρ F' := fun k hk v hv =>
    ⟨isKStableOn_orthogonal hK hTK k hk v hv.1, hFK k hk v hv.2⟩
  haveI : FiniteDimensional ℂ F' := Submodule.finiteDimensional_of_le inf_le_right
  have hlt : F' < F := by
    refine lt_of_le_of_ne inf_le_right fun h => hT0 ?_
    rw [eq_bot_iff]
    intro x hx
    have hxF' : x ∈ F' := h ▸ hTF hx
    have := Submodule.inner_right_of_mem_orthogonal hx hxF'.1
    rw [Submodule.mem_bot]
    exact inner_self_eq_zero.1 this
  have hF'M : F' ≤ M :=
    ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) F' inferInstance rfl hF'K
      fun T' hT' => hM T' (hT'.trans inf_le_right)
  have hsup : T ⊔ F' = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTF
  rw [← hsup]
  exact sup_le hTM hF'M

theorem starProjection_mem (W : Submodule ℂ H) [W.HasOrthogonalProjection] (x : H) : W.starProjection x ∈ W := by
  rw [Submodule.starProjection_apply]; exact (W.orthogonalProjection x).2

theorem cdom_of_not_le_orthogonal (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε ρ Λ S) (hTK : IsKStableOn ε ρ T)
    (hTirr : ∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) {v : H} (hvT : v ∈ T)
    (hv0 : v ≠ 0) (hvw : IsWtOn (Kset ε) ρ μ v) (hTS : ¬ T ≤ Sᗮ) : CDom ε μ Λ := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hSo : IsKStableOn ε ρ Sᗮ := isKStableOn_orthogonal hK hS.2.1
  have hmeet : T ⊓ Sᗮ = ⊥ :=
    (hTirr _ inf_le_left fun k hk x hx => ⟨hTK k hk x hx.1, hSo k hk x hx.2⟩).resolve_right
      fun h => hTS (inf_eq_left.1 h)
  have hPv : S.starProjection v ≠ 0 := by
    intro h
    have hv : v ∈ T ⊓ Sᗮ := ⟨hvT, (Submodule.starProjection_apply_eq_zero_iff S).1 h⟩
    rw [hmeet, Submodule.mem_bot] at hv
    exact hv0 hv
  have comm : ∀ k ∈ Kset ε, ∀ x, S.starProjection (ρ k x) = ρ k (S.starProjection x) := by
    intro k hk x
    have hx : ρ k x = ρ k (S.starProjection x) + ρ k (x - S.starProjection x) := by
      rw [← map_add, add_sub_cancel]
    rw [hx, map_add, Submodule.starProjection_eq_self_iff.2 (hS.2.1 k hk _ (starProjection_mem S x)),
      (Submodule.starProjection_apply_eq_zero_iff S).2 (hSo k hk _ (Submodule.sub_starProjection_mem_orthogonal x)),
      add_zero]
  refine hS.2.2.2.2 μ _ (starProjection_mem S v) hPv ?_
  intro θ hθ
  rw [← comm _ hθ, hvw θ hθ, map_smul]

theorem inner_eq_zero_of_ne (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {Λ Λ' : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε ρ Λ S) (hT : IsKTypeOf ε ρ Λ' T) (hne : Λ ≠ Λ') :
    ∀ s ∈ S, ∀ t ∈ T, ⟪s, t⟫_ℂ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs, t, ht, hst⟩ := hcon
  have hTS : ¬ T ≤ Sᗮ := fun h => hst (Submodule.inner_right_of_mem_orthogonal hs (h ht))
  have hST : ¬ S ≤ Tᗮ := fun h => hst (Submodule.inner_left_of_mem_orthogonal ht (h hs))
  obtain ⟨w, hwT, hw0, hww⟩ := hT.2.2.2.1
  obtain ⟨u, huS, hu0, huw⟩ := hS.2.2.2.1
  have h1 : CDom ε Λ' Λ := cdom_of_not_le_orthogonal hK hS hT.2.1 hT.2.2.1 hwT hw0 hww hTS
  have h2 : CDom ε Λ Λ' := cdom_of_not_le_orthogonal hK hT hS.2.1 hS.2.2.1 huS hu0 huw hST
  exact hne (GlobalTheory.LowHW.cdom_antisymm h2 h1)

end GlobalTheory.KPerp

open GlobalTheory.KPerp in

theorem GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ Z : Submodule ℂ H, Z ≤ kFinVec ε ρ →
        IsKStableOn ε ρ Z → Z ≠ kFinVec ε ρ → ∃ a : H, a ≠ 0 ∧ IsKFin ε ρ a ∧ ∀ z ∈ Z, ⟪a, z⟫_ℂ = 0 := by
  intro n ε H _ _ _ ρ hρ Z hZ hZK hne
  obtain ⟨hC, hcont, hK, hadm⟩ := hρ
  have hirr := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hC hcont hK).1
  obtain ⟨y, hy, hyZ⟩ := SetLike.not_le_iff_exists.1 fun h : kFinVec ε ρ ≤ Z => hne (le_antisymm hZ h)
  obtain ⟨F, hF, hyF, hFK⟩ := hy
  have hex : ∃ T : Submodule ℂ H, T ≤ F ∧ T ≠ ⊥ ∧ FiniteDimensional ℂ T ∧ IsKStableOn ε ρ T ∧
      (∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) ∧ ¬ T ≤ Z := by
    by_contra hcon
    push_neg at hcon
    exact hyZ (le_of_forall_irred hK Z _ F hF rfl hFK (fun T a b c d e => hcon T a b c d e) hyF)
  obtain ⟨S, -, hS0, hSfd, hSK, hSirr, hSZ⟩ := hex
  obtain ⟨Λ, hΛ⟩ := hirr S hSfd hS0 hSK hSirr
  set U : Submodule ℂ H := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S} with hUdef
  haveI hUfd : FiniteDimensional ℂ U := hadm Λ
  have hSU : S ≤ U := le_sSup ⟨le_top, hΛ⟩
  have hUK : IsKStableOn ε ρ U := by
    intro k hk v hv
    have : U ≤ U.comap (ρ k : H →ₗ[ℂ] H) :=
      sSup_le fun S' hS' x hx => show ρ k x ∈ U from le_sSup hS' (hS'.2.2.1 k hk x hx)
    exact this hv
  obtain ⟨x, hxS, hxZ⟩ := SetLike.not_le_iff_exists.1 hSZ
  set W : Submodule ℂ H := Z ⊓ U with hWdef
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have haW : x - W.starProjection x ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have haU : x - W.starProjection x ∈ U := U.sub_mem (hSU hxS) (starProjection_mem W x).2
  refine ⟨x - W.starProjection x, ?_, ⟨U, hUfd, haU, hUK⟩, ?_⟩
  · intro h
    have hx : x = W.starProjection x := sub_eq_zero.1 h
    exact hxZ (hx ▸ (starProjection_mem W x).1)
  · intro z hz
    obtain ⟨F', hF', hzF', hF'K⟩ := hZ hz
    have hGK : IsKStableOn ε ρ (F' ⊓ Z) := fun k hk v hv => ⟨hF'K k hk v hv.1, hZK k hk v hv.2⟩
    haveI : FiniteDimensional ℂ ↥(F' ⊓ Z) := Submodule.finiteDimensional_of_le inf_le_left
    have hle : F' ⊓ Z ≤ (ℂ ∙ (x - W.starProjection x))ᗮ := by
      refine le_of_forall_irred hK _ _ _ inferInstance rfl hGK ?_
      intro T hTG hT0 hTfd hTK hTirr t ht
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨Λ', hΛ'⟩ := hirr T hTfd hT0 hTK hTirr
      by_cases hL : Λ' = Λ
      · subst hL
        have hTU : T ≤ U := le_sSup ⟨le_top, hΛ'⟩
        have htW : t ∈ W := ⟨(hTG ht).2, hTU ht⟩
        exact Submodule.inner_left_of_mem_orthogonal htW haW
      · have hUT : U ≤ Tᗮ := sSup_le fun S' hS' s hs =>
          (Submodule.mem_orthogonal T s).2 fun t' ht' => inner_eq_zero_of_ne hK hΛ' hS'.2 hL t' ht' s hs
        exact Submodule.inner_left_of_mem_orthogonal ht (hUT haU)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle ⟨hzF', hz⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapVac

variable {D : D7}

theorem lnk_simil {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') :
    l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L.gram := by
  rw [Int.cast_one, one_mul]
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  exact mul_right_cancel₀ b c

theorem lnk_tau_ne {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') : l.τ ≠ 0 := by
  intro h0
  have e := l.map
  rw [h0, Matrix.zero_mulVec] at e
  have hz : ζ = 0 := neg_eq_zero.mp e.symm
  have n : D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L.gram *ᵥ ζ') = 0 := by
    rw [← l.norm, hz]; simp
  rcases mul_eq_zero.1 n with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (star_eq_zero.1 h3)
  · exact h.2 h1

theorem kap_surj {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) :
    Function.Surjective (l.κ S) := by
  obtain ⟨σ, _, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  intro x
  refine ⟨(rat σ : Mx D L.rank L.rank) ⬝ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S x, ?_⟩
  rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

theorem kap_add {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : l.κ S (v + w) = l.κ S v + l.κ S w :=
  (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).1 v w

theorem kap_sympl {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : symplOH L S (l.κ S v) (l.κ S w) = -symplOH S L v w := by
  have e := (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).2.2.2.2.1 v w
  unfold symplOH
  rw [e, Int.cast_one, one_mul, mul_neg]

theorem kap_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E}
    (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) (Ξ : WO L S → ℂ) (w' : WO S L)
    (hw : heisO ψ S L w' (fun w => star (Ξ (l.κ S w))) = fun w => star (Ξ (l.κ S w))) :
    heisO ψ L S (l.κ S w') Ξ = Ξ := by
  funext x
  obtain ⟨v, rfl⟩ := kap_surj h l S x
  have e := congrFun hw v
  simp only [heisO] at e
  have e2 := congrArg (starRingEnd ℂ) e
  rw [map_mul, GlobalTheory.AdjLawPf.conj_psi ψ hψ] at e2
  simp only [starRingEnd_apply, star_star] at e2
  simp only [heisO]
  rw [kap_sympl h l, ← kap_add h l]
  exact e2

theorem half_mul_left {m n k : ℕ} {e : AE D} (M : Mx D m n) {x : Mx D n k} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem half_mul_right {m n k : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hx]

theorem half_smul {m n : ℕ} {e : AE D} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx]

theorem half_adj {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) := by
  intro i j
  show cA D e * cA D (x j i) = cA D (x j i)
  rw [← map_mul, hx]

theorem split_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hv,
    by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]⟩

theorem kap_half {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    {e : AE D} {w : WO S L} (hh : IsHalf e (l.κ S w)) : IsHalf (cA D e) w := by
  obtain ⟨σ, hστ, _⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  have h1 : IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S (l.κ S w)) :=
    half_smul _ (half_mul_left _ (half_mul_right (half_adj hh) _))
  rw [Lnk.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj] at h1
  have h2 := half_mul_left (rat σ : Mx D L.rank L.rank) h1
  rwa [← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul] at h2

theorem kappa_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  intro D ψ hψ L S ζ ζ' h l Λ Ξ hv w hw
  refine ⟨?_, fun e he hh => ?_⟩
  · have e2 : (2 • l.κ S w : WO L S) = l.κ S (2 • w) := by rw [two_nsmul, two_nsmul, kap_add h l]
    rw [e2]
    exact kap_heis ψ hψ h l S Ξ _ (hv.1 w hw)
  · exact kap_heis ψ hψ h l S Ξ w (hv.2 (cA D e) (split_conj he) w hw (kap_half h l S hh))

end GlobalTheory.KapVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorFin

theorem isLocOp_of_mem_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (p : Place D)
    {x : WO S T → ℂ} (hx : x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt p w) f₀)) :
    IsThetaFunO ψ S T x ∧ IsLocOp ψ S T μ 𝓕 f₀ p x := by
  have hh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have ip := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨hh _ _ h₀, fun φ => φ w, fun _ _ => rfl, fun f hf => ⟨_, hh (wAt p w) f hf, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  | zero =>
    have hz : ∀ g, ipO μ 𝓕 (0 : WO S T → ℂ) g = 0 := fun g => by simp [ipO]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun _ => 0, fun _ _ => by simp,
      fun f _ => ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun g _ => hz g⟩, fun g _ => hz g⟩
  | add y z _ _ hy hz =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    obtain ⟨tz, M, M1, M2, M3⟩ := hz
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add ty tz, fun φ => L φ + M φ, fun c φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1, M1, mul_add]
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      obtain ⟨b, tb, hb⟩ := M2 f hf
      refine ⟨a + b, GlobalTheory.WeilVacMove.isTheta_add ta tb, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.2.1 b tb).1, ha g hg, hb g hg]
    · rw [((ip y g ty hg).2.2.2.1 z tz).1, L3 g hg, M3 g hg]
  | smul c y _ hy =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul c ty, fun φ => c * L φ, fun d φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1]
      ring
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      refine ⟨c • a, GlobalTheory.WeilVacMove.isTheta_smul c ta, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.1 c).1, ha g hg]
    · rw [((ip y g ty hg).2.2.1 c).1, L3 g hg]

theorem isLocOp_of_isLocal_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x :=
  fun D ψ θ S T sS sT ΛS ΛT f₀ _ _ hb hμ v x hx =>
    (isLocOp_of_mem_span (base_std hb) hμ (base_theta hb) (.inl v)
      (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)).2

end GlobalTheory.PlaceTensorFin
end

