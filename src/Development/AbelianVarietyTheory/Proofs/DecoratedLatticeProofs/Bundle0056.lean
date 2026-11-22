import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0054
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumModStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterArgument_congr_rootEntrySum_mod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagChi.chiArg_sub_rootSum | exact GlobalTheory.FlagChi.chiArg_sub_rootSum | (intros; apply GlobalTheory.FlagChi.chiArg_sub_rootSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShiftStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_residueFields_eq_prod_genericShift : ∀ (E : Type) [Field E] [NumberField E] (S : Type) [CommRing S] (Pg : Finset (Pl E)) (p p' : ∀ PP : Pl E, S →+* kP PP) (χ : S → ℂ) (ψ0 : ∀ PP : Pl E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ0 → (∀ s t, χ (s + t) = χ s * χ t) → (∀ s, (∀ PP ∈ Pg, p PP s = 0 ∧ p' PP s = 0) → χ s = 1) → (∀ u u' : ∀ PP : Pl E, kP PP, ∃ s, ∀ PP ∈ Pg, p PP s = u PP ∧ p' PP s = u' PP) → (∀ PP ∈ Pg, (∃ s, (∀ PP' ∈ Pg, (PP' ≠ PP → p PP' s = 0) ∧ p' PP' s = 0) ∧ χ s ≠ 1) ∧ ∃ s, (∀ PP' ∈ Pg, p PP' s = 0 ∧ (PP' ≠ PP → p' PP' s = 0)) ∧ χ s ≠ 1) → ∃ a₁ a₂ : ∀ PP : Pl E, kP PP, (∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0) ∧ ∀ s, χ s = ∏ PP ∈ Pg, ψ0 PP (a₁ PP * p PP s + a₂ PP * p' PP s) := by
  first | exact @GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | exact GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | (intros; apply GlobalTheory.LeviBlockCharacter.char_eq_prod_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualFormInvMemSubfield
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

theorem dualForm_ringHom_inv {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : A⁻¹.map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ (map_zero f) (map_one f)]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [show (A.map f).det = f A.det by rw [RingHom.map_det, RingHom.mapMatrix_apply]]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0
      exact hu (by rw [h0, map_zero])
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext i j
    simp

theorem dualForm_inv_mem_subfield {K : Type} [Field K] (K0 : Subfield K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0) (i j : Fin n) : H⁻¹ i j ∈ K0 := by
  set H0 : Matrix (Fin n) (Fin n) K0 := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hmap : H0.map K0.subtype = H := by ext a b; rfl
  rw [← hmap, ← dualForm_ringHom_inv]
  exact (H0⁻¹ i j).2

theorem isRatHerm_dualFrame (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K)
    (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    IsRatHerm K0 H X → IsRatHerm K0 (H⁻¹)ᵀ (Formalism.HN.dualFrame X) := by
  rintro ⟨hK0, hX⟩
  refine ⟨fun i j => dualForm_inv_mem_subfield K0 H hK0 j i, fun v => ?_⟩
  obtain ⟨hu, hm⟩ := hX v
  have huT : IsUnit ((X v)ᵀ).det := by rwa [Matrix.det_transpose]
  have hD : Formalism.HN.dualFrame X v = ((X v)ᵀ)⁻¹ := rfl
  rw [hD]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact huT.ringInverse
  · rw [Matrix.nonsing_inv_nonsing_inv _ huT, Matrix.transpose_map,
      dualForm_ringHom_inv, ← hm, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.transpose_mul]
    have hcu : IsUnit (X v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
    rw [Matrix.nonsing_inv_nonsing_inv _ hcu]
    congr 1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFullLatticeOfFg
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SpanLattice

open Formalism.L2.GlobalTheoryTheory.HLatOps

theorem exists_fullLattice_of_fg :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
      (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
      ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG →
      ∃ (j : ℕ) (e : Fin j → Fin n → K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ)
        (L : Submodule (𝓞 K) (Fin j → K)), LinearIndependent K e ∧ (∀ v, IsUnit (Y v).det) ∧
        Submodule.IsLattice K L ∧ (∀ x : Fin j → K, x ∈ L ↔ ∑ i, x i • e i ∈ N) ∧
        (∀ v, gram Y v (fun i => (Pi.single i 1 : Fin j → K)) = gram X v e) ∧
        lcv Y L = lcv X N := by
  intro K _ _ _ n X hX N hN
  set U : Submodule K (Fin n → K) := Submodule.span K (N : Set (Fin n → K)) with hU
  let c := Module.finBasis K U
  let e : Fin (finrank K U) → Fin n → K := fun i => (c i : Fin n → K)
  let ψ : (Fin (finrank K U) → K) →ₗ[K] (Fin n → K) := U.subtype ∘ₗ c.equivFun.symm.toLinearMap
  have hψ : ∀ x, ψ x = ∑ i, x i • e i := by
    intro x
    simp [ψ, e, Basis.equivFun_symm_apply]
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype U).comp c.equivFun.symm.injective
  have hrange : ∀ y ∈ U, ∃ x, ψ x = y := fun y hy =>
    ⟨c.equivFun ⟨y, hy⟩, by simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply]⟩
  have hmemU : ∀ x, ψ x ∈ U := fun x => (c.equivFun.symm x).2
  have hsingle : ∀ i, ψ (Pi.single i 1) = e i := by
    intro i
    rw [hψ, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  let L : Submodule (𝓞 K) (Fin (finrank K U) → K) := N.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L.map (ψ.restrictScalars (𝓞 K)) = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hrange y (Submodule.subset_span hy)
      exact ⟨x, hy, rfl⟩
  have hfg : L.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hinj (by rw [hmap]; exact hN)
  have hS := isSesq_comp (isSesq_maj (Pi.basisFun K (Fin n)) X) ψ
  have hP := posAt_comp (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin (finrank K U)))
    (isSesq_maj (Pi.basisFun K (Fin n)) X) (posAt_maj (Pi.basisFun K (Fin n)) X hX) ψ hinj
  obtain ⟨h1, h2, h3⟩ := of_form_spec K _ _ (Pi.basisFun K (Fin (finrank K U))) L _ hS hP
  let Y : InfinitePlace K → Matrix (Fin (finrank K U)) (Fin (finrank K U)) ℂ := fun v =>
    frameOf (gramOf (Pi.basisFun K (Fin (finrank K U)))
      (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)))
  have hY : ∀ v, IsUnit (Y v).det := h1
  have hm : ∀ v x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (finrank K U))) Y v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y) := h2
  have hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (finrank K U))) Y v x := fun v x => by
    rw [normAt_eq_sqrt (Pi.basisFun K (Fin n)) X v (ψ x)]
    exact (h3 v x).symm
  refine ⟨finrank K U, e, Y, L, ?_, hY, ⟨hfg, ?_⟩, fun x => ?_, fun v => ?_, ?_⟩
  · exact c.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · rw [eq_top_iff]
    intro x _
    have hsp : Submodule.span K (N : Set (Fin n → K)) =
        (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [Submodule.map_span, ← hmap]
      rfl
    have hx : ψ x ∈ (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [← hsp]
      exact hmemU x
    obtain ⟨y, hy, hxy⟩ := hx
    exact hinj hxy ▸ hy
  · rw [← hψ]
    rfl
  · ext a b
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, hm, hsingle]
  · have h := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin (finrank K U))) Y
      (Pi.basisFun K (Fin n)) X ψ hY hX hinj hn L hfg).1
    rw [hmap] at h
    unfold lcv
    rw [h]

end GlobalTheory.SpanLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem exists_isConjAt_of_embedding (K : Type) [Field K] [NumberField K] [StarRing K]
    (h : ∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) :
    ∃ v0 : InfinitePlace K, IsConjAt v0 := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨InfinitePlace.mk σ, fun a => ?_⟩
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]; exact hσ a
  · rw [e]
    simp only [ComplexEmbedding.conjugate_coe_eq]
    rw [hσ a]

theorem isConjAt_exists_main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    (∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) →
      ∃ v0 : InfinitePlace K, IsConjAt v0 :=
  fun K _ _ _ h => exists_isConjAt_of_embedding K h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagBasisLiftGramSignedPermutationStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFrame_gram_congr_flagGram : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ZMod' I g (1 - ew - sigA I ew) ∧ (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  first | exact @GlobalTheory.FlagBasis.GramLift.gramIn_lift | exact GlobalTheory.FlagBasis.GramLift.gramIn_lift | (intros; apply GlobalTheory.FlagBasis.GramLift.gramIn_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagRootSumDualEqSymmetricEdgeSumStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  first | exact @GlobalTheory.RootSumDual.rootSum_dual_edges | exact GlobalTheory.RootSumDual.rootSum_dual_edges | (intros; apply GlobalTheory.RootSumDual.rootSum_dual_edges <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagVecMemAndSpanStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagVec_mem_Lf_and_inMod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧ ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  first | exact @GlobalTheory.FlagBasis.flagVec_mem_and_span | exact GlobalTheory.FlagBasis.flagVec_mem_and_span | (intros; apply GlobalTheory.FlagBasis.flagVec_mem_and_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplier
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem heightTwo_unitTwist : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K,
    CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → σ (σ w) = w → ‖σ w - w‖ = 1 →
    (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) →
    ∃ ε : K, ‖ε‖ = 1 ∧ CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  intro K _ _ _ _ l σ hU hR f e hI w hw hσw hw1 hht
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_hondaType_evenFrobeniusPowers K l σ hU f e hI w hw hσw hw1
  have hc0 : ‖c 0‖ = 1 := GlobalTheory.T.height_two_hondaType_first_coeff_norm_eq_one K l σ hU f e hI c hc1 hc hht
  have hq : 2 ≤ l ^ 2 := by
    have h2 : 2 ≤ l := hU.1.two_le
    nlinarith
  have hτ : ∀ x, ‖(σ ^ 2) x‖ = ‖x‖ := by
    intro x
    rw [pow_two, RingHom.mul_def, RingHom.comp_apply, hU.2.2.2.2.1, hU.2.2.2.2.1]
  obtain ⟨c', hc'1, hc'⟩ := GlobalTheory.T.hondaType_reduction_to_one_term K l (l ^ 2) (σ ^ 2) hq hU.2.2.1 hτ f hI.1.1 c hc1 hc0 hc
  obtain ⟨ε, hε1, hε⟩ := GlobalTheory.T.exists_unit_solution_twisted_frobenius_square K l σ hU hR c' hc'1
  exact ⟨ε, hε1, GlobalTheory.T.honda_functional_equation_one_term_type K l σ hU f e hI.1 c' ε hε1 hε hc'⟩

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefreeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree : ∀ (I : AutInst) (g : ℕ), g ≠ 0 → (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) → ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  first | exact @GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | exact GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | (intros; apply GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvMulVecStarMemDual
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualInt

theorem star_mem_one_O {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : star a ∈ (1 : Submodule (𝓞 K) K) := by
  rw [Submodule.mem_one] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
    have := (r.isIntegral_coe).map (starRingAut (R := K) : K ≃+* K).toRingHom.toIntAlgHom
    simpa using this
  exact ⟨⟨_, hi⟩, rfl⟩

theorem hform_eq_dot {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (a b : Fin n → K) :
    hform H a b = star a ⬝ᵥ H *ᵥ b := by
  simp [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_comm]

theorem inv_mulVec_star_mem_dual {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : IsUnit H.det) (M : Submodule (𝓞 K) (Fin n → K))
    (y : Fin n → K) (hy : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) :
    H⁻¹ *ᵥ star y ∈ Formalism.HermitianLatticesTheory.dual (hform H) M := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro x hx
  change hform H x (H⁻¹ *ᵥ star y) ∈ (1 : Submodule (𝓞 K) K)
  rw [hform_eq_dot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  have e : star x ⬝ᵥ star y = star (y ⬝ᵥ x) := by
    simp [dotProduct, mul_comm]
  rw [e]
  exact star_mem_one_O (hy x hx)

theorem dual_form_integral :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det → ∀ M : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → ∀ y y' : Fin n → K,
      (∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      (∀ x ∈ M, y' ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      hform (H⁻¹)ᵀ y y' ∈ (1 : Submodule (𝓞 K) K) := by
  intro K _ _ _ n H _ hH M hM y y' hy hy'
  have hz := hM (inv_mulVec_star_mem_dual H hH M y hy)
  have e : hform (H⁻¹)ᵀ y y' = y' ⬝ᵥ (H⁻¹ *ᵥ star y) := by
    rw [hform_eq_dot, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rw [e]
  exact hy' _ hz

end GlobalTheory.DualInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevelStatement
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : Type) [Field k] (r : O →+* k), Function.Surjective r → ∀ (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ m : GL (Fin n) K, (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹ ∧ ψ (edgeVal ρ κ a (bc r x')) = ψ (edgeVal ρ κ a (bc r x))) → (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m⁻¹ * bc O.subtype x * m) → IsScal O m := by
  first | exact @GlobalTheory.ScalInt.isScal_of_normalises | exact GlobalTheory.ScalInt.isScal_of_normalises | (intros; apply GlobalTheory.ScalInt.isScal_of_normalises <;> assumption)
end

