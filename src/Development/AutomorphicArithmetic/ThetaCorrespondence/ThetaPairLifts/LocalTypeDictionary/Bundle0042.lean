import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0014
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0015
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLineDerivative
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
end GlobalTheory.ThetaLineDeriv
namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ m f f₁ r hR hD u
  have hS := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil γ hγ
  have key : ∀ i, ∃ (v : ℝ → ℂ) (w : ℂ), (∀ t : ℝ, HasSum (fun ξ : Fin a × Fin (a + a') → F =>
      G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)))
        (fun j => algebraMap F (AF F) (ξ j))) (v t)) ∧
      HasSum (fun ξ : Fin a × Fin (a + a') → F => G.M.co.rho B.ψ u (tens (evI F) (⇑(f₁ i)) (r i))
        (fun j => algebraMap F (AF F) (ξ j))) w ∧ HasDerivAt v w 0 := by
    intro i
    by_cases h0 : f i = 0
    · have ht0 : tens (evI F) (⇑(f i)) (r i) = 0 := by funext x; simp [tens, h0]
      have ht1 : tens (evI F) (⇑(f₁ i)) (r i) = 0 := by
        funext x
        have h := hD i (r i) (hR i) x
        simp only [ht0, map_zero, Pi.zero_apply] at h
        exact h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      refine ⟨fun _ => 0, 0, fun t => ?_, ?_, hasDerivAt_const _ _⟩
      · rw [ht0, map_zero, rho_zero]; exact hasSum_zero
      · rw [ht1, rho_zero]; exact hasSum_zero
    · obtain ⟨c, c', hc0, hl, hact⟩ := hS (f i)
      obtain ⟨T, hT'⟩ := GlobalTheory.ThetaSchrCont.exists_clm_hasSum G.M B.ψ hT.base.std u (f i) (r i) (hR i) h0
      have htens : tens (evI F) (⇑(f₁ i)) (r i) = tens (evI F) (⇑c') (r i) := by
        funext x
        have h1 := hD i (r i) (hR i) x
        have h2 : HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x)
            (tens (evI F) (⇑c') (r i) x) 0 := by
          have e : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑(f i)) (r i)) x) =
              fun t => c t (fun j => evI F (x j)) * r i x := by
            funext t; rw [hact t (r i) (hR i)]; rfl
          rw [e]
          exact (hasDerivAt_eval c (f i) c' hc0 hl _).mul_const _
        exact h1.unique h2
      refine ⟨fun t => T (c t), T c', fun t => ?_, ?_, hasDerivAt_clm c (f i) c' hc0 hl T⟩
      · rw [hact t (r i) (hR i)]; exact hT' (c t)
      · rw [htens]; exact hT' c'
  choose v w hv hw hd using key
  have e1 : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i)))) = ∑ i, v i t := by
    intro t
    rw [map_sum, rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hv i t) using 1
    funext ξ
    simp [Finset.sum_apply]
  have e2 : GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i))) = ∑ i, w i := by
    rw [rho_sum]
    refine HasSum.tsum_eq ?_
    convert hasSum_sum (s := Finset.univ) (fun i _ => hw i) using 1
    funext ξ
    simp [Finset.sum_apply]
  rw [show (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t))
      (∑ i, tens (evI F) (⇑(f i)) (r i))))) = fun t => ∑ i, v i t from funext e1, e2]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
  have e3 : (fun t : ℝ => ∑ i, v i t) = ∑ i, v i := by funext t; simp [Finset.sum_apply]
  rw [e3]
  exact hs
end GlobalTheory.ThetaLineDeriv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | exact _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.ThetaLineDeriv.lift_splits_locally <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationPlaceDecomposition
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
theorem GlobalTheory.PlaceDecomp.weil_decomposition_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  intro D θ hθ hp N U W _ _ _ ρ hρ τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  obtain ⟨e, he, he1⟩ := GlobalTheory.T.exists_K_finite_reproducing_function _ (N.M.ε τ) (W τ) (ρ τ) (hρ τ)
  have hcl := _root_.GlobalTheory.T.twist_placeDecomposition_hasCtp D θ hθ hp N U W ρ τ (fun f f' hf hf' => _root_.GlobalTheory.T.kFinite_isotypic_decomposition_additive D θ hθ hp N U f f' hf hf')
    (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).1 (GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem D θ hθ N U).2
  obtain ⟨m, a, c, haK, hQ, hA⟩ := GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ (N.M.ε τ) (N.M.H τ) (N.M.σ τ) hσ (HasCtp θ N U (TyOf θ N ρ) τ)
    (_root_.GlobalTheory.T.placewise_decomposition_translation_invariant D θ hθ hp N U W ρ τ) hcl.1 hcl.2.1 (_root_.GlobalTheory.T.placewise_decomposition_of_K_average D θ hθ hp N U W ρ τ) hcl.2.2 e he
  choose A hAop hAmv using fun j (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) => hA j u u.2
  have hexp := fun (f : GA D N.V → ℂ) (hf : f ∈ Cls θ N U) => _root_.GlobalTheory.T.twist_exists_exponential_model D θ hθ hp N τ f hf.1.1 (hf.1.2.2 τ)
  refine ⟨m, fun j => ⟨a j, haK j⟩, A, hAop, fun j f hf => ?_, fun f hf hTy => ?_⟩
  · choose S v ℓ C hW hc h using hexp f hf
    exact (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f) fun u => hAmv j u f hf).2
  · choose S v ℓ C hW hc h using hexp f hf
    have hform := fun j => (_root_.GlobalTheory.T.twist_gkMap_rankOne_values D θ hθ hp N τ f S v ℓ C hW hc h (c j) (fun u => A j u f)
      fun u => hAmv j u f hf).1
    funext x
    have h1 := (moves_avg hθ (N.M.fr_unit τ) (N.M.fr_gram τ) hσ he f x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1
      (one_mem_UJ _)
    simp only [res_one hθ (N.M.fr_unit τ), sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (haK j))).hasSum)
    have h3 : avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f x = f x := by
      have := he1 _ (hTy x)
      have h4 : f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK (1 : KG (N.M.ε τ)) * N.M.fr τ)) = f x :=
        res_one hθ (N.M.fr_unit τ) f x
      exact this.trans h4
    rw [Finset.sum_apply]
    simp only [hform]
    rw [← h2, h3]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_place_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f) τ := by
  first | exact @_root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | exact _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place | (intros; apply _root_.GlobalTheory.PlaceDecomp.weil_decomposition_at_place <;> assumption)
end
end

