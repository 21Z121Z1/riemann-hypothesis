import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0701
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlobalHoweTensorProductTransfer
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open scoped Classical
namespace GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}
variable (M : Model σ Y W) (T : Finset (Pl F))
end GlobalTheory.HoweGlobal.Transfer
end
noncomputable section
open scoped Classical
namespace GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))
end GlobalTheory.HoweGlobal.Transfer
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobal.Transfer in
theorem GlobalTheory.HoweGlobal.howe_tensor_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) [DecidableEq {v // v ∈ T}]
      (L : ↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ] ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = G.M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobal.relInf Bs G om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ v : T, ∀ x ∈ GlobalTheory.HoweGlobal.relFin G om v.1, ∀ (x₀ : ↥(G.M.Pol Bs.ψ Bs.emb))
          (y : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ v : T, ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)) →ₗ[ℂ] _)) v g)) t) ∈ N) := by
  intro _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm N hN T _ L hL
  have hM := hm.triple.geo.hM
  have hLe : ∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem G.M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem G.M T φ v h)
  have hpA := pure_mem_algD G.M T Bs.emb hM
  have hR := rest_ext G.M T hM
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)),
        GlobalTheory.HoweGlobal.relInf Bs G om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.2.2.2 γ hγ _ (hpA f hf φ) _ (hpA _ x.2 φ) (fun z => hD _ (hR f φ) z)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        have e : pure ((f₁ : SInf F (Fin a × Fin (a + a')))) (ext G.M T φ) =
            om (k, 1) (pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ)) := (hA _ (hR _ φ)).symm
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe, e]
        exact hN.2.2.1 k hk _ (hpA _ f.2 φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro v x hx x₀ y
    let ℓ := L ∘ₗ TensorProduct.mk ℂ _ _ x₀ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y v
    have hℓ : ∀ z, ℓ z = L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v z)) := fun z => rfl
    have hsub : augAt om v.1 ≤ (N.comap ℓ).map (SB (Fin a × Fin (a + a') → Fv F v.1)).subtype := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      refine ⟨⟨φ₁, hφ₁⟩ - ⟨φ, hφ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, hℓ, hℓ, hLe, hLe]
      have e : om (g, 1) (pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ, hφ⟩))) =
          pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ₁, hφ₁⟩)) := by
        rw [acts_ext G.M T hM (x₀ : SInf F (Fin a × Fin (a + a'))) (Function.update y v ⟨φ, hφ⟩) v ⟨φ₁, hφ₁⟩ ⇑(om (g, 1))
          (by rw [Function.update_self]; exact hA), Function.update_idem]
      rw [← e]
      exact hN.2.1 v.1 g hg _ (hpA _ x₀.2 _)
    obtain ⟨x', hx', he⟩ := hsub (Submodule.mem_comap.1 hx)
    have : x' = x := Subtype.ext he
    rw [← hℓ, ← this]
    exact hx'
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.1.2.2.1 k hk _ ht
    · let S : Submodule ℂ (↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add, Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.1.2.2.2 γ hγ _ ht _ (hLA _) (hS t)
  · intro v g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w => (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g w) (φ w)) =
          Function.update φ v (g (φ v)) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext G.M T hM _ φ v (g (φ v)) _ (hA (φ v))]
    rw [e]
    exact hN.1.2.1 v.1 h hh _ ht
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_howe_tensor_product_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) [DecidableEq {v // v ∈ T}]
      (L : ↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ] ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = G.M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobal.relInf Bs G om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ v : T, ∀ x ∈ GlobalTheory.HoweGlobal.relFin G om v.1, ∀ (x₀ : ↥(G.M.Pol Bs.ψ Bs.emb))
          (y : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ v : T, ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)) →ₗ[ℂ] _)) v g)) t) ∈ N) := by
  first | exact @_root_.GlobalTheory.HoweGlobal.howe_tensor_transfer | exact _root_.GlobalTheory.HoweGlobal.howe_tensor_transfer | (intros; apply _root_.GlobalTheory.HoweGlobal.howe_tensor_transfer <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasTypeAtCuspOfCuspValueType
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspValueType
section Model
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end Model
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
end GlobalTheory.CuspValueType
theorem GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ hθ N hN F hF w τ
  have hgood : GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) :=
    ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ),
      GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hN (tauE D τ))⟩
  have key : ∀ T, Mult.IsMultMap θ N.M ∅ 1 T → ∀ v, T v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := fun T hT v =>
    GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ (N.S τ) (T v) hP.discreteSeriesUpqExists
      (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
      hP.casselmanWallach hθ hN hgood (hT.aut v)
      (GlobalTheory.CuspValueType.isTypeAt_value θ hP.harishChandraModules N.M hT v τ)
  have main : ∀ T ∈ Mult.Mult θ N.M ∅ 1, ∀ w, PiTensorProduct.lift T w ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub θ N.V τ (N.S τ) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v =>
        rw [map_smul, PiTensorProduct.lift.tprod]
        exact Submodule.smul_mem _ r (key T hT v)
      | add a b ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    | zero =>
      intro w
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      intro w
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (ha w) (hb w)
    | smul c a _ ha =>
      intro w
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ c (ha w)
  have hF' := (Mult.mem_multT θ N.M ∅ 1 F).1 hF
  have eF : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [eF]
  exact main _ hF' w
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_value_has_prescribed_type : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam (D := D) θ → ∀ (N : GlobalTheory.Grid.Node D), N.V.SigOK → ∀ F ∈ N.Cusp θ, ∀ (w : SmT N.M) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  first | exact @_root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | exact _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type | (intros; apply _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.InfinityTypeOfFiniteCharacter
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotKerRealInv
open Matrix
private theorem minor_polynomial_substitution {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g (GlobalTheory.NormSum.minorPol D T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.NormSum.minorPol D T := by
  unfold GlobalTheory.NormSum.minorPol
  have key : ∀ (τ : D.what₂.Tau) (r : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (g τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ r
    rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : ℂ →+* MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ), mul_comm,
      ← Matrix.det_mul]
    congr 1
    ext1 i i'
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.CompactHowe.substF_X, Matrix.one_apply]
    rw [Finset.sum_eq_single (r i)]
    · simp [mul_comm]
    · intro b _ hb
      simp [hb]
    · simp
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  refine (Finset.prod_congr rfl fun j _ => key τ (T τ j).1).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]
private theorem minor_form_substitution {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) g (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  exact minor_polynomial_substitution T g
private theorem conj_transpose_inv_unitary {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (h : uᴴ * u = 1) :
    (((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * u * 1)⁻¹)ᵀ.map (starRingEnd ℂ) = u := by
  rw [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_eq_left_inv h]
  ext i j
  simp [Matrix.conjTranspose_apply]
private theorem infinity_type_of_finite_character {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) :
    χ'.HasInf (Formalism.L2.Host.embTau D) (fun τ => e * χ.n τ) := by
  intro u
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ u / ((‖φ τ u‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left hA, _root_.inv_zpow, ← Finset.prod_zpow] at hB'
  rw [eq_inv_of_mul_eq_one_left hB', inv_inv]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← _root_.zpow_mul, mul_comm]
private theorem infinity_exponent_of_bottom_pair {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (s : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P')
    (τ : D.what₂.Tau) :
    HasInfExp D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2))) τ
      ((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
  have h1 := infinity_type_of_finite_character P.W.chV' P.W.ep' _ hB.chars.2
  have h2 : (nuH G s i j).HasInfQ (tauE D) fun τ => -((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
    refine ⟨fun τ => -(P.W.ep' * P.W.chV'.n τ), fun τ => ?_, fun k => ?_⟩
    · have : ((2 * (P.n τ : ℤ) : ℤ) : ℚ) = ((P.W.ep' * P.W.chV'.n τ - (P.d : ℤ) : ℤ) : ℚ) := by rw [P.wt τ]
      push_cast at this ⊢
      linarith
    · have h3 := h1 k
      rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val] at h3
      rw [← inv_inv (((nuH G s i j).inf k : ℂˣ) : ℂ), h3, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [_root_.zpow_neg]
      rfl
  have h4 := GlobalTheory.Chain.StepVac.hasInfExp_inv
    (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G s i j hL) h2 τ)
  rw [neg_neg] at h4
  have e : G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) =
      (G.nu s i (j + 1))⁻¹ := by
    rw [mul_div_mul_right_eq_div, ← inv_div]
    rfl
  rw [e]
  exact h4
private theorem weil_rep_fixes_compact_vector {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T)
    {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P') (ea : P.a = A.rank) (ed : P.d = WW.rank)
    (Tp : Tup D P.a P.d P.n) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GinfC A) :
    X.ω s (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
      (GlobalTheory.BotFormula.minorF ea ed Tp)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
        (GlobalTheory.BotFormula.minorF ea ed Tp) := by
  have h := hX.is
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hW := h.weil s
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst s) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem s)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f s) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst s)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  have hgA : ∀ τ, gramAt D A τ = 1 := fun τ => by rw [gramAt, hX.std.1]; simp
  have hgW : ∀ τ, gramAt D WW τ = 1 := fun τ => by rw [gramAt, hX.stdW.1]; simp
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [e1, e2, e3, e4]
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ _ τ hθ hW.hecS hW.resS
  choose e he using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecS hW.resS (ha τ)
  let k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k
  have hk' : k' ∈ GinfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])
  have hu : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A k))ᴴ * compAt W.θ τ (Formalism.L2.Theta.mt A k) = 1 := fun τ => by
    have e : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).conjTranspose * (gramAt D A τ) * compAt W.θ τ (Formalism.L2.Theta.mt A k) =
      gramAt D A τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ A k τ
    rwa [hgA, Matrix.mul_one] at e
  have key := GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ A WW _ _ ((X.ω s).toSgn true) hW hθ (fun _ => 1) (fun _ => 1)
    (fun τ => by rw [hgA]; simp) (fun τ => by rw [hgW]; simp) a (fun τ => (P.n τ : ℚ) + (P.d : ℚ) / 2) ha
    (infinity_exponent_of_bottom_pair hL G s i j hB) (fun τ => e τ - A.rank) (fun τ => -(P.n τ : ℤ))
    (fun τ => by push_cast; rw [he τ]; show _ + (A.rank : ℚ) / 2 - _ = _; ring)
    (fun τ => by rw [← ed]; push_cast; ring) (X.f s) hf hv k' hk' 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed Tp)
  have c1 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.JointHarm.compAt_mt_one' W.θ τ WW
  have ck : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') = compAt W.θ τ (Formalism.L2.Theta.mt A k) := fun τ => rfl
  have s1 : (fun τ => (((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) *
      (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ).map (starRingEnd ℂ)) = fun _ => 1 := by
    funext τ
    show ((1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * 1).map (starRingEnd ℂ) = 1
    rw [c1, inv_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have s2 : (fun τ => (((((fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹ *
      compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') * (fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹)ᵀ).map
        (starRingEnd ℂ)) = fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A k) :=
    funext fun τ => conj_transpose_inv_unitary (hu τ)
  rw [s1, s2, minor_form_substitution, map_smul, smul_smul, ← Finset.prod_mul_distrib] at key
  have hone : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k')).det ^ (-(P.n τ : ℤ)) *
      (compAt W.θ τ (Formalism.L2.Theta.mt WW 1)).det ^ (e τ - A.rank) *
        (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ^ P.n τ) = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero
    rw [ck, c1, Matrix.det_one, _root_.one_zpow, mul_one, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hne)]
  rw [hone, one_smul] at key
  exact key
end GlobalTheory.BotKerRealInv
end
theorem _root_.GlobalTheory.T.bottom_kernel_real_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : Formalism.L2.Theta.GA D WW) (T : Tup D P.a P.d P.n),
        ∀ k ∈ GinfC A, ∀ y, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (y * k) =
          X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X hX s Q δ t0 P P' hB ea ed g Tp k hk y
  unfold Tri.ker thetaKO
  have e : X.ω s (y * k, g) = X.ω s (y, g) * X.ω s (k, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, Module.End.mul_apply, GlobalTheory.BotKerRealInv.weil_rep_fixes_compact_vector hL hX s hB ea ed Tp hk]
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormAverageApprox
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp
namespace GlobalTheory.KFinCuspApprox
theorem isCuspForm_kFinite_average : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D)
    (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ →
    IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro D θ hθ _ N τ e he φ hφ hc
  set A : Formalism.REAL.KG (N.M.ε τ) → GA D N.V :=
    fun k => atTau θ N.V τ ((N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ) with hA
  have hAc : Continuous A := (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
    GlobalTheory.SeriesToClosure.continuous_conjK fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hl : LeftInv (GQ N.V) φ := hφ.left
  have havg : ∀ x, GlobalTheory.KFinCuspApprox.avgN θ N τ e φ x = ∫ k, e k * φ (x * A k) ∂(Formalism.REAL.muK (N.M.ε τ)) :=
    fun x => rfl
  have hlA : LeftInv (GQ N.V) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := fun γ hγ g => by
    simp only [havg, mul_assoc, hl γ hγ]
  refine (isCuspFun_iff hlA).2 fun W hW => funext fun x => ?_
  have hcc := cocompact_single hW
  have h0 := congrFun ((isCuspFun_iff hl).1 hc W hW)
  set NN := NA (IsoFlag.single hW) with hNN
  have h𝓕 := isFundamentalDomain_stdDom ((GQ N.V).subgroupOf NN) (Measure.haar : Measure NN)
  have hfin := hcc.measure_ne_top h𝓕
  show constTermOn (GQ N.V) NN _ x = 0
  rw [hcc.constTermOn_eq_zero_iff h𝓕 hlA x]
  have hz : ∀ y, ∫ n in stdDom ((GQ N.V).subgroupOf NN), φ ((n : GA D N.V) * y) ∂(Measure.haar : Measure NN) = 0 :=
    fun y => (hcc.constTermOn_eq_zero_iff h𝓕 hl y).1 (h0 y)
  obtain ⟨K0, hK0, hs⟩ := hcc
  have hcont : Continuous fun p : NN × Formalism.REAL.KG (N.M.ε τ) => φ ((p.1 : GA D N.V) * x * A p.2) :=
    hφ.cont.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hAc.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hK0.prod (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hb : ∀ (n : NN) k, ‖φ ((n : GA D N.V) * x * A k)‖ ≤ C := fun n k => by
    obtain ⟨γ, hγ, hk⟩ := hs n
    have h1 := hC (γ * n, k) ⟨hk, trivial⟩
    have h2 := hl ((γ : NN) : GA D N.V) (Subgroup.mem_subgroupOf.1 hγ) ((n : GA D N.V) * x * A k)
    simp only [Subgroup.coe_mul] at h1
    have e1 : ((γ : NN) : GA D N.V) * n * x * A k = (γ : GA D N.V) * ((n : GA D N.V) * x * A k) := by
      simp only [mul_assoc]
    rwa [e1, h2] at h1
  obtain ⟨Ce, hCe⟩ := (isCompact_univ (X := Formalism.REAL.KG (N.M.ε τ))).exists_bound_of_continuousOn he.continuousOn
  haveI : IsFiniteMeasure ((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))) :=
    isFiniteMeasure_restrict.2 hfin
  have hint : Integrable (Function.uncurry fun (n : NN) (k : Formalism.REAL.KG (N.M.ε τ)) => e k * φ ((n : GA D N.V) * x * A k))
      (((Measure.haar : Measure NN).restrict (stdDom ((GQ N.V).subgroupOf NN))).prod (Formalism.REAL.muK (N.M.ε τ))) := by
    refine Integrable.mono' (integrable_const (Ce * C)) ?_ (ae_of_all _ fun p => ?_)
    · exact ((he.comp continuous_snd).mul hcont).aestronglyMeasurable
    · show ‖e p.2 * φ ((p.1 : GA D N.V) * x * A p.2)‖ ≤ Ce * C
      rw [norm_mul]
      exact mul_le_mul (hCe p.2 trivial) (hb p.1 p.2) (norm_nonneg _) ((norm_nonneg _).trans (hCe p.2 trivial))
  calc ∫ n in stdDom ((GQ N.V).subgroupOf NN), GlobalTheory.KFinCuspApprox.avgN θ N τ e φ ((n : GA D N.V) * x)
        ∂(Measure.haar : Measure NN)
      = ∫ n in stdDom ((GQ N.V).subgroupOf NN), ∫ k, e k * φ ((n : GA D N.V) * x * A k) ∂(Formalism.REAL.muK (N.M.ε τ))
        ∂(Measure.haar : Measure NN) := by simp only [havg]
    _ = ∫ k, ∫ n in stdDom ((GQ N.V).subgroupOf NN), e k * φ ((n : GA D N.V) * x * A k)
        ∂(Measure.haar : Measure NN) ∂(Formalism.REAL.muK (N.M.ε τ)) := integral_integral_swap hint
    _ = ∫ k, e k * 0 ∂(Formalism.REAL.muK (N.M.ε τ)) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [integral_const_mul, ← hz (x * A k)]
        simp only [mul_assoc]
    _ = 0 := by simp
end GlobalTheory.KFinCuspApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cuspForm_average_approx : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ φ : GA D N.V → ℂ, IsAutFunSm θ N.V φ → IsCuspFun N.V φ → IsCuspFun N.V (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | exact _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average | (intros; apply _root_.GlobalTheory.KFinCuspApprox.isCuspForm_kFinite_average <;> assumption)
end
end

