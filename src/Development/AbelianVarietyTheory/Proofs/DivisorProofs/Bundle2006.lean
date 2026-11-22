import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem hasOp_one (ψ : AddChar (AF F) ℂ) : HasOp (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl⟩

theorem hasOp_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOp ψ G) (hG' : HasOp ψ G') :
    HasOp ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul]
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul]
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]

theorem hasOp_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOp ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOp ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOp_one ψ) (fun _ _ _ _ hx hy => hasOp_mul hx hy) hG

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl F) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl F) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange

open GlobalTheory.SympChange in
theorem GlobalTheory.SympChange.change_of_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOp B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact GlobalTheory.T.weil_operator_for_levi_matrix F B.ψ hB.std hunr hnt _ A hA
    · exact GlobalTheory.T.weil_operator_for_unipotent_matrix F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weil_operator_for_weyl_element F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure⟩ :=
    hasOp_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    rw [locCo_eq M.co co G hGe v γ, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co hco x
  obtain ⟨y₁, z₁, h₁⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₁)
  obtain ⟨y₂, z₂, h₂⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₂)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e : (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
      (Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).1
          (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).1,
        Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).2
          (-(co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).2)) := rfl
  rw [e, h₁, h₂]
  ext (i | i) <;> simp

theorem actO_epsD_lagr : ∀ (D : D7) (S T : HSp D) (w : WO S T),
    actO (dblSp S) T (epsD S)⁻¹ 1 (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) = GlobalTheory.DiagSiegel.diagMat w := by
  intro D S T w
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w = (Matrix.fromCols w (-w)).submatrix id finSumFinEquiv.symm := by
    ext i j
    rcases h : finSumFinEquiv.symm j with k | k <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, h]
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_inv, h1, Matrix.one_mul, mt_epsD, hl, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [GlobalTheory.DiagSiegel.diagMat]

theorem epsD_mem_GQ : ∀ (D : D7) (S : HSp D), epsD S ∈ GQ (dblSp S) := by
  intro D S
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2
    ⟨blkGL finSumFinEquiv ((1, -1) : GL (Fin S.rank) D.host.E × GL (Fin S.rank) D.host.E), ?_, ?_⟩)
  · rw [show (dblSp S).gram = blkMat finSumFinEquiv S.gram (-S.gram) from gram_hdbl S, blkGL_mem_UJ]
    exact ⟨one_mem _, neg_one_mem_UJ _ _⟩
  · rw [bc_blkGL]
    apply Units.ext
    show blkMat finSumFinEquiv _ _ = blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1)
    simp [Formalism.UG.bc]

theorem rat_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T : HSp D) (χV χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D T →* Module.End ℂ (WO V T → ℂ)), IsWeilDatumO ψ V T χV χT ω →
    ∀ γ ∈ GQ V, ∀ f, IsThetaFunO ψ V T f → ∀ x, ω (γ, 1) f x = f (actO V T γ⁻¹ 1 x) := by
  intro D ψ V T χV χT ω hW γ hγ f hf x
  have hx : actO V T γ 1 (actO V T γ⁻¹ 1 x) = x := by
    simp only [actO, Formalism.L2.Theta.mt, map_one, Units.val_one, Matrix.one_mul, inv_inv, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, Matrix.mul_one]
  have e1 : ∀ (g : WO V T → ℂ) (y : WO V T), heisO ψ V T y g 0 = g y := by
    intro g y
    have h0 : symplOH V T 0 y = 0 := by simp [symplOH, symplO, hO]
    simp only [heisO, zero_add, h0, AddChar.map_zero_eq_one, one_mul]
  calc ω (γ, 1) f x = heisO ψ V T x (ω (γ, 1) f) 0 := (e1 _ _).symm
    _ = heisO ψ V T (actO V T γ 1 (actO V T γ⁻¹ 1 x)) (ω (γ, 1) f) 0 := by rw [hx]
    _ = ω (γ, 1) (heisO ψ V T (actO V T γ⁻¹ 1 x) f) 0 := by rw [← hW.om_heis γ 1 _ f hf]
    _ = heisO ψ V T (actO V T γ⁻¹ 1 x) f 0 :=
      hW.om_aut γ hγ 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf _)
    _ = f (actO V T γ⁻¹ 1 x) := e1 _ _

theorem exists_transpose_inv : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram

theorem siegel_conj : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := GlobalTheory.T.exists_siegelParabolic_conj_invTranspose

theorem chi_conj : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → ∀ z : (AE D)ˣ,
    χ (conjUnit D.sp.cm.sig z) = (χ z)⁻¹ := by
  intro D χ n h z
  have := congrArg (fun m : (AE D)ˣ →* Circle => m z) (comp_conjUnit_eq_inv h)
  simpa using this

theorem absA_conj : ∀ (D : D7) (z : (AE D)ˣ), absA D (conjUnit D.sp.cm.sig z) = absA D z :=
  fun _ z => absE_conjUnit _ z

theorem absA_eq_modu : ∀ (D : D7) (z : (AE D)ˣ),
    absA D z = (GlobalTheory.WeilM.adeleClass D.host.F).modu (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) z) :=
  fun D z => (GlobalTheory.ModuAdele.modu_norm_eq_absE D.host.F D.host.E z).symm

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem scalar_rule (D : D7) (S T : HSp D) (χT : (AE D)ˣ →* Circle) (hrT : ResEta D χT T.rank)
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    ((χT⁻¹ (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t)) : Circle) : ℂ) *
        npow (absA D (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t))) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero S T + (S.rank : ℂ) / 2) =
      GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT
        (Fintype.card (Fin T.rank)) t := by
  rw [MonoidHom.inv_apply, chi_conj D χT T.rank hrT, inv_inv, absA_conj, absA_eq_modu]
  unfold GlobalTheory.DiagSiegel.ruleFac GlobalTheory.Doubling.npow GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  rw [Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule
set_option maxHeartbeats 1000000 in

theorem thetaDiagInt_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
            ResEta D χS S.rank → ResEta D χT T.rank →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
            (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
            GlobalTheory.DblSchr.omdOf omd₀ p Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ) ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ
                         (GlobalTheory.DblSchr.omdOf omd₀ p Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT (Fintype.card (Fin T.rank)) t *
                GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco ν 𝓕 hν χS χT hχS hχT hrS hrT ωd hW omd₀ hTr p t hpt Φ hΦ
  have hBd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hB
  obtain ⟨g', hg'⟩ := exists_transpose_inv D (GlobalTheory.Doubling.dblSp S) (GlobalTheory.DblSchr.JBd S JB) ξ hBd
    (GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) =
      (1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)).1.1 := by
    simp [Formalism.L2.Theta.mt]
  have key := hTr 1 _ g' 1 h1 hg' Φ hΦ
  refine ⟨key.1, ?_⟩
  rw [show GlobalTheory.DblSchr.omdOf omd₀ p = omd₀ (1, GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm
    (GlobalTheory.DblSchr.incM_JBd S JB) p) from rfl, key.2]
  have hf : Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ (GlobalTheory.Doubling.dblSp S) T JA (GlobalTheory.DblSchr.JBd S JB) ξ hA hBd (κ ⊕ κ) (GlobalTheory.DblSchr.ddr co)
      (ddr_rat D S T JA JB ξ κ co hco) Φ hΦ
  have hdiag : ∀ F, Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T F →
      GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 F = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 F (epsD S) := by
    intro F hF
    show ∫ w in 𝓕, F (GlobalTheory.DiagSiegel.diagMat w) ∂ν =
      ∫ w in 𝓕, ωd (epsD S, 1) F (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) ∂ν
    congr 1
    funext w
    rw [rat_act D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd hW (epsD S) (epsD_mem_GQ D S) F hF, actO_epsD_lagr]
  obtain ⟨h, hεg, haP⟩ := siegel_conj D S JB p t hpt g' hg'
  have hlaw := GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ S T χT ωd hW ν 𝓕 hν _ hf h (epsD S)
  have e1 : GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (ωd (g', 1) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) (epsD S * g') := by
    rw [hdiag _ (hW.om_pres _ _ hf)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, hεg, hlaw, ← hdiag _ hf, haP]
  exact congrArg (· * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ))
    (scalar_rule D S T χT hrT t)
end GlobalTheory.DiagThetaRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberReferenceTuple
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem om_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem exists_bottom_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : condE G.pl ≠ ⊥ := condE_ne_bot _
  have hcop := GlobalTheory.FunObj.StdDatum.condE_isCoprime_conj G.pl
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → W.chV'.f u = 1 := by
    rw [hW2]; exact GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong hL G i j χν hν
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (condE G.pl) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (condE G.pl) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (condE G.pl) 0 R) = stdSum W (condE G.pl) 0 R := by
    intro k hk
    unfold stdSum
    rw [om_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (condE G.pl) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W (condE G.pl) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (condE G.pl) (botBig D i j + botSmall D i j) ≤
      blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
  let n : D.what₂.Tau → ℕ := fun τ => ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2).toNat
  have hwt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    intro τ
    rw [hW4, hW2, one_mul]
    obtain ⟨r, hr⟩ := χν.par τ
    have h1 := hn τ
    have h2 : ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2) = r := by omega
    simp only [n, h2]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hpres : Pres D ⊤ δ (levQ G.pl) e0 (stdSum W (condE G.pl) 0 R) := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact GlobalTheory.T.standardTheta_datum_presentation_level_norm D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ levQ G.pl ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl) :=
    { crv := hc
      pt0 := ht
      a := botBig D i j
      d := botBig D i j + botSmall D i j
      a_le := had
      d_even := hd
      e0 := e0
      vac := vac
      W := W
      n := n
      wt := hwt
      F := stdSum W (condE G.pl) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)
      J_le := blockLev_le _ _ _
      idx_ne := hidx_ne
      idx_le := hidx_le
      eig := heig }
  refine ⟨P, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩, fun h => GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ h⟩
  · show W.chV.f x ^ W.ep = _
    rw [hW1, hW3, zpow_one, hβ]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW2, hW4, zpow_one, hν]

end GlobalTheory.FunObj.StdDatum

end
end

