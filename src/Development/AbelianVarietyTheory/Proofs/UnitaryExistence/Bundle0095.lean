import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFramesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) B := by
  first | exact @GlobalTheory.HolEval.differentiableOn_evR | exact GlobalTheory.HolEval.differentiableOn_evR | (intros; apply GlobalTheory.HolEval.differentiableOn_evR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisationStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_isComplexUniformisation : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → IsUnf (unfOf e F M un) := by
  first | exact @GlobalTheory.FrameUnif.isUnf_built | exact GlobalTheory.FrameUnif.isUnf_built | (intros; apply GlobalTheory.FrameUnif.isUnf_built <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFifth
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkLocal

theorem markSpec_arch {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (g₀ : GA D V) (p : Σ k, Frame (M.X k).Ψ r)
    (hp : MarkSpec M V hr io th x₀ g₀ p) :
    ∃ γ : GA D V, ∀ k ∈ GfC V, ∀ h ∈ GinfC V, MarkSpec M V hr io th x₀ (g₀ * h)
      ⟨p.1, fun τ => (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * (g₀ * k * h))) * x₀ τ.1 :
        Matrix (Fin r) (Fin r) ℂ)⟩ := by
  obtain ⟨γ, hγ, h1, h2, -⟩ := hp
  refine ⟨γ, fun k hk h hh => ?_⟩
  have hk' : infHom V k = 1 := hk
  have hh' : finHom V h = 1 := hh
  have ef : finHom V (γ * (g₀ * h)) = finHom V (γ * g₀) := by
    simp only [map_mul, hh', mul_one]
  have ei : infHom V (γ * (g₀ * k * h)) = infHom V (γ * (g₀ * h)) := by
    simp only [map_mul, hk', mul_one]
  have eg : gLat V (γ * (g₀ * h)) = gLat V (γ * g₀) := by
    unfold gLat
    rw [ef]
  have e1 : latG V (γ * (g₀ * h)) = latG V (γ * g₀) := by
    unfold latG
    rw [eg]
  have e2 : latGHat V (γ * (g₀ * h)) = latGHat V (γ * g₀) := by
    unfold latGHat
    rw [eg]
  refine ⟨γ, hγ, ?_, ?_, fun τ => ?_⟩
  · rw [e1]
    exact h1
  · rw [e2, ef]
    exact h2
  · unfold archM
    rw [← ei]
    rfl

set_option maxHeartbeats 1000000 in

theorem dict_locally_continuous : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (M.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (M.X k).dom ∧ ∃ γ ∈ (M.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) := by
  intro hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec dict hdict g₀
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hN := GlobalTheory.LevelOpen.level_mem_nhds D (D.sp.W j) _ Kf
    (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hK g₀
  obtain ⟨γ, hγ⟩ := markSpec_arch M _ _ io th x₀ g₀ _ (hdict g₀)
  have hc := ((GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.W j)).2 _ (th (dict g₀).1) (M.X (dict g₀).1).cmType
    (hrec.2.2.2.2.1 _)).2.2.1
  refine ⟨_, hN, (dict g₀).1, fun u τ => (Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
    (finCongr (D.sp.W_rank j hj.1 hj.2)) (archM _ (th (dict g₀).1 τ) (γ * u)) * x₀ τ.1 :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ?_, ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (D.sp.W j)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (D.sp.W j).gram))
    refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact (((hc τ).comp (continuous_const.mul continuous_id)).matrix_reindex _ _).matrix_mul continuous_const
  · rintro _ ⟨k, hk, h, hh, rfl⟩
    have hkf := ((hK k).1 hk).1
    have hs := hγ k hkf h hh
    refine ⟨(GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec _ _ hs).1, ?_⟩
    have e : g₀ * k * h = 1 * (g₀ * h) * k := by
      rw [one_mul, mul_assoc, mul_assoc, (GlobalTheory.UnitarySplit.real_finite_split D _).2.1 h hh k hkf]
    exact GlobalTheory.T.frame_uniform_embedding_second hT hL D Q hQ j hj σ' g ty F hσ hty M io th x₀ hrec Kf hK (g₀ * h) 1 k _ _ (one_mem _) hk hs
      (e ▸ hdict (g₀ * k * h))

end GlobalTheory.MarkLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingFourth
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkDict

theorem unitary_of_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (J : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin n) (Fin n) ℂ)
    (h : u.transpose * (-(Matrix.reindex e e J).transpose) * u.map (starRingEnd ℂ) =
      -(Matrix.reindex e e J).transpose) :
    ((Matrix.reindex e.symm e.symm u).map (starRingEnd ℂ)).transpose * J * Matrix.reindex e.symm e.symm u = J := by
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg (fun x => Matrix.reindex e.symm e.symm x.transpose) h
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.reindex_apply, Equiv.symm_symm,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at h'
  rw [Matrix.mul_assoc]
  exact h'

theorem orth_mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : IsOrthogonalFrame X x₀) :
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) ∈ X.dom :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1
    (fun τ : X.Ψ => (x₀ τ.1 : Fin r → Fin r → ℂ)) (fun τ => h τ.1 τ.2)).1

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem markSpec_mul_inf {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} {r : ℕ}
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hx : ∀ k, IsOrthogonalFrame (M.X k) x₀)
    (h h' : GA D V) (hh' : h' ∈ GinfC V) (p : Σ k, Frame (M.X k).Ψ r) (hp : MarkSpec M V hr io th x₀ h p) :
    MarkSpec M V hr io th x₀ (h * h')
      ⟨p.1, rmul p.2 (archMat V th hr (fun c (τ : (M.X c).Ψ) => (x₀ τ.1 : Fin r → Fin r → ℂ)) h' p.1)⟩ := by
  obtain ⟨γ, hγ, h1, h2, h3⟩ := hp
  have hf : finHom V (γ * (h * h')) = finHom V (γ * h) := by
    rw [← mul_assoc, map_mul (finHom V) (γ * h), (show finHom V h' = 1 from hh'), mul_one]
  have hg : gLat V (γ * (h * h')) = gLat V (γ * h) := by unfold gLat; rw [hf]
  have hl : latG V (γ * (h * h')) = latG V (γ * h) := by unfold latG; rw [hg]
  have hl' : latGHat V (γ * (h * h')) = latGHat V (γ * h) := by unfold latGHat; rw [hg]
  refine ⟨γ, hγ, ?_, ?_, fun τ => ?_⟩
  · rw [hl]; exact h1
  · rw [hl', hf]; exact h2
  · have hd : IsUnit (x₀ τ.1).det := isUnit_iff_ne_zero.2 (orth_mem_dom (M.X p.1) x₀ (hx p.1) τ).1
    show mat p.2 τ * ((x₀ τ.1)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) h') * x₀ τ.1) = _
    rw [h3 τ, ← mul_assoc γ, archM_mul V _ (γ * h) h']
    simp only [Matrix.reindex_apply, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr hr).symm _, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]

set_option maxHeartbeats 1000000 in

theorem dictIsUnif_of_markSpec : ThetaUnifAV → Out.Laws → ∀ (D : D7) (Q : Par D), Q.Pins → ∀ (j : ℕ) (hj : InR D j) (σ' : KA Q.l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif (Q.Xo j) σ' ty), σ' (baseKA Q.l).ρ = Q.H.rt0 → IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty → ∀ (M : GlobalTheory.FrameUnif.ModelsOf F D.R.r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E)) (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), RecOK M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ → ∀ Kf : Subgroup (GA D (D.sp.W j)), IsLevelK (D.sp.W j) (D.host.g 0 * D.host.g 1) Kf → ∀ dict : GA D (D.sp.W j) → Σ k, Frame (M.X k).Ψ D.R.r, (∀ h, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h (dict h)) → (∀ h, (∃ p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p ∧ ∀ τ : (M.X p.1).Ψ, mat p.2 τ = x₀ τ.1) → ∀ τ : (M.X (dict h).1).Ψ, mat (dict h).2 τ = x₀ τ.1) → DictIsUnif (D.sp.W j) dict Kf th (D.sp.W_rank j hj.1 hj.2) := by
  intro hT hL D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK dict hd hpref
  have s1 := GlobalTheory.T.frame_uniform_embedding_second hT hL D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK
  have s2 := GlobalTheory.T.frame_uniform_embedding_third D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec Kf hK
  have sc := GlobalTheory.RecDict.component_attained_at_base_frame D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec
  have su := GlobalTheory.MarkUnit.mark_frame_unit D Q hQ j hj σ' g ty F h1 h2 M io th x₀ hrec
  obtain ⟨-, hW, -, -, hth, hx⟩ := hrec
  have s0 : ∀ h p, MarkSpec M (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) io th x₀ h p →
      ∃ γ' ∈ (M.X p.1).Γ, dict h = ⟨p.1, lact γ' p.2⟩ := fun h p hp =>
    s1 h 1 1 p (dict h) (one_mem _) (one_mem _) hp (by rw [one_mul, mul_one]; exact hd h)
  refine ⟨fun γ hγ h => ?_, fun k hk h => ?_,
    ⟨fun c (τ : (M.X c).Ψ) => (x₀ τ.1 : Fin D.R.r → Fin D.R.r → ℂ), fun c => ⟨?_, ?_⟩, fun h h' hh' => ?_⟩,
    fun h => (su h _ (hd h)).1, fun c x hxd => ?_, ?_⟩
  · exact s1 h γ 1 _ _ hγ (one_mem _) (hd h) (by rw [mul_one]; exact hd _)
  · exact s1 h 1 k _ _ (one_mem _) hk (hd h) (by rw [one_mul]; exact hd _)
  · exact orth_mem_dom _ x₀ (hx c)
  · obtain ⟨h, -, p, rfl, hp0, hp⟩ := sc c
    have e := hpref h ⟨p, hp, hp0⟩
    obtain ⟨γ', -, e'⟩ := s0 h p hp
    refine ⟨h, ?_⟩
    rw [e'] at e ⊢
    exact congrArg (Sigma.mk p.1) (funext fun τ => e τ)
  · exact s0 _ _ (markSpec_mul_inf M _ _ io th x₀ hx h h' hh' _ (hd h))
  · obtain ⟨h, -, p, rfl, hp0, hp⟩ := sc c
    obtain ⟨a1, a2⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E D.R.r (M.X p.1).p0
      (M.X p.1).Ψ (M.X p.1).Gm (M.X p.1).Gm_herm
    obtain ⟨x₁, b, hb, hx₁, rfl⟩ := a1 x hxd
    choose u hu hux using fun τ : (M.X p.1).Ψ => a2 τ.1 (x₀ τ.1) (mat (rmul x b) τ) (hx p.1 τ.1 τ.2)
      ((hx₁ τ).trans (hx p.1 τ.1 τ.2).symm)
    have hG : ∀ τ : D.host.E →+* ℂ, (M.X p.1).Gm.map τ = -(Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2))
        (finCongr (D.sp.W_rank j hj.1 hj.2)) ((D.sp.W j).gram.map τ)).transpose := by
      intro τ
      rw [(hW p.1).1]
      ext a b
      simp
    obtain ⟨h', hh', hu'⟩ := ((GlobalTheory.UnitaryGlue.adelic_glue D (D.sp.W j)).2 (M.X p.1).Ψ (th p.1) (M.X p.1).cmType
      (hth p.1)).2.2.2 (fun τ => Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2)).symm
        (finCongr (D.sp.W_rank j hj.1 hj.2)).symm (u τ))
      (fun τ => unitary_of_reindex _ _ _ (by rw [← hG]; exact hu τ))
    obtain ⟨γ', hγ', e'⟩ := s0 _ _ (markSpec_mul_inf M _ _ io th x₀ hx h h' hh' _ hp)
    refine ⟨h * h', γ', hγ', b, hb, e'.trans (congrArg (Sigma.mk p.1) (funext fun τ => ?_))⟩
    have hdet : IsUnit (x₀ τ.1).det := isUnit_iff_ne_zero.2 (orth_mem_dom (M.X p.1) x₀ (hx p.1) τ).1
    show (γ' : Matrix _ _ D.host.E).map τ.1 * (mat p.2 τ * ((x₀ τ.1)⁻¹ *
      Matrix.reindex (finCongr (D.sp.W_rank j hj.1 hj.2)) (finCongr (D.sp.W_rank j hj.1 hj.2))
        (archM (D.sp.W j) (th p.1 τ) h') * x₀ τ.1)) = ((γ' : Matrix _ _ D.host.E).map τ.1 * mat x τ) * mat b τ
    have hxb : mat x τ * mat b τ = u τ * x₀ τ.1 := hux τ
    rw [hp0 τ, hu' τ, ← Matrix.reindex_symm, Equiv.apply_symm_apply, Matrix.mul_assoc _ (mat x τ), hxb,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  · rintro h h' ⟨γ', hγ', e⟩
    exact s2 h h' (dict h) γ' hγ' (hd h) (by rw [← e]; exact hd h')

end GlobalTheory.MarkDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReadingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_value_eq_const_mul_reading : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n, toC (ψ (f p y)) = u * rdU U f k x.1 := by
  first | exact @GlobalTheory.FrameUnif.test_value_eq_const_mul_reading | exact GlobalTheory.FrameUnif.test_value_eq_const_mul_reading | (intros; apply GlobalTheory.FrameUnif.test_value_eq_const_mul_reading <;> assumption)
end

