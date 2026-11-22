import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0008
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0006
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  have e : ev0 (F := F) κ = GlobalTheory.MixUniq.ev0 κ := LinearMap.ext fun _ => rfl
  rw [e]
  exact GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible κ

theorem eval_zero_schrodinger_zero {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : κ → AF F) (Ψ : (κ → AF F) → ℂ) :
    ev0 κ (schr ψ (0, v) Ψ) = ev0 κ Ψ := by
  simp [ev0, schr]

theorem schr_zero_fst {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : κ → AF F) (Ψ : (κ → AF F) → ℂ) :
    schr ψ (0, v) Ψ = fun x => ψ (x ⬝ᵥ v) * Ψ x := by
  funext x
  simp [schr]

theorem siegelSmall_of (hF : SliceFacts) (hAC : AdaptedChar) : SiegelSmall := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std

  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar

  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]

  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]

  obtain ⟨t', ht', hdet⟩ := jPar d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSB
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_mul_conj {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) *
      cA σ ((Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E)) : (AE F E)ˣ) : AE F E) = 1 := by
  have h := congrArg Matrix.det (show ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have hu : IsUnit (incM F J).det := by
    have e : (incM F J).det = (inclR (F := F) (E := E) (AF F)) J.det := by
      rw [incM]
      exact (RingHom.map_det (inclR (F := F) (E := E) (AF F) : E →+* AE F E) J).symm
    rw [e]
    exact (Ne.isUnit hJ).map _
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  refine hu.mul_left_cancel ?_
  linear_combination h

theorem norm_det_unitary (hcm : IsCMExt F E σ) {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det (g : GL (Fin m) (AE F E))) = 1 := by
  obtain ⟨ξ, hq⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine Units.ext (hq.algebraMap_injective ?_)
  rw [Units.coe_map, Units.val_one, map_one]
  show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) _) = 1
  rw [hq.algebraMap_norm]
  exact det_mul_conj hJ g

end PositivityTheory.SiegelWeilFormula.Ald

end
end

