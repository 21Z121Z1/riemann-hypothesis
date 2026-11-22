import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0502
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import GroundTheory.AutomorphicForms.ReductionHeight
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
section
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def smL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Sm E a →ₗ[ℂ] AutomorphicForm.archSmooth E a where
  toFun φ := ⟨φ.1, sm_mem_archSmooth E a φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smL_injective : Function.Injective (smL E a) := fun _ _ h =>
  Subtype.ext (congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1) h)

def liB (X : (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  lie E a (mMap E a (X : ArchMatrix E a))

def lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) : Module.End ℂ (Sm E a) :=
  ∑ i, liB (b i) * liB (b i)

def omegaOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ) :
    Module.End ℂ (Sm E a) :=
  ∑ i, (ε i : ℂ) • (liB (b i) * liB (b i))

theorem smL_liB (X : (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (liB X ψ) = uAction (UniversalEnvelopingAlgebra.ι ℝ X) (smL E a ψ) := by
  apply Subtype.ext
  funext g
  rw [uAction_ι_apply]
  change lieD (mMap E a (X : ArchMatrix E a)) ψ.1 g = _
  have h1 := (isExpLieAlgebra E a).hasDerivAt_rightDeriv (sm_mem_archSmooth E a ψ g)
    ((isExpLieAlgebra E a).ofLie X) 1
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  have hc : HasDerivAt (fun t : ℝ => toL (toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))).val) (mMap E a (X : ArchMatrix E a)) 0 := by
    have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (X : ArchMatrix E a)))
        (NormedSpace.exp ((0 : ℝ) • (X : ArchMatrix E a)) * (X : ArchMatrix E a)) 0 :=
      hasDerivAt_exp_smul_const (X : ArchMatrix E a) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    have h4 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact toL_toGL E a _
  have h0 : toGL E a ((isExpLieAlgebra E a).expG ((0 : ℝ) • (isExpLieAlgebra E a).ofLie X)) = 1 := by
    simp [toGL]
  have h2 := hasDerivAt_curve ψ g (fun t => toGL E a ((isExpLieAlgebra E a).expG
      (t • (isExpLieAlgebra E a).ofLie X))) (mMap E a (X : ArchMatrix E a)) h0 hc
  refine h2.unique (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  simp only [archSlice_apply, one_mul, infEmb_eq]

theorem smL_lapOp {d : ℕ} (b : Fin d → (isExpLieAlgebra E a).lieSubalgebra) (ψ : Sm E a) :
    smL E a (lapOp b ψ) = ∑ i, uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
      (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) (smL E a ψ)) := by
  simp only [lapOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply, smL_liB]

theorem smL_omegaOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (ψ : Sm E a) : smL E a (omegaOp b ε ψ) = uAction (casimir b ε) (smL E a ψ) := by
  simp only [omegaOp, casimir, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    Module.End.mul_apply, smL_liB, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext g
  simp [Complex.real_smul]

theorem omegaOp_comm_liB {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (X : (isExpLieAlgebra E a).lieSubalgebra) :
    omegaOp b ε * liB X = liB X * omegaOp b ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hz : casimir b ε ∈ (isExpLieAlgebra E a).centerU :=
    casimir_mem_center hε2 horth archTraceForm_symm archTraceForm_lie
  have hc := Subalgebra.mem_center_iff.1 hz (UniversalEnvelopingAlgebra.ι ℝ X)
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, smL_liB, smL_liB, smL_omegaOp,
    ← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationInduced
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.MemO

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_cont {a b : ℕ} (e : a = b) : Continuous (castM k e) ∧ Continuous (castM k e).symm := by
  subst e
  exact ⟨continuous_id, continuous_id⟩

theorem exists_compact_cell (i t : ℕ) (C : Set (Mir k ((i + 1) + t + 1))) (hC : IsCompact C) (hCl : ∀ c ∈ C, c ∉ Cl k i t) :
    ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ C, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k), ∃ m ∈ N,
      c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m := by
  refine hC.induction_on (p := fun S => ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ S, ∃ h ∈ HPG k (i + 1) (t + 1),
    ∃ (d : Fin (t + 1) → k), ∃ m ∈ N, c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, by simp⟩
  · rintro s t' hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun c hc => h c (hst hc)⟩
  · rintro s t' ⟨N, hN, h⟩ ⟨N', hN', h'⟩
    refine ⟨N ∪ N', hN.union hN', ?_⟩
    rintro c (hc | hc)
    · obtain ⟨a, ha, d, m, hm, e⟩ := h c hc
      exact ⟨a, ha, d, m, Or.inl hm, e⟩
    · obtain ⟨a, ha, d, m, hm, e⟩ := h' c hc
      exact ⟨a, ha, d, m, Or.inr hm, e⟩
  · intro x hx
    obtain ⟨V, hV, μ, hμ, hs⟩ := GlobalTheory.T.exists_continuous_local_section_of_not_mem_Cl k i t x (hCl x hx)
    obtain ⟨V', hV', hcl, hsub⟩ := exists_mem_nhds_isClosed_subset hV
    refine ⟨C ∩ V', Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV'), μ '' (C ∩ V'), ?_, ?_⟩
    · exact (hC.inter_right hcl).image_of_continuousOn (hμ.mono (fun y hy => hsub hy.2))
    · intro c hc
      obtain ⟨a, ha, d, e⟩ := hs c (hsub hc.2)
      exact ⟨a, ha, d, μ c, ⟨c, hc, rfl⟩, e⟩
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_fin (n : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin n → k) (borel _) _ (muD k n) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem smInt_lin {n : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') {F : (Fin n → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (T ∘ F) = T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI := muD_fin (k := k) n
  exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear _ T l c

theorem smInt_zero' {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun _ => (0 : W)) = 0 := by
  unfold GlobalTheory.CompanionTheory.Rodier.smInt
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have : (fun _ : Fin n → k => (0 : W)) ⁻¹' {v} = ∅ := by
      ext x
      simp [Ne.symm hv]
    rw [this]
    simp

variable {i t : ℕ}

theorem eO_equiv (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (h : HPG k i (t + 1)) (m : Mir k (i + (t + 1))) :
    eO ψ f ((h : Mir k (i + (t + 1))) * m) = sigO τ σ ψ h (eO ψ f m) := by
  obtain ⟨hη, hproj⟩ := GlobalTheory.T.weyl_conj_parabolic_proj k i t h
  set a' := (pgProj k i (t + 1) h).1 with ha'
  set w' := (pgProj k i (t + 1) h).2 with hw'
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) with hy
  set η := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ with hηd
  have e1 : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) ((h : Mir k (i + (t + 1))) * m)) = η * y := by
    rw [map_mul, map_mul, hηd, hy]
    group
  let Tm : (phiN ψ τ).V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a', w')
  let sc : ℂ := ((dpowM i (1 / 2) a' : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w' : ℂˣ) : ℂ)
  let G : (Fin (t + 1) → k) → (phiN ψ τ).V ⊗[ℂ] σ.V := fun d => qO τ σ ψ (evX f (dEmb k i t d * y))
  have hpt : ∀ d, qO τ σ ψ (evX f (dEmb k i t d * (η * y))) = (sc • Tm) (G ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
    intro d
    obtain ⟨c, u, hc, hu, he⟩ := GlobalTheory.T.unipotent_factorization_character_trivial k ψ i t h d
    have e2 : dEmb k i t d * (η * y) =
        ((⟨η, hη⟩ : HPG k (i + 1) (t + 1)) : Mir k ((i + 1) + (t + 1))) * ((c : Mir k ((i + 1) + (t + 1))) *
          (dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) * y)) := by
      have he' : dEmb k i t d * η = η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := he
      calc dEmb k i t d * (η * y) = (dEmb k i t d * η) * y := (mul_assoc _ _ _).symm
        _ = (η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) * y := by rw [he']
        _ = _ := by rw [mul_assoc, mul_assoc]
    have e3 : ∀ (hh : HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + (t + 1))),
        evX f ((hh : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ hh (evX f x) := fun hh x =>
      (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 hh x
    rw [e2, e3, e3]
    have e4 : ∀ (hh : HPG k (i + 1) (t + 1)) (v), sigX τ σ hh v =
        extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) hh) v := fun _ _ => rfl
    rw [e4, hproj, GlobalTheory.T.twisted_coinvariant_levi_action, e4, hc, GlobalTheory.T.coinvariant_unipotent_character_trivial k i t ψ τ σ u hu]
    rfl
  have hl := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y
  have hl2 := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f (η * y)
  have hG : IsLocallyConstant G := hl.1.comp (qO τ σ ψ)
  have hGc : HasCompactSupport G := hl.2.comp_left (map_zero (qO τ σ ψ))
  have key : qO τ σ ψ (intO f (η * y)) =
      ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) • (sc • Tm) (qO τ σ ψ (intO f y)) := by
    have s1 : qO τ σ ψ (intO f (η * y)) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
        (fun d => ((sc • Tm) ∘ G) ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl2.1 hl2.2]
      congr 1
      funext d
      exact hpt d
    have s2 : qO τ σ ψ (intO f y) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) G := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl.1 hl.2]
      rfl
    rw [s1, GlobalTheory.T.integral_mulVec_change_modulus k (t + 1) _ w' ((sc • Tm) ∘ G) (hG.comp _) (hGc.comp_left (map_zero _)),
      smInt_lin (sc • Tm) hG hGc, s2]
  have e5 : sigO τ σ ψ h = Tm := rfl
  unfold eO
  rw [e1, ← hy, key, e5, map_smul, map_mul]
  have h6 : ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) * sc = 1 := GlobalTheory.T.modulus_characters_product_one k i t h
  rw [LinearMap.smul_apply, smul_smul, smul_smul, Units.val_mul]
  congr 1
  linear_combination ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) * h6

theorem eO_supp (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k (i + (t + 1))), IsCompact C ∧
      ∀ g, eO ψ f g ≠ 0 → ∃ h ∈ HPG k i (t + 1), ∃ c ∈ C, g = h * c := by
  have ee : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨C, hC, hCl, hsupp⟩ := GlobalTheory.T.support_compact_mod_parabolic_off_closed k i t τ σ f hf
  obtain ⟨N, hN, hcell⟩ := exists_compact_cell i t C hC hCl
  refine ⟨(castM k ee).symm '' N, hN.image (castM_cont ee).2, fun g hg => ?_⟩
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) with hy
  have hne : intO f y ≠ 0 := fun h0 => hg (by
    unfold eO
    rw [show wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) g) = y from rfl, h0, map_zero, smul_zero])
  obtain ⟨d, hd⟩ : ∃ d, evX f (dEmb k i t d * y) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold intO
    rw [show (fun d => evX f (dEmb k i t d * y)) = fun _ => 0 from funext hcon]
    exact smInt_zero'
  obtain ⟨h1, hh1, c, hc, e1⟩ := hsupp _ hd
  obtain ⟨h2, hh2, d2, m2, hm2, e2⟩ := hcell c hc
  have e3 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g * m2⁻¹) =
      (h1 * h2) * dEmb k i t d2 * wEl k i t := by
    have e4 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) =
        h1 * (h2 * dEmb k i t d2 * wEl k i t * sEmb k ((i + 1) + t) m2) := by
      rw [← e2, ← e1, hy, mul_assoc]
    rw [map_mul, map_inv, ← mul_assoc, e4]
    group
  obtain ⟨h', hh', e5⟩ := GlobalTheory.T.open_cell_double_coset_uniqueness k i t _ d d2 (h1 * h2) (mul_mem hh1 hh2) e3
  refine ⟨h', hh', (castM k ee).symm m2, ⟨m2, hm2, rfl⟩, ?_⟩
  apply (castM k ee).injective
  rw [map_mul, MulEquiv.apply_symm_apply, e5]
  group

theorem memOAlt (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  let F : indSpace (HPG k i (t + 1)) (sigO τ σ ψ) := ⟨eO ψ f, fun h g => eO_equiv ψ τ σ f h g⟩
  have hF : F ∈ smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ)) := by
    show IsOpen {g | ind (HPG k i (t + 1)) (sigO τ σ ψ) g F = F}
    convert GlobalTheory.T.isOpen_right_invariance_orbit_coefficient k i t ψ τ σ f using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h m
      exact congrFun (congrArg Subtype.val h) m
    · intro h
      exact Subtype.ext (funext h)
  obtain ⟨C, hC, hs⟩ := eO_supp ψ τ σ f hf
  exact ⟨⟨⟨F, hF⟩, C, hC, hs⟩, rfl⟩
end

theorem eO_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ f hf
  exact memOAlt i t ψ τ σ f hf

end GlobalTheory.CompanionTheory.BZPhiPG.MemO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpaceStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_minors_determine_column_space : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Cramer.main | exact GlobalTheory.CompanionTheory.GodementH.Cramer.main | (intros; apply GlobalTheory.CompanionTheory.GodementH.Cramer.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductOfProductsAssociative
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ProdFlattenDep

open GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in

theorem of_iso {d c M : ℕ} (len : Fin d → ℕ) (y : ∀ i, Fin (len i) → IrrGL k) (N : Fin d → ℕ)
    (hN : ∀ i, ∑ j, (y i j).1 = N i) (hM : ∑ i, N i = M) (z : Fin c → IrrGL k) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

end GlobalTheory.CompanionTheory.ProdFlattenDep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_transpose_inverse_dual_reverse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x (Fin.rev a))).1 = N, Nonempty (Representation.Equiv ((prodIrr x hd).comp (thetaW k N)) (prodIrr (fun a => dualCl (x (Fin.rev a))) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | exact GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphismStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | exact GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_integral_coefficients_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl F) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | exact GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | (intros; apply GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

variable (F) in

def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLeStatement
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_index_ne_zero_of_open_le : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H), IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧ ∀ (T C : Subgroup H) (x : H), (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 → (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | exact GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNorm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ResCardAbsNorm

theorem resCard_completion_eq_absNorm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (resCard (w.adicCompletion E) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ w
  exact_mod_cast GlobalTheory.LFun.SatBoundGL.resCard_completion w

end GlobalTheory.CompanionTheory.ResCardAbsNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGLMulVecAndNabsDet
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
end

