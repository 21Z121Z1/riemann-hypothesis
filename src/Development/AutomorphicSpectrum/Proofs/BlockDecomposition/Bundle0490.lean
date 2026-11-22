import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import GroundTheory.GlobalFields.TateThesis.GlobalZetaInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHom
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinear
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Lin

open GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_add {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) {φ₁ φ₂ : (Fin n → k) → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    @smInt _ _ (borel _) _ _ (muD k n) (φ₁ + φ₂) =
      @smInt _ _ (borel _) _ _ (muD k n) φ₁ + @smInt _ _ (borel _) _ _ (muD k n) φ₂ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  exact smInt_add (muD k n) l₁ c₁ l₂ c₂

theorem muD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) (c : ℂ) {φ : (Fin n → k) → W}
    (l : IsLocallyConstant φ) (h : HasCompactSupport φ) :
    @smInt _ _ (borel _) _ _ (muD k n) (c • φ) = c • @smInt _ _ (borel _) _ _ (muD k n) φ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  have e : (⇑(c • LinearMap.id : W →ₗ[ℂ] W) ∘ φ) = c • φ := rfl
  rw [← e, smInt_linear (muD k n) (c • LinearMap.id : W →ₗ[ℂ] W) l h]
  rfl

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def tw (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V :=
  fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)

theorem tw_add (ψ : AddChar k Circle) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (f + g) y = tw ψ f y + tw ψ g y :=
  funext fun _ => smul_add _ _ _

theorem tw_smul (ψ : AddChar k Circle) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (c • f) y = c • tw ψ f y :=
  funext fun d => by
    show (_ : ℂ) • (c • evX f _) = c • ((_ : ℂ) • evX f _)
    exact smul_comm _ _ _

theorem tw_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (tw ψ f y) := by
  have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
    (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
  have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
      (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
    h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
  exact IsLocallyConstant.comp₂ h2 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (fun a b => a • b)

theorem tw_cs (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    HasCompactSupport (tw ψ f y) := by
  refine (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2.mono fun d hd h0 => hd ?_
  have h0' : evX f (dEmb k i t d * y) = 0 := h0
  show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
  rw [h0', smul_zero]

theorem intO_add (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (f + g) y = intO f y + intO g y :=
  muD_add (t + 1) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).2

theorem intO_smul (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (c • f) y = c • intO f y :=
  muD_smul (t + 1) c (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2

theorem intC_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (f + g) y = intC ψ f y + intC ψ g y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_add ψ f g y)).trans
    (muD_add (t + 1) (tw_lc ψ hψ f y) (tw_cs ψ f y) (tw_lc ψ hψ g y) (tw_cs ψ g y))

theorem intC_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (c • f) y = c • intC ψ f y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_smul ψ c f y)).trans
    (muD_smul (t + 1) c (tw_lc ψ hψ f y) (tw_cs ψ f y))

theorem scaled_add {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u : ℂ)
    {a b c : A} (h : a = b + c) : u • T a = u • T b + u • T c := by
  rw [h, map_add, smul_add]

theorem scaled_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u c : ℂ)
    {a b : A} (h : a = c • b) : u • T a = c • u • T b := by
  rw [h, map_smul, smul_comm]

theorem eC_eO_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
    eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f g c
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · exact scaled_add (qC τ σ) _ (intC_add ψ hψ f g _)
  · exact scaled_smul (qC τ σ) _ c (intC_smul ψ hψ c f _)
  · exact scaled_add (qO τ σ ψ) _ (intO_add f g _)
  · exact scaled_smul (qO τ σ ψ) _ c (intO_smul c f _)

end GlobalTheory.CompanionTheory.BZPhiPG.Lin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbedding
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_gal_extending_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  intro l _ K μ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ_[l]) (E := Om l) (K := Om l)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (L := K.1) μ
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing
open IsDedekindDomain Matrix Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  have hA : ∀ i k, ‖A i k‖ ≤ ‖toL A‖ := fun i k =>
    (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  have hB : ∀ i k, ‖B i k‖ ≤ ‖toL B‖ := fun i k =>
    (norm_le_pi_norm (toL B i) k).trans (norm_le_pi_norm (toL B) i)
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖toL B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq (by simp)
  exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (norm_nonneg _))

theorem height_mul_le' (y z : GL (Fin a) (Cinf E)) :
    CuspRep.height (y * z) ≤ (1 + 2 * a) * (CuspRep.height y * CuspRep.height z) := by
  have h1 := norm_toL_mul_le (y.val) (z.val)
  have h2 := norm_toL_mul_le ((z⁻¹).val) ((y⁻¹).val)
  have e1 : (y * z).val = y.val * z.val := rfl
  have e2 : ((y * z)⁻¹).val = (z⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have hy := one_le_height y
  have hz := one_le_height z
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL z.val)
  have n3 := norm_nonneg (toL (y⁻¹).val)
  have n4 := norm_nonneg (toL (z⁻¹).val)
  have m1 : ‖toL y.val‖ * ‖toL z.val‖ ≤ CuspRep.height y * CuspRep.height z :=
    mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n2 (by linarith)
  have m2 : ‖toL (z⁻¹).val‖ * ‖toL (y⁻¹).val‖ ≤ CuspRep.height y * CuspRep.height z := by
    rw [mul_comm]
    exact mul_le_mul (by unfold CuspRep.height; linarith) (by unfold CuspRep.height; linarith) n4 (by linarith)
  have m3 : 1 ≤ CuspRep.height y * CuspRep.height z := one_le_mul_of_one_le_of_one_le hy hz
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have : CuspRep.height (y * z) = 1 + ‖toL (y * z).val‖ + ‖toL ((y * z)⁻¹).val‖ := rfl
  rw [this, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left m1 ha, mul_le_mul_of_nonneg_left m2 ha]

theorem continuous_height : Continuous (CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => (y.val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => ((y⁻¹).val : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_coe_inv
  have n1 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL y.val‖ := (continuous_norm (E := Lie E a)).comp h1
  have n2 : Continuous fun y : GL (Fin a) (Cinf E) => ‖toL (y⁻¹).val‖ := (continuous_norm (E := Lie E a)).comp h2
  unfold CuspRep.height
  exact (continuous_const.add n1).add n2

abbrev gInf (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

abbrev gFin (g : GA E a) : GL (Fin a) (Af E) := GeneralLinearGroup.map (pFin E) g

theorem continuous_gInf : Continuous (gInf : GA E a → GL (Fin a) (Cinf E)) :=
  GASplit.continuous_glMap a (pInf E) (GASplit.continuous_pInf E)

theorem continuous_gFin : Continuous (gFin : GA E a → GL (Fin a) (Af E)) :=
  GASplit.continuous_glMap a (pFin E) (GASplit.continuous_pFin E)

theorem exists_height_bound {S : Set (GA E a)} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ S, CuspRep.height (gInf g) ≤ B := by
  obtain ⟨B, hB⟩ := (hS.image (continuous_height.comp continuous_gInf)).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_growth_uniform {φ : Sm E a} (hφ : IsAutForm φ) {T : Set (GL (Fin a) (Af E))} (hT : IsCompact T) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t ∈ T, ∀ y, ‖φ.1 (finGL E a t * infGL E a y)‖ ≤ C * CuspRep.height y ^ N := by
  choose Cf Nf hf using fun x : GL (Fin a) (Af E) => hφ.growth (finGL E a x)
  have hU : ∀ x ∈ T, {t | x⁻¹ * t ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 x := fun x _ =>
    (hφ.level.preimage (continuous_const.mul continuous_id :
      Continuous fun t : GL (Fin a) (Af E) => x⁻¹ * t)).mem_nhds (by
        change finRep E a (x⁻¹ * x) φ = φ
        rw [inv_mul_cancel, map_one]; rfl)
  obtain ⟨s, -, hs⟩ := hT.elim_nhds_subcover _ hU
  refine ⟨∑ x ∈ s, |Cf x|, s.sup Nf, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t ht y => ?_⟩
  obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.1 (hs ht)
  have hk : finRep E a (x⁻¹ * t) φ = φ := hxt
  have e : φ.1 (finGL E a t * infGL E a y) = φ.1 (finGL E a x * infGL E a y) := by
    have h1 : finGL E a t = finGL E a x * finGL E a (x⁻¹ * t) := by
      rw [← map_mul, mul_inv_cancel_left]
    have h2 := congrFun (congrArg Subtype.val hk) (finGL E a x * infGL E a y)
    refine Eq.trans ?_ h2
    change _ = φ.1 (finGL E a x * infGL E a y * finGL E a (x⁻¹ * t))
    rw [h1, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hf x y).trans ?_
  refine (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_
  refine mul_le_mul (Finset.single_le_sum (f := fun x => |Cf x|) (fun _ _ => abs_nonneg _) hx)
    (pow_le_pow_right₀ hy (Finset.le_sup hx)) (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w) (x.1 w)

abbrev dg (a : ℕ) (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : GA E a :=
  diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i))

theorem gFin_dg (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) : gFin (dg (E := E) a ρ hρ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact FiniteAdeleRing.ext _ fun v => posIdele_finite (K := E) (ρ i) (hρ i) v
  · exact map_zero _

theorem height_gInf_dg_le (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) : CuspRep.height (gInf (dg (E := E) a ρ hρ)) ≤ 3 * L := by
  have hL0 : 0 ≤ L := by linarith
  have key : ∀ i w, ‖pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w‖ = ρ i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (K := E) (ρ i) (hρ i) w
  have key' : ∀ i w, ‖pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w‖ = (ρ i)⁻¹ := fun i w => by
    have h1 : pInf E ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E]) w *
        pInf E (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E]) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.mul_inv, map_one, Pi.one_apply]
    have h2 := congrArg norm h1
    rw [norm_mul, key, norm_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have b1 : ‖toL (gInf (dg (E := E) a ρ hρ)).val‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key]; exact (hL i).1
    · simpa using hL0
  have b2 : ‖toL ((gInf (dg (E := E) a ρ hρ))⁻¹).val‖ ≤ L := by
    rw [← map_inv]
    refine (pi_norm_le_iff_of_nonneg hL0).2 fun i => (pi_norm_le_iff_of_nonneg hL0).2 fun j =>
      (pi_norm_le_iff_of_nonneg hL0).2 fun w => ?_
    change ‖pInf E ((diagonal fun i => (((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E)⁻¹ : IdeleGroup E) : 𝔸[E])) i j) w‖ ≤ L
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [key']; exact (hL i).2
    · simpa using hL0
  unfold CuspRep.height
  linarith

theorem gFin_infEmb (y : AutomorphicForm.archGroup E a) : gFin (AutomorphicForm.infEmb E a y : GA E a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := AutomorphicForm.prodEquiv_infEmb (K := E) (n := a) y
  have h2 := congrArg (fun p => (p.2 : GL (Fin a) (Af E)) i j) h
  exact h2

theorem finGL_mul_infGL (g : GA E a) : finGL E a (gFin g) * infGL E a (gInf g) = g := by
  rw [← infGL_comm]; exact infGL_mul_finGL g

theorem box_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∀ ω : Set (AdelicGLn.AdelicGL E a), IsCompact ω → ∃ N : ℕ, ∀ Q : Set (AutomorphicForm.archGroup E a), IsCompact Q → ∃ C : ℝ,
    ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL E a)), ∀ y ∈ Q, ∀ L : ℝ, 1 ≤ L →
      (∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) →
      ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (ρ i) (hρ i)) * kk * AutomorphicForm.infEmb E a y)‖ ≤ C * L ^ N) := by
  intro E _ _ _ a φ hφ ω hω
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := isCompact_maxCompact
  have hT : IsCompact ((fun p : GA E a × GA E a => gFin p.1 * gFin p.2) '' (ω ×ˢ (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)))) :=
    (hω.prod hK).image ((continuous_gFin.comp continuous_fst).mul (continuous_gFin.comp continuous_snd))
  obtain ⟨C₀, N, hC₀, hgrow⟩ := exists_growth_uniform hφ hT
  refine ⟨N, fun Q hQ => ?_⟩
  obtain ⟨B₁, hB₁, h₁⟩ := exists_height_bound (E := E) (a := a) hω
  obtain ⟨B₂, hB₂, h₂⟩ := exists_height_bound (E := E) (a := a) hK
  obtain ⟨B₃, hB₃, h₃⟩ := exists_height_bound (E := E) (a := a)
    (hQ.image (AutomorphicForm.continuous_infEmb (K := E) (n := a)))
  set c : ℝ := 1 + 2 * a with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C₀ * (c * (c * (c * (B₁ * 3)) * B₂) * B₃) ^ N, fun b hb ρ hρ kk hk y hy L hL1 hL => ?_⟩
  set D : GA E a := dg a ρ hρ with hD
  set Y : GA E a := AutomorphicForm.infEmb E a y with hY
  set x : GA E a := b * D * kk * Y with hx
  have hfin : gFin x = gFin b * gFin kk := by
    simp only [hx, map_mul, hD, gFin_dg, hY, gFin_infEmb, mul_one]
  have hinf : gInf x = gInf b * gInf D * gInf kk * gInf Y := by
    simp only [hx, map_mul]
  have hb' := h₁ b hb
  have hk' := h₂ kk hk
  have hy' := h₃ Y ⟨y, hy, rfl⟩
  have hd' : CuspRep.height (gInf D) ≤ 3 * L := height_gInf_dg_le ρ hρ hL1 hL
  have hH : CuspRep.height (gInf x) ≤ (c * (c * (c * (B₁ * 3)) * B₂) * B₃) * L := by
    have o1 := one_le_height (gInf b)
    have o2 := one_le_height (gInf D)
    have o3 := one_le_height (gInf kk)
    have o4 := one_le_height (gInf Y)
    have s1 : CuspRep.height (gInf b * gInf D) ≤ c * (B₁ * (3 * L)) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hb' hd' (by linarith) hB₁) hc0)
    have s2 : CuspRep.height (gInf b * gInf D * gInf kk) ≤ c * ((c * (B₁ * (3 * L))) * B₂) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s1 hk' (by linarith) (by positivity)) hc0)
    have s3 : CuspRep.height (gInf b * gInf D * gInf kk * gInf Y) ≤ c * ((c * ((c * (B₁ * (3 * L))) * B₂)) * B₃) :=
      (height_mul_le' _ _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul s2 hy' (by linarith) (by positivity)) hc0)
    rw [hinf]
    exact s3.trans_eq (by ring)
  have hbound := hgrow (gFin x) ⟨(b, kk), ⟨hb, hk⟩, hfin.symm⟩ (gInf x)
  rw [finGL_mul_infGL] at hbound
  refine hbound.trans ?_
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ hC₀
  exact pow_le_pow_left₀ (by linarith [one_le_height (gInf x)]) hH N

end GlobalTheory.CompanionTheory.BoxBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLatticeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_max_even_adapted_lattice : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h → ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | exact GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | (intros; apply GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.Affgl

theorem exists_monic_aeval_mem_of_le_sup {R : Type*} [Ring R] [Algebra ℂ R] (A : Subalgebra ℂ R)
    (V I : Submodule ℂ R) [FiniteDimensional ℂ V] (h : ∀ z ∈ A, z ∈ V ⊔ I) (z : R) (hz : z ∈ A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ I := by
  have hmemA : ∀ p : Polynomial ℂ, Polynomial.aeval z p ∈ A := by
    intro p
    have e : Polynomial.aeval z p = ((Polynomial.aeval (⟨z, hz⟩ : A) p : A) : R) := by
      simpa using (Polynomial.aeval_algHom_apply A.val (⟨z, hz⟩ : A) p)
    rw [e]
    exact Subtype.property _
  let f : Polynomial ℂ →ₗ[ℂ] R ⧸ I := I.mkQ ∘ₗ (Polynomial.aeval z).toLinearMap
  have hf : ∀ p, f p ∈ V.map I.mkQ := by
    intro p
    obtain ⟨v, hv, i, hi, e⟩ := Submodule.mem_sup.1 (h _ (hmemA p))
    refine ⟨v, hv, ?_⟩
    change I.mkQ v = I.mkQ (Polynomial.aeval z p)
    have hi0 : I.mkQ i = 0 := by simpa using hi
    rw [← e, map_add, hi0, add_zero]
  let g : Polynomial ℂ →ₗ[ℂ] V.map I.mkQ := f.codRestrict _ hf
  have hnot : ¬ Function.Injective g := fun hinj =>
    Polynomial.not_finite (R := ℂ) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hgp, hp⟩ : ∃ p, g p = 0 ∧ p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => hcon p hp)
  have hI : Polynomial.aeval z p ∈ I := by
    have : f p = 0 := congrArg Subtype.val hgp
    simpa [f] using this
  refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [map_mul, Polynomial.aeval_C, ← Algebra.commutes, ← Algebra.smul_def]
  exact I.smul_mem _ hI

theorem exists_monic_aeval_apply_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (J : Set (Module.End ℂ (Sm E a))) (hJ : Cofin J) (z : Module.End ℂ (Sm E a))
    (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) →
      Polynomial.aeval z p φ = 0 := by
  obtain ⟨-, V, hV, hcov⟩ := hJ
  obtain ⟨p, hp, hI⟩ := exists_monic_aeval_mem_of_le_sup (Zalg E a) V _ hcov z hz
  refine ⟨p, hp, fun φ hφ => ?_⟩
  have key : ∀ y ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, y φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, j, hj, rfl⟩ := hy
      simp [hφ j hj]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key _ hI

theorem minpoly_on_killed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ z ∈ Zalg E a, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ a J hJ z hz => exists_monic_aeval_apply_eq_zero E a J hJ z hz

end GlobalTheory.CompanionTheory.Affgl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivativeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nontrivial_derivative : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | exact GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKerStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧ (∀ x ∈ U, IsUnitAt w x) ∧
      ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | exact GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | (intros; apply GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetweenStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_compact_open_between : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)),
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWittComplementFrameStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_witt_complement_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CFin.exists_witt_basis | exact GlobalTheory.CompanionTheory.CFin.exists_witt_basis | (intros; apply GlobalTheory.CompanionTheory.CFin.exists_witt_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationEqConjNilpotentIntegralStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_eq_conj_nilpotent_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' | exact GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' | (intros; apply GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHomStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_weights_invariant_hom : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 → IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → (⨆ μ, wtDual E μ) = ⊤ → ∀ M : Finset (Fin n → ℤ), (∀ (ν : Fin n → ℤ) (v : V), v ≠ 0 → v ∈ hwSp E1 E2 (wtR ν) → wtDual E ν ≠ ⊥ → ν ∈ M) → ∀ t ∈ invA σ E, (∀ μ ∈ M, ∀ ξ ∈ hwOf G (wtR μ), t ξ = 0) → t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw | exact GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw | (intros; apply GlobalTheory.CompanionTheory.RealCountG.InjG.eq_zero_of_hw <;> assumption)
end

