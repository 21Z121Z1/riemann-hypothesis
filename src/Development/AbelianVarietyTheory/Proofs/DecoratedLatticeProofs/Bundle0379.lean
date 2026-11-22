import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem cA_cA'' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    show (a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e)) = _
    rw [show D.sp.cm.sig (D.sp.cm.sig e) = e from star_star e]

theorem unitary (V : HSp D) (hg : V.gram = 1) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * mt V g = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  rw [hg, Matrix.map_one (incA D) (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

theorem mt_inv_eq (V : HSp D) (hg : V.gram = 1) (g : GA D V) : mt V g⁻¹ = ((mt V g).map (cA D))ᵀ := by
  have h1 := unitary V hg g
  have h2 : mt V g * mt V g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  calc mt V g⁻¹ = (((mt V g).map (cA D))ᵀ * mt V g) * mt V g⁻¹ := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

set_option synthInstance.maxHeartbeats 200000 in

theorem int_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (x : Fin V.rank → D.host.E) (hx : x ∈ N) (i : Fin V.rank) :
    finPart D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) ∈ intAE D := by
  rw [GlobalTheory.SplitDec.int_iff]
  have := (hM x).1 hx i
  have e : toEAf D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) = (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [e]; exact this

theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

set_option synthInstance.maxHeartbeats 200000 in

theorem int_conj (V : HSp D) (hg : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (s : Fin V.rank → D.host.E) (hs : s ∈ N) (j : Fin V.rank) :
    finPart D (∑ l, cA D (incA D (s l)) * mt V g l j) ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff]
  have e : cA D (∑ l, cA D (incA D (s l)) * mt V g l j) = (mt V g⁻¹ *ᵥ fun k => incA D (s k)) j := by
    rw [mt_inv_eq V hg g, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, cA_cA'', mul_comm]
  rw [e]; exact int_of_moves V g N hM s hs j

theorem single_mem (S T : HSp D) (hgS : S.gram = 1) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (i0 : Fin T.rank) (j0 : Fin S.rank) :
    (Matrix.single i0 j0 (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) : WO S T) ∈
      latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have hint : ∀ {n : ℕ} (k : Fin n), Pi.single k (1 : D.host.E) ∈ intVec D n := by
    intro n k l
    by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, Pi.single j0 1, hint j0,
    Pi.single i0 1, hint i0, ?_⟩
  ext i j
  rw [Matrix.of_apply, hgS]
  have hsum : ∑ k, star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) k) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j =
      star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) j) := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
  rw [hsum]
  by_cases hi : i = i0
  · subst hi
    by_cases hj : j = j0
    · subst hj
      rw [Matrix.single_apply_same, Pi.single_eq_same, Pi.single_eq_same, star_one, mul_one, mul_one]
    · rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), Pi.single_eq_of_ne hj, star_zero, mul_zero,
        TensorProduct.tmul_zero]
  · rw [Matrix.single_apply_of_row_ne (Ne.symm hi), Pi.single_eq_of_ne hi, mul_zero, zero_mul,
      TensorProduct.tmul_zero]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem row_one {n : ℕ} (s : Fin n → D.host.E) (l : Fin n) :
    ∑ m, star (s m) * (1 : Matrix (Fin n) (Fin n) D.host.E) m l = star (s l) := by
  rw [Finset.sum_eq_single l (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, mul_one]

set_option synthInstance.maxHeartbeats 200000 in

theorem gen_mem (S T : HSp D) (hgS : S.gram = 1) (hgT : T.gram = 1) (g : GA D S) (h : GA D T)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : Moves S rfl g N) (hN' : Moves T rfl h N') (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (s : Fin S.rank → D.host.E) (hs : s ∈ N) (t : Fin T.rank → D.host.E) (ht : t ∈ N') :
    actO S T g⁻¹ h⁻¹ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))
      ∈ latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have e1 : actO S T g⁻¹ h⁻¹
      (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) := by
    ext i j
    simp only [actO, inv_inv, Matrix.mul_apply, Matrix.of_apply, hgS, row_one, gen_eq,
      ← GlobalTheory.FinPl.FrameLat.cA_incA, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e1, Matrix.matrix_eq_sum_single ((Matrix.of fun i j =>
    ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))]
  refine sum_mem fun i0 _ => sum_mem fun j0 _ => ?_
  rw [Matrix.of_apply, ← smul_eq_mul, ← Matrix.smul_single]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (single_mem S T hgS α hα c hc i0 j0)
  rw [map_mul]
  exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (int_of_moves T h N' hN' t ht i0) (int_conj S hgS g N hN s hs j0)

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

theorem latO_moved_onto : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  intro D S T a b hS hT hgS hgT g _ h _ N N' hN hN' u' hu'
  subst hS; subst hT
  refine ⟨actO S T g⁻¹ h⁻¹ u', ?_, ?_⟩
  · let Ψ : WO S T →+ WO S T :=
      { toFun := actO S T g⁻¹ h⁻¹
        map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
        map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
    have key : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) ≤
        (latO S T (intVec D _) (intVec D _) (fun _ => True)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩
      exact gen_mem S T hgS hgT g h N N' hN hN' α hα c hc s hs t ht
    exact key hu'
  · simp only [actO]
    rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * u'), ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.mul_one,
      ← Matrix.mul_assoc, ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.one_mul]

end GlobalTheory.LatMoveStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts GlobalTheory.FinWeilO GlobalTheory.LatCoef in

theorem GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv S v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (Om (embV S v a, 1) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v a, 1)))))⁻¹ * Lift.pet μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  intro D ψ S T hψ lam w₀ Om h μ 𝓕 hμ v a f₁ f₂ h₁ h₂
  obtain ⟨η, hηdef⟩ : ∃ η : AF D.host.F, η = pairA D.host.F 0 (singleV D.host.F v 1) := ⟨_, rfl⟩
  have hε : IsPlaceIdem D v η := hηdef ▸
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hg : SuppPl η S (embV S v a) := hηdef ▸ GlobalTheory.PlaceTensor.suppPl_emb S v a
  have hk : SuppPl η T (1 : GA D T) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have H := isHeis_opF hψ.1 S T h.hw
  have hphase : ∀ x : XF S T, phase ψ w₀ x * (starRingEnd ℂ) (phase ψ w₀ x) = 1 := fun x => by
    rw [Complex.mul_conj', show ‖phase ψ w₀ x‖ = 1 from hψ.1.2.1 _]; simp
  have laws := fun g : thetaSub ψ S T => GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2
  let ℓ : thetaSub ψ S T →ₗ[ℂ] ℂ :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
      map_add' := fun g g' => ((laws g).2.2.2.1 g' g'.2).1
      map_smul' := fun c g => ((laws g).2.2.1 c).1 }
  have hℓ : ∀ a' ∈ latF S T (frameLat S) (frameLat T), ∀ g,
      ℓ (opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') g) = ℓ g := by
    intro a' ha' g
    obtain ⟨x, hx⟩ : ∃ x, x = mulF S T (algebraMap (AF D.host.F) (AE D) η) a' := ⟨_, rfl⟩
    have hfix := opF_mulF_fix h hε h₂.2 ha'
    rw [← hx] at hfix ⊢
    have hg' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin g.2
    have hf' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin f₂.2
    have l2' := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ hg' hf'
    have l3 := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ ((thetaSub ψ S T).smul_mem (phase ψ w₀ x) hg') hf'
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (opF hψ.1 S T w₀ x g : WO S T → ℂ) f₂ = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
    conv_lhs => rw [← hfix]
    rw [coe_opF, coe_opF, (l3.2.2.1 (phase ψ w₀ x)).2, (l2'.2.2.1 (phase ψ w₀ x)).1,
      ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2).2.2.2.2.2.2.1 x).1, ← mul_assoc, mul_comm (starRingEnd ℂ _),
      hphase, one_mul]
  have hm : ∀ a' ∈ latF S T (frameLat S) (frameLat T),
      opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') f₁ = f₁ := fun a' ha' =>
    opF_mulF_fix h hε h₁.2 ha'
  exact coef_of_local_vacuum H lam _ h.sd h.span (rhoF S T (embV S v a, 1)) (h.sd' _) (h.fin _) (Om (embV S v a, 1)) (h.op _)
    (h.vac _) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap])
    (fun a' ha' => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hε) _ ha')
    (fun x => XF.ext (by
      rw [coe_mulF, coe_mulF, smul_smul, ← map_mul, placeIdem_mul_self hε]))
    (fun x => XF.ext (by
      have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
          (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
        rw [sub_smul, one_smul]; rfl
      rw [coe_rhoF, e1, actO_smul, hoff]))
    (fun x => XF.ext (actO_smul _ _ _ _)) ℓ hℓ f₁ hm

namespace GlobalTheory.VacSource

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem inv_neg_pow_mul (x : ℂ) (N M : ℕ) :
    ((-x) ^ (N * M))⁻¹ = ((((-1 : ℂˣ) ^ N : ℂˣ) : ℂ) * (x ^ N)⁻¹) ^ (M : ℤ) := by
  rw [zpow_natCast, pow_mul, ← inv_pow, neg_pow, mul_inv, ← inv_pow (-1 : ℂ), inv_neg_one]
  push_cast
  rfl

theorem vacuum_matrixCoefficient_source_inert_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∃ φ : GU c S.rank → ℂ, KerU ϖ (qV D.host.F v) T.rank ((-1) ^ T.rank) φ ∧ ∀ (g : GU c S.rank) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) f₁) f₂ = φ g * Lift.pet μ 𝓕 f₁ f₂ := by
  intro D ψ S T χS χT om hom μ 𝓕 hμ v w h hw uS uT c ϖ e hU he
  classical
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w₀, Om, hL⟩ := GlobalTheory.FinWeilO.exists_isLatRep hom.std (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hlam
  refine ⟨fun g => (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
    ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm g), 1)))))⁻¹,
    fun d t ht k₁ hk₁ k₂ hk₂ => ?_, fun g f₁ f₂ h₁ h₂ => ?_⟩
  · show (lam _)⁻¹ = _
    rw [GlobalTheory.T.relIndex_homLattice_inert_move_source D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂, map_pow, GlobalTheory.LamInert.lam_qV_inert D lam hlam v w hw]
    have hs0 : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [← Int.toNat_of_nonneg hs0, zpow_natCast]
    generalize (∑ i, max (d i) 0).toNat = M
    exact inv_neg_pow_mul _ _ _
  · let g₁ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₁, h₁.1⟩
    let g₂ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₂, h₂.1⟩
    have hn := GlobalTheory.T.weilDatum_source_inertPlace_eq_latticeIntertwiner D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam v w h hw uS uT (e.symm g) g₁
    have hc := GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source D ψ S T hom.std lam w₀ Om hL μ 𝓕 hμ v (e.symm g) g₁ g₂ h₁ h₂
    show Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) (g₁ : WO S T → ℂ)) (g₂ : WO S T → ℂ) = _ * Lift.pet μ 𝓕 (g₁ : WO S T → ℂ) (g₂ : WO S T → ℂ)
    rw [hn, hc]

end GlobalTheory.VacSource

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem halfMod_eq_detPow {D : D7} {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := rfl

theorem halfMod_rank_zero {D : D7} (n : ℕ) (a : GL (Fin 0) (AE D)) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, Subsingleton.elim a 1, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem wittDecomposition_levi_emb_acts_isotropic {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.e.map (incA D) = d.e.map (incA D) ⬝ a.1 := by
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]

theorem wittDecomposition_levi_emb_acts_anisotropicCore {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.i₀.map (incA D) = d.i₀.map (incA D) ⬝ mt S₀ g := by
  have e2 : d.i₀.map (incA D) = d.j0 := rfl
  rw [e2, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]

theorem heisO_extX_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ)
    (f : WO S T → ℂ) : heisO ψ S T (d.extX T 0) f = f := by
  funext w
  simp only [heisO, map_zero, add_zero, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem levi_origin_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨hz, -, hl⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, -, -, hiso⟩ := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hom.std
    refine ⟨1, 1, continuous_const, fun _ => rfl, continuous_const, fun _ _ => rfl, fun a g f hf => ?_⟩
    rw [hz S S₀ T d μ 𝓕 hμ, hz S S₀ T d μ 𝓕 hμ, (hl S S₀ d).1, one_mul, hiso χS χT om om₀ hom hom₀ g 1 f hf,
      halfMod_rank_zero]
    simp
  · obtain ⟨hsp, hr, -, -, -, hm, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    obtain ⟨α, ξ, hα, hξ, h⟩ := GlobalTheory.T.leviFactor_scalars_automorphicCharacters D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT om hom χS χT om₀ hom₀
    refine ⟨α, ξ, hα.1, hα.2, hξ.1, hξ.2, fun a g f hf => ?_⟩
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hr]; exact hμ
    rw [hm, hm, heisO_extX_zero, heisO_extX_zero, halfMod_eq_detPow]
    exact h μ 𝓕 hμ' a g (d.levi a * d.emb0 g) (wittDecomposition_levi_emb_acts_isotropic d a g) (wittDecomposition_levi_emb_acts_anisotropicCore d a g) f hf

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGramStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_of_rank_one_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  first | exact @GlobalTheory.Fam.WeilTup.weilOK_fam | exact GlobalTheory.Fam.WeilTup.weilOK_fam | (intros; apply GlobalTheory.Fam.WeilTup.weilOK_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedModelUnipotentFormulasStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittMixedModel_unipotent_formulas : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ b, d.mixS T ψ μ 𝓕 (om (d.nB b, 1) f) x = heisO ψ S₀ T (x ⬝ b) (d.mixS T ψ μ 𝓕 (f) x)) ∧ ∀ c, d.mixS T ψ μ 𝓕 (om (d.nC c, 1) f) x = ψ (d.qS T c x) • d.mixS T ψ μ 𝓕 (f) x := by
  first | exact @GlobalTheory.MixUnip.mixS_unip | exact GlobalTheory.MixUnip.mixS_unip | (intros; apply GlobalTheory.MixUnip.mixS_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEq
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.Conj

theorem fixInv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : VA X.B.I)
    (h : X.B.I.fmat (X.xu u) *ᵥ v = v) : X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul X, Matrix.one_mulVec]

theorem prj_conj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  intro D X u y
  have hE : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.eV X a = GlobalTheory.ScalW.eV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).1
  have hF : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.fV X a = GlobalTheory.ScalW.fV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).2
  simp only [GlobalTheory.ScalW.prj, GlobalTheory.St.G.FrameClose.hA_move, hE, hF, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_sum, Matrix.mulVec_smul]

end GlobalTheory.ScalW.Conj
end
end

