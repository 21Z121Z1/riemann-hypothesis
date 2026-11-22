import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0436
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem om_theta_eq {ψ : AddChar (AF D.host.F) ℂ} {S' T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ)} (hW : IsWeilDatumO ψ S' T' χS χT om) {e : AE D}
    (he : e * e = e) (hinf : infPart D e = 0) {ΛS : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} (hS : IsSelfDualC S' ΛS) (hT : IsSelfDualC T' ΛT)
    {f₀ : WO S' T' → ℂ} (hf₀ : IsThetaFunO ψ S' T' f₀) (g : GA D S' × GA D T')
    (hΛ : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g.1 g.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True))
    {c : ℂ} (hc : c ≠ 0) (h0 : om g f₀ = c • f₀) {Tm : (WO S' T' → ℂ) →ₗ[ℂ] (WO S' T' → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Tm)
    {Φ f : WO S' T' → ℂ}
    (hf : IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e (latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True)) 1 f₀ Φ f) :
    om g f = Tm (c • fun x => Φ (actO S' T' g⁻¹.1 g⁻¹.2 x)) := by
  have hΛ' : ∀ u, u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      actO S' T' g⁻¹.1 g⁻¹.2 u ∈ latO S' T' (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    intro u
    have e1 : actO S' T' g.1 g.2 (actO S' T' g⁻¹.1 g⁻¹.2 u) = u := by
      rw [Prod.fst_inv, Prod.snd_inv]; exact GlobalTheory.AdelicLatMove.actO_actO_inv _ _ _ _ u
    rw [hΛ (actO S' T' g⁻¹.1 g⁻¹.2 u), e1]
  have hinv : om g⁻¹ f₀ = c⁻¹ • f₀ := by
    have e2 : om g⁻¹ (om g f₀) = f₀ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h0, LinearMap.map_smul] at e2
    calc om g⁻¹ f₀ = c⁻¹ • (c • om g⁻¹ f₀) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • f₀ := by rw [e2]
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S' T' ΛS ΛT hS hT e he hinf f₀ hf₀ Tm hTm
  have hmod := GlobalTheory.SchrMove.isPlaceModel_move hW hΛ' hTm hth (inv_ne_zero hc) hinv
  have hfe : f = ((c⁻¹)⁻¹ • (om g⁻¹ ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S' T' g⁻¹.1 g⁻¹.2))) Φ := hf.2 _ hmod
  rw [hfe, inv_inv, LinearMap.smul_apply, LinearMap.map_smul, LinearMap.comp_apply, LinearMap.comp_apply,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, LinearMap.map_smul]
  rfl

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem keepStd (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) :=
  GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice S j hj k hk v

theorem mulVec_mulVec_inv {n : ℕ} {R : Type} [CommRing R] (X : GL (Fin n) R) (v : Fin n → R) :
    X.1 *ᵥ ((X⁻¹).1 *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem keepPair (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : GA D (G.V (.grid i D.R.m))) (y : GA D (G.V (.grid (i + 1) D.R.m)))
    (hxf : x ∈ GfC (G.V (.grid i D.R.m))) (hyf : y ∈ GfC (G.V (.grid (i + 1) D.R.m)))
    (hx : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid i D.R.m)) x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid i D.R.m))))
    (hy : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (i + 1) D.R.m)) y).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (i + 1) D.R.m))))
    (u : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) := by
  have sdT := S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩
  have sdS := S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩
  obtain ⟨βT, hβT⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdT.1.fg sdT.1.span_eq_top
  obtain ⟨βS, hβS⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ sdS.1.fg sdS.1.span_eq_top
  have keep : ∀ {V : HSp D} (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)),
      Formalism.L2.DIV.IsFrame β Λ → ∀ X : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D),
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ X.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → X ∈ Formalism.L2.DIV.St β := by
    intro V Λ β hβ X hX
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ X).2 ⟨fun v hv => (hX v).1 hv, fun v hv => ?_⟩
    refine (hX _).2 ?_
    rw [mulVec_mulVec_inv]
    exact hv
  have stx := keep _ βT hβT _ hx
  have sty := keep _ βS hβS _ hy
  have sty' : Formalism.IndefR.Lev.finE (G.pS (.chi i D.R.m : Pair T)) (negGA _ y) ∈ Formalism.L2.DIV.St βS := sty
  exact GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
    (S.N.latS (.chi i D.R.m)) (S.N.latT (.chi i D.R.m)) βS βT (isSelfDualC_neg sdS) sdT hβS hβT
    (negGA _ y) x sty' stx u

theorem keepLow (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 u ∈
        latO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T)) (S.N.latS (.chi j D.R.m) : Set _) (S.N.latT (.chi j D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid j D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid j D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j) (by omega) 1 (moved S j k) (one_mem _) h2 h1 h3 u

theorem keepHigh (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (u : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    u ∈ latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 u ∈
        latO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)) (S.N.latS (.chi (j + 1) D.R.m) : Set _) (S.N.latT (.chi (j + 1) D.R.m) : Set _) (fun _ => True) := by
  have h1 : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1 + 1) D.R.m))) := by
    intro v
    have e0 : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1 = 1 := MonoidHom.map_one _
    have e1 : (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1 + 1) D.R.m)) 1).1 *ᵥ v = v := by rw [e0]; exact Matrix.one_mulVec v
    rw [e1]
  have h2 : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) := ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u _).2
  have h3 := keepStd S j hj k hk
  exact keepPair S (i := j + 1) (by omega) (moved S j k) 1 h2 (one_mem _) h3 h1 u

theorem selfDual (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) :
    IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m)) ∧ IsSelfDualC (G.pT (.chi i D.R.m : Pair T)) (S.N.latT (.chi i D.R.m)) :=
  ⟨isSelfDualC_neg (S.N.selfDual (X := .grid (i + 1) D.R.m) ⟨hi, rfl⟩), S.N.selfDual (X := .grid i D.R.m) ⟨by omega, rfl⟩⟩

theorem vacScalar (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m))
    (hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈
        latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) :
    ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) :=
  GlobalTheory.T.chiArrowPair_moves_standardVacuum_by_scalar S hi x y hΛ

end GlobalTheory.RowVertexInv.FactorTheta

namespace GlobalTheory.RowVertexInv.FactorTheta

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem position_theta (S : GridChoice W U) {t : T} {e : AE D} (d : PureDat G t)
    (hd : (∀ j, (d.1 j).e = e ∧ (d.1 j).z = 1) ∧ ∀ i, (d.2 i).e = e ∧ (d.2 i).z = 1)
    (hv : (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) := by
  have key : ∀ {p : Pair T} (x : FinDatum G t p), x.e = e → x.z = 1 → S.Z.HasVec x →
      IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
        (latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) 1 (S.Z.vac p) x.fn (S.Z.vec x) := by
    intro p x hxe hxz hx
    obtain ⟨f, hf⟩ := hx
    have h1 : S.Z.vec x = f := by
      rw [Normal.vec, FinDatum.vec_eq W hf, hxz]
      have h2 : W.om p (1, 1) = 1 := map_one _
      rw [h2]; rfl
    rw [h1, ← hxe]; exact hf
  rcases a with j | i
  · exact key (d.1 j) (hd.1 j).1 (hd.1 j).2 (hv.1 j)
  · exact key (d.2 i) (hd.2 i).1 (hd.2 i).2 (hv.2 i)

theorem scalar_ne_zero {p : Pair T} (g : GA D (G.pS p) × GA D (G.pT p)) {c : ℂ} {f : WO (G.pS p) (G.pT p) → ℂ}
    (hf : f ≠ 0) (h : W.om p g f = c • f) : c ≠ 0 := by
  intro hc
  apply hf
  have e1 : W.om p g⁻¹ (W.om p g f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h, hc, zero_smul, map_zero] at e1
  exact e1.symm

theorem vac_ne_zero (S : GridChoice W U) {i : ℕ} (hi : i + 1 ≤ D.R.m) : S.Z.vac (.chi i D.R.m) ≠ 0 := by
  intro h0
  obtain ⟨⟨p, hp⟩, hn⟩ := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2.norm
  have := hn p hp
  simp [nrm2, h0] at this

theorem vecOf_eq_intertwiner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}, S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∃ (c₁ c₂ : ℂ) (Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a), W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) ∧ W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) ∧ ∀ d ∈ τ.support, ∀ a, vecOf S d a = Tm a (fnOf d a) ∧ moveV S j hj k (vecOf S d) a = Tm a (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) := by
  intro D T L sc G W U S t Φ β τ hexp hvec j hj k hk
  classical
  obtain ⟨e, he, hsupp, -⟩ := hexp
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  let Tm : ∀ a, FactorFn G t a →ₗ[ℂ] FactorFn G t a := fun a =>
    Classical.epsilon (IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)))
  have hth : ∀ d ∈ τ.support, ∀ a, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (fnOf d a) (vecOf S d a) :=
    fun d hd a => position_theta S d ⟨fun j' => ⟨((hsupp d hd).1 j').2.1, ((hsupp d hd).1 j').2.2⟩,
      fun i => ⟨((hsupp d hd).2 i).2.1, ((hsupp d hd).2 i).2.2⟩⟩ (hvec d hd) a
  have hTm : ∀ d ∈ τ.support, ∀ a, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) (S.N.latS (positionPair t D.R.m a) : Set _)
        (S.N.latT (positionPair t D.R.m a) : Set _) fun _ => True) 1 (S.Z.vac (positionPair t D.R.m a)) (Tm a) ∧
      vecOf S d a = Tm a (fnOf d a) := by
    intro d hd a
    have h := hth d hd a
    have hs := Classical.epsilon_spec h.1
    exact ⟨hs, h.2 _ hs⟩
  have hj1 : j + 1 ≤ D.R.m := by omega
  have hj2 : j + 1 + 1 ≤ D.R.m := by omega
  obtain ⟨c₁, hc₁⟩ := vacScalar S hj1 1 ((S.N.u _)⁻¹ * k * S.N.u _) (keepLow S j hj k hk)
  obtain ⟨c₂, hc₂⟩ := vacScalar S hj2 ((S.N.u _)⁻¹ * k * S.N.u _) 1 (keepHigh S j hj k hk)
  refine ⟨c₁, c₂, Tm, hc₁, hc₂, fun d hd a => ⟨(hTm d hd a).2, ?_⟩⟩
  by_cases h2 : a = .inr ⟨j + 1, hj⟩
  · subst h2
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j + 1, hj⟩) = W.om (.chi (j + 1) D.R.m)
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (vecOf S d (.inr ⟨j + 1, hj⟩)) := by
      unfold moveV; exact Function.update_self _ _ _
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j + 1, hj⟩) = c₂ := by unfold scaleAt; exact Function.update_self _ _ _
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j + 1, hj⟩) = fun x => fnOf d (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
      unfold movFn; exact Function.update_self _ _ _
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj2).1 (selfDual S hj2).2 (S.Z.vac_is (.chi (j + 1) D.R.m) ⟨hj2, rfl⟩).2.theta _ (keepHigh S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj2) hc₂) hc₂ (hTm d hd (.inr ⟨j + 1, hj⟩)).1 (hth d hd (.inr ⟨j + 1, hj⟩))
  by_cases h1 : a = .inr ⟨j, by omega⟩
  · subst h1
    have hne : (Sum.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
    have e1 : moveV S j hj k (vecOf S d) (.inr ⟨j, by omega⟩) = W.om (.chi j D.R.m)
        (G.toPair (.chi j D.R.m) 1 (moved S j k)) (vecOf S d (.inr ⟨j, by omega⟩)) := by
      unfold moveV; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e2 : scaleAt j hj c₁ c₂ (.inr ⟨j, by omega⟩) = c₁ := by
      unfold scaleAt; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    have e3 : movFn S j hj k (fnOf d) (.inr ⟨j, by omega⟩) = fun x => fnOf d (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
      unfold movFn; exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
    rw [e1, e2, e3]
    exact om_theta_eq (W.om_is _ (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)) hee hinf
      (selfDual S hj1).1 (selfDual S hj1).2 (S.Z.vac_is (.chi j D.R.m) ⟨hj1, rfl⟩).2.theta _ (keepLow S j hj k hk)
      (scalar_ne_zero _ (vac_ne_zero S hj1) hc₁) hc₁ (hTm d hd (.inr ⟨j, by omega⟩)).1 (hth d hd (.inr ⟨j, by omega⟩))
  · have e1 : moveV S j hj k (vecOf S d) a = vecOf S d a := by
      unfold moveV; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e2 : scaleAt j hj c₁ c₂ a = 1 := by
      unfold scaleAt; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    have e3 : movFn S j hj k (fnOf d) a = fnOf d a := by
      unfold movFn; exact (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)
    rw [e1, e2, e3, one_smul]
    exact (hTm d hd a).2

end GlobalTheory.RowVertexInv.FactorTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineSchrodingerModel
section
noncomputable section

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Classical
open MeasureTheory

namespace GlobalTheory.ArchLine

open scoped SchwartzMap

theorem realLine : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  have hex : ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁ := fun h hh f => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hCM hψ hW h hh f
  obtain ⟨hadd, hsmul, hone, hmul⟩ := GlobalTheory.T.archimedean_weilOperators_linear_one_mul M ψ χX χW om hW hex
  obtain ⟨aadd, asmul, amul⟩ := GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul M
  have hγU : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := fun t => hγ.2 _
  have hγ0 : γ (Multiplicative.ofAdd 0) = 1 := by rw [ofAdd_zero, map_one]
  have hγadd : ∀ s t : ℝ, γ (Multiplicative.ofAdd (s + t)) = γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t) :=
    fun s t => by rw [ofAdd_add, map_mul]
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F) = N := ⟨_, rfl⟩
  obtain ⟨C, φ, hφ, hC⟩ := pairingCoords (Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d))
    (isPairing_trP _) N hN
  let S : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := archOp om (γ (Multiplicative.ofAdd t))
      map_add' := hadd _ (hγU t)
      map_smul' := hsmul _ (hγU t) }
  let A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := fun t =>
    { toFun := archAct M (γ (Multiplicative.ofAdd t))
      map_add' := aadd _
      map_smul' := asmul _ }
  let ψt : ℝ → (Fin N ⊕ Fin N → ℝ) →ₗ[ℝ] (Fin N ⊕ Fin N → ℝ) := fun t =>
    φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hψt : ∀ t w, ψt t w = φ (archAct M (γ (Multiplicative.ofAdd t)) (φ.symm w)) := fun t w => rfl
  let g : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := fun t => LinearMap.toMatrix' (ψt t)
  have hg : ∀ t w, g t *ᵥ w = ψt t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  let P1 : SInf F (Fin n × Fin d) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let P2 : GlobalTheory.RealWeil.Sch (Fin N) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let eΦ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := ContinuousLinearEquiv.equivOfInverse P1 P2
    (fun f => by ext x; simp [P1, P2]) (fun h => by ext x; simp [P1, P2])
  have hΦ : ∀ f x, eΦ f x = f (C.symm x) := fun f x => rfl
  have hΦs : ∀ h x, eΦ.symm h x = h (C x) := fun h x => rfl
  let T : ℝ → GlobalTheory.RealWeil.Sch (Fin N) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := fun t =>
    eΦ.toLinearMap ∘ₗ S t ∘ₗ eΦ.symm.toLinearMap
  have hT : ∀ t h x, T t h x = archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h) (C.symm x) := fun t h x => rfl
  refine ⟨Fin N, inferInstance, inferInstance, eΦ, g, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [g, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action M γ hγ _))
  · have e : ψt 0 = LinearMap.id := LinearMap.ext fun w => by rw [hψt, hγ0, archAct_one]; simp
    simp only [g, e, LinearMap.toMatrix'_id]
  · intro s t
    have e : ψt (s + t) = ψt s ∘ₗ ψt t := LinearMap.ext fun w => by
      rw [hψt, LinearMap.comp_apply, hψt, hψt, hγadd, amul, LinearEquiv.symm_apply_apply]
    simp only [g, e, LinearMap.toMatrix'_comp]
  · intro t
    have hsym : ∀ w w', GlobalTheory.RealWeil.sympl (ψt t w) (ψt t w') = GlobalTheory.RealWeil.sympl w w' := fun w w' => by
      rw [hψt, hψt, hφ, GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨Mx, hMx⟩ := symplMatrix (Fin N) (ψt t) hsym
    have e : g t = Mx := Matrix.toLin'.injective (LinearMap.ext fun w => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hg, hMx])
    rw [e]; exact Mx.2
  · refine LinearMap.ext fun h => ?_
    ext x
    rw [hT, hγ0, hone, hΦs]
    simp
  · intro s t
    refine LinearMap.ext fun h => ?_
    ext x
    show archOp om (γ (Multiplicative.ofAdd (s + t))) (eΦ.symm h) (C.symm x) =
      archOp om (γ (Multiplicative.ofAdd s)) (eΦ.symm (T t h)) (C.symm x)
    rw [hγadd, hmul _ (hγU s) _ (hγU t)]
    congr 2
    exact (eΦ.symm_apply_apply (S t (eΦ.symm h))).symm
  · intro t w h h₁ hh₁
    have hf : ⇑(eΦ.symm h₁) = schrF (trP F (Fin n × Fin d)) (φ.symm w) ⇑(eΦ.symm h) := by
      have e1 : ⇑(eΦ.symm h) = ⇑h ∘ ⇑C := funext (hΦs h)
      rw [e1, hC, LinearEquiv.apply_symm_apply]
      funext y; rw [hΦs, hh₁]; rfl
    have key := GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger M ψ χX χW om hψ hW hex _ (hγU t) (φ.symm w) _ _ hf
    have e2 : ⇑(archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h)) = ⇑(T t h) ∘ ⇑C := by
      funext y; rw [Function.comp_apply, hT, ContinuousLinearEquiv.symm_apply_apply]
    funext x
    rw [hT, key, e2, hC, hg, hψt]
    simp
  · intro t h
    have e := GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq M ψ χX χW om hW hex _ (hγU t) N C (eΦ.symm h)
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · simp only [hΦs, ContinuousLinearEquiv.apply_symm_apply]
  · intro h x
    exact GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator M ψ χX χW om hW hex γ hγ (eΦ.symm h) (C.symm x)
  · intro t f
    have e : eΦ.symm (T t (eΦ f)) = archOp om (γ (Multiplicative.ofAdd t)) f := by
      ext y; rw [hΦs, hT]; simp
    rw [e]
    exact acts_archOp om _ f (hex _ (hγU t) f)

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScalingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_hermitian_scaling : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram),
  ∀ (f₀ : WO (sgn ε M) X → ℂ), IsVacF ψ θ (frSgn ε A) B f₀ →
  ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Xs, ∃ g : ℝ → GA D M,
    (∀ t : ℝ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hJ (g t) = γ (Multiplicative.ofAdd t)) ∧
    ∀ P : PolF D X.rank M.rank, ∃ Q ∈ GlobalTheory.RealQuot.coinv ε A B eT, ∀ z,
      HasDerivAt (fun t : ℝ => ω (g t, 1) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) (ptF ψ θ (frSgn ε A) B f₀ Q z) 0 := by
  first | exact @GlobalTheory.OmegaDer.line_deriv_mem_coinv | exact GlobalTheory.OmegaDer.line_deriv_mem_coinv | (intros; apply GlobalTheory.OmegaDer.line_deriv_mem_coinv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTraceAddCharAtPlaceMemSubfieldOfRootsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}, (∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) → HasConductor (psiAt W w) 1 → ∀ (x : Kw w), valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1 → (psiAt W w x : ℂ) ∈ F := by
  first | exact @GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | exact GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | (intros; apply GlobalTheory.FunObj.psiAt_mem_subfield_of_roots <;> assumption)
end

