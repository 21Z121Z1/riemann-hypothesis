import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem dLine_apply' {S T : HSp D} {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_add_line (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {L L' : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L') (hL0' : ∀ t, (L' t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T (L + L') f = dLine ψ S T L f + dLine ψ S T L' f := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hS : Continuous (L + L') := hL.add hL'
  have hS0 : ∀ t, ((L + L') t).map (finPart D) = 0 := fun t => by
    rw [AddMonoidHom.add_apply, Matrix.map_add _ (finPart D).map_add, hL0 t, hL0' t, add_zero]
  funext w
  rw [Pi.add_apply, dLine_apply' h hl hlam hS hS0 hf, dLine_apply' h hl hlam hL hL0 hf, dLine_apply' h hl hlam hL' hL0' hf,
    AddMonoidHom.add_apply, map_add, ContinuousLinearMap.map_add]
  have e : phase lam S T (L 1 + L' 1) w = phase lam S T (L 1) w + phase lam S T (L' 1) w := by
    show lam (symplOH S T w (L 1 + L' 1)) = lam (symplOH S T w (L 1)) + lam (symplOH S T w (L' 1))
    rw [symplOH_add_right, map_add]
  rw [e]
  ring

variable {W A A' : HSp D} (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (S : HSp D)

theorem inl_fst_add_inr_snd (x : WO W S) : inlH d S (fstH d S x) + inrH d S (sndH d S x) = x := by
  rw [inlH_apply, inrH_apply, fstH_apply, sndH_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger A' S (d.resS S x).2) = (d.resS S x).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger A' S _
  rw [this, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem dLine_inlH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    dLine ψ W S ((inlH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split d, map_add, fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inrH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    dLine ψ W S ((inrH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ S A' M (G u) v) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split d, map_add, fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

end GlobalTheory.BiJoinDeriv

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove

theorem dLine_join : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  intro D ψ hψ W A S A' d G hG M hM hM0
  have h1 : ∀ s, (fstH d S (M s)).map (finPart D) = 0 := fun s => map_mul_eq_zero_left _ (hM0 s) _
  have h2 : ∀ s, (sndH d S (M s)).map (finPart D) = 0 := fun s => fin_dagger A' S (map_mul_eq_zero_left _ (hM0 s) _)
  refine ⟨h1, h2, ?_⟩
  have hj := isThetaFunO_join d hG
  have eM : M = (inlH d S).comp ((fstH d S).comp M) + (inrH d S).comp ((sndH d S).comp M) := by
    ext1 t
    exact (inl_fst_add_inr_snd d S (M t)).symm
  rw [eM, dLine_add_line hψ ((continuous_inlH d S).comp ((continuous_fstH d S).comp hM)) (fun t => map_inlH d S _ (h1 t))
    ((continuous_inrH d S).comp ((continuous_sndH d S).comp hM)) (fun t => fin_inrH d S (h2 t)) hj,
    dLine_inlH, dLine_inrH, ← eM]
  funext x
  simp only [Pi.add_apply, join_apply]

end GlobalTheory.BiJoinDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := by
  first | exact @GlobalTheory.HeisTarget.main | exact GlobalTheory.HeisTarget.main | (intros; apply GlobalTheory.HeisTarget.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemEMulIdemE
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacUnion

variable {D : D7}

open Classical in

def idemF (v : Pl D) : Af D.host.F :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    show (if w = v then (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.F w) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem evalV_idemF (v w : Pl D) : evalV D.host.F w (idemF v) = if w = v then 1 else 0 := rfl

theorem af_ext {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [mul_zero]

def idemE (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA _ 0 (idemF v))

theorem idemE_mul_gen (v : Pl D) (α : Af D.host.F) (x : D.host.E) :
    idemE v * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x := by
  rw [idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idemE_smul_gen (v : Pl D) (α : Af D.host.F) (x : Fin T.rank → Fin S.rank → D.host.E) :
    idemE v • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
      Matrix.of fun i j => pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x i j := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]

theorem idemE_smul_mem (v : Pl D) {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    idemE v • u ∈ latO S T LS LT (· = v) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    have hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w := hα
    have hmem : idemF v * α ∈ intAf D.host.F := by
      simp only [intAf, Set.mem_setOf_eq]
      intro w
      rw [map_mul]
      refine mul_mem ?_ (hα' w)
      rw [evalV_idemF]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩
    rw [map_mul, evalV_idemF, if_neg hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.VacUnion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCut

variable {D : D7}

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem mt_mul (V : HSp D) (x y : GA D V) : mt V (x * y) = mt V x * mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) : Function.Injective (mt V) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) (D.sp.cm.sig)).toRingHom (a ⊗ₜ 1) = a ⊗ₜ 1
  simp

theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem entry_mem (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpOff V P) (i j : Fin V.rank) (u : Pl D) (hu : P u) :
    compAt D u ((mt V g - 1) i j) = 0 := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idOff D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idOff D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idOff D P) (mt V g i j) =
      Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V g - 1) i j ∈ idOff D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  unfold idOff at h4
  rw [Ideal.mem_iInf] at h4
  exact (RingHom.mem_ker).mp (h4 ⟨u, hu⟩)

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_of_placeIdem {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε = eFin D.host.F v := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  unfold eFin
  congr 1
  refine af_ext _ fun u => ?_
  by_cases hu : u = v
  · subst hu; rw [h1, evalV_single_same]
  · rw [h2 u hu, evalV_single_ne _ hu]

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_idem (v : Pl D) : eFin D.host.F v * eFin D.host.F v = eFin D.host.F v := by
  refine Prod.ext (mul_zero _) ?_
  change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
  refine af_ext _ fun u => ?_
  rw [map_mul]
  by_cases hu : u = v
  · subst hu; rw [evalV_single_same, mul_one]
  · rw [evalV_single_ne _ hu, mul_zero]

theorem compAt_eq (u : Pl D) (y : AE D) : compAt D u y = Algebra.TensorProduct.map (evalV D.host.F u) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := rfl

theorem baseAdele_ext_infinite_finite {a b : AF D.host.F} (h1 : fstA D.host.F a = fstA D.host.F b) (h2 : sndA D.host.F a = sndA D.host.F b) :
    a = b := Prod.ext h1 h2

open GlobalTheory.LocWeil.PlaceIdem in
theorem c_mul {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (a : AF D.host.F)
    (ha : ∀ u, u ∉ Set.range v → evalV D.host.F u (sndA D.host.F a) = 0) :
    (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * a = 0 := by
  classical
  have hf : ∀ w, fstA D.host.F (eFin D.host.F (v w)) = 0 := fun w => rfl
  have hs : ∀ w, sndA D.host.F (eFin D.host.F (v w)) = singleV D.host.F (v w) 1 := fun w => rfl
  have hp1 : fstA D.host.F (pairA D.host.F 1 0) = 1 := rfl
  have hp2 : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp1]
    simp [hf]
  · rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp2]
    simp only [hs, sub_zero]
    refine af_ext _ fun u => ?_
    rw [map_mul, map_zero, map_sub, map_one, map_sum]
    by_cases hu : u ∈ Set.range v
    · obtain ⟨w0, rfl⟩ := hu
      rw [Finset.sum_eq_single w0 (fun w _ hw => evalV_single_ne _ (fun e => hw (hv e).symm))
        (by simp), evalV_single_same, sub_self, zero_mul]
    · rw [ha u hu, mul_zero]

theorem repr_zero2 {F E A A' A'' ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing A'] [Algebra F A'] [CommRing A''] [Algebra F A''] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (f : A →ₐ[F] A') (g : A' →ₐ[F] A'') (y : A ⊗[F] E)
    (hy : Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) = 0) (k : ι) :
    g (f ((Algebra.TensorProduct.basis A b).repr y k)) = 0 := by
  rw [← GlobalTheory.InfZeroFinSum.repr_map_id b f, ← GlobalTheory.InfZeroFinSum.repr_map_id b g, hy, map_zero, Finsupp.zero_apply]

theorem key_gen {F E A ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (c : A) (y : A ⊗[F] E)
    (hy : ∀ k, c * (Algebra.TensorProduct.basis A b).repr y k = 0) : algebraMap A (A ⊗[F] E) c * y = 0 := by
  refine (Algebra.TensorProduct.basis A b).ext_elem fun k => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]
  exact hy k

open GlobalTheory.LocWeil.PlaceIdem in
theorem key {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (y : AE D)
    (hy : ∀ u, u ∉ Set.range v → compAt D u y = 0) :
    algebraMap (AF D.host.F) (AE D) (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => c_mul v hv _ fun u hu => ?_
  exact repr_zero2 (Module.finBasis D.host.F D.host.E) (sndA D.host.F) (evalV D.host.F u) y ((compAt_eq u y).symm.trans (hy u hu)) k

theorem idempotent_mul_entry_eq_zero_of_cut_inverse {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M N : Matrix (Fin n) (Fin n) R)
    (h1 : (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R)) * N = 1) (i j : Fin n) : E * (M * N - 1) i j = 0 := by
  have h2 : E • (M * N) = E • (1 : Matrix (Fin n) (Fin n) R) := by
    have h3 := congrArg (fun X => E • X) h1
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, hE] at h3
    have h4 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
    rw [h4, zero_smul, add_zero] at h3
    exact h3
  have := congrArg (fun X => X i j) h2
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  rw [Matrix.sub_apply, mul_sub, this, sub_self]

theorem idempotent_mul_cut_sub_one_entry {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    E * (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hE

theorem exists_widePullback_of_iteratedLine {R : Type} [CommRing R] {n : ℕ} (t : R) (M : Matrix (Fin n) (Fin n) R)
    (hk : ∀ i j, (1 - t) * (M - 1) i j = 0) : M = t • M + (1 - t) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  have := hk i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
  linear_combination this

theorem mt_list_prod (V : HSp D) {W : Type} (h : W → GA D V) (E : W → AE D)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hh : ∀ w, mt V (h w) = E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (horth : ∀ w w', w ≠ w' → E w * E w' = 0) :
    ∀ l : List W, l.Nodup → mt V ((l.map h).prod) = (l.map E).sum • M + (1 - (l.map E).sum) • 1
  | [], _ => by simp [mt_one]
  | w :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mt_mul, mt_list_prod V h E M hh horth l hl.2, hh, List.map_cons,
      List.sum_cons]
    apply cut_mul
    rw [← List.sum_map_mul_left]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact horth w y (fun e => hl.1 (e ▸ hy))

set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in

theorem prod_of_trivOff : ∀ (D : D7) (V : HSp D) (W : Type) [Fintype W] [DecidableEq W] (v : W → Pl D) (e : W → AE D),
    Function.Injective v → (∀ w, IsSplitIdem D (e w) ∧ ∃ ε, IsPlaceIdem D (v w) ε ∧
      e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε) →
    ∀ g ∈ grpOff V (fun x => x ∉ Set.range v), ∃ a ∈ GinfC V, ∃ h : W → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w w', w ≠ w' → Commute (h w) (h w')) ∧ (∀ w, Commute a (h w)) ∧
      g = a * (Finset.univ.toList.map h).prod ∧
      ∀ w, ∀ i j, (e w + cA D (e w)) * (mt V (g * (h w)⁻¹) - 1) i j = 0 := by
  intro D V W _ _ v e hv he g hg
  set E : W → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨_, ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  set r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) with hrdef
  have hrr : r * r = r := by
    rw [hrdef, ← map_mul]
    congr 1
    exact baseAdele_ext_infinite_finite (by rw [map_mul]; exact mul_one _) (by rw [map_mul]; exact mul_zero _)
  have hrE : ∀ w, r * E w = 0 := fun w => by
    rw [hrdef, hEdef, ← map_mul]
    have : pairA D.host.F 1 0 * eFin D.host.F (v w) = 0 :=
      baseAdele_ext_infinite_finite (by rw [map_mul, map_zero]; exact mul_zero _) (by rw [map_mul, map_zero]; exact zero_mul _)
    rw [this, map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  obtain ⟨a, ha⟩ := cut_exists V g r hrr (cA_algebraMap _)
  set M := mt V g with hM
  have hsum : (Finset.univ.toList.map E).sum = ∑ w, E w := Finset.sum_map_toList _ _
  refine ⟨a, ?_, h, ?_, ?_, ?_, ?_, ?_⟩
  · show finHom V a = 1
    have h0 : finPart D r = 0 := by
      rw [hrdef, finPart_algebraMap]
      exact TensorProduct.zero_tmul _ _
    apply Units.ext
    change (mt V a).map (finPart D) = 1
    rw [ha, GlobalTheory.GfCut.map_idem, h0, zero_smul, zero_add, sub_zero, one_smul]
  · intro w i j
    rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) M i j
  · intro w w' hww
    show h w * h w' = h w' * h w
    apply mt_injective
    rw [mt_mul, mt_mul, hh, hh, cut_mul _ _ (hEo w w' hww), cut_mul _ _ (hEo w' w (Ne.symm hww)), add_comm (E w)]
  · intro w
    show a * h w = h w * a
    apply mt_injective
    rw [mt_mul, mt_mul, hh, ha, cut_mul _ _ (hrE w), cut_mul _ _ (by rw [mul_comm]; exact hrE w), add_comm r]
  · apply mt_injective
    rw [mt_mul, mt_list_prod V h E M hh hEo _ (Finset.nodup_toList _), ha, hsum]
    have hrS : r * ∑ w, E w = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun w _ => hrE w
    rw [cut_mul _ _ hrS]
    have hk : ∀ i j, (1 - r - ∑ w, E w) * (M - 1) i j = 0 := fun i j => by
      have := key v hv ((M - 1) i j) (fun u hu => entry_mem V _ g hg i j u hu)
      rwa [map_sub, map_sub, map_one, map_sum] at this
    exact exists_widePullback_of_iteratedLine _ M fun i j => by rw [← sub_sub]; exact hk i j
  · intro w i j
    rw [hE w]
    have h1 : (E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) * mt V (h w)⁻¹ = 1 := by
      rw [← hh w, ← mt_mul, mul_inv_cancel, mt_one]
    rw [mt_mul]
    exact idempotent_mul_entry_eq_zero_of_cut_inverse _ (hEE w) _ _ h1 i j

end GlobalTheory.SplitCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartzStatement
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  first | exact @GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | exact GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | (intros; apply GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGramStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartanInv_standardInvolution_doubledGram : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ s : RealMat (dblSp A), IsStdInv A μ s → ∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (s τ) := by
  first | exact @GlobalTheory.CartStd.isCartanInv_stdInv | exact GlobalTheory.CartStd.isCartanInv_stdInv | (intros; apply GlobalTheory.CartStd.isCartanInv_stdInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  first | exact @GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | exact GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | (intros; apply GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms <;> assumption)
end

