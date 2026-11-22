import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShifted
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.OneSide

section Abstract

variable {n : ℕ} {Y S M : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup M] [Module ℂ M]

theorem exists_shift (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (hA : Formalism.REAL.GlRel A) (hB : Formalism.REAL.GlRel B) (L : Y → M →ₗ[ℂ] S) (lam : Fin n → Fin n → ℂ)
    (h : ∀ i j y f, A i j (L y f) = L y (B i j f + lam i j • f)) :
    ∃ c : ℂ, ∀ i j y f, A i j (L y f) =
      L y ((B i j + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) f) := by
  by_cases h0 : ∀ y f, L y f = 0
  · exact ⟨0, fun i j y f => by rw [h0, h0, map_zero]⟩
  push Not at h0
  obtain ⟨y, f, h0⟩ := h0
  have key : ∀ i j k l, (if j = k then lam i l else 0) = (if l = i then lam k j else 0) := by
    intro i j k l
    have h1 : (A i j * A k l - A k l * A i j) (L y f) = L y ((B i j * B k l - B k l * B i j) f) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, h, map_add, map_smul, map_sub, smul_add]
      module
    rw [hA, hB] at h1
    have h2 : ((if j = k then lam i l else 0) - (if l = i then lam k j else 0)) • L y f = 0 := by
      rw [sub_smul]
      split_ifs at h1 ⊢ <;>
        simp only [LinearMap.sub_apply, LinearMap.zero_apply, h, map_add, map_smul, map_sub, map_zero,
          zero_smul] at h1 ⊢ <;>
        linear_combination (norm := module) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0)
  rcases n with _ | n
  · exact ⟨0, fun i => i.elim0⟩
  refine ⟨lam 0 0, fun i j y f => ?_⟩
  rw [h]
  by_cases c : i = j
  · subst c
    have := key i 0 0 i
    simp only [if_true] at this
    simp [this]
  · have := key i i i j
    simp only [if_true, if_neg (Ne.symm c)] at this
    simp [this, c]

theorem prod_intertwine (L : M →ₗ[ℂ] S) : ∀ (k : ℕ) (a : Fin k → Module.End ℂ S) (b : Fin k → Module.End ℂ M),
    (∀ i f, a i (L f) = L (b i f)) → ∀ f, (List.ofFn a).prod (L f) = L ((List.ofFn b).prod f)
  | 0, _, _, _, f => by simp
  | k + 1, a, b, e, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      prod_intertwine L k _ _ fun i => e i.succ, e]

theorem gelfA_intertwine (L : M →ₗ[ℂ] S) (A : Fin n → Fin n → Module.End ℂ S) (B : Fin n → Fin n → Module.End ℂ M)
    (h : ∀ i j f, A i j (L f) = L (B i j f)) (k : ℕ) (f : M) :
    GlobalTheory.SmoothForms.gelfA A k (L f) = L (GlobalTheory.SmoothForms.gelfA B k f) := by
  rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_intertwine L _ _ _ (fun _ => h _ _) f

end Abstract

theorem gelf_kernel : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  intro D θ hθ V Y M _ _ κ hκ τ Q hQ hd
  choose lam hlam using hd
  have hR : ∀ X (hX : X ∈ lieAt V τ) f y, Rder θ V τ X (κ f y) = κ (Q X f + lam X hX • f) y :=
    fun X hX f y => funext fun g => (hlam X hX f y g).deriv
  have hC : ∀ Z, ∃ l : ℂ, ∀ f y, RderC θ V τ Z (κ f y) = κ (Q Z f + l • f) y := by
    intro Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    refine ⟨lam _ h1 + Complex.I * lam _ h2, fun f y => ?_⟩
    rw [RderC, hR _ h1, hR _ h2]
    have e := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    generalize lam _ h1 = a
    generalize lam _ h2 = b
    generalize (1 / 2 : ℂ) • (Z + conjAt V τ Z) = P at e ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) = P' at e ⊢
    rw [← e]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply]
    module
  choose l hl using hC
  let L : Y → M →ₗ[ℂ] SmFun θ V := fun y =>
    LinearMap.codRestrict (SmFun θ V) ((LinearMap.proj y).comp κ) fun f => hκ f y
  obtain ⟨c, hc⟩ := exists_shift _ _ (glRel_derEnd hθ V τ) hQ L (fun i j => l (Matrix.single i j 1))
    fun i j y f => Subtype.ext (hl _ f y)
  refine ⟨c, fun k f y => ?_⟩
  have := gelfA_intertwine (L y) _ (fun i j => Q (Matrix.single i j 1) +
    if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) (fun i j => hc i j y) k f
  exact (GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (L y f)).trans (congrArg Subtype.val this)

end GlobalTheory.Mem.Lift.OneSide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SJ.PairMain

theorem op_ramCrd_eq {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : St.LevelSubgroupCharacter) (w u : D.what₂.Word) (hw : w = u)
    (p : PerW St hK w) (q : PerW St hK u) (hpq : HEq p q) {n : ℕ} (b : Fin n → (D.mem w).A.Mram) (c : Fin n → ℂ)
    (φ : (D.mem u).A.Mram) (hc : HEq (∑ i, c i • b i) φ) (T : Cu St u hK)
    (hT : colDictL St q.Tr hK T = ((φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    (((p.op (ramCrd b c) : HHX St)) : L2X St) = PuFun St u hK q.Dt T := by
  subst hw
  obtain rfl := eq_of_heq hpq
  obtain rfl := eq_of_heq hc
  have h1 : ramCrd b c = Submodule.inclusion inf_le_left (∑ i, c i • b i) := by
    show Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ b c) = _
    rw [Fintype.linearCombination_apply]
    rfl
  have h2 : (colDict St p.Tr hK p.hI p.hB).symm (Submodule.inclusion inf_le_left (∑ i, c i • b i)) = T := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [colDict_apply, hT]
    rfl
  rw [h1]
  simp only [PerW.op, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2]
  rfl

theorem pair_step : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  intro D Bs A X fc s R cr M St G hK pw wdD bR hw hSp hb
  generalize (fc X.zs).Sp = SP at hSp ⊢
  subst hSp
  intro sEE sEEc hE j κ₀ hκ₀ hout u
  obtain rfl := eq_of_heq hE
  refine ⟨starRingEnd ℂ κ₀, (map_ne_zero _).2 hκ₀, ?_⟩
  intro F φ T hT
  refine (Pair.inner_tw_of_smul (E := HHX St) s (sEE (M.eR F) : Tw s (HHX St))
    ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ)) : Tw s (HHX St)) κ₀
    ((conjHH St G (j F) : HHX St)) (hout F)).trans ?_
  congr 2
  have hcc : cjVec s _ (cjv s (M.cφ u φ)) = M.cφ u φ := funext fun i => cj_cj s _
  have hP : Tw.out (s := s) ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ))) =
      (pw (wdD (R.wU u))).op (ramCrd (bR (R.wU u)) (M.cφ u φ)) :=
    (spOf_Pu s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR (R.wU u) (cjv s (M.cφ u φ))).trans (by rw [hcc])
  have key := op_ramCrd_eq St hK _ u (hw u) _ _ (congr_arg_heq pw (hw u)) (bR (R.wU u)) (M.cφ u φ) _
    (Pair.sum_coord_heq M u _ (hw u) (bR (R.wU u)) (hb u) φ) T hT
  rw [Submodule.coe_inner]
  exact congrArg _ ((congrArg Subtype.val hP).trans key)

end GlobalTheory.Mem.SJ.PairMain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFie
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense

namespace GlobalTheory.CuspRep.CsdInf

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem star_expU (z : Cinf L) :
    Units.map (starRingEnd (Cinf L)).toMonoidHom (expU z) = expU (star z) :=
  Units.ext (funext fun w => by
    change starRingEnd ℂ (Complex.exp (z w)) = Complex.exp (star (z w))
    rw [← Complex.exp_conj]
    rfl)

theorem lie_iff (χ : HChar L) :
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  constructor
  · intro h u
    obtain ⟨z, rfl⟩ : ∃ z, expU z = u := ⟨_, expU_log u⟩
    rw [star_expU, ← expU_add]
    apply Units.ext
    have h1 := h z
    rw [map_neg] at h1
    rw [chiInf_expU, map_add, ← h1, neg_add_cancel, Complex.exp_zero, Units.val_one]
  · intro h z
    have h1 : ∀ t : ℝ, Complex.exp (t * dchi χ (z + star z)) = 1 := fun t => by
      have h2 := h (expU (t • z))
      rw [star_expU, ← expU_add, star_smul, star_trivial, ← smul_add] at h2
      rw [← Complex.real_smul, ← map_smul, ← chiInf_expU, h2, Units.val_one]
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (z + star z))) (dchi χ (z + star z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (z + star z))).cexp
    rw [funext h1] at h2
    have h3 := h2.unique (hasDerivAt_const _ _)
    rw [map_add] at h3
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h3).symm

theorem inf_eq (χ : HChar L) (k : Lˣ) :
    χ.inf k = chiInf χ (Units.map (pInf L).toMonoidHom (diagUnits L k)) := by
  rw [HChar.inf, chiInf, MonoidHom.comp_apply, MonoidHom.comp_apply, NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem pInf_conj (k : Lˣ) :
    Units.map (pInf L).toMonoidHom (diagUnits L (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k)) =
      Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map (pInf L).toMonoidHom (diagUnits L k)) :=
  Units.ext (pInf_complexConj (k : L))

theorem field_iff (χ : HChar L) :
    (∀ k : Lˣ, χ.inf (Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj L)).toMonoidHom k) = (χ.inf k)⁻¹) ↔
      ∀ u : (Cinf L)ˣ, chiInf χ (u * Units.map (starRingEnd (Cinf L)).toMonoidHom u) = 1 := by
  classical
  constructor
  · intro h u
    let q : Loc (∅ : Finset (HeightOneSpectrum (𝓞 L))) →* Cinf L := (pInf L).toMonoidHom.comp (incl ∅)
    have hq : Continuous q := (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst) : Continuous fun y w => q y w)
    have h2 : ∀ y, chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1 :=
      fun y => (denseRange_units ∅).induction_on
        (p := fun y => chiInf χ (Units.map q y * Units.map (starRingEnd (Cinf L)).toMonoidHom (Units.map q y)) = 1) y
        (isClosed_eq ((continuous_chiInf χ).comp ((hq.units_map _).mul
          ((Continuous.units_map _ continuous_star).comp (hq.units_map _)))) continuous_const) fun k => by
        have e : Units.map q (Units.map (proj ∅) (diagUnits L k)) = Units.map (pInf L).toMonoidHom (diagUnits L k) := rfl
        rw [e, ← pInf_conj, map_mul, ← inf_eq, ← inf_eq, h k, mul_inv_cancel]
    have h3 := h2 (Units.map (proj ∅) (infId L u))
    have e : Units.map q (Units.map (proj ∅) (infId L u)) = u := Units.ext (by
      change (infEq L).symm (1 - infEq L 1 + infEq L u) = u
      simp)
    rwa [e] at h3
  · intro h k
    have h1 := h (Units.map (pInf L).toMonoidHom (diagUnits L k))
    rw [← pInf_conj, map_mul, ← inf_eq, ← inf_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1

end GlobalTheory.CuspRep.CsdInf

open GlobalTheory.CuspRep.CsdInf in

theorem GlobalTheory.CuspRep.csdInf_iff : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
      ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have e : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      Units.map (AlgEquiv.toRingEquiv (IsCMField.complexConj H.E)).toMonoidHom k :=
    fun k => Units.ext (host_complexConj H k).symm
  show (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹
  simp only [e]
  exact (lie_iff χ).trans (field_iff χ).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JIota

theorem heq_iota_iff_eq_trans_castAdelicGroup (D : D7) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) :
    HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔
      ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  rw [heq_iff_eq]
  constructor
  · intro e; subst e; rfl
  · intro e; subst e; rfl

theorem heq_iota_iff : ∀ (D : D7) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA), HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ↔ ι = (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv :=
  fun D St h ι => heq_iota_iff_eq_trans_castAdelicGroup D St.B.I h ι

end GlobalTheory.Mem.JIota
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 8000000 in
theorem chart_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : Ch i),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
      P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
      (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i h1 h2 β
  obtain ⟨k, hk⟩ := hS.mid i h1 h2
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS i (le_of_succ_m h2) (F.ch i h1 h2 β) (F.glevC i h1 h2 β) (hk.lb β)
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) i (le_of_succ_m h2) (Equiv.refl _) (fun c : {c // chOf i c = β} => (I.rec7 l Z).clsLat u i c.1)
    (F.ch i h1 h2 β) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := hy, st_eq := hst }⟩

set_option maxHeartbeats 8000000 in
theorem top_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hm : i ≤ (I.rec7 l Z).R.m) (him : i = (I.rec7 l Z).R.m) (β : Ch i) (hβ : ∀ c, chOf i c = β),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
      P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
      (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i hm him β hβ
  subst him
  obtain ⟨k, hk⟩ := hS.ends _ hm (Or.inr rfl)
  obtain ⟨L, hLb, hUl, hU⟩ := GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel I hOk hP l Z u F hS _ hm ((F.cls _ hm (Or.inr rfl)).toChart) F.glevM (hk.lb ())
  obtain ⟨C, hy, hst⟩ := GlobalTheory.T.hermitianClassCondition_of_chartClasses (I.rec7 l Z) _ hm (Equiv.subtypeUnivEquiv hβ) (fun c => (I.rec7 l Z).clsLat u _ c)
    ((F.cls _ hm (Or.inr rfl)).toChart) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := fun c => hy ⟨c, hβ c⟩, st_eq := fun c => hst ⟨c, hβ c⟩ }⟩

set_option maxHeartbeats 8000000 in
theorem level_classes_of {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
    (hS : I.StdF l Z u F) (hU : Nonempty (Unique (Ch (I.rec7 l Z).R.m))) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : Ch i) :
    ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
      (∀ h2 : i + 1 ≤ (I.rec7 l Z).R.m,
        SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
          P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
          (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1)) ∧
      (∀ (him : i = (I.rec7 l Z).R.m) (hβ : ∀ c, chOf i c = β),
        SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
          P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
          (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1)) := by
  by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
  · obtain ⟨P, hP2⟩ := chart_level_classes I hOk hP l Z u F hS i h1 h2 β
    exact ⟨P, fun _ => hP2, fun him _ => absurd h2 (by omega)⟩
  · have him : i = (I.rec7 l Z).R.m := by omega
    have hβ : ∀ c, chOf i c = β := by
      intro c
      subst him
      obtain ⟨U⟩ := hU
      exact Subsingleton.elim _ _
    obtain ⟨P, hP3⟩ := top_level_classes I hOk hP l Z u F hS i hm him β hβ
    exact ⟨P, fun h => absurd h h2, fun _ _ => hP3⟩

set_option maxHeartbeats 8000000 in
theorem hermColsCh_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  intro B X I hOk hP l Z Ch chOf F hf hm hS
  have L0 := fun u => GlobalTheory.T.columnLevel_of_stepZeroFormsLevel_trueColumns I hOk hP l Z u (F u) (hS u)
  have LP := fun u i h1 hm' β => level_classes_of I hOk hP l Z u (F u) (hS u) (hm u) i h1 hm' β
  have LF := fun u v => GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns I hOk hP l Z u (F u) (hS u) v
  refine ⟨fun u => (L0 u).choose, fun u i h1 hm' β => (LP u i h1 hm' β).choose.1,
    fun u i h1 hm' β => (LP u i h1 hm' β).choose.2, fun u => (F u).atT.eV, fun u v => (LF u v).choose, ?_⟩
  exact {
    eV := fun u => rfl
    fv := fun u v a => (LF u v).choose_spec a
    car0 := fun u => (L0 u).choose_spec.1
    carC := fun u i h1 h2 β => (LP u i h1 (le_of_succ_m h2) β).choose_spec.1 h2
    carM := fun u => (LP u _ (one_le_m _) le_rfl _).choose_spec.2 rfl (fun c => @Unique.eq_default _ (hm u).some (chOf u _ c))
    sp := fun u => (L0 u).choose_spec.2.1
    fr0 := fun u => (L0 u).choose_spec.2.2 }

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSide_classes_eq_formClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.clsP_hermitian | exact GlobalTheory.Mem.Col2.HAt.clsP_hermitian | (intros; apply GlobalTheory.Mem.Col2.HAt.clsP_hermitian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.primes_over_level_place | exact GlobalTheory.Mem.Col2.HAt.primes_over_level_place | (intros; apply GlobalTheory.Mem.Col2.HAt.primes_over_level_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_pullback : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), N.j ≫ π = M.j → ∀ (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced N (L.pull π hπ) k cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPull.induced_pull | exact GlobalTheory.TrueGeo.InducedPull.induced_pull | (intros; apply GlobalTheory.TrueGeo.InducedPull.induced_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.IndScale

section Values

variable {k K : Type} [Field k] [Field K] {Z : Scheme.{0}} [IsIntegral Z] (p : Z ⟶ Sp k)

theorem unitAt_constFn (x : Z) {a : k} (ha : a ≠ 0) : UnitAt x (Cartier.constFn p a) :=
  unitAt_fnOf (U := ⊤) (x := x) trivial trivial (ha.isUnit.map (algX p ⊤)).unit

theorem valAt_constFn (φ : k →+* K) (y : Sp K ⟶ Z) (hy : y ≫ p = spMap φ) (a : k) :
    valAt y (Cartier.constFn p a) = φ a := by
  have h := OfModel.valAt_fnOf y (U := ⊤) trivial le_top (algX p ⊤ a)
  refine h.trans ?_
  have e1 : p.appLE ⊤ ⊤ le_top ≫ y.appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp only [hy]
    rfl
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ ⊤ le_top ≫ y.appLE ⊤ ⊤ le_top ≫
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc (p.appLE ⊤ ⊤ le_top), e1, e2, Iso.inv_hom_id_assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

theorem valAt_ne_zero (y : Sp K ⟶ Z) {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [OfModel.valAt_algebraMap]
  exact (ha.map _).ne_zero

theorem ratVal_constFn {σ : k →+* ℂ} (y : CxPts p σ) (a : k) :
    ratVal (Cartier.constFn p a) y = σ a :=
  (ratVal_fnOf (y := y) mem_ptsIn_top trivial (algX p ⊤ a)).trans (ev_algX mem_ptsIn_top a)

end Values

theorem induced_shift : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (b : 𝓞 F), b ≠ 0 →
    ∀ ht : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖, A.Induced M L k cf →
    A.Induced M (L.shift (fun σ => Real.log ‖σ b‖) ht) k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  intro F _ _ C Y A M L k cf b hb ht ⟨hfin, r, hr, hinf, hv⟩
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hb
  have hu (x : Y.X) := unitAt_constFn Y.str x hb'
  let c : Y.Fnˣ := Units.mk0 (Cartier.constFn Y.str (algebraMap (𝓞 F) F b)) (hu (genericPoint Y.X)).ne_zero
  have hc : (c : Y.Fn) = Cartier.constFn Y.str (algebraMap (𝓞 F) F b) := rfl
  refine ⟨?_, fun i => r i * c, ⟨hr.isLB, (hr.add_principal c).isRatSec, fun i x hx => ?_⟩, ?_, ?_⟩
  · refine (hfin.union (sum_log_embedding_add_finsum_log_adicAbv_eq_zero F _ hb').1).subset fun v h => ?_
    by_contra h'
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h'
    exact h (by simp only [h'.1, h'.2, zero_div, add_zero])
  · refine (hr.isEqn i x hx).iff_unitAt.2 ?_
    rw [Units.val_mul, mul_div_cancel_left₀ _ (r i).ne_zero]
    exact hu x
  · intro σ y y' i f hy hi hf
    have h₁ : RegAt (under y) (f * (r i : Y.Fn)) := (hr.isEqn i _ hi).regularAt_iff.1 hf
    have h₂ : 0 < ‖σ (algebraMap (𝓞 F) F b)‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb')
    refine (hinf σ y y' i f hy hi hf).trans ?_
    change _ = ‖ratVal (f * ((r i : Y.Fn) * (c : Y.Fn))) y‖ ^ 2 *
      Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * Real.log ‖σ (algebraMap (𝓞 F) F b)‖))
    rw [← mul_assoc, hc, ratVal_mul h₁ (hu _).regAt, ratVal_constFn, norm_mul, neg_add, Real.exp_add,
      Real.exp_neg (2 * _), show (2 : ℝ) * Real.log ‖σ (algebraMap (𝓞 F) F b)‖ =
        Real.log (‖σ (algebraMap (𝓞 F) F b)‖ ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos h₂ 2)]
    field_simp
  · intro v e y yt i h hi
    have h₁ : below y.1 ∈ (L.B.pull M.j).U i := OfModel.le_chart M L.B e y yt h hi trivial
    have h₂ : UnitAt (below y.1) (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
      have := ((A.D.exists_isEqn (below y.1)).choose_spec.nsmul k).iff_unitAt.1 (hr.isEqn i _ h₁)
      rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    refine (hv v e y yt i h hi).trans ?_
    rw [← mul_assoc, Units.val_mul _ c, hc, OfModel.valAt_mul _ h₂.regAt (hu _).regAt,
      valAt_constFn Y.str _ y.1 y.2, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (valAt_ne_zero _ h₂)) (AbsoluteValue.ne_zero _ hb')]
    field_simp
    ring

end GlobalTheory.TrueGeo.IndScale
end
end

