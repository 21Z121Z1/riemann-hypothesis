import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNonsplitSignPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.FinSign

theorem ordL_eq_zero_of_v_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (h : Valued.v x = 1) : ordL x = 0 := by
  unfold ordL
  rw [dif_neg (by rw [h]; exact one_ne_zero)]
  simp [h]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  intro E _ _ _ hU n γ₀ H₀ _ _ hpos P₁
  obtain ⟨hd0, -⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine (GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 _ hd0)).subset ?_
  rintro w ⟨hw, hs⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0]
  intro h1
  apply hs
  unfold sgnOn
  have hv : Valued.v (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H₀
        (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))).det) = 1 :=
    (w.valuedAdicCompletion_eq_valuation' _).trans h1
  rw [aeval_map_mat, GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁), ordL_eq_zero_of_v_eq_one hv]
  simp

end GlobalTheory.CompanionTheory.FinSign
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecReindex

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_under (v : PlF E) : ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  refine ⟨⟨Q, hQmax.isPrime, ?_⟩, ?_⟩
  · rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  · ext1
    exact hQ

def secEquiv {S : Set (Pl E)} (hS : IsSection S) : S ≃ PlF E :=
  Equiv.ofBijective (fun w => w.1.under (𝓞 (maximalRealSubfield E))) (by
    constructor
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
      exact Subtype.ext ((hS u).unique ⟨hu, rfl⟩ ⟨hu', h.symm⟩)
    · intro v
      obtain ⟨w, rfl⟩ := exists_under v
      obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
      exact ⟨⟨u, hu⟩, huw⟩)

theorem secPl_eq {S : Set (Pl E)} (hS : IsSection S) (u : S) :
    secPl S (secEquiv hS u) = some u.1 := by
  have hv : secEquiv hS u = u.1.under (𝓞 (maximalRealSubfield E)) := rfl
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = secEquiv hS u := ⟨u.1, u.2, hv.symm⟩
  rw [secPl, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact congrArg some ((hS u.1).unique ⟨h1, h2.trans hv⟩ ⟨u.2, rfl⟩)

theorem reindex : Reindex := by
  intro E _ _ _ S hS g
  rw [show (∏ᶠ (w : Pl E) (_ : w ∈ S), g w) = ∏ᶠ u : S, g u from
    (finprod_set_coe_eq_finprod_mem S).symm]
  exact finprod_eq_of_bijective (secEquiv hS) (secEquiv hS).bijective
    (fun u => by rw [secPl_eq hS u] <;> rfl)

end GlobalTheory.CompanionTheory.SecReindex

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.EulerV

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finite_above (v : PlF E) : Finite (Above v) := by
  by_cases h : Nonempty (Above v)
  · obtain ⟨u⟩ := h
    refine Finite.of_injective (β := (GlobalTheory.EulerTw.orb E u.1 : Finset (Pl E)))
      (fun w => ⟨w.1, (GlobalTheory.EulerTwRestr.mem_orb_iff u.1 w.1).2 (w.2.trans u.2.symm)⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · haveI := not_nonempty_iff.1 h
    infer_instance

def pn (n : ℕ) (v : PlF E) : GL (Fin n) (Af E) →* GL (Fin n) (Av v) := GeneralLinearGroup.map (projv v)

def ev {v : PlF E} (w : Above v) : GL (Fin n) (Av v) →* GLw n w.1 :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)

def Kn (n : ℕ) (v : PlF E) : Subgroup (GL (Fin n) (Av v)) :=
  ⨅ w : Above v, (GlobalTheory.LFun.KGL w.1 n).comap (ev w)

theorem mem_Kn {v : PlF E} {y : GL (Fin n) (Av v)} : y ∈ Kn n v ↔ ∀ w : Above v, ev w y ∈ GlobalTheory.LFun.KGL w.1 n := by
  simp only [Kn, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem ev_pn {v : PlF E} (w : Above v) (g : GL (Fin n) (Af E)) :
    ev w (pn n v g) = GeneralLinearGroup.map (pLoc E w.1) g := rfl

theorem mem_Kv {a b : ℕ} {v : PlF E} {y : Yv a b v} : y ∈ Kv a b v ↔ y.1 ∈ Kn a v ∧ y.2 ∈ Kn b v := by
  simp only [Kv, Subgroup.mem_iInf, Subgroup.mem_comap, mem_Kn, Subgroup.mem_prod, forall_and]
  rfl

theorem mem_Kf_iff {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ v : PlF E, pn n v g ∈ Kn n v := by
  have h : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [h]
  refine ⟨fun H v => mem_Kn.2 fun w => H w.1, fun H w => ?_⟩
  exact mem_Kn.1 (H (w.under (𝓞 (maximalRealSubfield E)))) ⟨w, rfl⟩

theorem continuous_projv (v : PlF E) : Continuous (projv v) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval w.1

theorem continuous_pn (v : PlF E) : Continuous (pn n v) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_projv v))

theorem continuous_ev {v : PlF E} (w : Above v) : Continuous (ev (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

theorem isOpen_Kn (v : PlF E) : IsOpen (Kn n v : Set (GL (Fin n) (Av v))) := by
  haveI := finite_above v
  rw [Kn, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun w =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w.1 n).1.preimage (continuous_ev w)

theorem pn_ext {g h : GL (Fin n) (Af E)} (H : ∀ v : PlF E, pn n v g = pn n v h) : g = h :=
  GlobalTheory.EulerTwRestr.gl_ext fun w => by
    exact congrArg (ev ⟨w, rfl⟩) (H (w.under (𝓞 (maximalRealSubfield E))))

theorem eventually_mem_Kn (g : GL (Fin n) (Af E)) : ∀ᶠ v : PlF E in cofinite, pn n v g ∈ Kn n v := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  have hx : ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
    filter_upwards [h1, h2] with w h1 h2
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
      fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩
  refine eventually_cofinite.2 (((eventually_cofinite.1 hx).image
    fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, mem_Kn, not_forall, ev_pn] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem exists_lift (y : ∀ v : PlF E, GL (Fin n) (Av v)) (hy : ∀ᶠ v : PlF E in cofinite, y v ∈ Kn n v) :
    ∃ x : GL (Fin n) (Af E), ∀ v, pn n v x = y v := by
  let un : Pl E → PlF E := fun w => w.under (𝓞 (maximalRealSubfield E))
  let Y : ∀ w : Pl E, GLw n w := fun w => ev (⟨w, rfl⟩ : Above (un w)) (y (un w))
  have hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w n := by
    have hB := eventually_cofinite.1 hy
    refine eventually_cofinite.2 ((hB.biUnion fun v _ => Set.finite_coe_iff.1 (finite_above v)).subset ?_)
    intro w hw
    refine Set.mem_iUnion₂.2 ⟨un w, fun h => hw (mem_Kn.1 h ⟨w, rfl⟩), rfl⟩
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  refine ⟨⟨M, M', hMM', hM'M⟩, fun v => Units.ext (Matrix.ext fun i j => funext ?_)⟩
  rintro ⟨w, rfl⟩
  rfl

theorem exists_Kf_lift {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    ∃ x ∈ Kf E n, pn n v x = k := by
  have hm : ∀ u : PlF E, (Function.update (fun u : PlF E => (1 : GL (Fin n) (Av u))) v k) u ∈ Kn n u := by
    intro u
    by_cases h : u = v
    · subst h
      simpa using hk
    · simp [Function.update_of_ne h, one_mem]
  obtain ⟨x, hx⟩ := exists_lift _ (Eventually.of_forall hm)
  exact ⟨x, mem_Kf_iff.2 fun u => by rw [hx]; exact hm u, by rw [hx]; simp⟩

theorem isCompact_Kn (v : PlF E) : IsCompact (Kn n v : Set (GL (Fin n) (Av v))) := by
  have e : (Kn n v : Set (GL (Fin n) (Av v))) = pn n v '' (Kf E n : Set (GL (Fin n) (Af E))) := by
    ext k
    refine ⟨fun hk => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
      exact ⟨x, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact mem_Kf_iff.1 hg v
  rw [e]
  exact (GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).image (continuous_pn v)

theorem coe_Kv (a b : ℕ) (v : PlF E) : (Kv a b v : Set (Yv a b v)) =
    (Kn a v : Set (GL (Fin a) (Av v))) ×ˢ (Kn b v : Set (GL (Fin b) (Av v))) :=
  Set.ext fun _ => mem_Kv

theorem mem_prod_iff (a b : ℕ) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v := by
  rw [Subgroup.mem_prod, mem_Kf_iff, mem_Kf_iff]
  simp only [mem_Kv, forall_and]
  rfl

theorem isOpen_Kf : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isOpen_Kglob

theorem isCompact_Kf : IsCompact (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isCompact_Kglob

theorem coe_level (a b : ℕ) : {x : Gf E a b | ∀ v, pv a b v x ∈ Kv a b v} =
    (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
  Set.ext fun x => (mem_prod_iff a b x).symm

theorem isRestrGroup (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) := by
  refine ⟨fun w => w.elim, fun v => ?_, fun v => ?_, fun v => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · exact ((continuous_pn v).comp continuous_fst).prodMk ((continuous_pn v).comp continuous_snd)
  · rw [coe_Kv]
    exact (isOpen_Kn v).prod (isOpen_Kn v)
  · rw [coe_Kv]
    exact (isCompact_Kn v).prod (isCompact_Kn v)
  · exact Prod.ext (pn_ext fun v => congrArg Prod.fst (H v)) (pn_ext fun v => congrArg Prod.snd (H v))
  · filter_upwards [eventually_mem_Kn x.1, eventually_mem_Kn x.2] with v h1 h2
    exact mem_Kv.2 ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun v => (y v).1) (hy.mono fun v h => (mem_Kv.1 h).1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun v => (y v).2) (hy.mono fun v h => (mem_Kv.1 h).2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun v => Prod.ext (h₁ v) (h₂ v)⟩
  · rw [coe_level]
    exact isOpen_Kf.prod isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ v, pv a b v x ∈ Kv a b v} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← coe_level]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact isCompact_Kf.prod isCompact_Kf

theorem cjv_spec (hC : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hC E v
  rw [cjv, dif_pos h]
  exact h.choose_spec.2 x

theorem pn_thF (hC : CjEx) (n : ℕ) (v : PlF E) (x : GL (Fin n) (Af E)) :
    pn n v (thF E n x) = thetaGL n (cjv v) (pn n v x) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_spec hC v) x

theorem pv_thP (hC : CjEx) (a b : ℕ) (v : PlF E) (x : Gf E a b) :
    pv a b v (thP E a b x) = thv a b v (pv a b v x) :=
  Prod.ext (pn_thF hC a v x.1) (pn_thF hC b v x.2)

theorem theta_mem_Kn (hC : CjEx) {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    thetaGL n (cjv v) k ∈ Kn n v := by
  obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
  rw [← pn_thF hC]
  exact mem_Kf_iff.1 (GlobalTheory.EulerTwKU.thF_mem_Kglob x hx) v

theorem main : RestrV := fun hC E _ _ _ a b =>
  ⟨isRestrGroup a b, fun v x => pv_thP hC a b v x,
    fun v k hk => mem_Kv.2 ⟨theta_mem_Kn hC (mem_Kv.1 hk).1, theta_mem_Kn hC (mem_Kv.1 hk).2⟩,
    mem_prod_iff a b⟩

end GlobalTheory.CompanionTheory.EulerV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameCompletes
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FrameComplete

open Matrix

section Abstract

variable {A : Type*} [CommRing A] [StarRing A] {ι α β ρ τ : Type*}
  [Fintype ι] [Fintype α] [Fintype β] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem gram_conj {G : Matrix ι ι A} (hG : Gᴴ = G) (M : Matrix ι α A) (N : Matrix ι β A) :
    (Mᴴ * (G * N))ᴴ = Nᴴ * (G * M) := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem orth_part {G : Matrix ι ι A} (hG : Gᴴ = G) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e : A} {x : Matrix ι ρ A} {v : Matrix ι τ A} (hv : e • v = v)
    (hxx : xᴴ * (G * x) = e • B)
    (hq : vᴴ * (G * v) - (Bi * (xᴴ * (G * v)))ᴴ * (B * (Bi * (xᴴ * (G * v)))) = 0) :
    xᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 ∧
      (v - x * (Bi * (xᴴ * (G * v))))ᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 := by
  set c := xᴴ * (G * v) with hc
  set y := Bi * c with hy
  have hec : e • c = c := by
    conv_lhs => rw [hc, ← Matrix.mul_smul, ← Matrix.mul_smul, hv]
  have hBy : B * y = c := by rw [hy, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have h1 : xᴴ * (G * (v - x * y)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hc, ← Matrix.mul_assoc G, ← Matrix.mul_assoc, hxx,
      Matrix.smul_mul, hBy, hec, sub_self]
  refine ⟨h1, ?_⟩
  have h2 : (v - x * y)ᴴ * (G * x) = 0 := by
    rw [← gram_conj hG, h1, conjTranspose_zero]
  have h3 : (v - x * y)ᴴ * (G * v) = vᴴ * (G * v) - yᴴ * c := by
    rw [conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, Matrix.mul_assoc, ← hc]
  rw [Matrix.mul_sub, Matrix.mul_sub, h3, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * x), h2,
    Matrix.zero_mul, sub_zero, ← hBy]
  exact hq

theorem exists_dual {G Gi : Matrix ι ι A} (hG : Gᴴ = G) (hGi : G * Gi = 1)
    {e h : A} (he : e * e = e) (hse : star e = e) (hh : h + h = 1) (hsh : star h = h)
    {x : Matrix ι ρ A} {u : Matrix ι τ A} {L : Matrix τ ι A} (hu : e • u = u)
    (hxu : xᴴ * (G * u) = 0) (huu : uᴴ * (G * u) = 0) (hLx : L * x = 0) (hLu : L * u = e • 1) :
    ∃ w : Matrix ι τ A, e • w = w ∧ xᴴ * (G * w) = 0 ∧ uᴴ * (G * w) = e • 1 ∧ wᴴ * (G * w) = 0 := by
  set w₀ : Matrix ι τ A := Gi * (e • L)ᴴ with hw₀
  have hGw : G * w₀ = (e • L)ᴴ := by rw [hw₀, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hew : e • w₀ = w₀ := by
    rw [hw₀, ← Matrix.mul_smul, conjTranspose_smul, hse, smul_smul, he]
  have h1 : xᴴ * (G * w₀) = 0 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLx, smul_zero, conjTranspose_zero]
  have h2 : uᴴ * (G * w₀) = e • 1 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLu, smul_smul, he, conjTranspose_smul, hse,
      conjTranspose_one]
  have h3 : w₀ᴴ * (G * u) = e • 1 := by
    rw [← gram_conj hG, h2, conjTranspose_smul, hse, conjTranspose_one]
  set Q := w₀ᴴ * (G * w₀) with hQ
  have hQh : Qᴴ = Q := gram_conj hG w₀ w₀
  have heQ : e • Q = Q := by
    conv_lhs => rw [hQ, ← Matrix.mul_smul, ← Matrix.mul_smul, hew]
  have hP : (h • Q)ᴴ = h • Q := by rw [conjTranspose_smul, hsh, hQh]
  have hw : e • (w₀ - u * (h • Q)) = w₀ - u * (h • Q) := by
    rw [smul_sub, hew, ← Matrix.smul_mul, hu]
  have hxw : xᴴ * (G * (w₀ - u * (h • Q))) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h1, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), hxu,
      Matrix.zero_mul, sub_zero]
  have huw : uᴴ * (G * (w₀ - u * (h • Q))) = e • 1 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h2, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), huu,
      Matrix.zero_mul, sub_zero]
  refine ⟨w₀ - u * (h • Q), hw, hxw, huw, ?_⟩
  have h4 : w₀ᴴ * (G * (w₀ - u * (h • Q))) = Q - h • Q := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hQ, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), h3,
      Matrix.smul_mul, Matrix.one_mul, smul_comm, heQ]
  rw [conjTranspose_sub, Matrix.sub_mul, h4, conjTranspose_mul, hP, Matrix.mul_assoc, huw,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, heQ, sub_sub, ← add_smul, hh, one_smul, sub_self]

theorem gram_three {G : Matrix ι ι A} {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (x : Matrix ι κ₁ A) (u : Matrix ι κ₂ A) (w : Matrix ι κ₃ A) :
    (fromCols (fromCols x u) w)ᴴ * (G * fromCols (fromCols x u) w) =
      fromBlocks (fromBlocks (xᴴ * (G * x)) (xᴴ * (G * u)) (uᴴ * (G * x)) (uᴴ * (G * u)))
        (fromRows (xᴴ * (G * w)) (uᴴ * (G * w)))
        (fromCols (wᴴ * (G * x)) (wᴴ * (G * u))) (wᴴ * (G * w)) := by
  ext (( i | i) | i) ((j | j) | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]

end Abstract

def gam {K ρ τ : Type*} [Zero K] [One K] [DecidableEq τ] (b : Matrix ρ ρ K) :
    Matrix ((ρ ⊕ τ) ⊕ τ) ((ρ ⊕ τ) ⊕ τ) K :=
  fromBlocks (fromBlocks b 0 0 0) (fromRows 0 1) (fromCols 0 1) 0

theorem gam_map {K L ρ τ : Type*} [Semiring K] [Semiring L] [DecidableEq τ] (f : K →+* L)
    (b : Matrix ρ ρ K) : (gam (τ := τ) b).map f = gam (b.map f) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply, apply_ite f]

theorem gam_det {K : Type*} [Field K] {r t : ℕ} (b : Matrix (Fin r) (Fin r) K) (hb : b.det ≠ 0) :
    (gam (τ := Fin t) b).det ≠ 0 := by
  have hinv : ∀ i j, ∑ a, b⁻¹ i a * b a j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine Matrix.det_ne_zero_of_left_inverse (B := gam (τ := Fin t) b⁻¹) ?_
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [gam, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hinv]

section Involution

variable {A : Type} [CommRing A] {ι ρ τ : Type} [Fintype ι] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem complete_frame (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {G Gi : Matrix ι ι A}
    (hG : (G.map σ)ᵀ = G) (hGi : G * Gi = 1) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e h : A} (he : e * e = e) (hse : σ e = e) (hh : h + h = 1) (hsh : σ h = h)
    {x : Matrix ι ρ A} {v : Matrix ι τ A} {L : Matrix τ ι A} (hx : e • x = x) (hv : e • v = v)
    (hxx : (x.map σ)ᵀ * (G * x) = e • B)
    (hq : (v.map σ)ᵀ * (G * v) - ((Bi * ((x.map σ)ᵀ * (G * v))).map σ)ᵀ *
      (B * (Bi * ((x.map σ)ᵀ * (G * v)))) = 0)
    (hLx : L * x = 0) (hLv : L * v = e • 1) :
    ∃ N : Matrix ι ((ρ ⊕ τ) ⊕ τ) A, e • N = N ∧ (N.map σ)ᵀ * (G * N) = e • gam B ∧
      (∀ i j, N i (Sum.inl (Sum.inl j)) = x i j) ∧
      ∀ i j, N i (Sum.inl (Sum.inr j)) = (v - x * (Bi * ((x.map σ)ᵀ * (G * v)))) i j := by
  letI : StarRing A :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hmap : ∀ {α β : Type} (M : Matrix α β A), (M.map σ)ᵀ = Mᴴ := fun M => by
    ext i j; rfl
  simp only [hmap] at hG hxx hq ⊢
  obtain ⟨hxu, huu⟩ := orth_part hG hB hv hxx hq
  set u : Matrix ι τ A := v - x * (Bi * (xᴴ * (G * v))) with hu
  have heu : e • u = u := by
    have hy : e • (x * (Bi * (xᴴ * (G * v)))) = x * (Bi * (xᴴ * (G * v))) := by
      rw [← Matrix.smul_mul, hx]
    rw [hu, smul_sub, hv, hy]
  have hLu : L * u = e • 1 := by
    rw [hu, Matrix.mul_sub, hLv, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]
  obtain ⟨w, hew, hxw, huw, hww⟩ :=
    exists_dual hG hGi he (show star e = e from hse) hh (show star h = h from hsh) heu hxu huu hLx hLu
  refine ⟨fromCols (fromCols x u) w, ?_, ?_, fun i j => rfl, fun i j => rfl⟩
  · ext i ((j | j) | j)
    · simpa using congrFun (congrFun hx i) j
    · simpa using congrFun (congrFun heu i) j
    · simpa using congrFun (congrFun hew i) j
  · have hux : uᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxu, conjTranspose_zero]
    have hwx : wᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxw, conjTranspose_zero]
    have hwu : wᴴ * (G * u) = e • 1 := by
      rw [← gram_conj hG, huw, conjTranspose_smul, conjTranspose_one]
      exact congrArg (· • (1 : Matrix τ τ A)) hse
    rw [gram_three, hxx, hxu, huu, hxw, huw, hww, hux, hwx, hwu]
    ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply]

end Involution

theorem frame_completes : ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ e : AE D, e * e = e → cA D e = e → ∃ Γ : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) D.host.E, Γ.det ≠ 0 ∧ ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z → (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0) → ∃ N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D), e • N = N ∧ (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) = e • Γ.map (incA D) ∧ (∀ i j, N i (Sum.inl (Sum.inl j)) = z.1 i j) ∧ ∀ i j, N i (Sum.inl (Sum.inr j)) = (z.2 - mm z.1 (yv V b₀ z)) i j := by
  intro D r t V b₀ hb e he hse
  refine ⟨gam b₀.1, gam_det _ hb, ?_⟩
  rintro ⟨x, v⟩ ⟨L₁, L₂, -, -, h21, h22⟩ ⟨hx, hv, hxx, hq⟩
  have hdet : IsUnit (HSpace.gram V).det := isUnit_iff_ne_zero.2 (isHermND_gram V).2
  have hGi : gA V * giA V = 1 := by
    have := rat_mul (D := D) (HSpace.gram V) (HSpace.gram V)⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet] at this
    exact this.symm.trans (by simp [rat])
  have hB : rat (D := D) b₀.1 * rat b₀.1⁻¹ = 1 := by
    have := rat_mul (D := D) b₀.1 b₀.1⁻¹
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb)] at this
    exact this.symm.trans (by simp [rat])
  have hh : incA D 2⁻¹ + incA D 2⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hsh : cA D (incA D 2⁻¹) = incA D 2⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_ofNat]
  obtain ⟨N, h1, h2, h3, h4⟩ := complete_frame (cA D) cA_cA (G := gA V) (Gi := giA V) (adj_gA V) hGi
    hB he hse hh hsh (x := x) (v := v) (L := L₂) hx hv hxx hq h21 h22
  refine ⟨N, h1, ?_, h3, h4⟩
  rw [gam_map]
  exact h2

end GlobalTheory.CompanionTheory.FrameComplete
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_sum_nondegenerate_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem <;> assumption)
end

