import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.map (pLoc E w) g).1 i j = pLoc E w (g.1 i j) := rfl

theorem loc_inv_val (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (pLoc E w) g)⁻¹).1 i j = pLoc E w ((g⁻¹).1 i j) := by
  rw [← map_inv]; rfl

theorem gl_ext {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g = Matrix.GeneralLinearGroup.map (pLoc E w) h) :
    g = h :=
  Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w =>
    congrArg (fun x : GLw n w => x.1 i j) (H w)))

theorem mem_KGL_iff {w : Pl E} {x : GLw n w} : x ∈ GlobalTheory.LFun.KGL w n ↔
    (∀ i j, x.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (x⁻¹).1 i j ∈ w.adicCompletionIntegers E :=
  GlobalTheory.AdelicU.mem_GLint_iff

theorem mem_Kglob {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    g ∈ Kglob E n ↔ ∀ w : Pl E, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  simp only [Kglob, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem coe_Kglob : (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    (PIW.ClassFinD.KGL E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  ext g
  change g ∈ Kglob E n ↔ PIW.ClassFinD.MatInt g.val ∧ PIW.ClassFinD.MatInt (g⁻¹).val
  rw [mem_Kglob]
  simp only [mem_KGL_iff, loc_val, loc_inv_val]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

theorem isCompact_Kglob : IsCompact (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  rw [coe_Kglob]; exact GlobalTheory.isCompact_KGL E n

theorem isOpen_Kglob : IsOpen (Kglob E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := by
  have hO : IsOpen ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} := by
    have e : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) | PIW.ClassFinD.MatInt M} =
        ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) => M i j) ⁻¹'
          ((PIW.ClassFinD.Ohat E : Subring (FiniteAdeleRing (𝓞 E) E)) : Set (FiniteAdeleRing (𝓞 E) E)) := by
      ext M; simp [PIW.ClassFinD.MatInt]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((continuous_apply j).comp (continuous_apply i))
  rw [coe_Kglob]
  exact (hM.preimage Units.continuous_val).inter (hM.preimage Units.continuous_coe_inv)

theorem mem_orb_iff (u w : Pl E) :
    w ∈ orb E u ↔ w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  rw [orb, Finset.mem_insert, Finset.mem_singleton, GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact GlobalTheory.SplitPts.conjPl_self_conjSrc u
  · have e := eq_conjSrc h
    change w = conjSrc (IsCMField.complexConj E).toRingEquiv u
    rw [e]
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm

theorem existsUnique_orb {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) : ∃! u, u ∈ S ∧ w ∈ orb E u := by
  obtain ⟨u, ⟨huS, hu⟩, huniq⟩ := hS w
  exact ⟨u, ⟨huS, (mem_orb_iff u w).2 hu.symm⟩,
    fun u' h => huniq u' ⟨h.1, ((mem_orb_iff u' w).1 h.2).symm⟩⟩

end GlobalTheory.EulerTwRestr

namespace GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (pLoc E w) (prjG E n T g) =
      if w ∈ T then Matrix.GeneralLinearGroup.map (pLoc E w) g else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [loc_val]
  have he : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl
  change pLoc E w ((idem E T • g.1 + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) i j) = _
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
    map_sub, map_one, he]
  split_ifs with h
  · rw [one_mul, sub_self, zero_mul, add_zero, loc_val]
  · rw [zero_mul, zero_add, sub_zero, one_mul, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem prjG_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    prjG E n T (prjG E n T g) = prjG E n T g :=
  gl_ext fun w => by rw [loc_prjG, loc_prjG]; split_ifs with h <;> simp [loc_prjG, h]

theorem loc_eq_one_of_mem_Gam {u w : Pl E} {y : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} (hy : y ∈ Gam E n u)
    (hw : w ∉ orb E u) : Matrix.GeneralLinearGroup.map (pLoc E w) y = 1 := by
  obtain ⟨g, rfl⟩ := hy
  rw [loc_prjG, if_neg hw]

theorem pfU_val (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (pfU E n u g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) = prjG E n (orb E u) g := rfl

theorem mem_KU_pfU {u : Pl E} {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)} :
    pfU E n u g ∈ KU E n u ↔ ∀ w ∈ orb E u, Matrix.GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w n := by
  rw [show KU E n u = (Kglob E n).subgroupOf (Gam E n u) from rfl, Subgroup.mem_subgroupOf, pfU_val, mem_Kglob]
  refine ⟨fun h w hw => ?_, fun h w => ?_⟩
  · have := h w
    rwa [loc_prjG, if_pos hw] at this
  · rw [loc_prjG]
    split_ifs with hw
    · exact h w hw
    · exact one_mem _

theorem continuous_prjM (T : Finset (Pl E)) : Continuous (prjM E n T) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) =>
    idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
  exact (continuous_const_smul _).add continuous_const

theorem continuous_prjG (T : Finset (Pl E)) : Continuous (prjG E n T) :=
  Units.continuous_iff.2 ⟨(continuous_prjM T).comp Units.continuous_val,
    (continuous_prjM T).comp Units.continuous_coe_inv⟩

theorem continuous_pfU (u : Pl E) : Continuous (pfU E n u) :=
  continuous_induced_rng.2 (continuous_prjG (orb E u))

end GlobalTheory.EulerTwRestr

open GlobalTheory.EulerTw GlobalTheory.EulerTwRestr in

theorem GlobalTheory.EulerTwRestr.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)),
    IsSection S → GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)))
      (fun u : S => GlobalTheory.EulerTw.pfU E n u.1) (fun u : S => GlobalTheory.EulerTw.KU E n u.1) := by
  intro E _ _ _ n S hS
  have hu := existsUnique_orb hS
  choose σ hσS hσw using fun w => (hu w).exists
  have hσu : ∀ (w u : Pl E), u ∈ S → w ∈ orb E u → u = σ w := fun w u h1 h2 =>
    (hu w).unique ⟨h1, h2⟩ ⟨hσS w, hσw w⟩
  have hlev : ∀ x, (∀ u : S, pfU E n u.1 x ∈ KU E n u.1) ↔ x ∈ Kglob E n := by
    intro x
    rw [mem_Kglob]
    exact ⟨fun h w => mem_KU_pfU.1 (h ⟨σ w, hσS w⟩) w (hσw w), fun h u => mem_KU_pfU.2 fun w _ => h w⟩
  refine ⟨fun w => w.elim, fun u => continuous_pfU _, fun u => ?_, fun u => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_Kglob.preimage continuous_subtype_val
  · have e : (KU E n u.1 : Set (Gam E n u.1)) = pfU E n u.1 '' (Kglob E n : Set _) := by
      ext y
      refine ⟨fun hy => ⟨y.1, hy, Subtype.ext ?_⟩, ?_⟩
      · obtain ⟨g, hg⟩ := y.2
        rw [pfU_val, ← hg, prjG_prjG]
      · rintro ⟨g, hg, rfl⟩
        exact mem_KU_pfU.2 fun w _ => mem_Kglob.1 hg w
    rw [e]
    exact isCompact_Kglob.image (continuous_pfU _)
  · intro x y _ hf
    refine gl_ext fun w => ?_
    have h := congrArg (fun z : Gam E n (σ w) => Matrix.GeneralLinearGroup.map (pLoc E w) z.1) (hf ⟨σ w, hσS w⟩)
    simp only [pfU_val, loc_prjG, if_pos (hσw w)] at h
    exact h
  · intro x
    have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (x.1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
      eventually_all.2 fun i => eventually_all.2 fun j => (x.1 i j).2
    have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w ((x⁻¹).1 i j) ∈ (w : Pl E).adicCompletionIntegers E :=
      eventually_all.2 fun i => eventually_all.2 fun j => ((x⁻¹).1 i j).2
    have hx : ∀ᶠ w in cofinite, Matrix.GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
      filter_upwards [h1, h2] with w h1 h2
      exact mem_KGL_iff.2 ⟨fun i j => by rw [loc_val]; exact h1 i j, fun i j => by rw [loc_inv_val]; exact h2 i j⟩
    have hB := eventually_cofinite.1 hx
    refine eventually_cofinite.2 (((hB.preimage Subtype.val_injective.injOn).union
      (hB.preimage ((conjSrc_injective (IsCMField.complexConj E).toRingEquiv).comp Subtype.val_injective).injOn)).subset ?_)
    intro u hu
    simp only [Set.mem_setOf_eq, mem_KU_pfU, not_forall] at hu
    obtain ⟨w, hw, hwx⟩ := hu
    rcases (by simpa [orb] using hw : w = u.1 ∨ w = cPl E u.1) with rfl | rfl
    · exact Or.inl hwx
    · exact Or.inr hwx
  · intro a y hy
    have hc : ∀ᶠ w in cofinite,
        Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1 ∈ GlobalTheory.LFun.KGL w n := by
      have hB := eventually_cofinite.1 hy
      refine eventually_cofinite.2 ((hB.biUnion fun u _ => (orb E u.1).finite_toSet).subset ?_)
      intro w hw
      exact Set.mem_iUnion₂.2 ⟨⟨σ w, hσS w⟩,
        fun h => hw (mem_Kglob.1 (Subgroup.mem_subgroupOf.1 h) w), hσw w⟩
    let M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) := Matrix.of fun i j =>
      ⟨fun w => (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).1 i j,
        hc.mono fun w h => (mem_KGL_iff.1 h).1 i j⟩
    let M' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) := Matrix.of fun i j =>
      ⟨fun w => ((Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1)⁻¹).1 i j,
        hc.mono fun w h => (mem_KGL_iff.1 h).2 i j⟩
    have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
        (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q := fun P Q h =>
      Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
    have hMM' : M * M' = 1 := hloc _ _ fun w => by
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).mul_inv
    have hM'M : M' * M = 1 := hloc _ _ fun w => by
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact (Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1).inv_mul
    let x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) := ⟨M, M', hMM', hM'M⟩
    have hx : ∀ w, Matrix.GeneralLinearGroup.map (pLoc E w) x =
        Matrix.GeneralLinearGroup.map (pLoc E w) (y ⟨σ w, hσS w⟩).1 := fun w =>
      Units.ext (Matrix.ext fun i j => rfl)
    refine ⟨x, fun w => w.elim, fun u => Subtype.ext (gl_ext fun w => ?_)⟩
    rw [pfU_val, loc_prjG]
    split_ifs with hw
    · have e : (⟨σ w, hσS w⟩ : S) = u := Subtype.ext (hσu w u.1 u.2 hw).symm
      rw [hx w, e]
    · exact (loc_eq_one_of_mem_Gam (y u).2 hw).symm
  · have e : {x | ∀ u : S, pfU E n u.1 x ∈ KU E n u.1} = (Kglob E n : Set _) := Set.ext hlev
    rw [e]
    exact isOpen_Kglob
  · intro C _
    have e : {x | (∀ w, GlobalTheory.RestrMeas.noArch (GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) w x ∈ C w) ∧
        ∀ u : S, pfU E n u.1 x ∈ KU E n u.1} = (Kglob E n : Set _) :=
      Set.ext fun x => ⟨fun h => (hlev x).1 h.2, fun h => ⟨fun w => w.elim, (hlev x).2 h⟩⟩
    rw [e]
    exact isCompact_Kglob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPoStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), toSub (UL n w) (cLoc w ((finPt γ : finU E n) : UA E n)) = locPt w γ := by
  first | exact @GlobalTheory.BCT.locPt_finPt | exact GlobalTheory.BCT.locPt_finPt | (intros; apply GlobalTheory.BCT.locPt_finPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConjugation_involutive_valuation_preserving : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  first | exact @GlobalTheory.BCT.cj_involutive_valuation | exact GlobalTheory.BCT.cj_involutive_valuation | (intros; apply GlobalTheory.BCT.cj_involutive_valuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOneStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSign_full_charpoly_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) → ∀ γ : GLw n w, kapSign n w γ.val.charpoly γ = 1 := by
  first | exact @GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | exact GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one | (intros; apply GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignKernelCharFactorConjInvariantStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSign_kernel_charFactor_conj_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ (Q₁ : (w.adicCompletion E)[X]) (γ g : UL n w), kapSign n w Q₁ (g⁻¹ * γ * g).1 = kapSign n w Q₁ γ.1 := by
  first | exact @GlobalTheory.BCT.kapSign_conj | exact GlobalTheory.BCT.kapSign_conj | (intros; apply GlobalTheory.BCT.kapSign_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTestFactorNeZeroOfGlobalProductNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem factor_ne_zero_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU E n, (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w n) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  intro E _ _ _ n S K' f hT y hy hne w hw h0
  set F : Pl E → ℂ := fun w => f w (toSub _ (cLoc w y.1)) with hF
  have hev : ∀ᶠ v in cofinite, F v = 1 := by
    filter_upwards [hT.2, hy] with v hv hyv
    simp only [hF, hv]
    have hmem : toSub (UL n v) (cLoc v y.1) ∈ KL n v := by
      unfold toSub
      split_ifs with h
      · exact (Subgroup.mem_subgroupOf).2 hyv
      · exact Subgroup.one_mem _
    exact Set.indicator_of_mem (show toSub (UL n v) (cLoc v y.1) ∈ ((KL n v : Subgroup (UL n v)) : Set (UL n v)) from hmem) _
  have hfin : (Function.mulSupport F).Finite := by
    have := Filter.eventually_cofinite.1 hev
    exact this
  have hfin' : (S ∩ Function.mulSupport F).Finite := hfin.subset Set.inter_subset_right
  apply hne
  show ∏ᶠ v ∈ S, F v = 0
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod F hfin']
  apply Finset.prod_eq_zero (i := w)
  · rw [Set.Finite.mem_toFinset]
    refine ⟨hw, ?_⟩
    rw [Function.mem_mulSupport]
    change f w (toSub _ (cLoc w y.1)) ≠ 1
    rw [h0]; exact zero_ne_one
  · exact h0

end GlobalTheory.BCT.SuppFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def glueM (T : Finset (Pl E)) (f : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E)) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  fun i j => ⟨fun v => if v ∈ T then f v i j else (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
    rw [if_neg (by simpa using hv), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem pLoc_ext {a b : FiniteAdeleRing (𝓞 E) E} (h : ∀ v, pLoc E v a = pLoc E v b) : a = b :=
  Subtype.ext (funext h)

theorem matrix_ext_pLoc {A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ v, A.map (pLoc E v) = B.map (pLoc E v)) : A = B := by
  refine Matrix.ext fun i j => ?_
  exact pLoc_ext E fun v => congrFun (congrFun (h v) i) j

theorem map_glueM (T : Finset (Pl E)) (f : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E)) (v : Pl E) :
    (glueM E n T f).map (pLoc E v) = if v ∈ T then f v else 1 := by
  refine Matrix.ext fun i j => ?_
  change (if v ∈ T then f v i j else (1 : Matrix (Fin n) (Fin n) (v.adicCompletion E)) i j) =
    (if v ∈ T then f v else 1) i j
  split_ifs <;> rfl

theorem glueM_mul (T : Finset (Pl E)) (f f' : ∀ v : Pl E, Matrix (Fin n) (Fin n) (v.adicCompletion E))
    (hf : ∀ v, f v * f' v = 1) : glueM E n T f * glueM E n T f' = 1 := by
  refine matrix_ext_pLoc E n fun v => ?_
  rw [Matrix.map_mul, map_glueM, map_glueM, Matrix.map_one _ (map_zero _) (map_one _)]
  split_ifs
  · exact hf v
  · exact one_mul 1

def glueG (T : Finset (Pl E)) (g : ∀ v : Pl E, GLw n v) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  ⟨glueM E n T (fun v => (g v : Matrix (Fin n) (Fin n) (v.adicCompletion E))),
    glueM E n T (fun v => (((g v)⁻¹ : GLw n v) : Matrix (Fin n) (Fin n) (v.adicCompletion E))),
    glueM_mul E n T _ _ fun v => (g v).mul_inv, glueM_mul E n T _ _ fun v => (g v).inv_mul⟩

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernelStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  first | exact @GlobalTheory.RatFix.ratfix | exact GlobalTheory.RatFix.ratfix | (intros; apply GlobalTheory.RatFix.ratfix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffLocalStatement
section
open Filter GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_local : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)), (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  first | exact @GlobalTheory.BCT.mem_cptPart_iff_local | exact GlobalTheory.BCT.mem_cptPart_iff_local | (intros; apply GlobalTheory.BCT.mem_cptPart_iff_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReductionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integral_of_commute_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.IntMatSep.integral_of_commute_sep | exact GlobalTheory.IntMatSep.integral_of_commute_sep | (intros; apply GlobalTheory.IntMatSep.integral_of_commute_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.StabInt.mem_KGL_of_commute | exact GlobalTheory.StabInt.mem_KGL_of_commute | (intros; apply GlobalTheory.StabInt.mem_KGL_of_commute <;> assumption)
end

