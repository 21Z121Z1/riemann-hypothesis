import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeGeneratedByHighest
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0129
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
section
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RatDiscrete

theorem finite_bounded {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (B : ℝ) :
    {x : n → E | x ∈ Λ ∧ ∀ (τ : E →+* ℂ) i, ‖τ (x i)‖ ≤ B}.Finite := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hm' : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
  have h1 := (NumberField.Embeddings.finite_of_norm_le E ℂ (‖(m : ℂ)‖ * B)).preimage
    (f := fun a : E => (m : E) * a) (mul_right_injective₀ hm').injOn
  refine (Set.Finite.pi' fun _ : n => h1).subset fun x hx i => ⟨hΛ x hx.1 i, fun τ => ?_⟩
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.2 τ i) (norm_nonneg _)

variable (I : AutInst)

theorem exists_place (τ : I.E →+* ℂ) : ∃ v, ∀ a, ‖τ a‖ = ‖I.φ v a‖ := by
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := τ.comp (algebraMap I.F I.E)
  have hψ : ComplexEmbedding.IsReal ψ :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk ψ))
  refine ⟨InfinitePlace.mk ψ, fun a => ?_⟩
  obtain ⟨b, hb⟩ := (I.cm.fixed (a * star a)).1 (by rw [star_mul, star_star])
  have h1 : τ (a * star a) = I.φ (InfinitePlace.mk ψ) (a * star a) := by
    rw [← hb, I.φ_over, InfinitePlace.embedding_mk_eq_of_isReal hψ]
    rfl
  have h2 := congrArg norm h1
  simp only [map_mul, I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj] at h2
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h2

def IsImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) (x : I.GA) : Prop :=
  (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) ∧
    I.fmat x.2 = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem subsingleton_isImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) :
    {x | IsImage I γ x}.Subsingleton := fun _ hx _ hy =>
  Prod.ext (funext fun v => Subtype.ext (Units.ext ((hx.1 v).trans (hy.1 v).symm)))
    (Subtype.ext (Units.ext (hx.2.trans hy.2.symm)))

theorem P_det (v) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem isImage_one : IsImage I 1 1 := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (P_det I v)]
    rfl
  · rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem isImage_mul {γ δ x y} (hx : IsImage I γ x) (hy : IsImage I δ y) :
    IsImage I (γ * δ) (x * y) := by
  refine ⟨fun v => ?_, ?_⟩
  · have : uMat ((x * y).1 v) = uMat (x.1 v) * uMat (y.1 v) := rfl
    rw [this, hx.1, hy.1, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  · have : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
    rw [this, hx.2, hy.2, Matrix.map_mul]

theorem isImage_inv {γ : GL (Fin I.n) I.E} {x} (hx : IsImage I γ x) :
    IsImage I (γ⁻¹ : GL (Fin I.n) I.E) x⁻¹ := by
  refine ⟨fun v => ?_, ?_⟩
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.1 v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) ?_
    have := hx.1 v
    unfold uMat at this
    rw [this]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
    rw [← Matrix.mul_assoc (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ (P_det I v)]
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) ?_
    have := hx.2
    unfold AutInst.fmat at this
    rw [this, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

def ratSub : Subgroup I.GA where
  carrier := I.GFset
  one_mem' := ⟨1, one_mem _, isImage_one I⟩
  mul_mem' := fun ⟨γ, hγ, hx⟩ ⟨δ, hδ, hy⟩ => ⟨γ * δ, mul_mem hγ hδ, isImage_mul I hx hy⟩
  inv_mem' := fun ⟨γ, hγ, hx⟩ => ⟨γ⁻¹, inv_mem hγ, isImage_inv I hx⟩

theorem countable_GFset : I.GFset.Countable := by
  haveI : Countable I.E := Countable.of_equiv _ (Module.finBasis ℚ I.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  refine (Set.countable_iUnion fun γ => (subsingleton_isImage I γ).countable).mono ?_
  rintro x ⟨γ, -, hx⟩
  exact Set.mem_iUnion.2 ⟨γ, hx⟩

theorem exists_bound {C : Set I.GA} (hC : IsCompact C) : ∃ B : ℝ, ∀ x ∈ C, ∀ v i j,
    ‖(I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j‖ ≤ B := by
  have hc : Continuous fun x : I.GA => fun v i j => (I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j := by
    refine continuous_pi fun v => ?_
    exact (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp
      ((continuous_apply v).comp continuous_fst)))).matrix_mul continuous_const
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun x hx v i j => (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
    ((norm_le_pi_norm _ v).trans (hB x hx)))⟩

theorem finite_coset (g : I.Gf) (B : ℝ) :
    {γ : Matrix (Fin I.n) (Fin I.n) I.E | (∀ v i j, ‖I.φ v (γ i j)‖ ≤ B) ∧
      ∃ y : I.Gf, g⁻¹ * y ∈ I.Kset ∧ I.fmat y = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))}.Finite := by
  classical
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  set G : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := g.1 with hGdef
  obtain ⟨e, he, s, hs, hsg, -⟩ := Formalism.UG.P.levelaf_exists_denom (E := I.E) G
  have hfin := Formalism.UG.P.adelstab_finite G I.Lf d e hd0 he hup (Formalism.UG.P.adelstab_entries G e s hs hsg)
  set u : I.E := algebraMap (𝓞 I.F) I.E c with hu
  have hu0 : u ≠ 0 := Formalism.UG.P.adelstab_algebraMap_ne_zero c hc0
  obtain ⟨Bu, hBu⟩ : ∃ Bu : ℝ, ∀ τ : I.E →+* ℂ, ‖τ u‖ ≤ Bu :=
    ⟨_, fun τ => Finite.le_ciSup (fun τ : I.E →+* ℂ => ‖τ u‖) τ⟩
  have h1 := (Set.Finite.pi' fun _ : Fin I.n => finite_bounded _ hfin (Bu * B)).preimage
    (f := fun (γ : Matrix (Fin I.n) (Fin I.n) I.E) j i => u * γ i j) (by
      intro a _ b _ h
      ext i j
      exact mul_left_cancel₀ hu0 (congrFun (congrFun h j) i))
  refine h1.subset ?_
  rintro γ ⟨hb, y, hy, hγ⟩ j
  refine ⟨?_, fun τ i => ?_⟩
  · have hs : (Pi.single j (Formalism.UG.P.levelafC I.E c) : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := by
      convert hlow (Pi.single j 1) fun i => ?_ using 1
      · funext i
        by_cases h : i = j <;> simp [h]
      · rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
    have h2 := (hy _).1 hs
    rw [Formalism.UG.P.adelstab_mem_iff]
    convert h2 using 1
    change _ = (((G⁻¹ : GL _ _) : Matrix _ _ _) * I.fmat y) *ᵥ _
    rw [← Matrix.mulVec_mulVec, hγ]
    congr 1
    funext i
    simp [hu, Formalism.UG.P.adelstab_incl_C, mul_comm]
  · obtain ⟨v, hv⟩ := exists_place I τ
    simp only [map_mul, norm_mul]
    rw [hv (γ i j)]
    exact mul_le_mul (hBu τ) (hb v i j) (norm_nonneg _) ((norm_nonneg _).trans (hBu τ))

theorem finite_inter {C : Set I.GA} (hC : IsCompact C) : (C ∩ I.GFset).Finite := by
  obtain ⟨-, -, -, -, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨B, hB⟩ := exists_bound I hC
  obtain ⟨t, -, ht⟩ := (hC.image continuous_snd).elim_nhds_subcover
    (fun g => {y | g⁻¹ * y ∈ I.Kset}) fun g _ =>
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show g⁻¹ * g ∈ I.Kset
        rw [inv_mul_cancel, ← hK]
        exact K.one_mem)
  refine ((t.finite_toSet.biUnion fun g _ => finite_coset I g B).biUnion
    fun γ _ => (subsingleton_isImage I γ).finite).subset ?_
  rintro x ⟨hx, γ, -, hγ⟩
  obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 (ht ⟨x, hx, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨γ, Set.mem_iUnion₂.2 ⟨g, hg, fun v i j => ?_, x.2, hgx, hγ.2⟩, hγ⟩
  have := hB x hx v i j
  rw [hγ.1 v] at this
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v),
    Matrix.mul_nonsing_inv _ (P_det I v), Matrix.mul_one, Matrix.map_apply] using this

theorem isFundamentalDomain (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : IsFundamentalDomain (ratSub I) fund (I.muA μf) := by
  refine IsFundamentalDomain.mk'' h.1.nullMeasurableSet (ae_of_all _ fun y => ?_) (fun γ hγ => ?_)
    fun γ => ((measurePreserving_mul_left (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (γ : I.GA).1).prod
      (measurePreserving_mul_left μf (γ : I.GA).2)).quasiMeasurePreserving
  · obtain ⟨γ, hγ, hy⟩ := h.2.1 y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · exact h.2.2 γ γ.2 fun e => hγ (Subtype.ext e)

theorem rational_points : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) :=
  fun I => ⟨ratSub I, rfl, (countable_GFset I).to_subtype, fun _ hC => finite_inter I hC,
    fun μf _ _ fund h => isFundamentalDomain I μf fund h⟩

end GlobalTheory.RatDiscrete
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepBoundOneRep

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem stepConst_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ stepConst n b P := by
  have h1 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg b)
  have h2 : 0 ≤ 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h3 : 0 ≤ 3 * (P : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg P)
  simp only [stepConst]
  linarith

theorem stepSpace_le {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ Vs) (hE : GlRel E)
    (hd : ∀ X, inG ε X → ∀ u : Vs, HasDerivAt (orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (u : Vs) (hu : (kSpan ε E u).map Vs.subtype = lowKSub ε lam σ) (P : ℕ) :
    stepSpace ε lam σ P ≤ (pfil ε E u P).map Vs.subtype := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, inG ε X) → ∀ w ∈ lowKSub ε lam σ,
      ∃ x : Vs, x ∈ pfil ε E u l.length ∧ (x : H) = dWord σ l w := by
    intro l
    induction l with
    | nil =>
      intro _ w hw
      rw [← hu] at hw
      obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hw
      refine ⟨x, ?_, ?_⟩
      · rw [List.length_nil, poincare_filtration_zero]
        exact hx
      · exact hxw
    | cons X l ih =>
      intro hl w hw
      obtain ⟨x, hx, hxe⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) w hw
      refine ⟨∑ a, ∑ b, X a b • E a b x, ?_, ?_⟩
      · exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
          Submodule.smul_mem _ _ (poincare_filtration_succ ε E u hE _ a b x hx)
      · change _ = dAct σ X (dWord σ l w)
        rw [← hxe, dAct, (hd X (hl X List.mem_cons_self) x).deriv]
  rw [stepSpace, Submodule.span_le]
  rintro v ⟨l, w, hl, hX, hw, rfl⟩
  obtain ⟨x, hx, hxe⟩ := key l hX w hw
  exact Submodule.mem_map.mpr ⟨x, pfil_monotone_in_length ε E u hl hx, hxe⟩

theorem smooth_of_mem_lowKSub {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hU : IsURepOn (UJset ε) σ)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) (v : H) (hv : v ∈ lowKSub ε lam σ) :
    SmoothOnGV ε (fun g => σ g v) := by
  obtain ⟨α, hα, hαc, hfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hU hS
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hcα : Continuous (fun g : UJ ε => α (umat g)) := by
    refine continuous_iff_continuousAt.mpr fun g₀ => ?_
    obtain ⟨U, F, hUo, hgU, hF, hFα⟩ := hα (umat g₀) g₀.2
    have hev : (fun g : UJ ε => F (umat g)) =ᶠ[nhds g₀] (fun g : UJ ε => α (umat g)) := by
      filter_upwards [hcu.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgU)] with g hg
      exact (hFα _ hg g.2).symm
    exact ((hF.continuousOn.continuousAt (hUo.mem_nhds hgU)).comp hcu.continuousAt).congr hev
  have hcσ : Continuous (fun g : UJ ε => σ (umat g) v) :=
    (hU.2.2 v).comp_continuous hcu fun g => g.2
  have hint : Integrable (fun g : UJ ε => α (umat g) • σ (umat g) v) (muG ε) :=
    (hcα.smul hcσ).integrable_of_hasCompactSupport (hαc.smul_right)
  have hv : v = ∫ g : UJ ε, α (umat g) • σ (umat g) v ∂(muG ε) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [← integral_inner hint y, ← hfix v hv y]
    simp only [inner_smul_right]
  have hsm := GlobalTheory.GardingSmooth.garding_smooth n ε H σ hU α hα hαc v
  rw [← hv] at hsm
  exact hsm

theorem stepBound_of_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (b : ℝ), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → (∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ)) → (∀ a, |lam a| ≤ b ^ 2) → (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) ∧ (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖w‖) := by
  intro n ε H _ _ _ σ lam b hU hS heig hb
  obtain ⟨Vs, E, hVs, hGl, hUn, hD, hEq⟩ := SmoothVecMod.smoothVec_unitary_module n ε H σ hU
  have hlow : lowKSub ε lam σ ≤ Vs := fun v hv =>
    (hVs v).mpr (smooth_of_mem_lowKSub ε lam σ hU hS v hv)
  obtain ⟨u, -, hKu, hmap, hfd⟩ := GlobalTheory.KTypeHighest.kType_generated_by_highest n ε H σ Vs E hU
    ⟨hVs, hGl, hUn, hD, hEq⟩ _ (lowKSub ε lam σ) hS hlow
  have huS : (u : H) ∈ lowKSub ε lam σ := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (mem_kSpan_self' ε E u)
  have hCas := GlobalTheory.CasimirEigen.cas_eq_of_isZEigen n ε H σ Vs E lam hU ⟨hVs, hGl, hUn, hD, hEq⟩ u
    (heig _ huS)
  have hKind : KindA ε E lam u := ⟨hKu, hCas, hfd⟩
  have hAlg := GlobalTheory.algebraic_step_bound Vs n ε E lam u b hGl hUn hKind hb
  have hC : ∀ P : ℕ, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P := fun P => stepConst_nonneg n b P
  have hmem : ∀ (P : ℕ) (w : H), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P →
      ∃ x : Vs, x ∈ pfil ε E u P ∧ (x : H) = w := fun P w hw =>
    Submodule.mem_map.mp (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P hw)
  have hact : ∀ X, inG ε X → ∀ x : Vs,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H) = ((∑ a, ∑ c, X a c • E a c x : Vs) : H) := fun X hX x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, (hD X hX x).deriv]
  have hbound : ∀ P : ℕ, ∀ x ∈ pfil ε E u P,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hAlg
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ (pfil ε E u P) := pfil_finite_dimensional ε E u hfd P
    exact Submodule.finiteDimensional_of_le
      (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P)
  · intro w hw
    obtain ⟨x, -, rfl⟩ := hmem P w hw
    exact fun X hX => (hD X hX x).differentiableAt
  · intro F hF w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hON := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).1 F hF
    calc ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) (x : H)‖ ^ 2
        = ∑ i, ‖∑ a, ∑ c, F i a c • E a c x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hact (F i) (hF.1 i) x]
          rfl
      _ = ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hON
      _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hbound P x hx
      _ = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := rfl
  · intro X hX w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hsq := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).2 X
    have hhs : 0 ≤ Formalism.REAL.hs X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hnorm : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ = ‖∑ a, ∑ c, X a c • E a c x‖ := by
      rw [hact X hX x]
      rfl
    have h2 : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ ^ 2 ≤
        (Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖) ^ 2 := by
      rw [hnorm, mul_pow, mul_pow, Real.sq_sqrt hhs]
      calc ‖∑ a, ∑ c, X a c • E a c x‖ ^ 2 ≤ Formalism.REAL.hs X * ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hsq
        _ ≤ Formalism.REAL.hs X * (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound P x hx) hhs
        _ = Formalism.REAL.hs X * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := by
          rw [mul_assoc]
          rfl
    have hr : 0 ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hC P)) (norm_nonneg _)
    nlinarith [norm_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H))]

end GlobalTheory.StepBoundOneRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueezeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_small_ball_density_of_squeeze : ∀ (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal), v ≠ ⊤ → (∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal, Filter.Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧ f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) → Filter.Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) := by
  first | exact @GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | exact GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | (intros; apply GlobalTheory.IwConst.tendsto_div_pow_of_squeeze <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpacesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  first | exact @GlobalTheory.ComplPos.complement_totPos | exact GlobalTheory.ComplPos.complement_totPos | (intros; apply GlobalTheory.ComplPos.complement_totPos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | exact GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicativeStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_real_points_bijective_multiplicative : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) → ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧ Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧ ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E), Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  first | exact @GlobalTheory.CovDom.transport_real_points | exact GlobalTheory.CovDom.transport_real_points | (intros; apply GlobalTheory.CovDom.transport_real_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G

theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hc.deg2
  have : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  classical
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom hc.sig hc.sig
    (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])
  have hs : ∀ y, s y = star y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h
    have hall : ∀ y : E, y ∈ (algebraMap F E).range := fun y => (hc.fixed y).1 (by
      rw [← hs, ← h]; rfl)
    have h1 : Module.finrank F E = 1 := by
      apply finrank_eq_one (1 : E) one_ne_zero
      intro w
      obtain ⟨a, ha⟩ := hall w
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
    rw [hc.deg2] at h1
    omega
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]
  rfl

theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitaryStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_on_dual_quotient_iff_mem_localUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  first | exact @GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc | exact GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc | (intros; apply GlobalTheory.St.G.FunFix.trivial_iff_mem_Uloc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreservingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentModelProductAction_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (k r : ℕ) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E), (∀ w, gM A γ w ∈ Nset k r) → MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  first | exact @GlobalTheory.SnMass.VolN.actM_measurePreserving | exact GlobalTheory.SnMass.VolN.actM_measurePreserving | (intros; apply GlobalTheory.SnMass.VolN.actM_measurePreserving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRightChangeMovesFlagComplementStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_right_change_moves_flag_complement : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (VS D) D.R.rS T') (γ₁ γ₂ m n' : GV D), γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' → ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  first | exact @GlobalTheory.UnipRight.unip_right | exact GlobalTheory.UnipRight.unip_right | (intros; apply GlobalTheory.UnipRight.unip_right <;> assumption)
end

