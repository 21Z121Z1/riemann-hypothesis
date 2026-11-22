import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegion
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lineStab (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    Subgroup (ratPts σ J) where
  carrier := {γ | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J γ.1).1 * adMat F x = l.1 • adMat F x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
    refine ⟨l₁ * l₂, ?_⟩
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, h₂, Matrix.mul_smul, h₁, smul_smul, mul_comm]
  inv_mem' := by
    rintro γ ⟨l, hl⟩
    refine ⟨l⁻¹, ?_⟩
    have e : (matHom _ σ J (γ.1)⁻¹).1 * (matHom _ σ J γ.1).1 = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have := congrArg (fun M => (matHom _ σ J (γ.1)⁻¹).1 * M) hl
    simp only [← Matrix.mul_assoc, e, Matrix.one_mul, Matrix.mul_smul] at this
    simp only [Subgroup.coe_inv]
    have h2 : (↑l⁻¹ : AF F ⊗[F] E) • adMat F x = (↑l⁻¹ : AF F ⊗[F] E) • (↑l • ((matHom _ σ J (γ.1)⁻¹).1 * adMat F x)) :=
      congrArg _ this
    rw [h2, ← Units.smul_def, inv_smul_smul]

theorem exists_reps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  let R := QuotientGroup.rightRel (lineStab σ J x)
  refine ⟨Set.range (fun q : Quotient R => q.out), fun γ => ⟨(Quotient.mk R γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · have := Quotient.mk_out (s := R) γ
    exact (QuotientGroup.rightRel_apply.1 this)
  · rintro t ⟨⟨q, rfl⟩, ht⟩
    have h1 : R q.out γ := QuotientGroup.rightRel_apply.2 ht
    have h2 : Quotient.mk R q.out = Quotient.mk R γ := Quotient.sound h1
    rw [Quotient.out_eq] at h2
    rw [h2]

end GlobalTheory.EisRes

namespace GlobalTheory.EisRes

theorem levelAll_inv_near_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ s ∈ V, ∀ k ∈ levelAll σ J L a, ∀ g, H₀ s (g * k) = H₀ s g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH hsm hhol
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hI : IsIwaHtG σ J (col0 X) L a h := hS.2.2.2.2.2.2

  have hinv : ∀ g, ∀ k ∈ levelAll σ J L a, h (g * k) = h g := by
    intro g k hk
    obtain ⟨p, l, hpl, k', hk', rfl⟩ := hI.1 g
    rw [mul_assoc, hI.2 p l hpl _ (Subgroup.mul_mem _ hk' hk), hI.2 p l hpl k' hk']
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)

  have Heisenberg₂ : ∀ s : ℂ, ρ.re < s.re → ∀ g, ∀ k ∈ levelAll σ J L a, Eis s (g * k) = Eis s g := by
    intro s hs g k hk
    rw [hρre] at hs
    have h1 := hP.1 T hT s hs (g * k)
    have h2 := hP.1 T hT s hs g
    simp only [← mul_assoc, hinv _ k hk] at h1
    exact h1.unique h2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  refine ⟨Metric.ball ρ ε, Metric.ball_mem_nhds ρ hε, fun s hs k hk g => ?_⟩
  have hd : ∀ g', DifferentiableOn ℂ (fun s => H₀ s g') (Metric.ball ρ ε) := fun g' =>
    (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g')).mono hball
  have a1 := (hd (g * k)).analyticOnNhd Metric.isOpen_ball
  have a2 := (hd g).analyticOnNhd Metric.isOpen_ball
  set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
  have hz₀b : z₀ ∈ Metric.ball ρ ε := by
    rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
  have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : (fun s => H₀ s (g * k)) =ᶠ[𝓝 z₀] fun s => H₀ s g := by
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hsU : s ∈ U₀ := hball hs'.1
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    rw [hH s hsU hne, hH s hsU hne, Heisenberg₂ s hs'.2 g k hk]
  exact a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b hev hs

end GlobalTheory.EisRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntryMemSubringOfTraceGramUnitStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entry_mem_subring_of_trace_gram_unit : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  first | exact @GlobalTheory.TraceGram.entry_mem_of_trace_gram | exact GlobalTheory.TraceGram.entry_mem_of_trace_gram | (intros; apply GlobalTheory.TraceGram.entry_mem_of_trace_gram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelianStatement
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_kills_idealPowerTorsion_semiAbelian : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  first | exact @GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one | exact GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one | (intros; apply GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.VacLine

variable {F : Type} [Field F] [NumberField F]

def mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

def slice {κ : Type} (Φ : (κ → AF F) → ℂ) (x : κ → mixedEmbedding.mixedSpace F) : (κ → Af F) → ℂ :=
  fun y => Φ (mkPt x y)

def finOp (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (p : (κ → Fv F v) × (κ → Fv F v))
    (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun y => psiLoc ψ v ((fun i => evalV F v (y i)) ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 / 2) * g (y + fun i => singleFin v (p.1 i))

def vacProd {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem evI_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) :
    evI F (mkPt x y i) = x i := by
  simp [mkPt, evI]

theorem evFin_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) (v : Pl F) :
    evFin F v (mkPt x y i) = evalV F v (y i) := rfl

theorem mkPt_eq {κ : Type} (z : κ → AF F) : mkPt (fun i => evI F (z i)) (fun i => (z i).2) = z := by
  funext i
  show ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1), (z i).2) = z i
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem pure_mkPt {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (mkPt x y) = f x * vacProd φ y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure vacProd
  simp only [evI_mkPt, evFin_mkPt]

theorem at_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

end GlobalTheory.VacLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalCenterEqCircleIntegralShiftedOrder
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem eval_center_eq_circleIntegral_shifted_order : ∀ {X : Type} (s₀ : ℂ) (k k₀ : ℕ) (r : ℝ) (V : Set ℂ) (Eis H H₀ : ℂ → X → ℂ), 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → (∀ g, DifferentiableOn ℂ (H · g) V) → (∀ g, DifferentiableOn ℂ (H₀ · g) V) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) →
    (∀ s ∈ V, s ≠ s₀ → ∀ g, H₀ s g = (s - s₀) ^ k₀ * Eis s g) →
    ∀ g, H s₀ g = (2 * ↑Real.pi * Complex.I)⁻¹ * circleIntegral (fun z => (z - s₀) ^ ((k : ℤ) - k₀ - 1) * H₀ z g) s₀ r := by
  intro X s₀ k k₀ r V Eis H H₀ hr hV hball hH hH₀ hHE hH₀E g
  have hdc : DiffContOnCl ℂ (H · g) (Metric.ball s₀ r) :=
    ((hH g).mono (by
      intro z hz; exact hball (Metric.closure_ball_subset_closedBall hz))).diffContOnCl
  have hc := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (Metric.mem_ball_self hr)
  simp only [smul_eq_mul] at hc
  rw [← hc]
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hzV : z ∈ V := hball (Metric.sphere_subset_closedBall hz)
  have hne : z - s₀ ≠ 0 := by
    intro h0
    rw [Metric.mem_sphere, dist_eq_norm, h0, norm_zero] at hz
    exact hr.ne' hz.symm
  have hz' : z ≠ s₀ := sub_ne_zero.mp hne
  simp only
  rw [hHE z hzV hz' g, hH₀E z hzV hz' g]
  rw [← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_add₀ hne, ← zpow_add₀ hne]
  congr 2
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable → ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P → y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  first | exact @GlobalTheory.BCT.IntUnitConj.main | exact GlobalTheory.BCT.IntUnitConj.main | (intros; apply GlobalTheory.BCT.IntUnitConj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FinEtPoints

theorem epi_spMap_field (k L : Type) [Field k] [Field L] (f : k →+* L) : Epi (spMap f) := by
  exact Flat.epi_of_flat_of_surjective _

theorem exists_point_of_finite_etale (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀) : IsFinite p → Etale p →
    ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) →
      ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  intro hf he x hx
  let Ω := AlgebraicClosure K
  let i : K →+* Ω := algebraMap K Ω
  let j : k₀ →+* K := algebraMap k₀ K
  let t : Sp Ω ⟶ Sp k₀ := spMap (i.comp j)
  have ht : spMap i ≫ spMap j = t := by
    simp only [t, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hti : Epi t := epi_spMap_field _ _ _
  have hii : Epi (spMap i) := epi_spMap_field _ _ _
  obtain ⟨zΩ⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z₀⟩ : Nonempty (Sp k₀) := inferInstance
  obtain ⟨hfin₁, hc₁⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t zΩ
  obtain ⟨hfin₀, hc₀⟩ := GlobalTheory.FinEt.card_points_eq_finrank p (𝟙 (Sp k₀)) z₀
  let F : {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} → {y : Sp Ω ⟶ X // y ≫ p = t} :=
    fun y ↦ ⟨t ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext ((cancel_epi t).mp congr(($hab).1))
  have hcard : Nat.card {y : Sp Ω ⟶ X // y ≫ p = t} ≤ Nat.card {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} := by
    rw [hc₁, hc₀, Subsingleton.elim (t zΩ) ((𝟙 (Sp k₀) : Sp k₀ ⟶ Sp k₀) z₀)]
  have hFb : Function.Bijective F := hFi.bijective_of_nat_card_le hcard
  obtain ⟨⟨x₀, hx₀⟩, hF⟩ := hFb.2 ⟨spMap i ≫ x, by rw [Category.assoc, hx, ht]⟩
  refine ⟨x₀, hx₀, ?_⟩
  have h1 : spMap i ≫ (spMap j ≫ x₀) = spMap i ≫ x := by
    rw [← Category.assoc, ht]
    exact congr(($hF).1)
  exact (cancel_epi (spMap i)).mp h1

end GlobalTheory.FinEtPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesOrthonormalJ
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLiftComp

open Matrix GlobalTheory.RealLiftGen

theorem exists_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (InfinitePlace F → Mat R S), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) ∧ ∀ w (M M' : Mat R S), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (InfinitePlace F → Mat R S) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm R S * (k g w).map star = Jm R S := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSig
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.RealLiftCompD

open Matrix GlobalTheory.RealLiftGen

theorem exists_compD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) ∧ ∀ w (M M' : Mat (R w) (S w)), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm (R w) (S w) := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm (R w) (S w) * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm (R w) (S w)), Matrix.mul_assoc (Jm (R w) (S w)), hF, Jm_mul_Jm]
    have h2 : (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm (R w) (S w) * (k g w).map star = Jm (R w) (S w) := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftCompD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboliStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ GlobalTheory.JSW.mirS E S m ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, (∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ GlobalTheory.JSW.mirS E S m, p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  first | exact @GlobalTheory.JSW.MirPatch.Cover.exists_cover | exact GlobalTheory.JSW.MirPatch.Cover.exists_cover | (intros; apply GlobalTheory.JSW.MirPatch.Cover.exists_cover <;> assumption)
end

