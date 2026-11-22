import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0038
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0071
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftHermitianIsometryModLevelSelfDual
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem evR_eq_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hF ⟨inst, hnab⟩ r g X bas idx e x L y y₂ A hov hs hx hL q0 hr eL hr' hn
    hlet θ v κ hread hvac hκ mk hmk hA Cl _ w La Nc gam vol ep Vs _ _ io xs a hLa hH Y hY f hf
  obtain ⟨vc, hvc, hev⟩ := hf ℂ hF y y₂ hov
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = algebraMap c.F ℂ :=
    RingHom.ext fun t => hF t
  rw [hev, mul_assoc, clsSum, Finset.mul_sum _ _ κ]
  refine congrArg (fun t => evR d.Xo₂ d.c₂ d.cδ y₂ * t) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := hLa k
  have hV : (La k).La ∈ Vset E n d.l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset E n (La k).La).2.1 _ (Nc k) d.l₂.odd.pos h1 h2 h3
  have hP := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hH k)
  have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A hs hx hL q0 n hr eL hr' hn hlet
    d.nab₂ hnab θ v κ hread hvac hκ mk hmk hA (La k).La hV (Nc k) h3 (Y k) (hY k) a _ hP _ 1 (vc k) (hvc k)
  rw [h, MvPolynomial.map_map, hcomp]
  simp only [hF, map_mul, map_inv₀, map_natCast, inv_one, map_one]
  ring

end GlobalTheory.ClsVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostIdempotentTraceEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem cmHost_idempotent_trace_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem mem_vset (Λ : GenLat E n) {M : ℕ} (hM : 3 ≤ M) (hU : Λ.Unimod) (hT : Λ.TrivAt M) :
    Λ.La ∈ Vset E n M := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  rw [GenLatCmp.std_eq, GenLatCmp.span_smul_le] at h1 h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      omega
    · exact hk0
  exact ⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]
  congr 1
  funext z
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

theorem theta_finsum (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} [Fintype T] (W : T → ℂ)
    (Y : T → Matrix (Fin n) (Fin r) E) (a : ℂ) {u : TF n g} (hu : IsSB u)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ᶠ q, W q • heisG X bas (Y q) (a • u)) P x =
      a * ∑ q, W q * thP X hr bas idx (heisG X bas (Y q) u) P x := by
  have h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u := by
    funext t
    simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h1]
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _
    fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _

omit [IsCMField E] in

theorem index_Ln (Λ : GenLat E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]
  rfl

omit [IsCMField E] in

theorem zCard_eq (Λ : GenLat E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem cancel_idx {b κ S Q : ℂ} {m z j : ℕ} (hb : b ≠ 0) (hz0 : 0 < z) (hz : z = m * j) :
    b⁻¹ * (m : ℂ)⁻¹ * Q * (z : ℂ) * κ * ((((Real.sqrt (j : ℝ) : ℝ) : ℂ))⁻¹ * S) * b =
      Q * κ * S * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
  subst hz
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mul_pos_left hz0
  have hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hj).ne'
  have h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hj.le).symm
  rw [Nat.cast_mul]
  generalize ((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2
  rw [h2]
  field_simp

theorem change_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → IsMu (t ^ 2 * ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ) ∧ ∀ (wq : (Fin n → LevQ Dw l) → c.F), FixesDatum c h wq → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq (actLat h Λ) b' N' (pushLet c h P) y v' → v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol
    have h2 : ∏ i : Fin g, rowType X (idx i) h.det =
        ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ := by
      simp only [hty]
      rw [e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp [Formalism.L2.PjFree.relab]
    rwa [h2] at h1
  intro wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependentStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_frame_readings_linearIndependent : ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  first | exact @GlobalTheory.Dict.readings_independent | exact GlobalTheory.Dict.readings_independent | (intros; apply GlobalTheory.Dict.readings_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftHermitianIsometryModLevelSelfDualStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open GlobalTheory.AdLat GlobalTheory.UnRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_hermitianIsometryModLevel_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n m : ℕ), Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → 0 < m → ∀ (Λ : GenLat E n) (io : Λ.La →ₗ[𝓞 E] StdMod E n m), Λ.Unimod → IsIsomMod Λ m io → ∀ k : ℕ, 0 < k → ∃ io' : Λ.La →ₗ[𝓞 E] StdMod E n (m * k), IsIsomMod Λ (m * k) io' ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, io' v j = Ideal.Quotient.mk _ (x j)) → ∀ j, io v j = Ideal.Quotient.mk _ (x j) := by
  first | exact @GlobalTheory.IsomLift.exists_lift | exact GlobalTheory.IsomLift.exists_lift | (intros; apply GlobalTheory.IsomLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  first | exact @GlobalTheory.KerOntoStd.exists_trivAt_isMov | exact GlobalTheory.KerOntoStd.exists_trivAt_isMov | (intros; apply GlobalTheory.KerOntoStd.exists_trivAt_isMov <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU perFr
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ReadAll

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem isSB_smul' (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  refine ⟨R, hR, fun x hx => hsupp x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩
  simp only [Pi.smul_apply, hper x y hy]

theorem isSB_finsum {J : Sort*} {f : J → TF n g} (h : ∀ i, IsSB (f i)) : IsSB (∑ᶠ i, f i) := by
  rw [finsum_def']
  split_ifs with hfin
  · exact Finset.sum_induction _ IsSB
      (fun φ ψ hφ hψ => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ ψ hφ hψ).1)
      isSB_zero (fun i _ => h i.down)
  · exact isSB_zero

theorem isSB_phiF {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (he : Even n) (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n)
    (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) (hv : IsSB (v₀ L)) :
    IsSB (phiF bas D 𝔐 hn v₀ L Λ) := by
  have hH : ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) :=
    fun y φ hφ => ((heisG_laws E r X g bas idx n hs he).2.2.2 y φ hφ).1
  have hP : IsSB (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
    unfold projA
    refine isSB_smul' _ (isSB_finsum fun ψ => isSB_finsum fun hψ => ?_)
    obtain ⟨y, -, rfl⟩ := hψ
    exact isSB_smul' _ (hH y _ hv)
  unfold phiF unitv
  exact isSB_finsum fun c => isSB_smul' _ (hH _ _ (isSB_smul' _ hP))

theorem perFr_cast {X' X : Data E r} (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨hp, hg, h0, hxi, hka⟩ := h
  cases X'
  cases X
  dsimp only at hp hg h0 hxi hka
  subst hp hg h0 hxi hka
  unfold Formalism.L2.PjFree.perFr
  rfl

set_option maxHeartbeats 400000 in
private theorem differentiableOn_and_bchar_equivariant_lact_castFr {X' X : Data E r} (h : SameSp X' X) {ga : GL (Fin r) E} (hUn : IsUn X ga)
    {la : Wt X.Ψ r} {la' : Wt X'.Ψ r} (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i)
    (Q : Frame X.Ψ r → ℂ) (hQ : DifferentiableOn ℂ Q X.dom)
    (hw : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (c0 : ℂ) :
    DifferentiableOn ℂ (fun x => c0 * Q (lact ga (castFr h.psi x))) X'.dom ∧
      ∀ x ∈ X'.dom, ∀ b ∈ Bor X'.Ψ r,
        c0 * Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * (c0 * Q (lact ga (castFr h.psi x))) := by
  have hm : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    GlobalTheory.Dict.Extend.lact_mem hUn (GlobalTheory.Dict.SameSp.castFr_mem_dom h hx)
  refine ⟨(hQ.comp ((GlobalTheory.Dict.Extend.differentiable_lact ga).comp
    (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn hm).const_mul c0, fun x hx b hb => ?_⟩
  rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hw _ (hm x hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb),
    GlobalTheory.Dict.Pull.cast_bchar h.psi hl]
  ring

end GlobalTheory.Dict.ReadAll

open GlobalTheory.Dict.ReadAll GlobalTheory.Dict.Pull GlobalTheory.Dict.Extend in

theorem GlobalTheory.Dict.rdU_short_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (W : UW U) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ X W.g Dw.p n a) (D : SW.Level X) (hn : r ≤ n), Dc.e = W.e → LevTie d σ ph D hn → ∀ v₀ : Lt E r → TF n W.g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ (k : U.Comp) (h : SameSp (U.X k) X) (ga : GL (Fin r) E) (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsUn X ga → mapL ga (U.X k).Λ ∈ D.lats → IsMark l (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) → IsDual X l (σ (zetaM c)) (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ C : ℂ, C ≠ 0 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f ∈ sec Xo c a n, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → ∀ x ∈ (U.X k).dom, rdU U f k x = C * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) (lact ga (castFr h.psi x)) := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hg hU hr hlev hnab hunitC ph ψ x₀ hpin W X a hdom Dc D hn hDe
    htie v₀ hvac x0
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI : Algebra d.c₂.F ℂ := (σ.comp d.eF.symm.toAlgHom.toRingHom).toAlgebra
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  obtain ⟨hrpq, hk, -, -, hsec, -⟩ := hU'
  obtain ⟨u, hu0, hmain⟩ := GlobalTheory.Dict.ShortPt.shortRule_value hCI E H Dw l Xo c n d
    (fun t => by show σ (d.eF.symm (d.eF t)) = σ t; rw [AlgEquiv.symm_apply_apply])
    hlev hnab (fun y₂ => hunitC _ y₂) ph ψ x₀ hpin r W.g Dw.p X a Dc D hn hdom.2 hrpq htie v₀ hvac x0
  refine ⟨u, hu0, ?_⟩
  intro k h ga δ hUn hlat hmark hdual hx0
  obtain ⟨ρ, hρ, hall⟩ := hmain _ hlat _ δ hmark hdual hx0
  rw [hDe] at hall
  have hself : SelfD (U.X k) (U.X k).Λ := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hg hU hr W k).2.1
  have hvL : IsSB (v₀ (mapL ga (U.X k).Λ)) := (hvac _ hlat).1
  have hwt : ∀ (τ : X.Ψ) (i : Fin r),
      wtOf X Dc.hr Dc.k Dc.k' n τ i = laU U a n k ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i := by
    intro τ i
    rw [Dc.wt_eq]
    unfold wtX Formalism.L2.PjFree.laU
    simp only [h.p0]
  let Jx := {q : Lt E n × ℕ × (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ×
      (sec Xo c a n) // q.1 ∈ Vset E n d.l₂.M ∧ NOK q.1 q.2.1 d.l₂.M ∧
        IsShortRule Xo c d (⟨q.1⟩ : GenLat E n) q.2.1 x0 q.2.2.1.1 q.2.2.2.1}
  let R : Jx → Frame (U.X k).Ψ r → ℂ := fun i => rdU U i.1.2.2.2.1 k
  let T : Jx → Frame (U.X k).Ψ r → ℂ := fun i x => u i.1.1 i.1.2.1 *
    thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) i.1.1)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ i.1.2.2.1.1)) (lact ga (castFr h.psi x))
  have hol : ∀ i, DifferentiableOn ℂ (R i) (U.X k).dom ∧ DifferentiableOn ℂ (T i) (U.X k).dom ∧
      ∀ x ∈ (U.X k).dom, ∀ b ∈ Bor (U.X k).Ψ r,
        R i (rmul x b) = bchar (laU U a n k) b * R i x ∧ T i (rmul x b) = bchar (laU U a n k) b * T i x := by
    intro i
    have hs := hsec a n hdom i.1.2.2.2.1 i.1.2.2.2.2 k
    have ht := GlobalTheory.SW.theta_holomorphic_weight E r X W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 Dc.k Dc.k' _
      (GlobalTheory.Dict.ReadAll.isSB_phiF Dc.idx Dc.sympl hdom.2 D (Mfr l) hn v₀ _ i.1.1 hvL) _ (Dc.mem _ i.1.2.2.1.2)
    obtain ⟨hd, hw⟩ := GlobalTheory.Dict.ReadAll.differentiableOn_and_bchar_equivariant_lact_castFr h hUn hwt _ ht.1 ht.2.1 (u i.1.1 i.1.2.1)
    exact ⟨hs.1, hd, fun x hx b hb => ⟨hs.2.1 x hx b hb, hw x hx b hb⟩⟩
  have unit : ∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x := by
    intro x hx hunit
    obtain ⟨Dc', hDe', -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k) a W.e hg hrpq (hk k).1 (hk k).2
      hself hdom
    have hpv' : ∀ x v j, pv (U.X k) Dc'.idx x v j =
        perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2 := by
      rw [← hDe']; exact Dc'.per_eq
    have hrt' : ∀ j, rowType (U.X k) (Dc'.idx j) = Formalism.L2.PjFree.relab c σ (W.e j).1 := by
      rw [← hDe']; exact Dc'.ty_eq
    obtain ⟨A, hMk, θ, hRd, hMn⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hg hU hr W k Dc'.bas Dc'.idx
      Dc'.sympl hpv' hrt' ⟨x, hx⟩ hunit
    have hpv : ∀ v, pv (U.X k) Dc'.idx x v = pv X Dc.idx (castFr h.psi x) v := by
      intro v
      funext j
      rw [hpv', Dc.per_eq, hDe, GlobalTheory.Dict.ReadAll.perFr_cast h]
    have hrow : ∀ j, rowType (U.X k) (Dc'.idx j) = rowType X (Dc.idx j) := by
      intro j
      rw [hrt', Dc.ty_eq, hDe]
    obtain ⟨hxm, hun, -, A', hRd', hMn', hMk'⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r W.g (U.X k) X h Dc'.bas
      Dc'.idx Dc.bas Dc.idx W.e x (U.X k).Λ (unC U k ⟨x, hx⟩) A ga Dc'.sympl Dc.sympl hx hself hUn hpv hrow
    obtain ⟨κ, hκn, hκ⟩ := hall _ hxm (hun hunit) _ A' θ (hMk' _ hMk) (hRd' θ hRd) (hMn' θ hMn)
    refine ⟨κ, hκn, fun i => ?_⟩
    have hev := hκ i.1.1 i.2.1 i.1.2.1 i.2.2.1 i.1.2.2.1.1 i.1.2.2.1.2 i.1.2.2.2.1 i.2.2.2
    have hrd : rdU U i.1.2.2.2.1 k x = evR Xo c i.1.2.2.2.1 (unC U k ⟨x, hx⟩) := by
      simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
      rfl
    simp only [R, T]
    rw [hrd]
    exact hev.trans (_root_.mul_assoc _ _ _)
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Jx R T ρ hρ hol unit
  refine ⟨C, hC0, fun Λ hΛ N hN P hP f hf hsr x hx => ?_⟩
  have hx' := hC ⟨(Λ, N, ⟨P, hP⟩, ⟨f, hf⟩), hΛ, hN, hsr⟩ x hx
  simp only [R, T] at hx'
  rw [hx', _root_.mul_assoc]
end

