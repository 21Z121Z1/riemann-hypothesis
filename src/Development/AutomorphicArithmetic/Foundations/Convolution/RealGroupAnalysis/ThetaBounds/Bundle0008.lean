import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CommonMajorant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs <;> positivity

private theorem wt_mono {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem common_majorant {F : Type} [Field F] [NumberField F] {n : ℕ} (e : Fin n → S4 F) (N : ℕ) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ i v, ‖(e i).1 v‖ ≤ B * wt K N v := by
  have h : ∀ i, ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, ‖(e i).1 v‖ ≤ B * wt K N v := by
    intro i
    obtain ⟨K, hK, hb⟩ := (wtBound F (e i)).2
    obtain ⟨B, hB⟩ := hb N
    refine ⟨K, hK, |B|, abs_nonneg B, fun v => ?_⟩
    exact (hB () (Set.mem_univ _) v).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (wt_nonneg K N v))
  choose K hK B hB hb using h
  refine ⟨⋃ i, K i, isCompact_iUnion hK, ∑ i, B i, Finset.sum_nonneg fun i _ => hB i, fun i v => ?_⟩
  calc ‖(e i).1 v‖ ≤ B i * wt (K i) N v := hb i v
    _ ≤ B i * wt (⋃ i, K i) N v :=
        mul_le_mul_of_nonneg_left (wt_mono (Set.subset_iUnion K i) N v) (hB i)
    _ ≤ (∑ i, B i) * wt (⋃ i, K i) N v :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ i))
          (wt_nonneg _ N v)

section Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E}

private theorem norm_eta (W : Weil D) (a : (A F)ˣ) : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
  have h' : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'

private theorem om_L_comm (W : Weil D) {y : GL (Fin 2) (Cinf E)} (hy : One F y) (k : G1 F) (φ : S4 F) :
    W.Om k (W.L (infGL E 2 y) φ) = W.L (infGL E 2 y) (W.Om k φ) := by
  have h := LinearMap.congr_fun (W.comm (infGL E 2 y) k) φ
  have hy' : nu F (infGL E 2 y) = 1 := hy
  rw [hy', cD_one_left] at h
  exact h.symm

private theorem norm_term (W : Weil D) {y : GL (Fin 2) (Cinf E)} (hy : One F y) (b : A F) (a : (A F)ˣ)
    (k : G1 F) (φ : S4 F) (ξ : Fin 4 → F) :
    ‖(W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 fun i => rt (ξ i)‖ =
      ab a ^ 2 * ‖(W.Om k φ).1 (D.act (infGL E 2 y)⁻¹ (sc a ξ))‖ := by
  have hy' : nu F (infGL E 2 y) = 1 := hy
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, om_L_comm W hy, W.Om_n, W.Om_m,
    W.L_apply, hy', ab_one]
  simp only [norm_mul, norm_ψ, one_mul, norm_eta, inv_one, Complex.ofReal_one, norm_one]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

end Pointwise

theorem UpperTheory.ConvolutionTheory.R2.Ff.thMaj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThMaj W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ c hc
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨K, hK, B, hB, hBe⟩ := common_majorant e N
  obtain ⟨C, hC⟩ := hN K hK c hc
  obtain ⟨C₀, hC₀⟩ := wtAct F E D
  refine ⟨n * B * |C₀| ^ N * C, 2 * N, fun y hy b a k hk hca => ?_⟩
  obtain ⟨hsum, htsum⟩ := hC a hca
  obtain ⟨cf, hcf, hk'⟩ := he k hk
  have hHt : 0 ≤ Ht y := by unfold Ht; positivity

  set T : ℝ := |C₀| ^ N * Ht y ^ (2 * N) with hT
  have hT0 : 0 ≤ T := by positivity
  have hTact : ∀ v, wt K N (D.act (infGL E 2 y)⁻¹ v) ≤ T * wt K N v := by
    intro v
    refine (hC₀ K N y v).trans (mul_le_mul_of_nonneg_right ?_ (wt_nonneg K N v))
    calc (C₀ * Ht y ^ 2) ^ N ≤ |(C₀ * Ht y ^ 2) ^ N| := le_abs_self _
      _ = T := by rw [abs_pow, abs_mul, abs_of_nonneg (pow_nonneg hHt 2), mul_pow, ← pow_mul, hT]
  have hM : 0 ≤ ab a ^ 2 * (n * B * T) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hT0)
  have hterm : ∀ ξ : Fin 4 → F, ‖(W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 fun i => rt (ξ i)‖ ≤
      (ab a ^ 2 * (n * B * T)) * wt K N (sc a ξ) := by
    intro ξ
    rw [norm_term W hy, hk']
    set u := D.act (infGL E 2 y)⁻¹ (sc a ξ) with hu
    have hval : (∑ i, cf i • e i : S4 F).1 u = ∑ i, cf i * (e i).1 u := by
      simp [Submodule.coe_sum, Finset.sum_apply]
    have hb : ‖(∑ i, cf i • e i : S4 F).1 u‖ ≤ n * B * wt K N u := by
      rw [hval]
      calc ‖∑ i, cf i * (e i).1 u‖ ≤ ∑ i, ‖cf i * (e i).1 u‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin n, B * wt K N u := Finset.sum_le_sum fun i _ => by
            rw [norm_mul]
            calc ‖cf i‖ * ‖(e i).1 u‖ ≤ 1 * (B * wt K N u) :=
                  mul_le_mul (hcf i) (hBe i u) (norm_nonneg _) zero_le_one
              _ = B * wt K N u := one_mul _
        _ = n * B * wt K N u := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    have hnB : 0 ≤ (n : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
    calc ab a ^ 2 * ‖(∑ i, cf i • e i : S4 F).1 u‖
        ≤ ab a ^ 2 * (n * B * (T * wt K N (sc a ξ))) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left (hTact _) hnB)) (sq_nonneg _)
      _ = (ab a ^ 2 * (n * B * T)) * wt K N (sc a ξ) := by ring
  have hs := hsum.hasSum.mul_left (ab a ^ 2 * (n * B * T))
  calc ‖Th (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1‖
      ≤ (ab a ^ 2 * (n * B * T)) * ∑' ξ, wt K N (sc a ξ) := tsum_of_norm_bounded hs hterm
    _ ≤ (ab a ^ 2 * (n * B * T)) * C := mul_le_mul_of_nonneg_left htsum hM
    _ = n * B * |C₀| ^ N * C * Ht y ^ (2 * N) * ab a ^ 2 := by rw [hT]; ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousScalarFour
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {F : Type} [Field F] [NumberField F]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_mono'' {F : Type} [Field F] [NumberField F]
    {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : S ⊆ S') (N : ℕ) (v : V4 F) :
    wt S N v ≤ wt S' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ S
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private noncomputable def sc4 {F : Type} [Field F] [NumberField F] : (A F)ˣ →* GL (Fin 4) (A F) :=
  Units.map (Matrix.scalar (Fin 4) : A F →+* Matrix (Fin 4) (Fin 4) (A F)).toMonoidHom

private theorem continuous_scalarFour {F : Type} [Field F] [NumberField F] :
    Continuous (sc4 (F := F)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun a : A F => Matrix.scalar (Fin 4) a
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)

private theorem scalarFour_mulVec {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (v : V4 F) :
    (sc4 a).val *ᵥ v = fun i => (a : A F) * v i := by
  funext i
  change (Matrix.scalar (Fin 4) (a : A F) *ᵥ v) i = _
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem UpperTheory.ConvolutionTheory.R2.Ff.omCpt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmCpt W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ C hC
  obtain ⟨-, hIw⟩ := iwa F
  obtain ⟨U, hUc, hU⟩ := hIw C hC
  obtain ⟨n, e, he⟩ := omFin F E D W φ hφ
  have hdom : ∀ i, Dom (Set.univ : Set Unit) fun _ => (e i).1 := fun i => (wtBound F (e i)).2
  choose Ki hKi hB using hdom
  have hK : IsCompact (⋃ i, Ki i) := isCompact_iUnion hKi
  obtain ⟨K', hK', hlin⟩ := wtLin F (sc4 '' U) (hUc.image continuous_scalarFour) _ hK
  obtain ⟨m, hm⟩ := (hUc.image (M.continuous_ab (F := F))).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hBl⟩ := hlin N
  choose Bi hBi using fun i => hB i N
  refine ⟨max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|), fun g hg v => ?_⟩
  obtain ⟨b, a, ha, k, hk, rfl⟩ := hU g hg
  obtain ⟨c, hc, hsum⟩ := he k hk
  have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [← norm_pow, h2, norm_one])
  set w : V4 F := fun i => (a : A F) * v i with hw
  have hψ : ∀ x : A F, ‖ψ x‖ = 1 := fun x => Circle.norm_coe _
  have h1 : ‖(W.Om (nU b * mD a * k) φ).1 v‖ = ab a ^ 2 * ‖(W.Om k φ).1 w‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, W.Om_n, W.Om_m, norm_mul,
      hψ, one_mul, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have h2 : (W.Om k φ).1 w = ∑ i, c i * (e i).1 w := by
    rw [hsum]
    simp [Finset.sum_apply]
  have hlinw : wt (⋃ i, Ki i) N w ≤ |B| * wt K' N v := by
    have := hBl (sc4 a) ⟨a, ha, rfl⟩ v
    rw [scalarFour_mulVec] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (wt_nonneg' _ _ _))
  have h3 : ‖(W.Om k φ).1 w‖ ≤ (∑ i, |Bi i|) * (|B| * wt K' N v) := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    calc ‖c i‖ * ‖(e i).1 w‖ ≤ 1 * ‖(e i).1 w‖ :=
          mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
      _ = ‖(e i).1 w‖ := one_mul _
      _ ≤ Bi i * wt (Ki i) N w := hBi i () (Set.mem_univ _) w
      _ ≤ |Bi i| * wt (Ki i) N w :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ |Bi i| * wt (⋃ i, Ki i) N w :=
          mul_le_mul_of_nonneg_left (wt_mono'' (Set.subset_iUnion Ki i) N w) (abs_nonneg _)
      _ ≤ |Bi i| * (|B| * wt K' N v) := mul_le_mul_of_nonneg_left hlinw (abs_nonneg _)
  have h4 : ab a ^ 2 ≤ max m 0 ^ 2 :=
    pow_le_pow_left₀ (M.ab_pos a).le ((hm ⟨a, ha, rfl⟩).trans (le_max_left _ _)) 2
  rw [h1]
  calc ab a ^ 2 * ‖(W.Om k φ).1 w‖
      ≤ max m 0 ^ 2 * ((∑ i, |Bi i|) * (|B| * wt K' N v)) :=
        mul_le_mul h4 h3 (norm_nonneg _) (by positivity)
    _ = max m 0 ^ 2 * ((∑ i, |Bi i|) * |B|) * wt K' N v := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Level W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  obtain ⟨κ, hκc, hκ⟩ := finTr F E D
  have hfo : IsOpen {k | TR.finRep F 2 k f = f} := (π.cusp f hf).1.level
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), TR.finRep F 2 (κ k) f = f := by
    have hm : {k | TR.finRep F 2 k f = f} ∈ 𝓝 (κ 1) := hfo.mem_nhds (by simp)
    exact hκc.continuousAt.eventually hm
  let S : Subgroup (GL (Fin 2) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E 2 (k * l) Φ = Φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E 2 k⁻¹ Φ = Φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E 2 k Φ = Φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_of_mem_nhds (H := S) (g := 1) ?_
  filter_upwards [lLevel F E D W φ, h1] with k hL hk
  refine Subtype.ext (funext fun g => ?_)
  change Φ.1 (g * finGL E 2 k) = Φ.1 g
  rw [hΦ, transl F E D W M, hL, hκ k]
  exact congrFun (congrArg (fun u => lift W M u φ) (congrArg Subtype.val hk)) g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SmCrit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical ContDiff

namespace UpperTheory.ConvolutionTheory.R2.Ff

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private noncomputable def invL (x : Lie E 2) : Lie E 2 := toL ((Matrix.of x)⁻¹)

private theorem invL_val (u : GL (Fin 2) (Cinf E)) : invL (toL u.val) = toL (u⁻¹).val := by
  simp [invL, Matrix.coe_units_inv]

private theorem contDiffOn_invL : ContDiffOn ℝ ∞ (invL (E := E)) (invSet E 2) := by
  have hdet : ContDiffOn ℝ ∞ (fun x : Lie E 2 => Ring.inverse (Matrix.of x).det) (invSet E 2) := by
    intro x hx
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (Matrix.of x).det :=
      hu ▸ contDiffAt_ringInverse ℝ u
    exact (h1.comp x contDiff_det.contDiffAt).contDiffWithinAt
  have hent : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => x i j := fun i j =>
    (contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)
  have hadj : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => (Matrix.adjugate (Matrix.of x)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
    · exact hent 1 1
    · exact (hent 0 1).neg
    · exact (hent 1 0).neg
    · exact hent 0 0
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hdet.mul (hadj i j).contDiffOn).congr fun x _ => ?_
  simp [invL, Matrix.inv_def]

private theorem chart_eq (Φ : GL (Fin 2) (A E) → ℂ) (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    chart Φ g = chart Φ (g * infGL E 2 u) ∘ lmul (toL (u⁻¹).val) := by
  rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem fd {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    DifferentiableAt ℝ (chart Φ g) (toL u.val) ∧
      ∀ Z, fderiv ℝ (chart Φ g) (toL u.val) Z = T (lmul (toL (u⁻¹).val) Z) (g * infGL E 2 u) := by
  have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E 2 := u.inv_mul
  have hd : DifferentiableAt ℝ (chart Φ (g * infGL E 2 u)) (lmul (toL (u⁻¹).val) (toL u.val)) := by
    rw [e1]; exact (h _).1
  have hc := hd.comp (toL u.val) (lmul (toL (u⁻¹).val)).differentiableAt
  rw [← chart_eq] at hc
  refine ⟨hc, fun Z => ?_⟩
  rw [chart_eq Φ g u, fderiv_comp _ hd (lmul (toL (u⁻¹).val)).differentiableAt, e1,
    ContinuousLinearMap.fderiv]
  exact (h _).2 _

private theorem diffOn {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) : DifferentiableOn ℝ (chart Φ g) (invSet E 2) := by
  intro x hx
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  exact (fd h g u).1.differentiableWithinAt

private theorem T_apply (T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)) (b : Module.Basis (Fin (Module.finrank ℝ (Lie E 2))) ℝ (Lie E 2))
    (Y : Lie E 2) (h : GL (Fin 2) (A E)) : T Y h = ∑ j, (b.repr Y j) • T (b j) h := by
  conv_lhs => rw [← b.sum_repr Y]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]

private theorem smN (S : Submodule ℂ (GL (Fin 2) (A E) → ℂ))
    (hS : ∀ Φ ∈ S, ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ), (∀ X, T X ∈ S) ∧
      ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (n : ℕ) : ∀ Φ ∈ S, ∀ g, ContDiffOn ℝ n (chart Φ g) (invSet E 2) := by
  induction n with
  | zero =>
    intro Φ hΦ g
    obtain ⟨T, -, h⟩ := hS Φ hΦ
    rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (diffOn h g).continuousOn
  | succ n ih =>
    intro Φ hΦ g
    obtain ⟨T, hT, h⟩ := hS Φ hΦ
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet).2 ⟨diffOn h g, by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun Z => ?_
    let b := Module.finBasis ℝ (Lie E 2)
    have hinv : ContDiffOn ℝ n (invL (E := E)) (invSet E 2) :=
      contDiffOn_invL.of_le (by exact_mod_cast le_top)
    have key : ContDiffOn ℝ n (fun x => ∑ j, (b.repr (rmul Z (invL x)) j) • chart (T (b j)) g x) (invSet E 2) :=
      ContDiffOn.sum fun j _ => ContDiffOn.smul
        ((LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn hinv)) (ih _ (hT _) g)
    refine key.congr fun x hx => ?_
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [(fd h g u).2 Z, T_apply T b, invL_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chart_val]
    rfl

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.smCrit :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], SmCrit E := by
  intro E _ _ _ S hc hd Φ hΦ g
  refine contDiffOn_infty.2 fun n => smN S (fun Φ hΦ => ?_) n Φ hΦ g
  obtain ⟨T, hT, h⟩ := hd Φ hΦ
  exact ⟨T, hT, smFre E Φ T (fun X g => hc _ (hT X) g) h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem measurable_tsum_complex {ι X : Type} [Countable ι] [MeasurableSpace X] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  have hS : MeasurableSet {x | Summable fun i => f i x} := by
    have hm : Measurable fun x => ∑' i, (‖f i x‖₊ : ENNReal) :=
      Measurable.ennreal_tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal
    have : {x | Summable fun i => f i x} = (fun x => ∑' i, (‖f i x‖₊ : ENNReal)) ⁻¹' Set.Iio ⊤ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, lt_top_iff_ne_top]
      rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
      simp only [coe_nnnorm]
      exact summable_norm_iff.symm
    rw [this]
    exact hm measurableSet_Iio
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι))
    (f := fun s => Set.indicator {x | Summable fun i => f i x} fun x => ∑ i ∈ s, f i x)
    (fun s => (Finset.measurable_sum s fun i _ => hf i).indicator hS) ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : Summable fun i => f i x
  · have h : Tendsto (fun s : Finset ι => ∑ i ∈ s, f i x) atTop (𝓝 (∑' i, f i x)) := by
      simpa [HasSum] using hx.hasSum
    simpa [Set.indicator, hx] using h
  · simp [Set.indicator, hx, tsum_eq_zero_of_not_summable hx, tendsto_const_nhds]

theorem UpperTheory.ConvolutionTheory.R2.Ff.thMeas :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThMeas W := by
  intro F E _ _ _ _ _ _ _ D W φ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hpt : ∀ v, Measurable fun g => (W.Om g φ).1 v := fun v =>
    ((W.cont φ).comp (continuous_id.prodMk continuous_const)).measurable
  have hψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp (continuous_adelicChar (K := F))
  have hhat : ∀ v, Measurable fun g => hat (W.Om g φ).1 v := by
    intro v
    have hc : Continuous fun p : G1 F × A F =>
        (W.Om p.1 φ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) :=
      ((W.cont φ).comp (continuous_fst.prodMk (continuous_const.update 1 continuous_snd))).mul
        (hψ.comp (continuous_snd.mul continuous_const).neg)
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := adeleMeasure F)).measurable
  refine ⟨?_, ?_, ?_, ?_, hhat⟩
  · exact measurable_tsum_complex _ fun ξ => hpt _
  · intro γ g
    simp only [map_mul, Module.End.mul_apply]
    exact W.th_Om γ _
  · intro r₀ r₁
    exact measurable_tsum_complex _ fun ξ => hhat _
  · intro γ g
    have h := (hatSt F E D W).row γ 0 (W.Om g φ)
    simp only [map_mul, Module.End.mul_apply]
    simpa using h
end

