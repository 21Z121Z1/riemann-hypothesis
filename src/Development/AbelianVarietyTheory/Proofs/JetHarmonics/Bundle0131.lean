import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSectionNormMultiple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeneratorsCompare

namespace GlobalTheory.RigPullExists

theorem exists_isRigPull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (f : G ⟶ G)
    [IsMonHom f] (k N : ℤ)
    (h : HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, f.left] ![N, -k])) {T : Over S}
    (σ : LB.Sec (LPow G Lr.L k T)) : ∃ σ₁ : LB.Sec (LPow G Lr.L N T), RigidNormaliserGenerators.IsRigPull G Lr f k N σ σ₁ := by
  have h1 := h.pull (snd T G).left
  rw [← fsum_comp] at h1
  obtain ⟨X0, hX0⟩ := h1.gen Lr.isLB (K' := Fin 2) ![(snd T G).left, (snd T G ≫ f).left] ![N, -k] (by
    congr 1
    funext i
    fin_cases i
    · exact (Category.comp_id _).symm
    · rfl)
  have ha : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hu : (ptSecT G (1 : T ⟶ G)).left ≫ (snd T G).left = T.hom ≫ eSec G := NormTheta.ptSec_snd
  have hu' : (ptSecT G (1 : T ⟶ G)).left ≫ (snd T G ≫ f).left = T.hom ≫ eSec G := by
    rw [Over.comp_left, ← Category.assoc, hu, Category.assoc]
    exact congrArg (T.hom ≫ ·) ha
  obtain ⟨α, hα, hn⟩ := exists_normalized_to Lr.isLB _ _ X0 hX0 (fst T G).left (ptSecT G (1 : T ⟶ G)).left
    NormTheta.ptSec_fst _ _ _ (NormTheta.rigT_isGen (T := T) Lr.rigGen (N - k)) (by
      simp only [fsum, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        hu, hu', ← Finsupp.single_add, sub_eq_add_neg])
  obtain ⟨σ₁, hσ⟩ := VVRank.exists_isTwistPull G (ψ := T ◁ f) (hm := whiskerLeft_snd _ _) Lr.isLB hα σ
  exact ⟨σ₁, α, hα, hn, hσ⟩

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F], letI := H.starRing; ∀ (a : 𝓞 E) (N : ℕ), a * star a = (N : 𝓞 E) → 0 < N → ∀ (k : ℕ) (σ : LB.Sec (LPow t.G P.U.LG.L (k : ℤ) (TF (R := V) F))), ∃ σ₁ : LB.Sec (LPow t.G P.U.LG.L ((k * N : ℕ) : ℤ) (TF (R := V) F)), RigidNormaliserGenerators.IsRigPull t.G P.U.LG (t.act.act a) (k : ℤ) ((k * N : ℕ) : ℤ) σ σ₁ := by
  intro V _ _ _ E _ _ _ H t P F _ _ a N hN _ k σ
  letI := H.starRing
  haveI := t.act.hom a
  refine exists_isRigPull P.U.LG (t.act.act a) _ _ ?_ σ
  rw [P.bundle]
  exact PullGenG.hasGen_pull t.PP t.cub t.act.toRingAct H.w0 a N hN (t.adj a) t.prim k

end GlobalTheory.RigPullExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSepDiscr
section
open NumberField TensorProduct

namespace GlobalTheory.IntSepElement

variable (E : Type) [Field E] [NumberField E]

open scoped Classical in

noncomputable def dualB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

theorem sum_dualB (z : E) :
    ∑ i, Algebra.trace ℚ E (z * integralBasis E i) • dualB E i = z := by
  classical
  conv_rhs => rw [← (dualB E).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualB, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

theorem repr_eq_trace (z : E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (dualB E i * z) := by
  classical
  have h : ∀ j, Algebra.trace ℚ E (dualB E i * integralBasis E j) = if j = i then 1 else 0 := by
    intro j
    have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
      (integralBasis E) i j
    rw [Algebra.traceForm_apply] at h
    convert h
    rfl
  conv_rhs => rw [← (integralBasis E).sum_repr z]
  rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, LinearMap.map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem trace_dualB_int (c : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualB E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← repr_eq_trace]
  exact integralBasis_repr_apply E c i

theorem sum_mul_dualB : ∑ i, integralBasis E i * dualB E i = 1 := by
  classical
  have key : ∀ z : E, Algebra.trace ℚ E ((∑ i, integralBasis E i * dualB E i) * z) = Algebra.trace ℚ E z := by
    intro z
    rw [Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) z, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_eq_trace]
    congr 1
    ring
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, key, one_mul, sub_self]

theorem discr_mul_dualB (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ y : 𝓞 E, (y : E) = ((discr E : ℤ) : E) * dualB E i := by
  classical
  have hmem : dualB E i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    refine ⟨(RingOfIntegers.basis E).repr a i, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (trace_dualB_int E a i).symm
  have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E) (fun i => by
      rw [integralBasis_apply]; exact (RingOfIntegers.isIntegral_coe _)) (Submodule.one_le.mp le_rfl) hmem
  rw [← coe_discr, Algebra.smul_def, mul_one, map_intCast] at this
  exact ⟨⟨_, this⟩, rfl⟩

theorem exists_sep_discr :
    ∃ x y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E, ∑ i, x i * y i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ a : 𝓞 E, (∑ i, (a * x i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E) = ∑ i, x i ⊗ₜ[ℤ] (a * y i) := by
  choose y hy using discr_mul_dualB E
  have hy' : ∀ i, algebraMap (𝓞 E) E (y i) = ((discr E : ℤ) : E) * dualB E i := hy
  refine ⟨RingOfIntegers.basis E, y, ?_, fun a => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_sum, map_intCast]
    simp only [map_mul, hy', ← integralBasis_apply]
    calc ∑ i, integralBasis E i * (((discr E : ℤ) : E) * dualB E i)
        = ((discr E : ℤ) : E) * ∑ i, integralBasis E i * dualB E i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_mul_dualB, mul_one]
  · have h1 : ∀ k, ∑ i, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i = a * y k := by
      intro k
      apply RingOfIntegers.coe_injective
      rw [map_sum, map_mul, hy']
      have h2 := sum_dualB E (dualB E k * algebraMap (𝓞 E) E a)
      calc ∑ i, algebraMap (𝓞 E) E ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i)
          = ((discr E : ℤ) : E) * ∑ i, Algebra.trace ℚ E
              (dualB E k * algebraMap (𝓞 E) E a * integralBasis E i) • dualB E i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have h3 := trace_dualB_int E (a * RingOfIntegers.basis E i) k
            have h4 : ((a * RingOfIntegers.basis E i : 𝓞 E) : E) = algebraMap (𝓞 E) E a * integralBasis E i := by
              rw [integralBasis_apply, ← map_mul]
            rw [h4, ← mul_assoc] at h3
            rw [h3, map_zsmul, hy', Int.cast_smul_eq_zsmul, mul_smul_comm]
        _ = _ := by rw [h2]; ring
    calc (∑ i, (a * RingOfIntegers.basis E i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E)
        = ∑ i, ∑ k, RingOfIntegers.basis E k ⊗ₜ[ℤ]
            ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E i)]
          rw [TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => by rw [← TensorProduct.tmul_sum, h1]

end GlobalTheory.IntSepElement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosure
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeKappa

theorem n1_add_eZ_le_add_card {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) (r + 1) => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r (r + 1)
  have hdual := fun J : Sub (2 * r + k + 1) (r + 1) =>
    GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) (l ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).1) (hSF ν hν0).1 hnz J
      (l (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) (r + 1), ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, l ν (ev (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • l (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) (r + 1), 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) (r + 1)) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (Formalism.QuantumDeterminants.fvec k r z)) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • l (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : l (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).1, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.WedgeKappa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem card_sigma_fibre {A B : Type} [Fintype A] (m : A → ℕ) (ty : A ≃ B) (s : A) :
    (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s).card = m s := by
  have h : (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s)
      = (Finset.univ : Finset (Fin (m s))).map (Function.Embedding.sigmaMk (β := fun s => Fin (m s)) s) := by
    ext ⟨a, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq, Finset.mem_map,
      Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem flag_of_numbering : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  intro C _ V d _ A _ m ty J _ X h
  have h1 : ∀ g s, X.rkF g (ty g s) = m g s := by
    intro g s
    unfold RowData.rkF
    simp only [h]
    convert card_sigma_fibre (m g) (ty g) s
  have h2 : ∀ g a, X.rkF g a = m g ((ty g).symm a) := by
    intro g a
    rw [← h1, Equiv.apply_symm_apply]
  refine ⟨h1, ⟨⟨fun g a c => ⟨(ty g).symm a, Fin.cast (h2 g a) c⟩, ?_, ?_⟩, fun g a c => ⟨rfl, rfl⟩⟩⟩
  · intro g a c c' hc
    exact Fin.cast_injective _ (eq_of_heq (Sigma.mk.inj hc).2)
  · intro g a c
    rw [h]
    exact Equiv.apply_symm_apply _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenSpread

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {l : ℕ}
    (a : Fin l → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem exists_defect_sum {O : Type} [CommRing O] {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H)
    (π : H ⟶ Spec (CommRingCat.of O)) (V : G.Opens) {l : ℕ} (c : Fin l → O) (t : Fin l → Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ m) z V (t i) -
          gs (g ≫ p) z ⊤ u * ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ s) z V (t i) := by
  choose f hf using fun i => EigenAll.exists_defect m s p V (t i) u
  refine ⟨∑ i, resTop _ (scal (p ≫ π) (c i)) * f i, fun Z g z hz => ?_⟩
  rw [gs_sum g z _ hz, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul g z _ hz, FieldBaseChange.gs_const _ g z _ hz, hf i Z g z hz, Category.assoc]
  ring

end GlobalTheory.EigenSpread

namespace GlobalTheory

theorem fn_eigen_equation_of_forall_geometric_point :
    ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  intro V O F _ _ _ _ _ hinj β G _ hG Z hfin hflat hred jZ hj U l c s k hyp
  let Y : Over (Spec (CommRingCat.of O)) :=
    Over.mk (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β)))
  have hY : Flat Y.hom := inferInstanceAs (Flat (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β))))
  let p : (Z ⊗ Y).left ⟶ Z.left := pullback.fst Z.hom Y.hom
  let PV : Over (Spec (CommRingCat.of V)) := Over.mk (p ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β))
  let r₀ : PV ⟶ G := Over.homMk (pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β))) (by
    change _ = pullback.fst Z.hom Y.hom ≫ Z.hom ≫ _
    rw [Category.assoc, pullback.condition, pullback.condition_assoc]
    rfl)
  let g₀ : PV ⟶ G := Over.homMk (p ≫ jZ) (by
    change _ = p ≫ Z.hom ≫ _
    rw [Category.assoc, hj])
  obtain ⟨f, hf⟩ := EigenSpread.exists_defect_sum (Y := (Z ⊗ Y).left) (r₀ * g₀).left r₀.left p Z.hom U c s k
  have h0 : f = 0 := by
    refine section_eq_zero_of_forall_geometric_point O F hinj Z Y hfin hflat hred hY _ f fun c₀ => ?_
    refine fn_ext fun x hx => ?_
    rw [EigenAll.gs_zero, gs_pull (𝟙 _) (c₀ ▷ Y).left x _ hx, Category.id_comp, hf _ _ x hx, sub_eq_zero]
    let ρ : Over.mk ((c₀ ▷ Y).left ≫ PV.hom) ⟶ PV := Over.homMk (c₀ ▷ Y).left rfl
    let e : (Pdiv.specO O F ⊗ Y).left ⟶ Spec (CommRingCat.of F) := pullback.fst (Pdiv.specO O F).hom Y.hom
    have e₁ : (c₀ ▷ Y).left ≫ p = e ≫ c₀.left := Over.whiskerRight_left_fst c₀
    have e₂ : (e ≫ c₀.left) ≫ Z.hom = e ≫ Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
      rw [Category.assoc, Over.w c₀]
      rfl
    have e₃ : (ρ ≫ r₀ * ρ ≫ g₀).left = (c₀ ▷ Y).left ≫ (r₀ * g₀).left := by
      rw [← MonObj.comp_mul]
      rfl
    have := hyp _ e c₀ (ρ ≫ r₀) (ρ ≫ g₀) (by rw [← e₁, Category.assoc]; rfl) x hx.2 (by rw [e₃]; exact hx.1)
    rw [e₃] at this
    rw [e₁, e₂]
    simp only [FieldBaseChange.constVal_specMap]
    exact this
  intro T q r g hg z hr hrg
  have hT : T.hom = q ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β) := by
    rw [← Over.w g, hg, Category.assoc, hj]
  let a : T.left ⟶ (Z ⊗ Y).left := pullback.lift q
    (pullback.lift r.left (q ≫ Z.hom) (by rw [Over.w r, hT, Category.assoc]))
    (pullback.lift_snd _ _ _).symm
  have e₁ : a ≫ p = q := pullback.lift_fst _ _ _
  let ρ : T ⟶ PV := Over.homMk a (by
    change a ≫ p ≫ _ = _
    rw [← Category.assoc, e₁, hT])
  have e₂ : a ≫ r₀.left = r.left := by
    change a ≫ pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β)) = _
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have e₃ : ρ ≫ r₀ = r := Over.OverMorphism.ext e₂
  have e₄ : ρ ≫ g₀ = g := Over.OverMorphism.ext (by
    change a ≫ p ≫ jZ = _
    rw [← Category.assoc, e₁, hg])
  have e₅ : a ≫ (r₀ * g₀).left = (r * g).left := by
    rw [← e₃, ← e₄, ← MonObj.comp_mul]
    rfl
  rw [← e₅] at hrg
  rw [← e₂] at hr
  have := hf _ a z ⟨hrg, hr⟩
  rw [h0, EigenAll.gs_zero, e₁, e₂, e₅] at this
  exact sub_eq_zero.1 this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem gap_step (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (k : ℕ) :
    gap r a (k + 1) + (if k + 1 < r then a (k + 1) else 0) = (if k < r then a k else 0) := by
  unfold gap
  by_cases h1 : k + 1 < r
  · have := h k (k + 1) (by omega) h1
    rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_pos h1, if_pos (show k < r by omega),
      Nat.add_sub_cancel]
    omega
  · by_cases h2 : k < r
    · rw [if_pos (show 1 ≤ k + 1 ∧ k + 1 ≤ r by omega), if_neg h1, if_pos h2, Nat.add_sub_cancel]
      omega
    · rw [if_neg (show ¬ (1 ≤ k + 1 ∧ k + 1 ≤ r) by omega), if_neg h1, if_neg h2]

private theorem gap_tele (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (i K : ℕ)
    (hK : i ≤ K) :
    ∑ k ∈ Finset.Icc (i + 1) K, gap r a k + (if K < r then a K else 0)
      = (if i < r then a i else 0) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, gap_step r a h K, ih]

private theorem gap_parts (r : ℕ) (a : ℕ → ℕ) (h : ∀ i j, i ≤ j → j < r → a j ≤ a i) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, k * gap r a k + K * (if K < r then a K else 0)
      = ∑ i ∈ Finset.range K, (if i < r then a i else 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_assoc, ← mul_add, gap_step r a h K,
      Finset.sum_range_succ, ← ih]
    ring

theorem gap_sums : ∀ (r : ℕ) (a : ℕ → ℕ), (∀ i j, i ≤ j → j < r → a j ≤ a i) → (∀ k, gap r a k ≠ 0 → 1 ≤ k ∧ k ≤ r) ∧ ∀ K, r ≤ K → (∀ i, i < r → ∑ k ∈ Finset.Icc (i + 1) K, gap r a k = a i) ∧ ∑ k ∈ Finset.Icc 1 K, k * gap r a k = ∑ i : Fin r, a i := by
  intro r a h
  refine ⟨fun k hk => ?_, fun K hK => ⟨fun i hi => ?_, ?_⟩⟩
  · by_contra hc
    exact hk (by unfold gap; rw [if_neg hc])
  · have := gap_tele r a h i K (by omega)
    rw [if_neg (show ¬ K < r by omega), if_pos hi, add_zero] at this
    exact this
  · have := gap_parts r a h K
    rw [if_neg (show ¬ K < r by omega), mul_zero, add_zero] at this
    rw [this, Fin.sum_univ_eq_sum_range a r, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

end GlobalTheory.RowAt
end

