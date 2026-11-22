import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeighted
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CayleyTens

theorem gram_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    PI.UpqRep.Hpk k r j i = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold PI.UpqRep.Hpk Formalism.QuantumDeterminants.Hpk
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | omega

theorem gram_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (i j : Fin (2 * r + k + 1)) :
    ∑ d, (if ε d then (1 : ℂ) else -1) * ((starRingEnd ℂ) (Q⁻¹ i d) * Q⁻¹ j d) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv (by
    have := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    simpa [Matrix.star_eq_conjTranspose] using this)
  rw [← gram_symm, ← hQ.1.2, hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [PI.UpqRep.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  by_cases h : ε d <;> simp [h, mul_comm]

theorem hhJ_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Q : Mx k r}
    (hQ : PI.UpqRep.IsCayleyU k r ε Q) (R : Rep k r) (x y : Fin (2 * r + k + 1) → R.smSub)
    (u v : Fin (2 * r + k + 1) → R.H)
    (hx : ∀ d, ((x d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • u c)
    (hy : ∀ d, ((y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • v c) :
    hhJ ε x y = hh (Formalism.QuantumDeterminants.Hpk k r) R u v := by
  unfold hhJ hh
  simp only [← gram_cayley hQ, Submodule.coe_inner, hx, hy, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem algTens_cayley : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr ep Q E F hRI hT hQ hE hF
  obtain ⟨io', pr', h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI muI io pr Q E F hRI hT.raw hQ.1.1 hE hF
  refine ⟨io', pr', ⟨h1, h2, h3, h4, h5, ?_, ?_⟩, h7⟩
  · intro s t hst y y'
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 t y')]
    exact hT.orth s t hst _ y.2 _ y'.2
  · intro s
    refine ⟨ep s, hT.ep_sq s, fun y y' => ?_⟩
    rw [hhJ_eq hQ R _ _ _ _ (h6 s y) (h6 s y'), Submodule.coe_inner]
    exact hT.iso s _ y.2 _ y'.2

end GlobalTheory.CayleyTens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfIsTypeOfParamEq
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

theorem exists_isometry_of_isType_of_param_eq :
    ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (u₁ u₂ : ℕ → ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π₁ u₁ → IsType (n + 1) r z π₂ u₂ → (∀ i ∈ Finset.Icc 1 (n + 1), u₁ i = u₂ i) → ∃ φ : V₁ ≃ₗᵢ[ℂ] V₂, ∀ h ∈ UWset (n + 1) r z, ∀ v, φ (π₁ h v) = π₂ h (φ v) := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ u₁ u₂ hz hT ht₁ ht₂ hu
  obtain ⟨hnt₁, hrep₁, hcont₁, hn₁, hirr₁, hcap₁⟩ := ht₁
  obtain ⟨hnt₂, hrep₂, hcont₂, hn₂, hirr₂, hcap₂⟩ := ht₂
  have hR₁ : IsRepW (n + 1) r z π₁ := ⟨hrep₁, hcont₁⟩
  have hR₂ : IsRepW (n + 1) r z π₂ := ⟨hrep₂, hcont₂⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), IsFrameOf (n + 1) r [z] B :=
    Qx8.frame_exists hz hT
  obtain ⟨g₁, q₁⟩ := frame_general_linear V₁ (n + 1) r (n + 1) z π₁ B hR₁ hB
  obtain ⟨g₂, q₂⟩ := frame_general_linear V₂ (n + 1) r (n + 1) z π₂ B hR₂ hB
  have i₁ : Irr (EB π₁ B) :=
    ⟨hnt₁, fun S hS => hirr₁ S (lie_stabilizer V₁ (n + 1) r z π₁ B hz hT hR₁ hB S hS)⟩
  have i₂ : Irr (EB π₂ B) :=
    ⟨hnt₂, fun S hS => hirr₂ S (lie_stabilizer V₂ (n + 1) r z π₂ B hz hT hR₂ hB S hS)⟩
  let m : Fin (n + 1) → ℂ := fun j => (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2
  have hc : ∀ w : ℂ, (∏ i ∈ Finset.Icc 1 (n + 1), (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 + (u₁ i : ℂ))) =
      cpol m w := by
    intro w
    rw [FrameExtension.prod_Icc_fin]
    unfold cpol
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [m]
    ring
  have c₁ : ∀ w v, qdet (EB π₁ B) w v = cpol m w • v := by
    intro w v
    rw [← q₁ w v, hcap₁ B hB w v, hc]
  have c₂ : ∀ w v, qdet (EB π₂ B) w v = cpol m w • v := by
    intro w v
    rw [← q₂ w v, hcap₂ B hB w v, ← hc]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by rw [hu i hi])
  obtain ⟨T, hTE⟩ := exists_linearEquiv_of_irreducible_capelli V₁ V₂ (n + 1) _ _ m g₁ g₂ i₁ i₂ c₁ c₂
  have hG := intertwiner_group_of_EB V₁ V₂ (n + 1) r z π₁ π₂ (T : V₁ →ₗ[ℂ] V₂) B hz hT hR₁ hR₂ hB hTE
  obtain ⟨φ, hφ⟩ := exists_isometry_of_intertwiner_of_irreducible V₁ V₂ (UWset (n + 1) r z)
    (fun h => π₁ h.1) (fun h => π₂ h.1) T (fun h v => hn₁ h.1 h.2 v) (fun h v => hn₂ h.1 h.2 v)
    (fun S hS => hirr₁ S (fun h hh v hv => hS ⟨h, hh⟩ v hv)) (fun h v => hG h.1 h.2 v)
  exact ⟨φ, fun h hh v => hφ ⟨h, hh⟩ v⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeries
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.LowestVector.exists_lowest_vector : _root_.PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : _root_.BranchingSupport.Rep k r), R.IsDS ε mu → ∀ (Q : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), _root_.PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ _root_.Formalism.REAL.KHighest ε E (_root_.Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (_root_.Formalism.REAL.kSpan ε E w) := by
  intro hKS k r ε mu R hDS Q E hQ hE
  have hFV := (_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ
  unfold _root_.PI.UpqRep.IsDS at hFV
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hFV
  unfold _root_.PI.UpqRep.IsKTypeOf at hS
  obtain ⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩ := hS
  have hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu := rfl
  have hstab := _root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK
  unfold _root_.BranchingSupport.Rep.IsE at hE
  set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def
  have hw0S : w0 ∈ S := S.smul_mem _ hvS
  have hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0 := by
    unfold _root_.PI.UpqRep.IsWtOn at hvw ⊢
    intro θ hθ
    rw [hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]
  have hnorm : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let w : R.smSub := ⟨w0, (hstab.1 w0 hw0S).2⟩
  have htor := _root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt
  let T : Submodule ℂ R.smSub := S.comap R.smSub.subtype
  have hT : _root_.Formalism.REAL.KStable ε E T := by
    unfold _root_.Formalism.REAL.KStable
    intro a b hab x hx
    show ((E a b x : R.smSub) : R.H) ∈ S
    rw [hE]
    exact hstab.2 a b hab x hx
  have hTfd : FiniteDimensional ℂ T := by
    let f : T →ₗ[ℂ] S :=
      LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact hval
  have hle : _root_.Formalism.REAL.kSpan ε E w ≤ T := by
    unfold _root_.Formalism.REAL.kSpan
    exact sInf_le ⟨hw0S, hT⟩
  refine ⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩
  unfold _root_.Formalism.REAL.KHighest
  refine ⟨htor.1, ?_⟩
  intro a b hab hεab
  by_contra hne
  have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
    rw [hE]
    exact hstab.2 a b hεab w0 hw0S
  have hne' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => hne (Submodule.coe_eq_zero.mp h)
  exact _root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab
    (hhigh _ _ hmem hne' (htor.2 a b))

end GlobalTheory.LowestVector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFinOrd

theorem exists_pow_mul_eq_one {F A : Type} [Field F] [Ring A] [Algebra F A] (U W : A) (e : F)
    (h : U * W = e • (W * U)) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M') (hU : U ^ M = 1) (hW : W ^ M' = 1) :
    ∃ n, 1 ≤ n ∧ (U * W) ^ n = 1 := by
  have h₁ : ∀ i : ℕ, U ^ i * W = e ^ i • (W * U ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', _root_.mul_assoc, ih, mul_smul_comm, ← _root_.mul_assoc, h, smul_mul_assoc, smul_smul,
        _root_.mul_assoc, pow_succ e]
  have h₂ : ∀ n : ℕ, ∃ t : ℕ, (U * W) ^ n = e ^ t • (W ^ n * U ^ n) := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (n + 1), ?_⟩
      rw [pow_succ, ht, smul_mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (U ^ n), ← pow_succ, h₁,
        mul_smul_comm, smul_smul, ← pow_add, ← _root_.mul_assoc, ← pow_succ]
  have h₃ : e ^ M • (1 : A) = 1 := by
    have a := h₁ M
    rw [hU, _root_.one_mul, _root_.mul_one] at a
    obtain ⟨m, rfl⟩ : ∃ m, M' = m + 1 := ⟨M' - 1, by omega⟩
    have b : W ^ m * W = W ^ m * (e ^ M • W) := congrArg _ a
    rw [mul_smul_comm, ← pow_succ, hW] at b
    exact b.symm
  obtain ⟨t, ht⟩ := h₂ (M * M')
  refine ⟨M * M' * M, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
  rw [pow_mul U, hU, one_pow, mul_comm M M', pow_mul W, hW, one_pow, _root_.mul_one] at ht
  rw [mul_comm M M', pow_mul, ht, smul_pow, one_pow, ← pow_mul, mul_comm t M, pow_mul]
  have := congrArg (· ^ t) h₃
  simpa only [smul_pow, one_pow] using this

theorem isAdd_symm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_scalar (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (hw : w.IsGen) (hw' : w'.IsGen) (Φ Φ' : Fam D.toPre F k →ₗ[F] Fam D.toPre F k)
    (hΦ : ∀ s, PhiRel D.toPre F k p w s (Φ s)) (hΦ' : ∀ s, PhiRel D.toPre F k p w' s (Φ' s)) :
    ∃ c : F, Φ = c • Φ' := by
  obtain ⟨c, -, hc⟩ := TWM.exists_ratio (F := F) D.toPre.P.isLB w hw w' hw' (fun _ _ _ => rfl)
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  refine phi_unique p w ((phiRel_iff hG p w hw _ _).1 (hΦ s)) ?_
  intro a β hβ T ρ z J hJ
  have h1 := (phiRel_iff hG p w' hw' s (Φ' s)).1 (hΦ' s) a β hβ T ρ z J hJ
  have h2 := hc _ (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z J hJ
  rw [LinearMap.smul_apply, sval_smul c (Φ' s) β ρ.left z hJ, h1, val_mul hJ, val_mul hJ]
  simp only [Units.val_mul]
  have alg : ∀ {S : Type} [CommRing S] (g a u x y y' : S), y = g * y' →
      g * (a * (u * (x * y'))) = a * (u * (x * y)) := fun g a u x y y' h => by rw [h]; ring
  exact alg _ _ _ _ _ _ h2

theorem finOrd_iff {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    FinOrd D F k p w ζ ↔ ∃ M : ℕ, 1 ≤ M ∧ ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) = 1 := by
  constructor
  · rintro ⟨M, hM, H⟩
    refine ⟨M, hM, LinearMap.ext fun s => ?_⟩
    have := H (fun i => ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)
      (fun i => Φ (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ (i : ℕ)) s)) (fun i => ⟨(hΦ _ _).2 rfl, by
        rw [DVR.isSmul_iff, Fin.val_succ, pow_succ', Module.End.mul_apply, LinearMap.smul_apply]⟩)
    exact fam_ext this
  · rintro ⟨M, hM, hpow⟩
    refine ⟨M, hM, fun ss ts H α j => ?_⟩
    have hstep : ∀ i : Fin M, ss i.succ = (ζ • Φ) (ss i.castSucc) := by
      intro i
      obtain ⟨h1, h2⟩ := H i
      rw [hΦ] at h1
      rw [DVR.isSmul_iff] at h2
      rw [h2, h1, LinearMap.smul_apply]
    have hall : ∀ i : ℕ, ∀ hi : i < M + 1,
        ss ⟨i, hi⟩ = ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ i) (ss 0) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
        exact hstep ⟨i, by omega⟩
    have hlast : ss (Fin.last M) = ss 0 := by
      rw [show Fin.last M = ⟨M, Nat.lt_succ_self M⟩ from rfl, hall M (Nat.lt_succ_self M), hpow]
      rfl
    rw [hlast]

theorem exists_pow_scalar (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Module.End F (Fam D.toPre F k)) (hΦ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) :
    ∃ c : F, Φ ^ k = c • 1 := by
  obtain ⟨c, -, hc⟩ := phiPow_of_globalFns hG V _ D F k hk p w hw
  refine ⟨c, LinearMap.ext fun s => ?_⟩
  have := hc (fun i => (Φ ^ (i : ℕ)) s) (fun i => (hΦ _ _).2 (by
    rw [Fin.val_succ, pow_succ', Module.End.mul_apply]; rfl))
  rw [DVR.isSmul_iff] at this
  exact this

end GlobalTheory.ThetaFinOrd

namespace GlobalTheory

open ThetaFinOrd in

theorem finOrd_criteria : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ (p : QkPt D.toPre F k) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))), w.IsGen → ∀ (ζ : F) (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s) → ∀ (s : Fam D.toPre F k) (M : ℕ), s ≠ 0 → 1 ≤ M → ((ζ • Φ) ^ M) s = s → FinOrd D F k p w ζ) ∧ ∀ (p p₁ p₂ : QkPt D.toPre F k), p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))) (w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → w₂.IsGen → (∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t') → ∀ ζ ζ₁ : F, FinOrd D F k p w ζ → FinOrd D F k p₁ w₁ ζ₁ → FinOrd D F k p₂ w₂ (ζ * ζ₁) := by
  intro hL V _ _ _ D F _ _ k hk
  have hG := hL.globalFns
  refine ⟨fun p w hw ζ Φ hΦ s M hs hM hfix => ?_, fun p p₁ p₂ hy hg w w₁ w₂ hw hw₁ hw₂ hc ζ ζ₁ h h₁ => ?_⟩
  · obtain ⟨c, hc⟩ := exists_pow_scalar hG hk p w hw Φ hΦ
    have e : ((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ k = ((ζ ^ k * c) ^ M) • 1 := by
      rw [← pow_mul, mul_comm M k, pow_mul, smul_pow, hc, smul_smul, smul_pow, one_pow]
    have f : ∀ n : ℕ, (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ M) ^ n) s = s := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hfix, ih]
    have g := f k
    rw [e, LinearMap.smul_apply, Module.End.one_apply] at g
    have g' : (ζ ^ k * c) ^ M = 1 := by
      have : ((ζ ^ k * c) ^ M - 1) • s = 0 := by rw [sub_smul, g, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    refine (finOrd_iff p w ζ Φ hΦ).2 ⟨M * k, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    rw [pow_mul, e, g', one_smul]
  · obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
    obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of_globalFns hG V _ D F k hk p₁ w₁ hw₁
    obtain ⟨Φ₂, hΦ₂⟩ := phiFun_of_globalFns hG V _ D F k hk p₂ w₂ hw₂
    obtain ⟨w', hw', hc'⟩ := ThetaMul.phi_mul_core hG p₁ p p₂ (hy.trans (add_comm _ _)) (isAdd_symm hg)
      w₁ w hw₁ hw
    have e₂ : Φ₂ = (Φ * Φ₁ : Module.End F (Fam D.toPre F k)) := LinearMap.ext fun s =>
      ((hΦ₂ _ _).1 (hc s _ _ ((hΦ₁ _ _).2 rfl) ((hΦ _ _).2 rfl))).symm
    obtain ⟨e, he⟩ := exists_scalar hG p₂ w₂ w' hw₂ hw' Φ₂ (Φ₁ * Φ : Module.End F (Fam D.toPre F k))
      (fun s => (hΦ₂ _ _).2 rfl) (fun s => hc' s _ _ ((hΦ _ _).2 rfl) ((hΦ₁ _ _).2 rfl))
    obtain ⟨M, hM, hU⟩ := (finOrd_iff p w ζ Φ hΦ).1 h
    obtain ⟨M', hM', hW⟩ := (finOrd_iff p₁ w₁ ζ₁ Φ₁ hΦ₁).1 h₁
    have m : (ζ • Φ : Module.End F (Fam D.toPre F k)) * (ζ₁ • Φ₁ : Module.End F (Fam D.toPre F k)) =
        (ζ * ζ₁) • Φ₂ := by
      rw [e₂, smul_mul_smul_comm]
    obtain ⟨n, hn, hp⟩ := exists_pow_mul_eq_one (F := F) (A := Module.End F (Fam D.toPre F k)) (ζ • Φ) (ζ₁ • Φ₁) e
      (by rw [m, he, smul_mul_smul_comm, smul_comm, mul_comm ζ₁ ζ]) hM hM' hU hW
    rw [m] at hp
    exact (finOrd_iff p₂ w₂ _ Φ₂ hΦ₂).2 ⟨n, hn, hp⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTensorStandardRep
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.TensorStd

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {k : ℕ}

def tenOp (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun c => ∑ d, C c d • (A ∘L PiLp.proj 2 (fun _ : Fin k => V) d)

theorem tenOp_apply (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tenOp C A y c = ∑ d, C c d • A (y d) := by
  simp [tenOp]

private lemma inner_map_of_norm_eq (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) (u w : V) :
    inner ℂ (A u) (A w) = inner ℂ u w :=
  (⟨A.toLinearMap, hA⟩ : V →ₗᵢ[ℂ] V).inner_map_map u w

theorem tenOp_norm (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V)
    (hC : ∀ d e, ∑ c, C c e * star (C c d) = if e = d then 1 else 0) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (y : PiLp 2 (fun _ : Fin k => V)) : ‖tenOp C A y‖ = ‖y‖ := by
  have key : inner ℂ (tenOp C A y) (tenOp C A y) = inner ℂ y y := by
    simp only [PiLp.inner_apply, tenOp_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, inner_map_of_norm_eq A hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ e, ∑ c, C c d * ((starRingEnd ℂ) (C c e) * inner ℂ (y e) (y d)) =
        (if d = e then 1 else 0) * inner ℂ (y e) (y d) := by
      intro e
      rw [← hC e d, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Complex.star_def]
      ring
    simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

end GlobalTheory.TensorStd

namespace GlobalTheory

open TensorStd

private lemma herm_sum_smul_left' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (u : Fin n → ℂ) :
    herm H (∑ c, a c • w c) u = ∑ c, a c * herm H (w c) u := by
  simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]

private lemma herm_sum_smul_right' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ c, a c • w c) = ∑ c, star (a c) * herm H v (w c) := by
  simp [herm, star_sum, sum_dotProduct, star_smul, smul_dotProduct]

theorem exists_tensor_standard_rep :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hiso hB
  obtain ⟨hcomp, hgrp⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB

  have hexp : ∀ h ∈ UWset k r z, ∀ d,
      h *ᵥ B d = ∑ e, herm (Hpk k r) (h *ᵥ B d) (B e) • B e := by
    intro h hh d
    obtain ⟨h1, h2⟩ := (hgrp h hh).1 (B d) (hB.1 d) (hB.2.2 d z (List.mem_singleton_self z))
    exact hcomp _ h1 h2
  refine ⟨fun h => tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    rw [tenOp_apply, hπ.1.1]
    simp [hB.2.1]
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    simp only [ContinuousLinearMap.comp_apply, tenOp_apply, hπ.1.2 a ha b hb, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← Matrix.mulVec_mulVec, hexp b hb d, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_smul_left']
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · rw [continuousOn_clm_apply]
    intro y
    have hrepr : ∀ h, tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h) y =
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm
          (fun c => ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
      intro h
      exact PiLp.ext fun c => by rw [tenOp_apply]; rfl
    simp only [hrepr]
    refine (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn ?_
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    refine ContinuousOn.smul ?_ (hπ.2.clm_apply continuousOn_const)
    exact Continuous.continuousOn (by unfold herm; fun_prop)
  · intro h hh y
    refine tenOp_norm _ _ (fun d e => ?_) (hiso h hh) y
    have hpres := (hgrp h hh).2.1 (B e) (B d)
    rw [hB.2.1 e d] at hpres
    rw [← hpres]
    conv_rhs => rw [hexp h hh d, herm_sum_smul_right']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · intro h hh y c
    exact tenOp_apply _ _ _ _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLetterMulBoundedFactorMemNormalFormSpanStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ X ∈ hats d.L, ∀ b ∈ bmon d, X * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | exact GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mul_bmon_mem_nfSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersProdMulMultiplierLeibnizStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hatLetters_prod_mul_multiplier_leibniz : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ hats L) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  first | exact @GlobalTheory.HatNF.prod_hats_mul_multiplier | exact GlobalTheory.HatNF.prod_hats_mul_multiplier | (intros; apply GlobalTheory.HatNF.prod_hats_mul_multiplier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriLoweringStepGlTensorDualStandardStatement
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pieri_lowering_step_gl_tensor_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ j, L j ≠ L l - 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l - 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.pieri_step_lowering | exact GlobalTheory.WigSh.pieri_step_lowering | (intros; apply GlobalTheory.WigSh.pieri_step_lowering <;> assumption)
end

