import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalRiemannExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem NormalRiemannExtension.proof (hloc : NormalRiemannExtensionLocal.Statement)
    (hirr : NormalLocallyIrreducible.Statement) : NormalRiemannExtension.Statement := by
  intro σ _ I h U f hI hIc hh hU hf hb
  classical
  have hex : ∀ w ∈ zeroSetIn I ∩ U, ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
        Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0}) := fun w hw =>
    hloc σ I h w U f hI hIc hh hw.1 (hU.mem_nhds hw.2) hf hb
  choose! V hVo hwV hVU F hF hFf using hex

  have hagree : ∀ w ∈ zeroSetIn I ∩ U, ∀ y ∈ zeroSetIn I ∩ U, y ∈ V w → F y y = F w y := by
    intro w hw y hy hyw
    have hWo : IsOpen (V y ∩ V w) := (hVo y hy).inter (hVo w hw)
    obtain ⟨B, -, hyB, hBW, -, hdense⟩ :=
      hirr σ I h y hI hIc hh hy.1 (V y ∩ V w) (hWo.mem_nhds ⟨hwV y hy, hyw⟩)
    set S := (zeroSetIn I ∩ B) \ {z | eval z h = 0}
    have hSW : insert y S ⊆ V y ∩ V w :=
      Set.insert_subset_iff.2 ⟨⟨hwV y hy, hyw⟩, fun z hz => hBW hz.1.2⟩
    have heq : Set.EqOn (F y) (F w) S := fun z hz => by
      have hzW := hBW hz.1.2
      rw [hFf y hy ⟨⟨hz.1.1, hzW.1⟩, hz.2⟩, hFf w hw ⟨⟨hz.1.1, hzW.2⟩, hz.2⟩]
    exact heq.of_subset_closure ((hF y hy).continuousOn.mono fun z hz => (hSW hz).1)
      ((hF w hw).continuousOn.mono fun z hz => (hSW hz).2) (Set.subset_insert y S)
      (Set.insert_subset_iff.2 ⟨hdense ⟨hy.1, hyB⟩, subset_closure⟩) (Set.mem_insert y S)
  refine ⟨fun z => if z ∈ zeroSetIn I ∩ U then F z z else f z, ?_, ?_⟩
  · intro w hw
    refine ⟨V w, hVo w hw, hwV w hw, F w, hF w hw, fun y hy => ?_⟩
    simp only [if_pos hy.1]
    exact hagree w hw y hy.1 hy.2
  · intro z hz
    simp only [if_pos hz.1]
    exact hFf z hz.1 ⟨⟨hz.1.1, hwV z hz.1⟩, hz.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

theorem NullSmaller.ringKrullDim_le_of_lt_succ {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'

theorem NullSmaller.proof : NullSmaller.Statement := by
  intro n d J hJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have htop : J = ⊤ := by
      by_contra h
      have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.2 h
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      exact absurd (h0.trans_lt hJ) (by simp)
    have hempty : zeroSetEuc J = ∅ := by
      ext z
      simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
    rw [hempty, measure_empty]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk := ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)
    have hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]
      refine hk.trans_lt ?_
      have : 2 * k < 2 * (k + 1) := by omega
      exact_mod_cast this
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    simpa using h0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothExtensionStep
section
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

theorem exists_isGoodPartialLift_extend (p : ℕ) [hp : Fact p.Prime] [CharP K p] {N : Ideal B}
    {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B} (hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p)
    {L : IntermediateField F K} {φ : L →ₐ[F] B} (hgood : IsGoodPartialLift p N u ψ ⟨L, φ⟩) {x : K}
    (hx : x ∉ L) :
    ∃ σ : Σ L : IntermediateField F K, L →ₐ[F] B,
      IsGoodPartialLift p N u ψ σ ∧ PartialLiftLE ⟨L, φ⟩ σ ∧ x ∈ σ.1 := by
  let _ : Algebra L B := φ.toRingHom.toAlgebra
  have : IsScalarTower F L B := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨hxp, hφx⟩ := hgood.1 x
  let a : L := ⟨x ^ p, hxp⟩
  have hirr : Irreducible (X ^ p - Polynomial.C a) := X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hx (by
    have hb' : (b : K) ^ p = x ^ p := congrArg Subtype.val hb
    have hbx := frobenius_inj K p (show frobenius K p (b : K) = frobenius K p x by
      rw [frobenius_def, frobenius_def]; exact hb')
    rw [← hbx]
    exact b.2)
  have hmonic : (X ^ p - Polynomial.C a).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hxroot : aeval x (X ^ p - Polynomial.C a) = 0 := by simp [a]
  have hmin : minpoly L x = X ^ p - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hxroot hmonic).symm
  have hint : IsIntegral L x := ⟨_, hmonic, hxroot⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
  have hroot : aeval c (minpoly L pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, map_sub, map_pow,
      aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    show c ^ p - φ a = 0
    rw [hφx, hψ x c hc, sub_self]
  let σ₁ := pb.lift c hroot
  let L' : IntermediateField F K := IntermediateField.restrictScalars F (L⟮x⟯)
  let σ : L' →ₐ[F] B := σ₁.restrictScalars F
  have hLL' : L ≤ L' := fun y hy => (L⟮x⟯).algebraMap_mem ⟨y, hy⟩
  have hext : ∀ y : L, σ (IntermediateField.inclusion hLL' y) = φ y := fun y => σ₁.commutes y
  have hring : (Ideal.Quotient.mk N).comp (algebraMap L B) = (u : K →+* B ⧸ N).comp (algebraMap L K) :=
    RingHom.ext fun l => hgood.2 l
  refine ⟨⟨L', σ⟩, ⟨fun z => ?_, fun y => ?_⟩, ⟨hLL', hext⟩, IntermediateField.mem_adjoin_simple_self L x⟩
  · obtain ⟨h, h'⟩ := hgood.1 z
    exact ⟨hLL' h, (hext ⟨_, h⟩).trans h'⟩
  · obtain ⟨f, hf⟩ := pb.exists_eq_aeval' ⟨y.1, y.2⟩
    have hy : (y : K) = aeval x f := by
      have h' := congrArg (algebraMap (L⟮x⟯) K) hf
      rw [← Polynomial.aeval_algebraMap_apply, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.AdjoinSimple.algebraMap_gen] at h'
      exact h'
    show Ideal.Quotient.mk N (σ₁ ⟨y.1, y.2⟩) = u y
    rw [hf, PowerBasis.lift_aeval, hy, aeval_def, aeval_def, Polynomial.hom_eval₂, hring, hc]
    exact (Polynomial.hom_eval₂ _ _ _ _).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPowerUnitCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix Polynomial

noncomputable section

theorem encard_pow_eq_of_ne_zero {m : ℕ} (hm : m ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    {a : ℂ | a ^ m = t}.encard = m := by
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have hset : {a : ℂ | a ^ m = t} = ↑(nthRootsFinset m t) := by
    ext a
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hm)]
  classical
  rw [hset, Set.encard_coe_eq_coe_finsetCard, nthRootsFinset_def,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ht), hζ.card_nthRoots,
    if_pos ⟨t ^ ((m : ℂ)⁻¹), Complex.cpow_nat_inv_pow t hm⟩]

theorem powerUnitCount_of_root {d m : ℕ} {F : (Fin (d + 1) → ℂ) → Fin d → ℂ}
    {H k : (Fin (d + 1) → ℂ) → ℂ} {s : Fin (d + 1) → ℂ} (hs0 : s 0 = 0)
    (hF : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s) (hHc : ContinuousAt H s) (hHs : H s ≠ 0)
    (hk : AnalyticAt ℂ k s) (hks : k s ≠ 0) (hkm : m ≠ 0 → ∀ τ, k τ ^ m = H τ)
    (hbij : Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s)) :
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m := by
  set Ψ : (Fin (d + 1) → ℂ) → Fin (d + 1) → ℂ := fun τ => vecCons (τ 0) (F τ) with hΨ
  set Φ : (Fin (d + 1) → ℂ) → Fin (d + 1) → ℂ := fun τ => vecCons (τ 0 * k τ) (F τ) with hΦ
  have h0 : AnalyticAt ℂ (fun τ : Fin (d + 1) → ℂ => τ 0) s :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt s
  have hΨa : AnalyticAt ℂ Ψ s := by
    refine (analyticAt_pi_iff (f := fun i τ => Ψ τ i)).mpr fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hΨ] using h0
    · simpa [hΨ] using hF j
  have hΦa : AnalyticAt ℂ Φ s := by
    refine (analyticAt_pi_iff (f := fun i τ => Φ τ i)).mpr fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · show AnalyticAt ℂ (fun τ => τ 0 * k τ) s
      exact h0.mul hk
    · simpa [hΦ] using hF j
  have hΨd : HasFDerivAt Ψ (fderiv ℂ Ψ s) s := hΨa.differentiableAt.hasFDerivAt
  have hΦs : HasStrictFDerivAt Φ (fderiv ℂ Φ s) s := hΦa.hasStrictFDerivAt
  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ s) s := hΦs.hasFDerivAt

  have hΨ0 : ∀ v, fderiv ℂ Ψ s v 0 = v 0 := by
    intro v
    have h1 := hasFDerivAt_pi'.mp hΨd 0
    have h2 : HasFDerivAt (fun τ => Ψ τ 0)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0) s :=
      hasFDerivAt_apply 0 s
    exact DFunLike.congr_fun (h1.unique h2) v
  have hΦ0 : ∀ v, fderiv ℂ Φ s v 0 = k s * v 0 := by
    intro v
    have h1 := hasFDerivAt_pi'.mp hΦd 0
    have h2 : HasFDerivAt (fun τ => Φ τ 0) (s 0 • fderiv ℂ k s +
        k s • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0) s :=
      (hasFDerivAt_apply 0 s).mul hk.differentiableAt.hasFDerivAt
    have h3 := DFunLike.congr_fun (h1.unique h2) v
    simpa [hs0] using h3
  have hsucc : ∀ v (j : Fin d), fderiv ℂ Φ s v j.succ = fderiv ℂ Ψ s v j.succ := by
    intro v j
    have h1 := hasFDerivAt_pi'.mp hΦd j.succ
    have h2 := hasFDerivAt_pi'.mp hΨd j.succ
    exact DFunLike.congr_fun (h1.unique h2) v
  have hinj : Function.Injective (fderiv ℂ Φ s) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply hbij.1
    rw [map_zero]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h1 : fderiv ℂ Φ s v 0 = 0 := by rw [hv]; rfl
      rw [hΦ0] at h1
      rw [hΨ0]
      simpa [hks] using h1
    · have h1 : fderiv ℂ Φ s v j.succ = 0 := by rw [hv]; rfl
      rw [hsucc] at h1
      simpa using h1
  have hsurj : Function.Surjective
      (fderiv ℂ Φ s : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ)) :=
    LinearMap.injective_iff_surjective.mp hinj
  let e : (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ Φ s : _ →ₗ[ℂ] _) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hΦe : HasStrictFDerivAt Φ (e : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) s := by
    have he : (e : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) = fderiv ℂ Φ s :=
      ContinuousLinearMap.ext fun v => rfl
    rw [he]
    exact hΦs
  obtain ⟨φ, hφ, hsrc⟩ : ∃ φ : OpenPartialHomeomorph (Fin (d + 1) → ℂ) (Fin (d + 1) → ℂ),
      ⇑φ = Φ ∧ s ∈ φ.source :=
    ⟨_, hΦe.toOpenPartialHomeomorph_coe, hΦe.mem_toOpenPartialHomeomorph_source⟩
  have hinjΦ : Set.InjOn Φ φ.source := hφ ▸ φ.injOn
  have hΦzero : ∀ τ, τ 0 = 0 → Φ τ = vecCons 0 (F τ) := by
    intro τ hτ
    simp [hΦ, hτ]
  have hΦk : ∀ τ, m ≠ 0 → τ 0 ^ m * H τ = (τ 0 * k τ) ^ m := by
    intro τ hm
    rw [mul_pow, hkm hm τ]
  refine ⟨φ.source ∩ {τ | ‖H s‖ / 2 < ‖H τ‖}, Filter.inter_mem (φ.open_source.mem_nhds hsrc)
    (hHc.norm.eventually (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hHs)))), ?_, ?_⟩
  · rintro τ ⟨⟨hτs, -⟩, hτ0⟩ τ' ⟨⟨hτ's, -⟩, hτ'0⟩ hFF
    apply hinjΦ hτs hτ's
    rw [hΦzero τ hτ0, hΦzero τ' hτ'0, hFF]
  intro P hP hPP
  have hPn : Φ '' P ∈ 𝓝 (vecCons 0 (F s)) := by
    rw [← hΦzero s hs0, ← hφ]
    exact φ.image_mem_nhds hsrc hP
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hPn
  have hpull : ∀ (a : ℂ) (w : Fin d → ℂ), ‖a‖ < ε → w ∈ Metric.ball (F s) ε →
      ∃ τ ∈ P, Φ τ = vecCons a w := by
    intro a w ha hw
    have hmem : vecCons a w ∈ Metric.ball (vecCons 0 (F s)) ε := by
      rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · rw [Metric.mem_ball, dist_eq_norm] at hw
        simpa using (norm_le_pi_norm (w - F s) j).trans_lt hw
    obtain ⟨τ, hτP, hτ⟩ := hball hmem
    exact ⟨τ, hτP, hτ⟩
  refine ⟨Metric.ball (F s) ε, if m = 0 then ‖H s‖ / 2 else ε ^ m, Metric.isOpen_ball,
    Metric.mem_ball_self hε, ?_, ?_, ?_⟩
  · split_ifs
    · exact half_pos (norm_pos_iff.mpr hHs)
    · positivity
  · intro w hw τ hτ hτ0 hFw
    obtain ⟨τ', hτ'P, hτ'⟩ := hpull 0 w (by simpa using hε) hw
    have : τ' = τ := hinjΦ (hPP hτ'P).1 hτ.1 (by rw [hτ', hΦzero τ hτ0, hFw])
    exact this ▸ hτ'P
  · intro w hw t ht0 htρ
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl] at htρ
      have hempty : {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ 0 * H τ = t} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr ?_
        rintro τ ⟨hτP, -, hτt⟩
        have h1 : ‖H s‖ / 2 < ‖H τ‖ := (hPP hτP).2
        rw [pow_zero, one_mul] at hτt
        rw [hτt] at h1
        linarith
      rw [hempty, Set.encard_empty]
      rfl
    rw [if_neg hm] at htρ
    have himg : Φ '' {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t} =
        (fun a => vecCons a w) '' {a : ℂ | a ^ m = t} := by
      ext x
      constructor
      · rintro ⟨τ, ⟨-, hFw, hτt⟩, rfl⟩
        refine ⟨τ 0 * k τ, ?_, ?_⟩
        · show (τ 0 * k τ) ^ m = t
          rw [← hΦk τ hm]
          exact hτt
        · simp [hΦ, hFw]
      · rintro ⟨a, ha, rfl⟩
        have ha' : a ^ m = t := ha
        have hlt : ‖a‖ < ε := by
          refine lt_of_pow_lt_pow_left₀ m hε.le ?_
          rw [← norm_pow, ha']
          exact htρ
        obtain ⟨τ, hτP, hτ⟩ := hpull a w hlt hw
        have h12 := vecCons_inj.mp (show vecCons (τ 0 * k τ) (F τ) = vecCons a w from hτ)
        refine ⟨τ, ⟨hτP, h12.2, ?_⟩, hτ⟩
        rw [hΦk τ hm, h12.1]
        exact ha'
    have hcons : Function.Injective (fun a : ℂ => (vecCons a w : Fin (d + 1) → ℂ)) :=
      fun a b hab => (vecCons_inj.mp hab).1
    rw [← (hinjΦ.mono fun τ hτ => (hPP hτ.1).1).encard_image, himg, hcons.encard_image,
      encard_pow_eq_of_ne_zero hm (norm_pos_iff.mp ht0)]

theorem PowerUnitCount.proof : PowerUnitCount.Statement := by
  intro d m O F H s hO hs hs0 hF hH hHs hbij
  have hFa : ∀ j, AnalyticAt ℂ (fun τ => F τ j) s := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O _ hO (differentiableOn_pi.mp hF j) s hs
  have hHa : AnalyticAt ℂ H s := ReciprocityTheory.AnForm.Osgood.osgood (d + 1) O H hO hH s hs
  by_cases hm : m = 0
  · exact powerUnitCount_of_root (k := fun _ => 1) hs0 hFa hHa.continuousAt hHs analyticAt_const
      one_ne_zero (fun h => (h hm).elim) hbij
  · have hroot : ∀ x : ℂ, (x ^ ((m : ℂ)⁻¹)) ^ m = x := fun x => Complex.cpow_nat_inv_pow x hm
    refine powerUnitCount_of_root (k := fun τ => H s ^ ((m : ℂ)⁻¹) * ((H s)⁻¹ * H τ) ^ ((m : ℂ)⁻¹))
      hs0 hFa hHa.continuousAt hHs ?_ ?_ ?_ hbij
    · refine analyticAt_const.mul ((analyticAt_const.mul hHa).cpow analyticAt_const ?_)
      show (H s)⁻¹ * H s ∈ Complex.slitPlane
      rw [inv_mul_cancel₀ hHs]
      exact Complex.one_mem_slitPlane
    · intro h
      rw [inv_mul_cancel₀ hHs, Complex.one_cpow, mul_one] at h
      apply hHs
      rw [← hroot (H s), h, zero_pow hm]
    · intro _ τ
      rw [mul_pow, hroot, hroot, mul_inv_cancel_left₀ hHs]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionBranchLocus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionBranchLocus.proof (hL : ProperOpenProjectionLocalCover.Statement)
    (hH : FibreDiscriminantHolomorphic.Statement) (hM : MaximalCountUnbranched.Statement) :
    ProperOpenProjectionBranchLocus.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hDc hDne hmaps hprop hopen
  have loc := hL σ X B k f d A D hB hf hXB hDo hmaps hprop hopen
  choose! U g n hUo hyU hUD hg hgd hle hgen using loc

  have key : ∀ y₀ ∈ D, ∀ y ∈ U y₀, n y = n y₀ := by
    intro y₀ hy₀ y hy
    have hyD : y ∈ D := hUD y₀ hy₀ hy
    obtain ⟨t₁, ht₁, hgt₁⟩ := hgd y₀ hy₀ (U y ∩ U y₀) ((hUo y hyD).inter (hUo y₀ hy₀))
      Set.inter_subset_right ⟨y, hyU y hyD, hy⟩
    have hWo : IsOpen (U y ∩ (U y₀ ∩ g y₀ ⁻¹' {0}ᶜ)) :=
      (hUo y hyD).inter ((hg y₀ hy₀).continuousOn.isOpen_inter_preimage (hUo y₀ hy₀) isOpen_compl_singleton)
    obtain ⟨t, ht, hgt⟩ := hgd y hyD _ hWo Set.inter_subset_left
      ⟨t₁, ht₁.1, ht₁.2, by simpa using hgt₁⟩
    have e1 := (hgen y hyD t ht.1 hgt).1
    have e2 := (hgen y₀ hy₀ t ht.2.1 (by simpa using ht.2.2)).1
    exact_mod_cast e1.symm.trans e2
  obtain ⟨y₀, hy₀⟩ := hDne
  have hcont : ContinuousOn n D := by
    intro y hy
    have hc0 : ContinuousAt (fun _ : Fin d → ℂ => n y) y := continuousAt_const
    have hca : ContinuousAt n y := by
      refine hc0.congr ?_
      filter_upwards [(hUo y hy).mem_nhds (hyU y hy)] with z hz
      exact (key y hy z hz).symm
    exact hca.continuousWithinAt
  have hN : ∀ y ∈ D, n y = n y₀ := fun y hy => hDc.constant hcont hy hy₀

  have hcov : IsGenericCountCover (X ∩ B) A D (n y₀) := by
    refine ⟨fun y hy => ?_, fun y hy => ⟨U y, g y, hUo y hy, hyU y hy, hUD y hy, hg y hy, hgd y hy,
      fun z hz hgz => ?_⟩⟩
    · have := hle y hy y (hyU y hy)
      rwa [hN y hy] at this
    · obtain ⟨h1, h2⟩ := hgen y hy z hz hgz
      exact ⟨by rw [h1, hN y hy], h2⟩

  obtain ⟨ys, hysU, hgys⟩ := hgd y₀ hy₀ (U y₀) (hUo y₀ hy₀) subset_rfl ⟨y₀, hyU y₀ hy₀⟩
  have hysD : ys ∈ D := hUD y₀ hy₀ hysU
  have hcys : {x | x ∈ X ∩ B ∧ A x = ys}.encard = (n y₀ : ℕ∞) := (hgen y₀ hy₀ ys hysU hgys).1
  have hfin := Set.finite_of_encard_eq_coe hcys
  obtain ⟨l₀, hl₀⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun p : hfin.toFinset.offDiag => (p.1.1 - p.1.2 : σ → ℂ))
    (fun p => sub_ne_zero.2 (Finset.mem_offDiag.1 p.2).2.2)
  let l : (σ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  refine ⟨fibreDiscr (X ∩ B) A l (n y₀), hH σ (X ∩ B) d A D (n y₀) l hDo hmaps hprop hopen hcov,
    ⟨ys, hysD, ?_⟩, ?_⟩
  · unfold fibreDiscr
    rw [dif_pos hcys, Finset.prod_ne_zero_iff]
    intro p hp
    have := hl₀ ⟨p, hp⟩
    simpa [l, map_sub, sub_eq_zero] using this
  · intro x hx hδ
    have hc : {x' | x' ∈ X ∩ B ∧ A x' = A x}.encard = (n y₀ : ℕ∞) := by
      by_contra hne
      exact hδ (by unfold fibreDiscr; rw [dif_neg hne])
    exact hM σ (X ∩ B) d A D (n y₀) hDo hmaps hprop hopen hcov x hx hc

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ProjDegreeEqFinrankAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace Objects

variable {n d : ℕ}

theorem linPoly_eq (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    linPoly A.mulVecLin i = GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i := by
  simp [linPoly, GroundTheory.Heights₂.Heights.ComplexSets.linPoly]

theorem projHom_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.projHom J A = projAlgHom J A.mulVecLin := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
    projAlgHom, linPoly_eq]

theorem isFiniteProjection_iff (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A ↔
      IsFiniteProjection J A.mulVecLin := by
  rw [IsFiniteProjection, ← projHom_eq]
  exact ⟨fun h => ⟨h.injective, h.finite⟩, fun h => ⟨h.1, h.2⟩⟩

theorem orthoRows_eq (d n : ℕ) :
    GroundTheory.Heights₂.Heights.ComplexSets.orthoRows d n = unitaryRows d n :=
  rfl

section Degree

variable (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]

end Degree

end Objects

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

