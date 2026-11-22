import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0008
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactGen
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ}

private def compR (D : InfD σ m) (i : Fin (m + 1)) :
    mixedEmbedding.mixedSpace E →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp
      (D.e.toRingHom.comp (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom))

private theorem continuous_compR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (compR D i) := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace E).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  have h1 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    rw [← he]; exact (GroundTheory.Global.homeomorphMixedSpace E).symm.continuous
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = ⇑(GroundTheory.Global.homeomorphMixedSpace F) := by
      funext x; rw [GroundTheory.Global.homeomorphMixedSpace_apply]
    rw [this]; exact (GroundTheory.Global.homeomorphMixedSpace F).continuous
  exact h2.comp ((continuous_apply i).comp (D.cont.comp h1))

private def compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  RingHom.mapMatrix (m := Fin n) (compR D i)

private theorem continuous_compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (compM D n i) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E) => M.map (compR D i)
  exact continuous_id.matrix_map (continuous_compR D i)

private theorem coe_compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      compM D n i (((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)) := by
  rfl

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) (Y' : archLie F n)
    (h : compM D n i (Y : ArchMatrix E n) = Y') :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG Y' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_compA, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG, ← h]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (compM D n i) (continuous_compM D n i) _
    ((NormedSpace.expSeries_radius_eq_top ℝ (ArchMatrix E n)).symm ▸ edist_lt_top _ _)

private theorem compR_along (D : InfD σ m) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k) (z : ℂ)
    (i : Fin (m + 1)) :
    compR D i (along τ z) = if i = k then along (τ.comp (algebraMap F E)) z else 0 := by
  have e : D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) =
      Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)) := by
    rw [h z, RingEquiv.apply_symm_apply]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    (D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) i) = _
  rw [e]
  by_cases hik : i = k
  · subst hik
    simp
  · rw [Pi.single_eq_of_ne hik, map_zero, if_neg hik]

private def xL {K : Type} [Field K] [NumberField K] (n : ℕ) (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) : archLie K n :=
  ⟨(Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩

private theorem compM_xL (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (i : Fin (m + 1)) :
    compM D n i (xL n τ p q z : ArchMatrix E n) =
      if i = k then (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n) else 0 := by
  change (Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E)).map (compR D i) = _
  by_cases hik : i = k
  · rw [if_pos hik]
    ext1 a b
    change _ = (Matrix.single p q (along (τ.comp (algebraMap F E)) z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · rw [compR_along D h, if_pos hik]
    · simp
  · rw [if_neg hik]
    ext1 a b
    change _ = (0 : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
    split_ifs
    · rw [compR_along D h, if_neg hik]
    · simp

private theorem compA_exp_self (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n k ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) =
      (isExpLieAlgebra F n).expG (t • xL n (τ.comp (algebraMap F E)) p q z) := by
  apply compA_expG
  change compM D n k (t • (xL n τ p q z : ArchMatrix E n)) = t • (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n)
  rw [map_real_smul (compM D n k) (continuous_compM D n k), compM_xL D n h, if_pos rfl]

private theorem compA_exp_ne (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k i : Fin (m + 1)} (h : InSlot D τ k)
    (hi : i ≠ k) (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n i ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) = 1 := by
  rw [compA_expG D n i _ 0, IsExpLieAlgebra.expG_zero]
  change compM D n i (t • (xL n τ p q z : ArchMatrix E n)) = 0
  rw [map_real_smul (compM D n i) (continuous_compM D n i), compM_xL D n h, if_neg hi, smul_zero]

private theorem lact_elem {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β)
    (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) (x : archGroup K n) :
    HasDerivAt (fun t : ℝ => β (x * (isExpLieAlgebra K n).expG (t • xL n τ p q z))⁻¹)
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β x⁻¹) 0 := by
  obtain ⟨h, -, -, -, -, -, -, e⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  rw [e, inv_inv, elem, IsExpLieAlgebra.rightUAction_ι]
  exact (isExpLieAlgebra K n).hasDerivAt_rightDeriv
    (f := fun g => β g⁻¹) h (xL n τ p q z) x

private theorem leftAction_tensor_generator (D : InfD σ m) [IsTotallyComplex F] (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)) (hk : InSlot D τ k)
    (φ : Fin (m + 1) → TI F n) (β : TI E n) (hφ : ∀ i, SmoothT (φ i)) (hβ : IsTens D φ β) (p q : Fin n) (z : ℂ) :
    IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k)))
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β) := by
  have hsm : SmoothT β := (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β hβ).1 hφ
  intro g
  set x := g⁻¹ with hx
  have hg : g = x⁻¹ := by rw [hx, inv_inv]
  set τ' := τ.comp (algebraMap F E)
  set C : ℂ := ∏ i ∈ Finset.univ.erase k, φ i (compA D n i g) with hC
  have h1 := lact_elem β hsm τ p q z x
  have h2 := lact_elem (φ k) (hφ k) τ' p q z (compA D n k x)
  have e : (fun t : ℝ => β (x * (isExpLieAlgebra E n).expG (t • xL n τ p q z))⁻¹) =
      fun t : ℝ => φ k (compA D n k x * (isExpLieAlgebra F n).expG (t • xL n τ' p q z))⁻¹ * C := by
    funext t
    rw [hβ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), map_inv (compA D n k), map_mul (compA D n k),
      compA_exp_self D n hk]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [map_inv (compA D n i), map_mul (compA D n i), compA_exp_ne D n hk (Finset.ne_of_mem_erase hi), mul_one, hx,
      map_inv (compA D n i), inv_inv]
  rw [e] at h1
  have h3 := h1.unique (h2.mul_const C)
  have hxk : (compA D n k x)⁻¹ = compA D n k g := by rw [hx, map_inv (compA D n k), inv_inv]
  rw [hxk, ← hg] at h3
  rw [h3, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  rw [hC]
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactGen :
    UpperTheory.ConvolutionTheory.L1.LactGen := by
  intro F E _ _ _ _ _ _ σ m D n τ k hk φ β hφ hβ p q z
  exact UpperTheory.ConvolutionTheory.L1.leftAction_tensor_generator D n τ k hk φ β hφ hβ p q z
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchFin
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.matchFin :
    UpperTheory.ConvolutionTheory.L1.MatchFin := by
  intro F E _ _ _ _ _ σ m v D n _ _ _ _ μE μF hE hF
  have hreg : UpperTheory.ConvolutionTheory.L1.RegOk (v.adicCompletion F) n := UpperTheory.ConvolutionTheory.L1.regOkPi.1 _ n
  obtain ⟨c, hc, hμ, hφ⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit (v.adicCompletion F) (CompletionsOver E v)
    (incFin E v) (galFin σ v) m D n μE μF hE hF hreg
  refine ⟨c, hc, hμ, fun φ h1 h2 => (hφ φ h1 h2).2.2, fun φ h => ?_⟩
  obtain ⟨hcomp, hglue, -, hgc, hcc, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (v.adicCompletion F) (CompletionsOver E v) (incFin E v) (galFin σ v) m D n
  let e : (Fin (m + 1) → GL (Fin n) (v.adicCompletion F)) ≃ₜ GL (Fin n) (CompletionsOver E v) :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext fun i => hcomp g i
      right_inv := hglue
      continuous_toFun := hgc
      continuous_invFun := continuous_pi hcc }
  have hΨc : Continuous fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) :=
    continuous_finset_prod _ fun i _ => (h i).1.comp (continuous_apply i)
  have hΨs : HasCompactSupport fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i) := by
    refine HasCompactSupport.intro' (K := Set.pi Set.univ fun i => tsupport (φ i))
      (isCompact_univ_pi fun i => (h i).2) (isClosed_set_pi fun i _ => isClosed_tsupport _) ?_
    intro g hg
    obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ g i ∉ tsupport (φ i) := by
      simpa [Set.mem_pi] using hg
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)
  have htens : D.tens n φ = (fun g : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) => ∏ i, φ i (g i)) ∘ e.symm :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [htens]
    exact hΨc.comp e.symm.continuous
  · rw [htens]
    exact hΨs.comp_isClosedEmbedding e.symm.isClosedEmbedding
  · have hpush := UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) (v.adicCompletion F)) μF m φ
      (fun i => (h i).1) (fun i => (h i).2)
    rw [← hpush]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer
    congr 1
    funext g
    simp only [UpperTheory.ConvolutionTheory.L1.Split.tens, hcomp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchInf
section
open MeasureTheory NumberField

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_tens (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [T2Space S] (ι : R →+* S) (s : S →+* S) (m : ℕ) (D : UpperTheory.ConvolutionTheory.L1.Split ι s m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μ : Measure (GL (Fin n) R)) [μ.IsHaarMeasure]
    (φ : Fin (m + 1) → GL (Fin n) R → ℂ) (hφ : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) :
    Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧
      D.transfer n μ (D.tens n φ) = UpperTheory.ConvolutionTheory.L1.cvAll μ m φ := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) R)).secondCountableTopology
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_finset_prod _ fun i _ => (hφ i).1.comp (h5 i)
  · have hK : IsCompact (D.glue n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (hφ i).2.isCompact).image h4
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨fun i => D.comp n i x, fun i _ => subset_tsupport _ ?_, h2 x⟩
    intro h0
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  · rw [← UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) R) μ m φ (fun i => (hφ i).1) (fun i => (hφ i).2)]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer UpperTheory.ConvolutionTheory.L1.Split.tens
    simp only [h1]

private theorem UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_sc (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem UpperTheory.ConvolutionTheory.L1.matchInf :
    UpperTheory.ConvolutionTheory.L1.MatchInf := by
  intro F E _ _ _ _ _ σ m D n _ _ _ _ μE μF hE hF
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' F
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' E
  haveI := UpperTheory.ConvolutionTheory.L1.matchInf_sc F
  obtain ⟨c, hc, hμ, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit _ _ _ _ m D n μE μF hE hF (UpperTheory.ConvolutionTheory.L1.regOkPi.2.2 F n)
  exact ⟨c, hc, hμ, fun φ h1 h2 => (hM φ h1 h2).2.2,
    fun φ hφ => UpperTheory.ConvolutionTheory.L1.matchInf_tens _ _ _ _ m D n μF φ hφ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section Unif

variable (A : Type*) [Field A] [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A]

private theorem val_le_unif {x : A} (hx : valuation A x < 1) :
    valuation A x ≤ valuation A (GLnLocal.uniformizer A : A) := by
  let y : 𝒪[A] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[A] ^ 1 := by
    rw [pow_one, ← IsLocalRing.residue_eq_zero_iff]
    exact (GLnLocal.residue_eq_zero_iff_valuation_lt_one A y).2 hx
  simpa using (GLnLocal.mem_maximalIdeal_pow_iff A (m := 1)).1 hy

end Unif

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

private theorem ef_eq_one (hs : Function.Surjective (completionMap v w)) :
    w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  rw [← finrank_eq_ramificationIdx_mul_inertiaDeg E v w]
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion F) (w.adicCompletion E)) :=
    ⟨(completionMap v w).injective, hs⟩
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

private theorem val_map (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    Valued.v (completionMap v w x) = Valued.v x := by
  have h := ef_eq_one v w hs
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h
  rw [valued_completionMap, he, pow_one]

private theorem le_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) ≤ 1 ↔ valuation (v.adicCompletion F) x ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one, val_map v w hs]

private theorem lt_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) < 1 ↔ valuation (v.adicCompletion F) x < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).lt_one_iff_lt_one, val_map v w hs]

private theorem eq_iff (hs : Function.Surjective (completionMap v w)) (x : v.adicCompletion F) :
    valuation (w.adicCompletion E) (completionMap v w x) = 1 ↔ valuation (v.adicCompletion F) x = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one,
    (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).eq_one_iff_eq_one, val_map v w hs]

private theorem val_unif (hs : Function.Surjective (completionMap v w)) :
    Valued.v (completionMap v w (GLnLocal.uniformizer (v.adicCompletion F) : v.adicCompletion F)) =
      Valued.v (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) := by
  obtain ⟨y, hy⟩ := hs (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)
  have hB := GLnLocal.valuation_uniformizer_lt_one (w.adicCompletion E)
  have hA := GLnLocal.valuation_uniformizer_lt_one (v.adicCompletion F)
  apply le_antisymm
  · have := val_le_unif (w.adicCompletion E) ((lt_iff v w hs _).2 hA)
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_iff_le.1 this
  · rw [← hy, val_map v w hs, val_map v w hs]
    have hy1 : valuation (v.adicCompletion F) y < 1 := by
      rw [← lt_iff v w hs, hy]; exact hB
    have := val_le_unif (v.adicCompletion F) hy1
    exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_iff_le.1 this

private theorem cont_symm (hs : Function.Surjective (completionMap v w))
    (φ : v.adicCompletion F ≃+* w.adicCompletion E) (hφ : ∀ x, φ x = completionMap v w x) :
    Continuous φ.symm := by
  refine continuous_of_continuousAt_zero φ.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero (w.adicCompletion E)).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero (v.adicCompletion F))).2 ?_
  intro γ _
  obtain ⟨c, hc⟩ : ∃ c, valuation (v.adicCompletion F) c = (γ : ValueGroupWithZero (v.adicCompletion F)) := by
    exact ValuativeRel.valuation_surjective (γ : ValueGroupWithZero (v.adicCompletion F))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact γ.ne_zero hc.symm
  refine ⟨Units.mk0 (valuation (w.adicCompletion E) (φ c))
    ((Valuation.ne_zero_iff _).2 ((map_ne_zero φ).2 hc0)), trivial, fun x hx => ?_⟩
  have hx' : valuation (w.adicCompletion E) x < valuation (w.adicCompletion E) (φ c) := hx
  have h2 := (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_iff_lt.1 hx'
  have h1 : Valued.v (φ.symm x) = Valued.v x := by
    rw [← val_map v w hs, ← hφ, RingEquiv.apply_symm_apply]
  rw [hφ, val_map v w hs, ← h1] at h2
  change valuation (v.adicCompletion F) (φ.symm x) < γ
  rw [← hc]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).lt_iff_lt.2 h2

variable (n : ℕ)

private theorem map_inj : Function.Injective (mapGL n (completionMap v w)) := fun a b h =>
  Units.ext (Matrix.ext fun i j => (completionMap v w).injective
    (congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g i j) h))

private theorem integral_iff (hs : Function.Surjective (completionMap v w)) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GLnLocal.integralGL (w.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n := by
  rw [GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
  simp only [Valuation.mem_integer_iff]
  exact and_congr (forall₂_congr fun i j => le_iff v w hs _) (forall₂_congr fun i j => le_iff v w hs _)

private theorem iw_iff (hs : Function.Surjective (completionMap v w)) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n := by
  rw [GLnLocal.mem_iwahori_iff, GLnLocal.mem_iwahori_iff]
  exact and_congr (forall₂_congr fun i j => le_iff v w hs _)
    (and_congr (forall₂_congr fun i j => forall_congr' fun _ => lt_iff v w hs _)
      (forall_congr' fun i => eq_iff v w hs _))

private theorem diag_fac (hs : Function.Surjective (completionMap v w)) (ν : Fin n → ℤ) :
    ∃ d ∈ GLnLocal.iwahori (w.adicCompletion E) n, Cartan.diagPow (w.adicCompletion E) n ν =
      mapGL n (completionMap v w) (Cartan.diagPow (v.adicCompletion F) n ν) * d := by
  set a : w.adicCompletion E :=
    completionMap v w (GLnLocal.uniformizer (v.adicCompletion F) : v.adicCompletion F) with ha
  set b : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hb
  have ha0 : a ≠ 0 := (map_ne_zero _).2 (Cartan.uniformizer_ne_zero (v.adicCompletion F))
  have hb0 : b ≠ 0 := Cartan.uniformizer_ne_zero (w.adicCompletion E)
  have hu : valuation (w.adicCompletion E) (b / a) = 1 := by
    rw [(ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one, map_div₀, ha,
      val_unif v w hs, div_self ((Valuation.ne_zero_iff _).2 hb0)]
  have hz : ∀ k : ℤ, valuation (w.adicCompletion E) ((b / a) ^ k) = 1 := fun k => by
    rw [map_zpow₀, hu, one_zpow]
  obtain ⟨x, hx, hxm⟩ := GLnLocal.exists_mem_iwahori (w.adicCompletion E) n
    (Matrix.diagonal fun i => (b / a) ^ ν i)
    (fun i j => by
      by_cases h : i = j
      · subst h; rw [Matrix.diagonal_apply_eq]; exact (hz _).le
      · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le')
    (fun i j hij => by
      rw [Matrix.diagonal_apply_ne _ hij.ne', map_zero]; exact zero_lt_one)
    (fun i => by rw [Matrix.diagonal_apply_eq]; exact hz _)
  refine ⟨x, hx, Units.ext ?_⟩
  have hm : ((mapGL n (completionMap v w) (Cartan.diagPow (v.adicCompletion F) n ν) : GL (Fin n) (w.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => a ^ ν i := by
    change (Cartan.diagPow (v.adicCompletion F) n ν : Matrix (Fin n) (Fin n) (v.adicCompletion F)).map (completionMap v w) = _
    rw [Cartan.coe_diagPow, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    simp only [Function.comp_apply, map_zpow₀, ha]
  rw [Units.val_mul, hxm, hm, Cartan.coe_diagPow, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← mul_zpow, mul_div_cancel₀ _ ha0]

private theorem coset_iff (hs : Function.Surjective (completionMap v w)) (ν : Fin n → ℤ)
    (hsurj : Function.Surjective (mapGL n (completionMap v w))) (g : GL (Fin n) (v.adicCompletion F)) :
    mapGL n (completionMap v w) g ∈ GM.iwCoset w ν ↔ g ∈ GM.iwCoset v ν := by
  obtain ⟨d, hd, hD⟩ := diag_fac v w n hs ν
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', hb'⟩ := hsurj (d * b)
    refine ⟨a', (iw_iff v w n hs _).1 ha, b', (iw_iff v w n hs _).1 (hb' ▸ mul_mem hd hb), map_inj v w n ?_⟩
    rw [h, map_mul, map_mul, hb', hD]
    simp only [mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨mapGL n (completionMap v w) a, (iw_iff v w n hs _).2 ha, d⁻¹ * mapGL n (completionMap v w) b,
      mul_mem (inv_mem hd) ((iw_iff v w n hs _).2 hb), ?_⟩
    rw [map_mul, map_mul, hD]
    simp only [mul_assoc, mul_inv_cancel_left]

private theorem norm_eq (hs : Function.Surjective (completionMap v w)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left (ef_eq_one v w hs)
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [h, Ideal.inertiaDeg'_eq_inertiaDeg, hf, pow_one]

private theorem main (hs : Function.Surjective (completionMap v w)) :
    (∃ e : GL (Fin n) (v.adicCompletion F) ≃ₜ* GL (Fin n) (w.adicCompletion E),
      ∀ g, e g = mapGL n (completionMap v w) g) ∧
    (∀ g, mapGL n (completionMap v w) g ∈ GLnLocal.integralGL (w.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n) ∧
    (∀ g, mapGL n (completionMap v w) g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n) ∧
    (∀ ν g, mapGL n (completionMap v w) g ∈ GM.iwCoset w ν ↔ g ∈ GM.iwCoset v ν) ∧
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
  let φ : v.adicCompletion F ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hs⟩
  have hφ : ∀ x, φ x = completionMap v w x := fun _ => rfl
  have hc : Continuous (completionMap v w) := continuous_completionMap v w
  have hc' : Continuous φ.symm := cont_symm v w hs φ hφ
  have hl : ∀ g, mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F) (mapGL n (completionMap v w) g) = g :=
    fun g => Units.ext (Matrix.ext fun i j => φ.symm_apply_apply _)
  have hr : ∀ g, mapGL n (completionMap v w) (mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F) g) = g :=
    fun g => Units.ext (Matrix.ext fun i j => φ.apply_symm_apply _)
  have hsurj : Function.Surjective (mapGL n (completionMap v w)) := fun y => ⟨_, hr y⟩
  refine ⟨⟨{ toFun := mapGL n (completionMap v w)
             invFun := mapGL n (φ.symm : w.adicCompletion E →+* v.adicCompletion F)
             left_inv := hl
             right_inv := hr
             map_mul' := map_mul _
             continuous_toFun := Units.continuous_iff.2
               ⟨Units.continuous_val.matrix_map hc, Units.continuous_coe_inv.matrix_map hc⟩
             continuous_invFun := Units.continuous_iff.2
               ⟨Units.continuous_val.matrix_map hc', Units.continuous_coe_inv.matrix_map hc'⟩ },
      fun _ => rfl⟩, integral_iff v w n hs, iw_iff v w n hs, fun ν => coset_iff v w n hs ν hsurj,
    norm_eq v w hs⟩

end Main

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.splitLoc :
    UpperTheory.ConvolutionTheory.L1.SplitLoc := by
  intro F E _ _ _ _ _ v w hs n
  exact UpperTheory.ConvolutionTheory.L1.main v w.1 n hs
end
end

