import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsProj
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem absProj_ext {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : D → H) (hd : ∀ w : H, (∀ v : D, inner ℂ w (e v) = 0) → w = 0) (L : H →L[ℂ] H)
    (hL : ∀ v, L (e v) = 0) (w : H) : L w = 0 := by
  have hperp : (Submodule.span ℂ (Set.range e))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    apply hd u
    intro v
    rw [inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).1 hu (e v) (Submodule.subset_span ⟨v, rfl⟩)
  have hcl : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]
  have hle : Submodule.span ℂ (Set.range e) ≤ LinearMap.ker (L : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hL v
  have hle' : (Submodule.span ℂ (Set.range e)).topologicalClosure ≤ LinearMap.ker (L : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hle L.isClosed_ker
  have hw : w ∈ LinearMap.ker (L : H →ₗ[ℂ] H) := hle' (hcl ▸ Submodule.mem_top)
  exact hw

theorem UpperTheory.V.Cj.H.absProj :
    UpperTheory.V.Cj.H.AbsProj := by
  intro G H _ _ _ _ R D A hD hiso hAR hsym hirr
  set s : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hsdef
  have hs : ∀ k : ℕ, s k ≠ 0 := fun k ↦ by
    simp only [hsdef]
    positivity
  have hs0 : Filter.Tendsto s Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense : ∀ (t : ℝ), t ≠ 0 → ∀ (w : H),
      (∀ (v : ↥D), inner ℂ w (↑(A v) + (Complex.I * ↑t) • ↑v) = 0) → w = 0 :=
    absDense G H R D A hD hiso hAR hsym hirr
  have hdense' : ∀ (k : ℕ) (w : H),
      (∀ v : ↥D, inner ℂ w (↑(A v) - (Complex.I * ↑(s k)) • ↑v) = 0) → w = 0 := by
    intro k w hw
    refine hdense (-(s k)) (neg_ne_zero.2 (hs k)) w fun v ↦ ?_
    have h : (↑(A v) : H) + (Complex.I * ((-(s k) : ℝ) : ℂ)) • (↑v : H)
        = ↑(A v) - (Complex.I * ↑(s k)) • ↑v := by
      push_cast
      rw [mul_neg, neg_smul, ← sub_eq_add_neg]
    rw [h]
    exact hw v
  have hT : ∀ k : ℕ, ∃ T : H →L[ℂ] H,
      (∀ v : ↥D, T (↑(A v) + (Complex.I * ↑(s k)) • ↑v) = ↑v) ∧ ∀ w : H, |s k| * ‖T w‖ ≤ ‖w‖ :=
    fun k ↦ absInv H D A hsym (s k) (hs k) (hdense (s k) (hs k))
  choose T hTinv hTbd using hT
  have hTR : ∀ (k : ℕ) (g : G) (w : H), T k (R g w) = R g (T k w) := by
    intro k g w
    have key := absProj_ext (fun v : ↥D ↦ (↑(A v) + (Complex.I * ↑(s k)) • ↑v : H))
      (hdense (s k) (hs k)) ((T k).comp (R g) - (R g).comp (T k)) ?_ w
    · simpa [sub_eq_zero] using key
    · intro v
      have hv : (R g) ↑v ∈ D := hD g v v.2
      have h1 : (R g) (↑(A v) + (Complex.I * ↑(s k)) • ↑v)
          = ↑(A ⟨(R g) ↑v, hv⟩) + (Complex.I * ↑(s k)) • ↑(⟨(R g) ↑v, hv⟩ : ↥D) := by
        rw [map_add, map_smul, hAR g v]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      rw [h1, hTinv k ⟨(R g) ↑v, hv⟩, hTinv k v]
      simp
  set K : Submodule ℂ H := (D.subtype ∘ₗ A).range.topologicalClosure with hKdef
  set P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - K.starProjection with hPdef
  have hPperp : ∀ (w : H) (v : ↥D), inner ℂ (P w) ↑(A v) = 0 := by
    intro w v
    have hAv : (↑(A v) : H) ∈ K :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (D.subtype ∘ₗ A) v)
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact Submodule.inner_left_of_mem_orthogonal hAv (K.sub_starProjection_mem_orthogonal w)
  have hclose : ∀ w : H, w - P w ∈ (D.subtype ∘ₗ A).range.topologicalClosure := by
    intro w
    simp only [hPdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, sub_sub_cancel]
    exact K.starProjection_apply_mem w
  have hlim := absLim H D A hsym s hs0 (fun k ↦ hdense (s k) (hs k)) hdense' T hTinv hTbd P
    hPperp hclose
  refine ⟨P, fun k ↦ (Complex.I * ↑(s k)) • T k, T, ?_, ?_, ?_, ?_, hPperp, ?_⟩
  · intro g w
    have h2 : Filter.Tendsto (fun k ↦ (Complex.I * ↑(s k)) • T k (R g w)) Filter.atTop
        (𝓝 (R g (P w))) := by
      refine (((R g).continuous.tendsto _).comp (hlim w)).congr fun k ↦ ?_
      simp [Function.comp_apply, map_smul, hTR k g w]
    exact tendsto_nhds_unique (hlim (R g w)) h2
  · intro k g w
    simp [ContinuousLinearMap.smul_apply, map_smul, hTR k g w]
  · intro k g w
    exact hTR k g w
  · intro k v
    have h := hTinv k v
    rw [map_add, map_smul] at h
    rw [ContinuousLinearMap.smul_apply]
    exact (eq_sub_of_add_eq h).symm
  · intro w
    simpa only [ContinuousLinearMap.smul_apply] using hlim w
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AppFacts
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem rT_map_on {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W) (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : ∀ φ ∈ N, A (T φ) = T (A φ)) (m : W ⊗[ℂ] (Fin d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  rw [← sum_cmp m]
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  exact Finset.sum_congr rfl fun i _ => by rw [h _ (hm i)]

private theorem rT_smLie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (N : Submodule ℂ (Sm E a)) (T : Module.End ℂ (Sm E a)) (hT : IsOp N T) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    smLie Ξ X (T.rTensor _ m) = T.rTensor _ (smLie Ξ X m) := by
  have h1 := rT_map_on N T (lie E a X) LinearMap.id (hT.lie X) m hm
  have h2 := rT_map_on N T LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (fun _ _ => rfl) m hm
  change TensorProduct.map (lie E a X) LinearMap.id (T.rTensor _ m) +
      TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (T.rTensor _ m) =
    T.rTensor _ (TensorProduct.map (lie E a X) LinearMap.id m + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) m)
  rw [map_add, h1, h2]

theorem UpperTheory.V.Cj.H.appFacts :
    UpperTheory.V.Cj.H.AppFacts := by
  intro E _ _ _ a U Ξ r hr N hN T hT q ω hω hv
  obtain ⟨-, -, hl, hc⟩ := levLin E a U Ξ q
  have hone : ∀ X i, ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) →
      lie E a (oneL E a) (T (cmp i (ω X))) = -m • T (cmp i (ω X)) := fun X i m hm => by
    rw [hT.lie _ _ (hv X i), (hl ω hω X i).2.2 m hm, map_smul]
  have hsq : ∀ X i, IsSq r (T (cmp i (ω X))) := fun X i => hN.sq _ (hT.maps _ (hv X i)) (hone X i _ hr)
  refine ⟨⟨?_, fun X i h => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, fun X i => ?_, fun X i => ?_, ?_⟩
  · intro k X
    rw [app_apply, app_apply, hω.equiv k X]
    exact rT_map_on N T _ _ (hT.rt _) _ (hv X)
  · rw [app_apply, hω.basic X i h, map_zero]
  · rw [hc]
    refine ⟨(hsq X i).left, fun u hu => ?_, hone X i⟩
    exact (hT.rt _ _ (hv X i)).trans (congrArg T ((hl ω hω X i).2.1 u hu))
  · rw [hc]
    exact hT.maps _ (hv X i)
  · rw [hc]
    exact Submodule.subset_span (hsq X i)
  · refine AlternatingMap.ext fun X => ?_
    rw [app_apply]
    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact rT_smLie Ξ N T hT _ _ (hv _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AutOf
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.autOf :
    UpperTheory.V.Cj.H.AutOf := by
  intro E _ _ _ a U hU Ξ m q ω hω X i hc hg
  have hl := (UpperTheory.V.Cj.H.levLin E a U Ξ q).2.2.1 ω hω X i
  obtain ⟨W, _, _, _, ρ, -, hρ⟩ := UpperTheory.V.Cj.H.kType E a Ξ q
  obtain ⟨T, w, hT, hw⟩ := hρ ω hω.equiv X i
  generalize cmp i (ω X) = φ at hc hg hl hw ⊢
  refine ⟨hl.1, ?_, ?_, ?_, hg⟩
  · exact Subgroup.isOpen_mono (H₁ := U)
      (H₂ := { carrier := {k | finRep E a k φ = φ}
               one_mem' := by simp
               mul_mem' := fun {x y} hx hy => by
                 rw [Set.mem_setOf_eq] at hx hy ⊢
                 rw [map_mul, Module.End.mul_apply, hy, hx]
               inv_mem' := fun {x} hx => by
                 rw [Set.mem_setOf_eq] at hx ⊢
                 conv_lhs => rw [← hx]
                 rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] })
      (fun u hu => hl.2.1 u hu) hU
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ k w, by rw [hT, hw]⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have key : ∃ c : ℂ, z φ = c • φ := by
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨t, u, rfl⟩ := hx
        exact ⟨_, hc t u⟩
      | algebraMap c => exact ⟨c, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨c + d, by rw [LinearMap.add_apply, hx, hy, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨d * c, by rw [Module.End.mul_apply, hy, map_smul, hx, mul_smul]⟩
    obtain ⟨c, h⟩ := key
    exact Submodule.mem_span_singleton.2 ⟨c, h.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasB
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H
open scoped ComplexOrder

theorem UpperTheory.V.Cj.H.casB :
    UpperTheory.V.Cj.H.CasB := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨c, hc⟩ := casXi E a n e he Ξ (-r)
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have hell : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), ell E a (toL (star X)) = ell E a (toL X) := fun X => by
    show (∑ w : InfinitePlace E, ∑ i, ((star X) i i w).re) / _ = (∑ w : InfinitePlace E, ∑ i, (X i i w).re) / _
    simp [Matrix.star_apply]
  have hS : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X))ᴴ * G = G * shift Ξ.dmat (-r) (toL (star X)) := fun X => by
    rw [shift_apply, shift_apply, hell, conjTranspose_add, add_mul, mul_add, hadj, conjTranspose_smul,
      conjTranspose_one, star_trivial (_ : ℝ), smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hQ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X) * shift Ξ.dmat (-r) (toL X))ᴴ * G =
        G * (shift Ξ.dmat (-r) (toL (star X)) * shift Ξ.dmat (-r) (toL (star X))) := fun X => by
    rw [conjTranspose_mul, mul_assoc, hS, ← mul_assoc, hS, mul_assoc]
  have h : (cas (shift Ξ.dmat (-r)) e)ᴴ * G = G * cas (shift Ξ.dmat (-r)) e := by
    unfold cas
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : star (e j).1 = (e j).1 := (e j).2
    have h2 : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
      rw [star_smul, h1]; simp
    have h3 : toL (-(Complex.I • (e j).1)) = -toL (Complex.I • (e j).1) := rfl
    rw [conjTranspose_sub, sub_mul, hQ, hQ, h1, h2, h3, map_neg, neg_mul_neg, mul_sub]
  rw [hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasCas
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.clFacts :
    UpperTheory.V.Cj.H.ClFacts := by
  intro E _ _ _ a μ _ _
  refine ⟨fun φ ψ s t hφ hψ => ?_, fun φ hl hφ h0 => ?_, fun φ g hφ => ?_, fun ψ φ F hψ e => ?_⟩
  · have hm : InL μ (s • φ + t • ψ) := by
      refine ⟨fun γ hγ g => ?_, ?_⟩
      · change s • φ.1 (γ * g) + t • ψ.1 (γ * g) = s • φ.1 g + t • ψ.1 g
        rw [hφ.1 γ hγ g, hψ.1 γ hγ g]
      · exact (hφ.2.const_smul s).add (hψ.2.const_smul t)
    refine ⟨hm, ?_⟩
    rw [cl_eq hm, cl_eq hφ, cl_eq hψ]
    exact (MemLp.toLp_add (hφ.2.const_smul s) (hψ.2.const_smul t)).trans
      (congrArg₂ (· + ·) (MemLp.toLp_const_smul s hφ.2) (MemLp.toLp_const_smul t hψ.2))
  · by_contra hne
    rw [cl_eq hφ] at h0
    exact GlobalTheory.CuspRep.CuspidalL2GL.toL2_ne_zero hφ (ContAut.continuous_of_isOpen_stab E a φ hl)
      (fun h => hne (Subtype.ext h)) h0
  · have hm : InL μ (rt E a g φ) := hφ.mul_right g
    rw [cl_eq hm, cl_eq hφ]
    exact (GlobalTheory.AutomorphicL2Unitary.right_translate_toL2 hφ g).symm
  · obtain ⟨h, hh⟩ := UpperTheory.V.Cj.H.convolution_L2_class (GA E a) (latticeGL E a) μ ψ.1
      (ContAut.continuous_of_isOpen_stab E a ψ hψ.2) hψ.1 F
    have hm : InL μ φ := by
      unfold InL
      rw [e]
      exact h
    rw [cl_eq hm, ← hh]
    congr 1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvAlg
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.cvAlg :
    UpperTheory.V.Cj.H.CvAlg := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs
  obtain ⟨hloc, hcnt⟩ := locInt G Γ μ
  obtain ⟨B, hB, hbd⟩ := cvCount G Γ μ ψ hψ hψs
  have hint : ∀ (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (x : G),
      MeasureTheory.Integrable (fun y ↦ GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) μ := by
    intro F x
    have hc : Continuous fun y : G ↦ ψ (y⁻¹ * x) :=
      hψ.comp (continuous_inv.mul continuous_const)
    have hs : HasCompactSupport fun y : G ↦ ψ (y⁻¹ * x) :=
      hψs.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
    simpa [smul_eq_mul] using (hloc F).integrable_smul_right_of_hasCompactSupport hc hs
  refine ⟨hint, ?_, ?_, ?_⟩
  · intro F F' s t
    funext x
    have hae : ∀ᵐ y ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑(s • F + t • F')) y
        = s * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y + t * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y := by
      have h := Filter.Eventually.and (MeasureTheory.Lp.coeFn_add (s • F) (t • F'))
        (Filter.Eventually.and (MeasureTheory.Lp.coeFn_smul s F)
          (MeasureTheory.Lp.coeFn_smul t F'))
      have h' := (GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff (μ := μ)).1 h
      filter_upwards [h'] with y hy
      obtain ⟨e1, e2, e3⟩ := hy
      simp only [GlobalTheory.AutomorphicL2Unitary.lift]
      rw [e1, Pi.add_apply, e2, e3]
      simp [smul_eq_mul]
    calc cv ψ (s • F + t • F') x
        = ∫ y, (s * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x))
            + t * (GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F') y * ψ (y⁻¹ * x))) ∂μ := by
          unfold UpperTheory.V.Cj.H.cv
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
          ring
      _ = (s • cv ψ F + t • cv ψ F') x := by
          rw [MeasureTheory.integral_add ((hint F x).const_mul s) ((hint F' x).const_mul t),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          simp [UpperTheory.V.Cj.H.cv, smul_eq_mul]
  · intro F γ hγ g
    unfold UpperTheory.V.Cj.H.cv
    rw [← MeasureTheory.integral_mul_left_eq_self _ γ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [GlobalTheory.AutomorphicL2Unitary.leftInv_lift _ γ hγ y, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro C hC
    have hK : IsCompact (tsupport ψ) := hψs
    obtain ⟨N, hN⟩ := hcnt (C * (tsupport ψ)⁻¹) (hC.mul hK.inv)
    refine ⟨B * (N : ℝ), fun F x hx ↦ ?_⟩
    refine hbd x N (fun g ↦ le_trans (Set.encard_le_encard ?_) (hN g)) F
    intro γ hγ
    simp only [Set.mem_setOf_eq] at hγ ⊢
    have hmem : ((γ : G) * g)⁻¹ * x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.2 hγ)
    have heq : (γ : G) * g = x * (((γ : G) * g)⁻¹ * x)⁻¹ := by group
    rw [heq]
    exact Set.mul_mem_mul hx (Set.inv_mem_inv.2 hmem)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DelLev
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} (X : Lie E a) (φ : Sm E a)
    (h : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.1 γ), fun u hu => ?_, fun m hm => ?_⟩
  · exact (LinearMap.congr_fun (lie_rt_fin X u) φ).symm.trans (congrArg (lie E a X) (h.2.1 u hu))
  · rw [lie_one_comm, h.2.2 m hm, map_smul]

private theorem adj_span (Ξ : AlgRep E a) (r : ℝ) (P : Sm E a → Prop) (hP : ∀ X φ, P φ → P (lie E a X φ)) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}) :
    smAdj Ξ r X m ∈ Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    rw [smAdj, adj_apply, smA_apply, smB_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩)
      (Submodule.subset_span ⟨_, _, hP X φ hφ, rfl⟩))
      (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private theorem k_adj (Ξ : AlgRep E a) (r : ℝ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    smK Ξ k * smAdj Ξ r (toL X) = smAdj Ξ r (toL (k.1 * X * star k.1)) * smK Ξ k := by
  obtain ⟨-, -, -, hA, hB, -⟩ := smAB E a Ξ
  refine LinearMap.ext fun m => ?_
  have h1 := LinearMap.congr_fun (hA k X) m
  have h2 := LinearMap.congr_fun (hB k X) m
  simp only [Module.End.mul_apply] at h1 h2 ⊢
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, (ellFacts E a).2.2.1 k X, LinearMap.map_smul_of_tower]

end

theorem UpperTheory.V.Cj.H.delLev :
    UpperTheory.V.Cj.H.DelLev := by
  intro E _ _ _ a n e he U Ξ r q ω
  refine ⟨fun h => ⟨delCochain E a n e he _ _ _ (fun k X => k_adj Ξ r k X.1) q ω h.equiv, fun X i hi => ?_, fun X => ?_⟩,
    fun h X => ?_⟩
  · rw [del_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.basic (Matrix.vecCons (e j) X) i.succ hi, map_zero]
  · rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ level_lie _ _ (h.val _)
  · refine mem_tens.1 (span_le_tens (P := fun φ => φ ∈ sqSub E a r) (fun _ h => h) ?_)
    rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ ((sqLie E a r).2) _ _ (mem_span_of_cmp (h _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.KugaSm
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem kugaSm_map {E : Type} [Field E] {a n : ℕ} (e : Fin n → Herm E a) {A A' : Type} [Ring A] [Module ℝ A]
    [Ring A'] [Module ℝ A'] (f : A →+* A') (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] A') (h : ∀ X, L' X = f (L X)) :
    cas L' e = f (cas L e) := by
  simp only [cas, map_sum, map_sub, map_mul, h]

private theorem kugaSm_A {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r : ℝ) :
    cas (shift (smA Ξ) r) e = (cas (shift (lie E a) r) e).rTensor (Fin Ξ.d → ℂ) := by
  refine kugaSm_map e (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)).toRingHom _ _ fun X => ?_
  change _ = (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)) _
  rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (r * ell E a X) (1 : Module.End ℂ (Sm E a)), map_smul, map_one,
    algebraMap_smul]
  rfl

private theorem kugaSm_B {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r c : ℝ) (h : HasCas Ξ r c e) :
    cas (shift (smB Ξ) (-r)) e = (c : ℂ) • 1 := by
  let f : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) (Sm E a)).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have h1 : cas (shift (smB Ξ) (-r)) e = f (cas (shift Ξ.dmat (-r)) e) := by
    refine kugaSm_map e f.toRingHom _ _ fun X => ?_
    change _ = f _
    rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (-r * ell E a X) (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul,
      map_one, algebraMap_smul, smB_apply]
    rfl
  rw [h1, show cas (shift Ξ.dmat (-r)) e = _ from h, map_smul, map_one]

theorem UpperTheory.V.Cj.H.kugaSm :
    UpperTheory.V.Cj.H.KugaSm := by
  intro E _ _ _ a n e he Ξ r c hc
  obtain ⟨a1, b1, hab, -, -, hinf⟩ := smAB E a Ξ
  obtain ⟨-, -, -, l4⟩ := ellFacts E a
  have hA := l4 _ _ r a1
  have hB := l4 _ _ (-r) b1
  have hsum : shift (smA Ξ) r + shift (smB Ξ) (-r) = smLie Ξ := by
    rw [shift_add_shift]
    exact LinearMap.ext fun X => add_sub_cancel (smA Ξ X) (smLie Ξ X)
  have hcom : ∀ X Y, Commute (shift (smA Ξ) r X) (shift (smB Ξ) (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hcas : cas (shift (smB Ξ) (-r)) e - cas (shift (smA Ξ) r) e = -(casA r c e).rTensor (Fin Ξ.d → ℂ) := by
    rw [kugaSm_A, kugaSm_B e Ξ r c hc, casA, LinearMap.rTensor_sub, LinearMap.rTensor_smul, neg_sub, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.rTensor_id]
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (shift (smB Ξ) (-r) - shift (smA Ξ) r) e (0 : Co Ξ (q + 1)) X = 0 := fun q X => by
    simp [del_apply]
  refine ⟨fun ω hω hd => ?_, fun q ω hω hd => ?_⟩
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaZero E a n e _ _ _ hcom ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply] at h
    rw [app_apply]
    exact neg_eq_zero.1 h.symm
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaSucc E a n e he _ _ _ hA hB hcom q ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply, add_zero] at h
    rw [app_apply, AlternatingMap.neg_apply]
    exact (neg_eq_iff_eq_neg.1 h.symm)
end

