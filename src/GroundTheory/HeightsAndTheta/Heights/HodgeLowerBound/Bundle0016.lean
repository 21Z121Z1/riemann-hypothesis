import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DetLineSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def GenSmooth (P : Ideal (MRing ι)) : Prop :=
  ∀ hP : P.IsPrime, haveI := hP
    ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
      Algebra.Smooth ℚ (TensorProduct ℤ ℚ (chartRingZ (genPt P) c))

def IsSncProv (P : Ideal (MRing ι)) (Bd : Finset (Ideal (MRing ι))) (d : ℕ) : Prop :=
  ∀ T ⊆ Bd, T.Nonempty →
    (∀ Q ∈ (P ⊔ ⨆ B ∈ T, B).minimalPrimes, IsHorizontal Q → IsArithVar Q (d + 1 - T.card) ∧ GenSmooth Q) ∧
      IsReduced (TensorProduct ℤ ℚ (MRing ι ⧸ (P ⊔ ⨆ B ∈ T, B)))

end Geo

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

namespace ComponentData

structure Clauses (D : ComponentData Ψ K ι) : Prop where
  genSmooth : GenSmooth D.P
  snc : IsSncProv D.P D.Bd D.n
  bd_eq : ∀ B ∈ D.Bd, ∀ W ∈ divSupp D.P (D.bdEq B), IsHorizontal W →
    W ∈ D.Bd ∧ multAt (D.P ⊔ Ideal.span {D.bdEq B}) W = 1
  metric_herm : ∀ τ z, (D.metric τ z)ᴴ = D.metric τ z
  metric_homog : ∀ τ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
    D.metric τ (fun p => c p.1 * z p) = ((∏ k, ‖c k‖ ^ (-2 * D.twist τ k) : ℝ) : ℂ) • D.metric τ z
  metric_pos : ∀ τ, ∀ z ∈ D.Xo, ∀ v : Fin D.N1 → ℂ, v ≠ 0 → (∀ a, ∑ l, evalC (D.what₂ τ a l) z * v l = 0) →
    0 < (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re
  metric_smooth : ∀ τ, ∃ U : Set (Cone ι), IsOpen U ∧ D.Xo ⊆ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z (a b : Fin D.N1) => D.metric τ z a b) U
  metric_conj : ∀ τ z, D.metric τ (fun p => starRingEnd ℂ (z p)) = (D.metric τ z).map (starRingEnd ℂ)
  logBounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ τ, ∀ z ∈ D.Xo, IsBlockUnit z →
    (∀ v : Fin D.N1 → ℂ, (∀ a, ∑ l, evalC (D.what₂ τ a l) z * v l = 0) →
      c / D.sncWeight z * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re ∧
      (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re ≤ C * ‖v‖ ^ 2) ∧
    ‖fderiv ℝ (fun z (a b : Fin D.N1) => D.metric τ z a b) z‖ ≤ C * Real.exp (D.sncWeight z / 2)
  hodge_mu : ∀ z ∈ D.Xo, ∀ (i : ι D.kMu) (r : ℂ) (g : Ψ → Matrix (Fin (D.N - D.j)) (Fin D.N1) ℂ),
    IsValAt D.P (D.muCoord i) z r → (∀ τ a l, IsValAt D.P (D.hodge τ a l) z (g τ a l)) →
    D.muLine.h z * (‖r‖ * ∏ τ, (((g τ).map (starRingEnd ℂ) * D.metric τ z * (g τ)ᵀ).det.re) ^ ((D.k0 : ℝ) / 2)) =
      ‖z ⟨D.kMu, i⟩‖
  hodge_det : ∀ τ, ∀ z ∈ D.Xo, ∀ (r : ℂ) (g : Matrix (Fin D.N) (Fin D.N1) ℂ),
    IsValAt D.P (D.detCoord τ) z r → (∀ a l, IsValAt D.P (D.basis τ a l) z (g a l)) →
    (D.detLine τ).h z * Real.sqrt ((g.map (starRingEnd ℂ) * D.metric τ z * gᵀ).det.re) = ‖r‖
  detLine_smooth : ∀ τ, IsSmoothHerm (D.detLine τ)
  muRef_smooth : IsSmoothHerm D.muRef ∧ IsConjInvariantH D.muRef
  ample_smooth : IsSmoothHerm D.ample ∧ IsConjInvariantH D.ample
  ample_pos : ∀ z ∈ mcPts D.P, ∀ w, IsConeTangent (Int.castRingHom ℂ) D.P z w → ¬ IsTorusDir z w →
    0 < leviForm (fun z => Real.log (D.ample.h z)) z w
  ample_ample : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAmpleGeneric D.P D.ample ∧
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAmpleOnFibres D.P D.ample.a
  lat : ∀ p ∈ D.S, ∀ τ r, IsSmoothHerm (D.latFl p τ r) ∧ IsConjInvariantH (D.latFl p τ r) ∧
    (∃ dn dd : K → ℕ, IsMultiHomog (D.latNum p τ r) dn ∧ IsMultiHomog (D.latDen p τ r) dd ∧
      ∀ k, (dn k : ℤ) - dd k = (D.latFl p τ r).a k) ∧
    D.latNum p τ r ∉ D.P ∧ D.latDen p τ r ∉ D.P ∧
    (∀ z ∈ mcPts D.P, (D.latFl p τ r).h z * ‖evalC (D.latDen p τ r) z‖ = ‖evalC (D.latNum p τ r) z‖) ∧
    ∀ W ∈ divSupp D.P (D.latNum p τ r) ∪ divSupp D.P (D.latDen p τ r), (IsHorizontal W ∨ charOf W ≠ p) →
      multAt (D.P ⊔ Ideal.span {D.latNum p τ r}) W = multAt (D.P ⊔ Ideal.span {D.latDen p τ r}) W
  cusp : ∀ I, IsTorusInv (D.cuspNorm I) ∧ ∀ z, 0 < D.cuspNorm I z
  cusp_psh : ∀ I, ∀ z ∈ D.Xo, ∀ w, IsConeTangent (Int.castRingHom ℂ) D.P z w →
    0 ≤ leviForm (fun z => Real.log (D.muLine.h z) / D.k0 - Real.log (D.cuspNorm I z)) z w
  reg_mu : IsRegSystem D.P D.Xo (fun z => Real.log (D.muRef.h z) / D.k0) (fun z => Real.log (D.ample.h z))
    D.sncWeight D.hodgeW D.regMu
  reg_cusp : IsRegSystemBdd D.P D.Xo (fun z => Real.log (D.muRef.h z) / D.k0) (fun z => Real.log (D.ample.h z))
    (fun z => D.hodgeW z + D.U z) D.regCusp
  reg_fl : ∀ τ r, IsRegSystem D.flagBundleIdeal D.flagComplexPointsOverX (fun w => Real.log ((fsLine (D.lineDeg τ r)).h w))
    (fun w => Real.log ((D.liftX D.ample).h w) +
      Real.log ((fsLine (Sum.elim (fun _ => 0) (fun _ => 1) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ)).h w))
    (fun w => D.sncWeight (D.xPart w)) (D.hodgeLineW τ r) (fun t => D.regFl t τ r)

def KBound (D : ComponentData Ψ K ι) (II : IntersectionSystem) : Prop :=
  ∀ W, IsAlgPt D.P W → -D.Kamp ≤ (RLine.single 1 D.ample).ht II W

end ComponentData

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

def FdegNeZero.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N), fdeg (Ψ := Ψ) (N := N) j hj ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagSign.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RootPoly Ψ N),
      IndefiniteRowSideFullHecke.LowerBoundFree.Nine.hFl II F = (-1) ^ (dimFl Ψ N + 1) * hFl Ψ N II F

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAltSumDet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace AltSumDet

def form (N r : ℕ) (V : (Fin r → Fin N) → ℂ) : MultilinearMap ℂ (fun _ : Fin r => Fin N → ℂ) ℂ :=
  ∑ q : Fin r → Fin N, V q • (MultilinearMap.mkPiAlgebra ℂ (Fin r) ℂ).compLinearMap
    (fun a => LinearMap.proj (q a))

theorem form_apply (N r : ℕ) (V : (Fin r → Fin N) → ℂ) (w : Fin r → Fin N → ℂ) :
    form N r V w = ∑ q, (∏ a, w a (q a)) * V q := by
  simp [form, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, mul_comm]

theorem sum_eq_zero_of_eq (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q)
    (w : Fin r → Fin N → ℂ) (i j : Fin r) (hw : w i = w j) (hij : i ≠ j) :
    ∑ q, (∏ a, w a (q a)) * V q = 0 := by
  have hw' : ∀ a, w (Equiv.swap i j a) = w a := by
    intro a
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hw]
    · rw [h2, hw]
    · rfl
  have hterm : ∀ q : Fin r → Fin N,
      (∏ a, w a ((q ∘ Equiv.swap i j) a)) * V (q ∘ Equiv.swap i j) = -((∏ a, w a (q a)) * V q) := by
    intro q
    have hp : ∏ a, w a ((q ∘ Equiv.swap i j) a) = ∏ a, w a (q a) := by
      calc ∏ a, w a ((q ∘ Equiv.swap i j) a)
          = ∏ a, w (Equiv.swap i j a) (q (Equiv.swap i j a)) := by
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hw' a]; rfl
        _ = ∏ a, w a (q a) := Equiv.prod_comp (Equiv.swap i j) (fun a => w a (q a))
    rw [hp, hV, Equiv.Perm.sign_swap hij]
    simp
  let e : (Fin r → Fin N) ≃ (Fin r → Fin N) := (Equiv.swap i j).arrowCongr (Equiv.refl (Fin N))
  have he : ∀ q, e q = q ∘ Equiv.swap i j := by
    intro q
    ext a
    simp [e, Equiv.arrowCongr_apply, Equiv.symm_swap]
  have hS : ∑ q, (∏ a, w a (q a)) * V q = -∑ q, (∏ a, w a (q a)) * V q := by
    rw [← Finset.sum_neg_distrib]
    conv_lhs => rw [← Equiv.sum_comp e (fun q => (∏ a, w a (q a)) * V q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [he q]
    exact hterm q
  linear_combination (1 / 2 : ℂ) * hS

def altForm (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q) :
    (Fin N → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ :=
  { form N r V with
    map_eq_zero_of_eq' := fun w i j hw hij => by
      change form N r V w = 0
      rw [form_apply]
      exact sum_eq_zero_of_eq N r V hV w i j hw hij }

theorem altForm_apply (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q)
    (w : Fin r → Fin N → ℂ) : altForm N r V hV w = ∑ q, (∏ a, w a (q a)) * V q :=
  form_apply N r V w

theorem proof : AltSumDet.Statement := by
  intro N r V A M _ hV
  let g : (Fin r → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ := (altForm N r V hV).compLinearMap A.mulVecLin
  have key := congrArg (fun F : (Fin r → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ => F (fun b a => M a b))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin r)) g)
  have hdet : (Pi.basisFun ℂ (Fin r)).det (fun b a => M a b) = M.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have h1 : g (fun b a => M a b) = ∑ q, (∏ a, (A * M) (q a) a) * V q := by
    simp only [g, AlternatingMap.compLinearMap_apply, altForm_apply, Matrix.mulVecLin_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
  have h2 : g (Pi.basisFun ℂ (Fin r)) = ∑ q, (∏ a, A (q a) a) * V q := by
    simp only [g, AlternatingMap.compLinearMap_apply, altForm_apply, Matrix.mulVecLin_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Pi.basisFun_apply]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, hdet] at key
  rw [← h1, ← h2, key, mul_comm]

end AltSumDet

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PColSpanFactor
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem ColSpanFactor.proof : ColSpanFactor.Statement := by
  intro N r h A g _hA hg hspan
  have hmem : ∀ b : Fin r, (fun p => firstCols g r h p b) ∈
      Submodule.span ℂ (Set.range fun a : Fin r => fun p => firstCols A r h p a) :=
    fun b => hspan (Submodule.subset_span ⟨b, rfl⟩)
  choose c hc using fun b => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem b)
  let M : Matrix (Fin r) (Fin r) ℂ := fun a b => c b a
  have hM : firstCols g r h = firstCols A r h * M := by
    ext p b
    rw [← congrFun (hc b) p]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨M, hM, fun hdet => ?_⟩
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hli : LinearIndependent ℂ (fun a : Fin r => fun p => firstCols g r h p a) :=
    (Matrix.linearIndependent_cols_of_det_ne_zero hg).comp _ (Fin.castLE_injective h)
  have hgx : firstCols g r h *ᵥ x = 0 := by
    rw [hM, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hsum : ∑ a, x a • (fun p => firstCols g r h p a) = 0 := by
    ext p
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using congrFun hgx p
  exact hx0 (funext fun a => Fintype.linearIndependent_iff.1 hli x hsum a)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFrameSpanTop
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem FrameSpanTop.proof : FrameSpanTop.Statement := by
  intro K _ ι _ Ω _ E _ _ N y W c f b hb
  obtain ⟨h0, -, -, hli, -⟩ := hb
  obtain ⟨k, f', c', -, -, hsum, hfr⟩ := W.frame c h0
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hsum
    · exact hk
  obtain ⟨b0, hli0, hsp0, -⟩ := hfr ⟨0, hk⟩
  let B : Module.Basis (Fin N) Ω E := Module.Basis.mk hli0 hsp0.ge
  have : FiniteDimensional Ω E := Module.Basis.finiteDimensional_of_finite B
  have hrank : Module.finrank Ω E = N := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  exact hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hrank])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFullColsFactor
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem FullColsFactor.proof : FullColsFactor.Statement := by
  intro N r h g hN hg
  obtain rfl : r = N := le_antisymm h hN
  refine ⟨g, ?_, hg⟩
  have hc : ∀ a : Fin r, Fin.castLE h a = a := fun a => Fin.ext rfl
  have h1 : firstCols (1 : Matrix (Fin r) (Fin r) ℂ) r h = 1 := by
    ext p a
    exact congrArg (fun x => (1 : Matrix (Fin r) (Fin r) ℂ) p x) (hc a)
  rw [h1, Matrix.one_mul]
  ext p a
  exact congrArg (fun x => g p x) (hc a)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFibreSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem HodgeFibreSpan.proof : HodgeFibreSpan.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D τ bfr b' R R' Rz R'z z hz hbfr hb' hF hR hR' hRz hR'z
  have hj : (jIdx D : ℕ) + 1 = D.j := by
    have := D.one_le_j
    simp only [jIdx]
    omega

  have hRR : ∀ k i, ∑ q, R' k q * R q i = if k = i then 1 else 0 := by
    intro k i
    refine Fintype.linearIndependent_iffₛ.mp hb' (fun k => ∑ q, R' k q * R q i)
      (fun k => if k = i then 1 else 0) ?_ k
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hR i]
    simp_rw [hR', Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨e, he, c, rfl, hcv⟩
    rw [← hF, Finsupp.mem_span_image_iff_linearCombination] at he
    obtain ⟨l, hl, hle⟩ := he
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hle

    have hc : ∀ q, c q = ∑ i, R q i * l i := by
      intro q
      refine Fintype.linearIndependent_iffₛ.mp hbfr c (fun q => ∑ i, R q i * l i) ?_ q
      rw [← hle]
      simp_rw [hR, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]

    have hl' : ∀ k, l k = ∑ q, R' k q * c q := by
      intro k
      simp_rw [hc, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hRR]
      simp
    set w : Fin D.N → ℂ := fun k => ∑ q, R'z k q * v q with hwdef
    have hw : ∀ k, IsValueAt D.y (l k) z (w k) := fun k => by
      rw [hl' k]
      exact LineFlag.isValueAt_sum _ _ fun q => LineFlag.isValueAt_mul (hR'z k q) (hcv q)
    have hw0 : ∀ k : Fin D.N, ¬ ((k : ℕ) < D.j) → w k = 0 := fun k hk => by
      have h0 := hw k
      rw [(Finsupp.mem_supported' _ _).mp hl k hk] at h0
      exact LineFlag.isValueAt_unique hz h0 (LineFlag.isValueAt_zero' _ _)
    have hv : v = ∑ i, w i • fun p => Rz p i := by
      funext p
      have h1 : IsValueAt D.y (c p) z (∑ i, Rz p i * w i) := by
        rw [hc p]
        exact LineFlag.isValueAt_sum _ _ fun i => LineFlag.isValueAt_mul (hRz p i) (hw i)
      rw [LineFlag.isValueAt_unique hz (hcv p) h1]
      simp [Finset.sum_apply, mul_comm]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < D.j
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)
    · rw [hw0 i hi, zero_smul]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    refine ⟨b' (Fin.castLE (jIdx D).isLt a), ?_, fun q => R q (Fin.castLE (jIdx D).isLt a), hR _,
      fun q => hRz q _⟩
    rw [← hF]
    exact Submodule.subset_span ⟨_, by simp only [Set.mem_ofPred_eq, Fin.val_castLE]; omega, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFibreSpecialise
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem HodgeFibreSpecialise.proof (hT : HodgeFrameTransition.Statement) (hS : HodgeFibreSpan.Statement)
    (hC : ColSpanFactor.Statement) (hC' : FullColsFactor.Statement) (hA : AltSumDet.Statement)
    (hP : PlueckerExpand.Statement) (hD : SameSpanAltDet.Statement) (hTop : FrameSpanTop.Statement) :
    HodgeFibreSpecialise.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D P τ b z wF wW hb hz hfib
  obtain ⟨c', f', hb', hbspan⟩ := hb
  obtain ⟨c, f, bfr, g, lF, lW, hfr, hdom, hg, hlF, hlW, hspan, hF, hW⟩ := hfib
  obtain ⟨b', R, R', Rz, R'z, hb'li, hb'span, hR, hR', hRz, hR'z, hRR⟩ :=
    hT II Ψ K ι Ω E D τ c f bfr z hz hfr hdom
  have hRdet : Rz.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hRR
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hZ : (∏ k, z ⟨k, c k⟩ ^ P.b k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hdom.1 k)
  have htw : twistFactor D.y c P.b ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
    zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hfr.1 k (Finset.mem_univ _))
  have hli := hb'.2.2.2.1
  refine ⟨?_, ?_⟩
  · have hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (jIdx D).isLt) = u '' {i | (i : ℕ) < D.j} := by
      intro u
      ext e
      simp only [Set.mem_range, Function.comp_apply, Set.mem_image, Set.mem_setOf_eq]
      have h1 := D.one_le_j
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, by rw [Fin.val_castLE]; have := a.isLt; simp only [jIdx] at this; omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by simp only [jIdx]; omega⟩, rfl⟩
    obtain ⟨M, hM, hMdet⟩ := hC D.N _ (jIdx D).isLt Rz g hRdet hg
      ((hspan.trans (hS II Ψ K ι Ω E D τ bfr b' R R' Rz R'z z hz hfr.2.2.2.1 hb'li hb'span hR hR' hRz hR'z)).le)
    obtain ⟨δ, hδ, hδφ⟩ := hD Ω (E τ) _ (b ∘ Fin.castLE (jIdx D).isLt) (b' ∘ Fin.castLE (jIdx D).isLt)
      (hli.comp _ (Fin.castLE_injective _)) (hb'li.comp _ (Fin.castLE_injective _))
      (by rw [hrange, hrange, hbspan, hb'span])
    refine ⟨δ * (twistFactor D.y c P.b)⁻¹, lF * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw),
      mul_ne_zero (mul_ne_zero hlF hMdet) hZ, fun m => ?_⟩
    obtain ⟨v, ⟨V, hV, rfl⟩, hwF⟩ := hF m
    obtain ⟨hV0, hVσ, w, hw, hsum⟩ := hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (jIdx D) m) bfr z V
      (fun p a => R p (Fin.castLE (jIdx D).isLt a)) (firstCols Rz _ (jIdx D).isLt) hz hV (fun p a => hRz _ _)
    refine ⟨_, w, ?_, hw, ?_⟩
    · have he : (fun a => ∑ q, R q (Fin.castLE (jIdx D).isLt a) • bfr q) = b' ∘ Fin.castLE (jIdx D).isLt :=
        funext fun a => (hR _).symm
      rw [hδφ, he]
      field_simp
    · rw [hwF, hM, hA D.N _ V _ M hV0 hVσ, hsum]
      ring
  · have hN : D.N ≤ (lastIdx D : ℕ) + 1 := by simp only [lastIdx]; omega
    have hsurj : Function.Surjective (Fin.castLE (lastIdx D).isLt) := fun i =>
      ⟨⟨i, lt_of_lt_of_le i.isLt hN⟩, rfl⟩
    have hrange : ∀ u : Fin D.N → E τ, Set.range (u ∘ Fin.castLE (lastIdx D).isLt) = Set.range u := by
      intro u
      rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    obtain ⟨M, hM, hMdet⟩ := hC' D.N _ (lastIdx D).isLt g hN hg
    obtain ⟨δ, hδ, hδφ⟩ := hD Ω (E τ) _ (b ∘ Fin.castLE (lastIdx D).isLt) (bfr ∘ Fin.castLE (lastIdx D).isLt)
      (hli.comp _ (Fin.castLE_injective _)) (hfr.2.2.2.1.comp _ (Fin.castLE_injective _))
      (by rw [hrange, hrange, hTop K ι Ω (E τ) D.N D.y (D.W τ) c' f' b hb',
        hTop K ι Ω (E τ) D.N D.y (D.W τ) c f bfr hfr])
    refine ⟨δ * (twistFactor D.y c P.b)⁻¹, lW * M.det * ∏ k, z ⟨k, c k⟩ ^ P.b k, mul_ne_zero hδ (inv_ne_zero htw),
      mul_ne_zero (mul_ne_zero hlW hMdet) hZ, fun m => ?_⟩
    obtain ⟨v, ⟨V, hV, rfl⟩, hwW⟩ := hW m
    have h1 : ∀ p a, IsValueAt D.y ((1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) z
        (firstCols (1 : Matrix (Fin D.N) (Fin D.N) ℂ) _ (lastIdx D).isLt p a) := by
      intro p a
      simp only [firstCols, Matrix.one_apply]
      split_ifs
      exacts [isValueAt_one_self _ _, LineFlag.isValueAt_zero' _ _]
    obtain ⟨hV0, hVσ, w, hw, hsum⟩ := hP K ι Ω (E τ) D.y c P.b D.N _ (P.gen τ (lastIdx D) m) bfr z V
      (fun p a => (1 : Matrix (Fin D.N) (Fin D.N) Ω) p (Fin.castLE (lastIdx D).isLt a)) _ hz hV h1
    refine ⟨_, w, ?_, hw, ?_⟩
    · have he : (fun a => ∑ q, (1 : Matrix (Fin D.N) (Fin D.N) Ω) q (Fin.castLE (lastIdx D).isLt a) • bfr q) =
          bfr ∘ Fin.castLE (lastIdx D).isLt := funext fun a => by simp [Matrix.one_apply]
      rw [hδφ, he]
      field_simp
    · rw [hwW, hM, hA D.N _ V _ M hV0 hVσ, hsum]
      ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBirationalRatioClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def BirationalRatioClosure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k), Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) → Subfield.closure (coneRatios y c) = ⊤

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

