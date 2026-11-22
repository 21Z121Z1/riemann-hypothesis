import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0541
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemNormsOfCongrEquiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} {X Y H : Matrix (Fin n) (Fin n) K}
    (h : X * H = H * Y) (p : K[X]) : aeval X p * H = H * aeval Y p := by
  have hpow : ∀ k : ℕ, X ^ k * H = H * Y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Matrix.mul_assoc, hpow, ← Matrix.mul_assoc,
      Algebra.commutes a H, Matrix.mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_norms_of_congr (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q)
    (hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e)
    (hιc : ∀ y, involBase Q k (ι y) = ι (cj w y))
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = eval₂ ι ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ₀.val.map (algebraMap E (w.adicCompletion E)) with hA
  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) := H₀.map (algebraMap E (w.adicCompletion E)) with hH
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := Matrix.charpoly_map _ _
  obtain ⟨f, hf⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c.val hAsep hc1.symm
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hinv
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    exact this
  have hHu : IsUnit H.det := by
    rw [hH, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet.isUnit).map _
  have hcT : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hdiv : atPl w γ₀.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h1 : cT (cj w) (aeval A f) * H = H * aeval A ((f.map (cj w)).comp (atPl w r₀)) := by
      rw [GlobalTheory.NormInert.cT_aeval, aeval_intertwine hcT, aeval_comp]
    have h2 : H * aeval A m = H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
      rw [hc2, hf, h1, Matrix.mul_assoc]
    have h3 : aeval A m = aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f := by
      have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hHu
      calc aeval A m = H⁻¹ * H * aeval A m := by rw [hHi, Matrix.one_mul]
        _ = H⁻¹ * H * (aeval A ((f.map (cj w)).comp (atPl w r₀)) * aeval A f) := by
          rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
        _ = _ := by rw [hHi, Matrix.one_mul]
    rw [map_sub, map_mul, ← h3, sub_self]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinvΦ : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = m + atPl w γ₀.val.charpoly * t := by
    rw [← ht]; ring
  have h0 : Φ (atPl w γ₀.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hz : Φ f * ib (Φ f) = inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) := by
    rw [hinvΦ, ← map_mul, hft, map_add, map_mul, h0, zero_mul, add_zero, hx]
    rfl
  have hu : IsUnit (Φ f) :=
    isUnit_of_mul_isUnit_left (by rw [hz]; exact x.isUnit.map _)
  exact ⟨hu.unit, Units.ext hz⟩

theorem mem_norms_of_congr_equiv (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    (j : w.adicCompletion E ≃+* k ⊗[maximalRealSubfield E] E)
    (hj1 : ∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e)
    (hj2 : ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (n : ℕ) (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n)
    (H₀ : Matrix (Fin n) (Fin n) E) (hdet : H₀.det ≠ 0)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E))
    (hc1 : c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) =
      (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hc2 : (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m =
      cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly)
    (x : (k ⊗[maximalRealSubfield E] plus Q)ˣ)
    (hx : inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) =
      eval₂ (((inclBase Q k).toRingHom).comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) m) :
    x ∈ norms Q k := by
  refine mem_norms_of_congr hU w hw k n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ _ (fun e => ?_) (fun y => ?_) x hx
  · change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  · change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]

end GlobalTheory.CompanionTheory.NormCongr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBound
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem JJ_preimage_box_eq_JJ_box : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB g v v'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hmono : ∀ {a a' : kˣ}, valuation k (a : k) ≤ valuation k (a' : k) →
      ∀ b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a, b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a' := by
    intro a a' haa' b hb
    have hb' : ∀ j, valuation k (b j) ≤ valuation k (a : k) := hb
    show ∀ j, valuation k (b j) ≤ valuation k (a' : k)
    exact fun j => le_trans (hb' j) haa'
  have hmin : ∀ a a' : kˣ, ∃ r : kˣ,
      valuation k (r : k) ≤ valuation k (a : k) ∧ valuation k (r : k) ≤ valuation k (a' : k) := by
    intro a a'
    rcases le_total (valuation k (a : k)) (valuation k (a' : k)) with h | h
    exacts [⟨a, le_rfl, h⟩, ⟨a', h, le_rfl⟩]
  obtain ⟨r₁, hr₁, h₁⟩ := GlobalTheory.T.shear_preserves_box_membership g
  obtain ⟨r₂, -, h₂⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₃, -, h₃⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T' hT' v'
  obtain ⟨r₄, h₄₁, h₄₂⟩ := hmin r₁ r₂
  obtain ⟨r, hr₄, hr₃⟩ := hmin r₄ r₃
  refine ⟨r, fun t ht t' hgt => ?_⟩
  set M : Set (Fin (n + 1) → k) :=
    {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'} with hM
  have hMimage : M = (fun y => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      *ᵥ y) '' (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t' : Set (Fin (n + 1) → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      show (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) ∈
          GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, SetLike.mem_coe] using hy
  have hMc : IsCompact M := by
    rw [hMimage]
    exact (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) t').image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hMm : MeasurableSet M := hMc.isClosed.measurableSet
  have hw : Continuous (GlobalTheory.CompanionTheory.MirPair.wt ψ n) := by
    unfold GlobalTheory.CompanionTheory.MirPair.wt
    exact continuous_subtype_val.comp (hψ.comp (continuous_apply (Fin.last n)).neg)
  have hf : Continuous fun x =>
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x :=
    hw.mul (GlobalTheory.T.mirabolic_coefficient_continuous T B hT v v')
  have hsub : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t : Set (Fin (n + 1) → k)) ⊆ M :=
    fun x hx => hgt x hx
  have key := GlobalTheory.T.fourier_box_integral_vanishing ν ψ c hψ hc (n + 1) t M
    (fun x => GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x)
    (GlobalTheory.CompanionTheory.MirPair.JJ ν ψ T B M v v') hMc hMm hf (by
      intro b hb
      have hbv : ∀ j, valuation k (b j) ≤ valuation k ((c * t⁻¹ : kˣ) : k) := hb
      have hb₁ := hmono (le_trans ht (le_trans hr₄ h₄₁)) b hb
      have hb₂ := hmono (le_trans ht (le_trans hr₄ h₄₂)) b hb
      have hb₃ := hmono (le_trans ht hr₃) b hb
      have hlast : valuation k (b (Fin.last n)) < 1 :=
        lt_of_le_of_lt (le_trans (hbv (Fin.last n)) (le_trans ht (le_trans hr₄ h₄₁))) hr₁
      have hinv : ∀ x, ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M :=
        fun x => h₁ b hb₁ t' x
      have h := GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hB b M v v'
        hlast (h₂ b hb₂) hinv
      rw [h₃ b hb₃] at h
      exact h)
  rw [Set.inter_eq_right.2 hsub] at key
  exact key.symm

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CompanionTheory.MixZ

theorem codimOne_holds : CodimOne := by
  intro X _ p D hD z hz
  let C : Closeds X := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C
  have hrange : Set.range I.subschemeι = closure {z} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hemb : Topology.IsEmbedding I.subschemeι := I.subschemeι.isClosedEmbedding.isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    have hs : IsIrreducible (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_singleton.closure
    haveI := Subtype.irreducibleSpace hs
    have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image
      hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective] at h2
    exact (irreducibleSpace_def _).2 h2
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = z := by
    have h1 := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact h1.eq isGenericPoint_closure
  have key := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι
    (by rw [hgen]; exact hz)
  calc topologicalKrullDim (closure ({z} : Set X))
      = topologicalKrullDim I.subscheme := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb hrange
    _ = D := key

end GlobalTheory.CompanionTheory.MixZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinetyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_unit_hilbert_ninety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ c : w.adicCompletion E, cj w c = c → Valued.v c = 1 → ∃ s : w.adicCompletion E, Valued.v s = 1 ∧ cj w s * s = c := by
  first | exact @GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | exact GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | (intros; apply GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSquareCoefficientLeDivisorBound
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeSq

theorem norm_char_prime {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖χ (p : ZMod N)‖ = 1 := by
  haveI : NeZero N := ⟨by rintro rfl; exact hpN (dvd_zero p)⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one χ u

theorem norm_prime_sq_pow {k N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {α β : ℂ} (hm : α * β = χ p * (p : ℂ) ^ (k - 1)) (hn : ‖α‖ = ‖β‖)
    (hpow : ∀ j, a (p ^ j) = ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i)) (j : ℕ) :
    ‖a (p ^ (2 * j))‖ ≤ ((2 * j + 1 : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
  have hsq : ‖α‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
    have h := congrArg norm hm
    rw [norm_mul, norm_mul, norm_char_prime χ hp hpN, one_mul, norm_pow, Complex.norm_natCast, ← hn] at h
    rw [sq]; exact h
  rw [hpow]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (2 * j + 1),
      ‖α ^ i * β ^ (2 * j - i)‖ = ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
    intro i hi
    have hi' : i ≤ 2 * j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_mul, norm_pow, norm_pow, ← hn, ← pow_add, Nat.add_sub_cancel' hi', pow_mul, hsq]
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem card_divisors_prime_sq {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ j) ^ 2).divisors.card = 2 * j + 1 := by
  rw [← pow_mul, mul_comm j 2, Nat.divisors_prime_pow hp]
  simp

theorem norm_sq_le : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) →
    ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  intro k N χ a he hE hS n
  obtain ⟨hmul, hpp⟩ := hE k N χ a he
  obtain ⟨h0, h1, -⟩ := he
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp hj =>
    intro hc
    have hpN : ¬ p ∣ N := fun hd =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_pow_self p hj.ne') hd)
    obtain ⟨α, β, hs, hm, hn⟩ := hS p hp hpN
    have hb := norm_prime_sq_pow hp hpN hm hn (hpp p hp α β hs hm) j
    rw [card_divisors_prime_sq hp j, ← pow_mul, mul_comm j 2]
    exact hb
  | zero =>
    intro _
    simp [h0]
  | one =>
    intro _
    simp [h1]
  | coprime m n hm hn hmn ihm ihn =>
    intro hc
    have hcm : Nat.Coprime m N := Nat.Coprime.coprime_mul_right hc
    have hcn : Nat.Coprime n N := Nat.Coprime.coprime_mul_left hc
    have hsq : Nat.Coprime (m ^ 2) (n ^ 2) := Nat.Coprime.pow 2 2 hmn
    rw [mul_pow, hmul _ _ hsq, norm_mul, hsq.card_divisors_mul]
    push_cast
    rw [mul_pow]
    calc ‖a (m ^ 2)‖ * ‖a (n ^ 2)‖
        ≤ (((m ^ 2).divisors.card : ℝ) * (m : ℝ) ^ (k - 1)) *
            (((n ^ 2).divisors.card : ℝ) * (n : ℝ) ^ (k - 1)) :=
          mul_le_mul (ihm hcm) (ihn hcn) (norm_nonneg _) (le_trans (norm_nonneg _) (ihm hcm))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.HeckeSq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSymCoeffLe
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfIntWeight

open Finset

noncomputable def symCoeff (r : ℂ) (j : ℕ) : ℂ :=
  ∑ i ∈ range (2 * j + 1), r ^ ((i : ℤ) - (j : ℤ))

theorem symCoeff_zero (r : ℂ) : symCoeff r 0 = 1 := by
  simp [symCoeff]

theorem symCoeff_succ {r : ℂ} (j : ℕ) :
    symCoeff r (j + 1) = symCoeff r j + r ^ (j + 1) + r⁻¹ ^ (j + 1) := by
  unfold symCoeff
  have e : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
  rw [e, sum_range_succ', sum_range_succ]
  have h1 : ∀ i : ℕ, r ^ (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = r ^ ((i : ℤ) - (j : ℤ)) := by
    intro i; congr 1; push_cast; ring
  simp_rw [h1]
  have h2 : r ^ (((2 * j + 1 : ℕ) : ℤ) - (j : ℤ)) = r ^ (j + 1) := by
    rw [← zpow_natCast]; congr 1; push_cast; ring
  have h3 : r ^ (((0 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = r⁻¹ ^ (j + 1) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]; congr 1
  rw [h2, h3]

theorem norm_symCoeff_le {r : ℂ} (hr : ‖r‖ = 1) (j : ℕ) :
    ‖symCoeff r j‖ ≤ 2 * (j : ℝ) + 1 := by
  unfold symCoeff
  refine (norm_sum_le _ _).trans ?_
  simp [norm_zpow, hr]

theorem hasSum_symCoeff {r X : ℂ} (hr : ‖r‖ = 1) (hX : ‖X‖ < 1) :
    HasSum (fun j : ℕ => symCoeff r j * X ^ j) ((1 + X) / ((1 - r * X) * (1 - r⁻¹ * X))) := by
  have r0 : r ≠ 0 := by
    intro h; simp [h] at hr
  have hrX : ‖r * X‖ < 1 := by simpa [hr] using hX
  have hrX' : ‖r⁻¹ * X‖ < 1 := by simpa [hr] using hX
  have hsum : Summable (fun j : ℕ => symCoeff r j * X ^ j) := by
    have g1 : Summable (fun j : ℕ => (j : ℝ) ^ 1 * ‖X‖ ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hX)
    have g0 : Summable (fun j : ℕ => ‖X‖ ^ j) :=
      summable_geometric_of_lt_one (norm_nonneg _) hX
    refine Summable.of_norm_bounded ((g1.mul_left 2).add g0) ?_
    intro j
    rw [norm_mul, norm_pow]
    have := mul_le_mul_of_nonneg_right (norm_symCoeff_le hr j) (pow_nonneg (norm_nonneg X) j)
    simpa [add_mul, mul_assoc] using this
  have hS := hsum.hasSum
  set S := ∑' j : ℕ, symCoeff r j * X ^ j with hSdef
  have hA := hasSum_geometric_of_norm_lt_one hrX
  have hB := hasSum_geometric_of_norm_lt_one hrX'
  have hS1 := (hasSum_nat_add_iff' 1).2 hS
  have hA1 := (hasSum_nat_add_iff' 1).2 hA
  have hB1 := (hasSum_nat_add_iff' 1).2 hB
  have hC := ((hS.mul_right X).add hA1).add hB1
  have hfun : (fun j : ℕ => symCoeff r (j + 1) * X ^ (j + 1)) =
      fun j : ℕ => symCoeff r j * X ^ j * X + (r * X) ^ (j + 1) + (r⁻¹ * X) ^ (j + 1) := by
    funext j
    rw [symCoeff_succ, mul_pow, mul_pow, pow_succ X j]
    ring
  rw [hfun] at hS1
  have key := hS1.unique hC
  simp only [range_one, sum_singleton, symCoeff_zero, pow_zero, mul_one] at key
  have n1 : (1 - r * X) ≠ 0 := by
    intro h
    have : r * X = 1 := by linear_combination -h
    simp [this] at hrX
  have n2 : (1 - r⁻¹ * X) ≠ 0 := by
    intro h
    have : r⁻¹ * X = 1 := by linear_combination -h
    simp [this] at hrX'
  have n3 : (1 - X) ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have val : S = (1 + X) / ((1 - r * X) * (1 - r⁻¹ * X)) := by
    have hk : (1 - X) * S = (1 - r * X)⁻¹ + (1 - r⁻¹ * X)⁻¹ - 1 := by
      linear_combination key
    have hq : (1 - r * X)⁻¹ + (1 - r⁻¹ * X)⁻¹ - 1
        = (1 - X) * ((1 + X) / ((1 - r * X) * (1 - r⁻¹ * X))) := by
      have hru : r * r⁻¹ = 1 := mul_inv_cancel₀ r0
      have hab : (1 - r⁻¹ * X) + (1 - r * X) - (1 - r * X) * (1 - r⁻¹ * X) = (1 - X) * (1 + X) := by
        linear_combination (-X ^ 2) * hru
      generalize (1 - r * X) = a at n1 hab ⊢
      generalize (1 - r⁻¹ * X) = b at n2 hab ⊢
      field_simp
      linear_combination hab
    exact mul_left_cancel₀ n3 (hk.trans hq)
  rwa [val] at hS

theorem localSeries : E2b := by
  intro r X hr hX
  have r0 : r ≠ 0 := by
    intro h; simp [h] at hr
  have n3 : (1 - X) ≠ 0 := by
    intro h
    have : X = 1 := by linear_combination -h
    simp [this] at hX
  have hterm : (fun j : ℕ => (∑ i ∈ range (2 * j + 1), r ^ i) * (r⁻¹ * X) ^ j) =
      fun j : ℕ => symCoeff r j * X ^ j := by
    funext j
    rw [mul_pow, ← mul_assoc]
    congr 1
    unfold symCoeff
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [zpow_sub₀ r0, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  have hval : (1 - X ^ 2) * ((1 - r * X)⁻¹ * (1 - X)⁻¹ * (1 - r⁻¹ * X)⁻¹) =
      (1 + X) / ((1 - r * X) * (1 - r⁻¹ * X)) := by
    have hc := mul_inv_cancel₀ n3
    rw [div_eq_mul_inv, mul_inv]
    linear_combination ((1 + X) * (1 - r * X)⁻¹ * (1 - r⁻¹ * X)⁻¹) * hc
  rw [hterm, hval]
  exact hasSum_symCoeff hr hX

end GlobalTheory.CompanionTheory.HalfIntWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjectiveStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)),
  ∃ f : XS τ σ, (∀ x ∈ Cl k i t, evX f x = 0) ∧ eO ψ f = (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto <;> assumption)
end

