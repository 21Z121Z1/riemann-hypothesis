import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0127
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.JacobianAtCurvePoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0123
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

theorem DivisorGoodPointBranches.proof : DivisorGoodPointBranches.Statement := by
  intro n d J u M q _hJ _hdim _hu hqJ hqu hreg hchart hdouble
  obtain ⟨A, O, V, g, -, hV, hqV, hg, hAg, hS⟩ := hreg
  obtain ⟨N₀, hN₀, hdbl⟩ := hdouble
  let F : Set (Fin n ⊕ Fin M.m → ℂ) :=
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}
  have hmemF : ∀ w, w ∈ F ↔ (w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q) :=
    fun w => Iff.rfl
  have hFfin : F.Finite := NormalModelFibre.fibre_finite M q
  obtain ⟨G, hGo, hGd⟩ := hFfin.t2_separation
  let _ : Fintype F := hFfin.fintype
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have hbr : ∀ b : Fin (Fintype.card F), ∃ γ : VarBranch J (d + 1) q, ∃ ord : ℕ,
      (∃ U ∈ 𝓝 (e b : Fin n ⊕ Fin M.m → ℂ), ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G (e b), IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius ord ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
    intro b
    have hb := (hmemF _).1 (e b).2
    obtain ⟨r, φ, k, hr, hφd, hφi, hφ0, hφZ, hφU, hvan, hinjD⟩ := hchart (e b) hb.1 hb.2
    obtain ⟨γ, h⟩ := GoodPointBranch.exists_branch M hqu hV hqV hg hAg hS hN₀ hdbl hb.2 hr hφd hφi hφ0
      hφZ hφU hvan hinjD ((hGo _).2.mem_nhds (hGo _).1)
    exact ⟨γ, k, h⟩
  choose γ ord hcovw himg hslice hvan hbij using hbr
  refine ⟨Fintype.card F, γ, ord, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
    ?_, ?_, ?_, hvan, hbij⟩
  · choose U hU hUc using hcovw
    obtain ⟨N, hN, hNU⟩ := NormalModelFibre.eventually_mem_of_fibre_subset M (q := q)
      (isOpen_iUnion fun b => isOpen_interior (s := U b)) (fun w hw hwq => by
        obtain ⟨b, hb⟩ := e.surjective ⟨w, (hmemF w).2 ⟨hw, hwq⟩⟩
        refine mem_iUnion.2 ⟨b, mem_interior_iff_mem_nhds.2 ?_⟩
        have hbw : (e b : Fin n ⊕ Fin M.m → ℂ) = w := congrArg Subtype.val hb
        rw [← hbw]
        exact hU b)
    refine ⟨N, hN, fun x hx => ?_⟩
    obtain ⟨w, hw, rfl⟩ := NormalModelFibre.exists_mem_fibre M hx.1
    obtain ⟨b, hb⟩ := mem_iUnion.1 (hNU w hw hx.2)
    exact mem_iUnion.2 ⟨b, hUc b w ⟨hw, interior_subset hb⟩⟩
  · choose N' hN' hN'c using hslice
    exact ⟨⋂ b, N' b, Filter.iInter_mem.2 hN',
      fun x hx hxu b => hN'c b x ⟨hx.1, mem_iInter.1 hx.2 b⟩ hxu⟩
  · intro b b' hbb' x hx
    obtain ⟨hxN, w, ⟨hw, hwG⟩, rfl⟩ := himg b x hx.1
    obtain ⟨-, w', ⟨hw', hw'G⟩, hww'⟩ := himg b' _ hx.2
    have hne : w ≠ w' := by
      rintro rfl
      have hdisj : Disjoint (G (e b)) (G (e b')) :=
        hGd (e b).2 (e b').2 (fun h => hbb' (e.injective (Subtype.ext h)))
      exact Set.disjoint_left.1 hdisj hwG hw'G
    exact hdbl w hw w' hw' hww'.symm hxN hne

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem JacobianRankOffHypersurface.eval_pderiv_sum_mul {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by
  simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]

theorem JacobianRankOffHypersurface.grad_mem_span {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem JacobianRankOffHypersurface.finrank_of_generators {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard

theorem JacobianRankOffHypersurface.exists_fin (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩ := hF n d J hJ hd b
  refine ⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩
  · have h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have h2 : I₀.card ≤ n := (Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)
    omega
  · intro w hw
    let M : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun j l ↦ b j l
    have hdet := hw
    rw [frameJacobianDet, RingHom.map_det] at hdet
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) =
        (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k)) := by
      funext k j
      simp [frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]
    rw [hrows] at hli
    exact hli.of_comp _

theorem JacobianRankOffHypersurface.proof_of_frame (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc
    rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩

theorem JacobianRankOffHypersurface.proof : JacobianRankOffHypersurface.Statement :=
  JacobianRankOffHypersurface.proof_of_frame
    (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveJacobian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem NormalCurveJacobian.proof (hDVR : NormalCurvePointDVR.Statement) : NormalCurveJacobian.Statement := by
  intro σ _ I w hI hint hdim hw
  obtain ⟨hd, hdvr⟩ := hDVR σ I w hI hint hdim hw
  let : Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  have : IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs
      (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  exact JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w)
    (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveRegularPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalCurveRegularPoint

theorem fderiv_eval_single {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by
  induction g using MvPolynomial.induction_on generalizing z with
  | C a => simp
  | add p q hp hq =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hq' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) q z trivial).differentiableAt
    simp only [map_add]
    rw [fderiv_fun_add hp' hq']
    simp [hp, hq]
  | mul_X p j hp =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hX : DifferentiableAt ℂ (fun x : σ → ℂ => x j) z := differentiableAt_apply j z
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul hp' hX]
    simp [hp, Derivation.leibniz, pderiv_X, Pi.single_apply, fderiv_apply, mul_comm]
    split_ifs <;> simp

end NormalCurveRegularPoint

theorem NormalCurveRegularPoint.proof (hJ : NormalCurveJacobian.Statement) : NormalCurveRegularPoint.Statement := by
  classical
  intro σ _ I w hI hnorm hdim hw
  obtain ⟨k, f, D, hk, hfI, hlin, hD, hgen⟩ := hJ σ I w hI hnorm hdim hw
  set W : Set (σ → ℂ) := {z | eval z D ≠ 0}
  have hWo : IsOpen W := isOpen_ne_fun (continuous_eval D) continuous_const
  have hder : ∀ j, (fun i : σ => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w (Pi.single i 1)) =
      fun i => eval w (pderiv i (f j)) := fun j => funext fun i =>
    NormalCurveRegularPoint.fderiv_eval_single (f j) w i
  let Φ : ((σ → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (σ → ℂ) :=
    { toFun := fun L i => L (Pi.single i 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin' : LinearIndependent ℂ (fun j => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w) := by
    refine LinearIndependent.of_comp Φ ?_
    convert hlin using 1
    funext j
    exact hder j
  obtain ⟨d, A, O, V, g, hd, hO, hV, hwV, hVW, hg, hAg, hset⟩ :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof σ (Fin k) (fun j z => eval z (f j)) w W
      (fun j => AnalyticOnNhd.eval_mvPolynomial (f j) w trivial) (fun j => hw _ (hfI j)) hlin'
      (hWo.mem_nhds hD)
  simp only [Fintype.card_fin] at hd
  obtain rfl : d = 1 := by omega
  refine ⟨A, O, V, g, hO, hV, hwV, hg, hAg, ?_⟩
  rw [← hset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨hzV, fun j => hz _ (hfI j)⟩
  · rintro ⟨hzV, hzf⟩
    refine ⟨fun q hq => ?_, hzV⟩
    have hspan : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzf j
    have h0 : eval z (D * q) = 0 := hspan (hgen q hq)
    rw [eval_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hzV)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionInjectiveOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : frameProj b I₀ (T x) = frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedDensityNonneg

theorem half_log_eq_phi (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (‖a‖ ^ 2 + ε) / 2 = phi (![a, ((√ε : ℝ) : ℂ)] : Fin 2 → ℂ) := by
  simp only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
  ring

end RegularizedDensityNonneg

theorem RegDensNonneg.proof : RegDensNonneg.Statement := by
  intro n d J A u ε x s hε hs
  have han : AnalyticAt ℂ s (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ x
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x)) :=
      ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]
    exact GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one

end

end GroundTheory.Heights₂.Heights
end

