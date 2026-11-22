import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
section
namespace Formalism.FourierDecayAlt.P.TLB

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
  Formalism.YangianSpanCharacter.T

noncomputable section

section gen

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem tprod_take_all (L : LevelData A r) (Y : ℂ) :
    L.Tprod Y = ((List.ofFn (L.Tl Y)).take r).reverse.prod := by
  unfold LevelData.Tprod
  rw [List.take_of_length_le (by simp)]

variable [StarRing A] [StarModule ℂ A]

theorem star_algMap (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (starRingEnd ℂ z) := by
  rw [← algebraMap_star_comm]; rfl

theorem star_Tl_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) (l : Fin r) :
    (L.Tl y l)ᴴ = (L.Tvl (starRingEnd ℂ y) l)ᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, LevelData.Tvl, conjTranspose_apply, star_add, star_neg, hp, hc, hci, star_algMap,
      sub_eq_add_neg]

theorem star_Tprod_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) :
    (L.Tprod y)ᴴ = (L.Tvprod (starRingEnd ℂ y))ᵀ := by
  rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose]
  unfold LevelData.Tprod
  rw [conjTranspose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun l => star_Tl_gen L hp hc hci y l)

end gen

section actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_pref_take (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ∀ n, Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n = ((List.ofFn (L.Tl Y)).take n).reverse.prod
  | 0 => by simp [Formalism.FourierDecayAlt.P.JCx2.rma_pref]
  | n + 1 => by
    by_cases h : n < r
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dif_pos h, rma_pref_take L Y n, List.take_add_one, List.reverse_append,
        List.prod_append]
      have e : (List.ofFn (L.Tl Y))[n]? = some (L.Tl Y ⟨n, h⟩) := by simp [h]
      rw [e]
      simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
        List.prod_nil, mul_one]
      congr 1
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dif_neg h, rma_pref_take L Y n, List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]

theorem tprod_zero_eq (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : tprod L Y 0 = L.Tprod Y := by
  have h : tprod L Y 0 = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y r := by
    have := Formalism.FourierDecayAlt.P.JCx2.rma_tprod_pref L Y r 0 (by omega)
    simpa [Formalism.FourierDecayAlt.P.JCx2.rma_pref] using this
  rw [h, rma_pref_take, tprod_take_all]

end actual

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

noncomputable section

theorem actual_algebra_facts : TL.ActualAlg := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hpl, -, hL, hQQ, -, -, hSL, hst⟩ := hD
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL
  have hcent : ∀ (l : Fin P.r) (Y : ℂ) (a b : Fin 2),
      st.QQ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    intro l Y a b
    obtain ⟨hp, -, hc, hci, -⟩ := hL
    have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
      fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
    have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
      intro i Y a b; rw [mul_neg, neg_mul, ht]
    rw [hQQ Y, Matrix.smul_apply]
    refine SMulMemClass.smul_mem _ ?_
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hp l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), P5.HerA.pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hc l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hci l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
  have hqq : ∀ Y i j, ∀ x ∈ siteOps L, Commute (st.QQ Y i j) x := by
    intro Y i j x hx
    have key := fun l => (StarSubalgebra.mem_centralizer_iff ℂ).1 (hcent l Y i j)
    simp only [siteOps, Set.mem_union, Set.mem_range] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · have h := key l
      exact (h (L.p l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.p l) (by simp [hol, site])).2
      rw [sp l] at h2
      exact Commute.neg_right_iff.1 (show Commute (st.QQ Y i j) (-L.pb l) from h2.symm)
    · exact (key l (L.c l) (by simp [hol, site])).1.symm
    · exact (key l (L.ci l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.c l) (by simp [hol, site])).2
      rw [sc l] at h2
      exact h2.symm
    · have h2 := (key l (L.ci l) (by simp [hol, site])).2
      rw [sci l] at h2
      exact h2.symm
  refine ⟨⟨hSL, hst, sp, sc, sci, hqq⟩, fun Y hY => ?_, fun Y hY => ?_⟩
  · have hY' : starRingEnd ℂ Y = Y := hY
    unfold P5.QQi
    simp only [Fin.val_zero]
    rw [hY, TLB.tprod_zero_eq, TLB.star_Tprod_gen L sp sc sci, hY']
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, cst, nP, LevelData.Ar, LevelData.Br,
      LevelData.Avr, LevelData.Bvr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  · obtain ⟨κ, hx, hxi, -⟩ :=
      P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD'
    classical
    set f : M.Ty P → ℂ := fun ρ => M.x0 P l0 ρ Y with hf
    set N : Finset ℂ := Finset.univ.image f
    set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
    have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
      intro ρ
      have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
      have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
      simpa only [id] using h
    have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
      funext ρ
      rw [← hp ρ]
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : M.Ty P => ℂ) ρ) f p
      rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
      rw [this]
      rfl
    refine ⟨p, ?_⟩
    rw [hxi Y hY, hx Y, Polynomial.aeval_algHom_apply]
    exact congrArg κ he

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
section
namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt

noncomputable section

theorem compact_support_facts : TL.CptFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs F hF
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  refine ⟨⟨ε, hε, ?_⟩, fun Dop hDop => ?_⟩
  · set R' : ℝ := |R| + 1 with hR'
    have hR0 : 0 < R' := by positivity
    obtain ⟨h1, h2⟩ := JCx2.pd_cut_nice (E := Wq →L[ℂ] Wp) hR0 hFs
    have hN : JC.NiceCoef Bs ε (fun g => JCx2.pdPhi (R'⁻¹ • g) • F g) :=
      ⟨h1, fun A m => h2 A m, fun g hg hne => by
        refine hεF g hg ?_
        intro h0; apply hne; simp [h0]⟩
    refine JCx2.mn_nice_congr (fun g hg => ?_) hN
    by_cases h0 : F g = 0
    · simp [h0]
    · have hgR : gN g ≤ R := hR g hg h0
      have hg0 : 0 ≤ gN g := Real.sqrt_nonneg _
      have hsq : JCx2.pdSq (R'⁻¹ • g) ≤ 1 := by
        rw [JCx2.pd_sq_smul, JCx2.pd_sq_eq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
        have : gN g ≤ R' := by rw [hR']; linarith [le_abs_self R]
        nlinarith
      simp [JCx2.pdPhi, JCx2.pd_chi_one hsq]
  · have hGc : Continuous (Gf k r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _
    have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε}, g ∈ GV k r →
        Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
        (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | R < gN g}, g ∈ GV k r → Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} :=
      Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
    have hsub : {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} ⊆ C6.domL Bs ∅ :=
      fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
    have hsF : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
    have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      intro T hT
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg
      refine ⟨hg.1, ?_⟩
      by_contra hlt
      exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
    refine ⟨⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg hgn => ?_⟩
    · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hDop T hT).1) hsT
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
    · refine PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g ?_ hg
      show Gf k r Bs.z Bs.z' g < ε
      by_contra hge
      exact hgn ⟨hg, lt_of_lt_of_le hε (not_lt.1 hge), by simp⟩

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CsliceContDiffAt
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem update_mem_OmX {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX r := by
  intro j
  by_cases hj : j = l
  · subst hj; simpa using ht
  · rw [Function.update_of_ne hj]; exact hc j

theorem cslice_contDiffAt (Φ : RadSp k r z z' π π') (g : Mx k r) {x : Fin r → ℂ} (hx : x ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) x := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨-, hs, -⟩ := Φ.2
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (x, g) ⟨hx, hg.1, hg.2⟩
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    have hV : IsOpen ((fun c' : Fin r → ℂ => (c', g)) ⁻¹' U) := hU.preimage hcont
    have hFx : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) x :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    refine hFx.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxU] with c' hc'
    exact hΦ (c', g) hc' hg.1
  · have h0 : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      exact radSp_zero_off Φ (x := (c', g)) (fun h => hg ⟨h.2.1, h.2.2⟩)
    rw [h0]; exact contDiffAt_const

theorem dZv_update {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (c : Fin r → ℂ) (l : Fin r) (t : ℂ)
    (hf : DifferentiableAt ℝ f (Function.update c l t)) :
    dZv (fun s => f (Function.update c l s)) t = wirt l f (Function.update c l t) ∧
      dZbv (fun s => f (Function.update c l s)) t = wirtBar l f (Function.update c l t) := by
  have hu := hasFDerivAt_update (𝕜 := ℝ) c (i := l) t
  have h := hf.hasFDerivAt.comp t hu
  have hd : ∀ v : ℂ, fderiv ℝ (fun s => f (Function.update c l s)) t v =
      fderiv ℝ f (Function.update c l t) (Pi.single l v) := by
    intro v
    rw [show (fun s => f (Function.update c l s)) = f ∘ Function.update c l from rfl, h.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  constructor
  · unfold dZv wirt; rw [hd, hd]
  · unfold dZbv wirtBar; rw [hd, hd]

theorem site_p_adj_g (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') (l : Fin r) (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (g : Mx k r)
    (h0 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ))) :
    ∫ t : ℂ, B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
    -∫ t : ℂ, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  set fΦ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΦ
  set fΨ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΨ
  set A : ℂ → (Wq →L[ℂ] Wp) := fun t => fΦ (Function.update c l t) with hA
  set Bf : ℂ → (Wq →L[ℂ] Wp) := fun t => fΨ (Function.update c l t) with hB
  have hupd : ContDiff ℝ ∞ (fun t : ℂ => Function.update c l t) :=
    contDiff_pi.mpr fun j => by
      by_cases hj : j = l
      · subst hj; simp only [Function.update_self]; exact contDiff_id
      · simpa [Function.update_of_ne hj] using contDiff_const
  have hAc : ContDiffOn ℝ 1 A {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hBc : ContDiffOn ℝ 1 Bf {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hpΦ : ∀ t : ℂ, t ≠ 0 → (X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = t • dZv A t := by
    intro t ht
    have hd := dZv_update (f := fΦ) c l t
      ((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.1]
    show pOp l fΦ (Function.update c l t) = _
    unfold pOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
  have hpΨ : ∀ t : ℂ, t ≠ 0 → (X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g =
      conj t • dZbv Bf t := by
    intro t ht
    have hd := dZv_update (f := fΨ) c l t
      ((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.2]
    show pbOp l fΨ (Function.update c l t) = _
    unfold pbOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
    rfl
  have e1 : (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (t • dZv A t) (Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΦ t ht]
  have e2 : (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (A t) (conj t • dZbv Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΨ t ht]
  have h1' := e1 ▸ h1
  have h2' := e2 ▸ h2
  rw [e1, e2]
  exact pLogAdjHS A Bf hAc hBc h0 h1' h2'

theorem site_p_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (Φ Ψ : RadSp k r z z' π π')
    (l : Fin r) (c : Fin r → ℂ) (hc : c ∈ OmX r)
    (h0 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h1 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp))
      (Function.update c l q.1) (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
        (Matrix.of q.2)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h2 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ)) :
    ∫ t : ℂ, pairAt μ (X.op l 0 Φ) Ψ (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
      -∫ t : ℂ, pairAt μ Φ (X.op l 3 Ψ) (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairAt
  simp only [← integral_div]
  rw [integral_integral_swap h1]
  conv_rhs => rw [integral_integral_swap h2]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [h0.prod_left_ae, h1.prod_left_ae, h2.prod_left_ae] with x hx0 hx1 hx2
  exact site_p_adj_g X Φ Ψ l c hc (Matrix.of x) hx0 hx1 hx2

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem foldCV_nil (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (H : B.Mat k r → E) :
    foldCV k r s [] H = H := rfl

theorem foldCV_cons (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (x : C.Letter)
    (a : List C.Letter) (H : B.Mat k r → E) :
    foldCV k r s (x :: a) H = s • Q.CV k r (x.2 : ℂ) (foldCV k r s a H) := rfl

theorem foldCV_mem {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_mem hcl hJ s a) x.2 s

theorem om_sub {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hU, hD, hG⟩ := hg
  refine ⟨⟨hU, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ ?_⟩
  show (a : ℕ) + 1 ≤ r
  omega

theorem energyTr_of_parts (hR : FoldRev) (hL : AdmLen) (hBF : BesselFoldBuilt) (hL2 : L2BoundAtTowerPlace) (hBe : BetaFrame) :
    EnergyTr := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hcl ε hε hJF a hadm
  have hB' := hB
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := hB'
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, _, _⟩ := hv v
  have hlen : a.length ≤ S.Ntop := hL E Wp Wq S v a hadm
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set J₁ := foldCV S.G.k S.G.r s a.reverse (B.JF Db F) with hJ₁
  have hJ₁m : J₁ ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_mem hcl hJF s _
  have hOpen : IsOpen (OmP S T v) := (isDom_omP Db.z_mem Db.z'_mem).1

  have hae : ∀ᵐ p ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)),
      bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p = 0 ∨
        B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p) = J₁ (B.gq Db p) := by
    have h0 := ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict Db)
    filter_upwards [h0] with p hp
    by_cases hq : p ∈ B.Qset Db
    · right
      have hg := Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db p (hp hq)
      rw [hBF E Wp Wq S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF a hlen _ hg]
      exact (hR _ _ _ _ _ _ _ _ _ hOpen hcl _ hJF s a _ (om_sub hg)).symm
    · left
      exact le_antisymm (not_lt.1 hq) (Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ p)
  have hN1 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (J₁ (B.gq Db q))) ≠ ⊤ := by
    have h := hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε a hlen
    unfold B.normSq at h
    unfold jNormSq at h ⊢
    rwa [lintegral_congr_ae (hae.mono fun p hp => ?_)] at h
    rcases hp with hp | hp
    · rw [show bcWeight S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') p = 0 from hp]
      simp
    · show ENNReal.ofReal (_ * ‖B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))‖ ^ 2) = _
      rw [hp]
  have hN2 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (B.JF Db F (B.gq Db q))) ≠ ⊤ :=
    hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε [] (Nat.zero_le _)
  have hBeq := hBe E Wp Wq S T v hplace e hFr J₁ hJ₁m (B.JF Db F) hJF hN1 hN2
  unfold C7.principalHermitianLattice B.beta
  show _ = MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.JF Db F))
  rw [← hBeq]
  unfold betaBig
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  rcases hp with hp | hp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _ =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _
    rw [hp]; simp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))) =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (J₁ (B.gq Db p)))
    rw [hp]

end Formalism.FourierDecayAlt.P.CutMP.En
end

