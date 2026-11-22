import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecompositionOfParts
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

set_option maxHeartbeats 400000 in
theorem c2_section_decomp_of_pieces : C2.SectionDecompOfParts := by
  intro _ hC1iii hURI hUp _ hUM _ hTM k r z z' γ hstd hpos hmono s hs
  have hz := hstd.2.1
  have hU := hUM k r z hz
  have hSg := symmetric_group_holds k r z hz.1
  have hNg := unipotent_subgroup_holds k r

  have hu1 : C2.uMap k r z 1 = 1 := hU.2 1 (one_mem_UW z)
  have huinv : ∀ x ∈ Sset k r z, C2.uMap k r z x⁻¹ = (C2.uMap k r z x)⁻¹ := by
    intro x hx
    have hxi := hSg.2.2 x hx
    have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hx)
    have : C2.uMap k r z x * C2.uMap k r z x⁻¹ = 1 := by
      rw [← (hU.1 x hx).2.2 _ hxi, Matrix.mul_nonsing_inv _ hxu, hu1]
    exact (Matrix.inv_eq_right_inv this).symm

  have huSg : ∀ σ ∈ C2.Sg k r z z' γ, σ ∈ Sset k r z ∧ ∃ v, v ∈ C2.UTset (r + 1) ∧ vᴴ ∈ C2.LPg (Zhat k r z z' γ) ∧
      C2.uMap k r z σ = v := by
    rintro σ ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
    have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
    have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
    have hhS : h ∈ Sset k r z := UW_sub_S hh
    have hs1 := hSg.2.1 _ hn0S _ hτS
    refine ⟨hSg.2.1 _ hs1 _ hhS, v, hv, hvL, ?_⟩
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul, Matrix.mul_one]

  have hRimg : ∀ ρ ∈ C2.Rst k r z z' γ, C2.uMap k r z ρ ∈ C2.UTset (r + 1) ∧ (C2.uMap k r z ρ)ᴴ ∈ C2.Lstg (Zhat k r z z' γ) := by
    intro ρ hρ
    have hmap := (hC1iii k r z z' γ hstd hpos).1.mapsTo hρ
    obtain ⟨h1, h2, h3⟩ := hmap
    have : C2.uMap k r z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} :=
      ⟨h1, _, h2, h3⟩
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono] at this
    exact this
  have hRS : ∀ ρ ∈ C2.Rst k r z z' γ, ρ ∈ Sset k r z := fun ρ hρ => hρ.1.1
  obtain ⟨hus, husUT, _⟩ := hU.1 s hs
  obtain ⟨⟨uρ, v⟩, ⟨huρ, hv, huρL, hvL, hue⟩, huniq⟩ := hUp (r + 1) (Zhat k r z z' γ) hmono _ husUT
  simp only at huρ hv huρL hvL hue

  have huρR : uρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} := by
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono]; exact ⟨huρ, huρL⟩
  obtain ⟨u', hu', hu'e⟩ := huρR.2
  have hmemT : (uρ, u') ∈ {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
      p.1 ∈ C2.UTset (r + 1) ∧ p.2 ∈ C2.UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨huρ, hu', hu'e⟩
  obtain ⟨ρ, hρ, hρe⟩ := (hC1iii k r z z' γ hstd hpos).1.surjOn hmemT
  have hρu : C2.uMap k r z ρ = uρ := congrArg Prod.fst hρe
  have hρS := hRS ρ hρ
  have hρu' : IsUnit ρ.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hρS)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ρ⁻¹ * s := ⟨_, rfl⟩
  have hσS : σ ∈ Sset k r z := by rw [hσ]; exact hSg.2.1 _ (hSg.2.2 _ hρS) _ hs
  have hσu : C2.uMap k r z σ = v := by
    rw [hσ, (hU.1 _ (hSg.2.2 _ hρS)).2.2 s hs, huinv ρ hρS, hρu, hue, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (C2x2.ut_unit huρ), Matrix.one_mul]
  obtain ⟨h1, hh1, n1, hn1, hσe⟩ := hσS
  have hh1S := UW_sub_S hh1
  have hn1S := N_sub_S (z := z) hn1
  have hn1u : C2.uMap k r z n1 = v := by
    rw [← hσu, hσe, (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1, Matrix.one_mul]
  have hh1inv := WeylGroupFacts.uw_inv hh1
  have hh1u : IsUnit h1.det := WeylGroupFacts.isUnit_of_uh hh1.1
  have hn2 : h1 * n1 * h1⁻¹ ∈ Nset k r := (unitary_weyl_normal_holds k r z hz.1 h1 hh1 n1 hn1).1
  have hn2u : C2.uMap k r z (h1 * n1 * h1⁻¹) = v := by
    rw [(hU.1 _ (hSg.2.1 _ hh1S _ hn1S)).2.2 _ (UW_sub_S hh1inv), (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1,
      hU.2 _ hh1inv, hn1u, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  obtain ⟨τv, hτv⟩ : ∃ τv, τv = C2.tauM k r z v := ⟨_, rfl⟩
  rw [← hτv] at hτN hτu
  have hτS : τv ∈ Sset k r z := N_sub_S hτN
  have hτunit : IsUnit τv.det := WeylGroupFacts.isUnit_of_uh hτN.1
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = h1 * n1 * h1⁻¹ * τv⁻¹ := ⟨_, rfl⟩
  have hn0N : n0 ∈ Nset k r := by rw [hn0]; exact hNg.2.1 _ hn2 _ (hNg.2.2 _ hτN)
  have hn0u : C2.uMap k r z n0 = 1 := by
    rw [hn0, (hU.1 _ (N_sub_S hn2)).2.2 _ (hSg.2.2 _ hτS), huinv _ hτS, hn2u, hτu,
      Matrix.mul_nonsing_inv _ (C2x2.ut_unit hv)]
  have hσdec : σ = n0 * τv * h1 := by
    rw [hσe, hn0, Matrix.mul_assoc (h1 * n1 * h1⁻¹), Matrix.nonsing_inv_mul _ hτunit, Matrix.mul_one,
      Matrix.mul_assoc (h1 * n1), Matrix.nonsing_inv_mul _ hh1u, Matrix.mul_one]
  have hσSg : σ ∈ C2.Sg k r z z' γ := ⟨n0, ⟨hn0N, hn0u⟩, v, hv, hvL, h1, hh1, by rw [hσdec, hτv]⟩
  refine ⟨(ρ, σ), ⟨hρ, hσSg, ?_⟩, ?_⟩
  · show s = ρ * σ
    rw [hσ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu', Matrix.one_mul]
  · rintro ⟨ρ', σ'⟩ ⟨hρ', hσ', hse⟩
    simp only at hρ' hσ' hse
    obtain ⟨hσ'S, v', hv', hv'L, hσ'u⟩ := huSg σ' hσ'
    obtain ⟨hρ'U, hρ'L⟩ := hRimg ρ' hρ'
    have hus' : C2.uMap k r z s = C2.uMap k r z ρ' * v' := by
      rw [hse, (hU.1 _ (hRS ρ' hρ')).2.2 _ hσ'S, hσ'u]
    have := huniq (C2.uMap k r z ρ', v') ⟨hρ'U, hv', hρ'L, hv'L, hus'⟩
    rw [Prod.ext_iff] at this
    simp only at this
    have hρρ : ρ' = ρ := (hC1iii k r z z' γ hstd hpos).2.1 hρ' hρ (this.1.trans hρu.symm)
    subst hρρ
    have hρ'u : IsUnit ρ'.det := hρu'
    have : σ' = ρ'⁻¹ * s := by
      rw [hse, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ'u, Matrix.one_mul]
    rw [this, hσ]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

section
variable (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
include hFm hDom1 hDom2

lemma words_all :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS := by
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR [] v (JF D F) g = ∫ p, xiP D p • dLR [] v (rho D p F) g ∂D.μSS := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      exact step_pair D hFm hDom1 hDom2 false (hv X List.mem_cons_self) (u := []) (v := v) (u2 := [])
        (v2 := X :: v) (by simp) hv' (by simp) hv (by simpa using hl) (by simp) (fun f => rfl)
        (ih hv' (by simp at hl; omega))
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    exact step_pair D hFm hDom1 hDom2 true (hu X List.mem_cons_self) (u := u) (v := v) (u2 := X :: u) (v2 := v)
      hu' hv hu hv hl (by simp) (fun f => rfl) (ih v hu' hv (by simp at hl; omega))

lemma ck_all : Formalism.FourierDecayAlt.Q.CkLev k r 0 m (Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') (JF D F) := by
  classical
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  intro g0 hg0
  have hg0G : g0 ∈ GV k r := hg0.1.1
  have hchart0 : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
    have h1 : (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) = Formalism.FourierDecayAlt.P.Ux10.co 0 :=
      funext fun i => (Formalism.FourierDecayAlt.P.Ux10.co_zero i).symm
    unfold Formalism.FourierDecayAlt.P.Ux10.chart Formalism.FourierDecayAlt.P.Ux10.kap
    rw [h1, Formalism.FourierDecayAlt.P.Ux10.Mv_co, Formalism.FourierDecayAlt.P.Ux10.prj_zero]
    simp
  have hcont : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_diff g0 Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom).continuousAt
  have hV : Formalism.FourierDecayAlt.P.Ux10.Dom k r ∩ Formalism.FourierDecayAlt.P.Ux10.chart g0 ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' ∈
      𝓝 (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) :=
    Filter.inter_mem (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
      (hcont.preimage_mem_nhds ((isOpen_OmPlus _ _).mem_nhds (by rw [hchart0]; exact hg0.2)))
  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1 hV
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hclb : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Metric.ball 0 δ1 :=
    Metric.closedBall_subset_ball (by rw [hδ]; linarith)
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => (hsub (hclb hY)).1
  set K := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKOm : K ⊆ Om k r D.z D.z' := by
    rintro _ ⟨Y, hY, rfl⟩
    exact (⟨Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0G (hcl hY), (hsub (hclb hY)).2⟩ :
      Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')
  have hKG : K ⊆ GV k r := fun x hx => (show x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' from hKOm hx).1
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 K hK hKOm
  set WS : Set (List (Mat k r) × List (Mat k r)) :=
    (fun w : List (Formalism.FourierDecayAlt.P.Ux10.J k r) => (w.map Formalism.FourierDecayAlt.P.Ux10.Lt, ([] : List (Mat k r)))) ''
      {w | w.length ≤ m} with hWSdef
  have hWS : WS.Countable := (Set.to_countable _).image _
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hWSl : ∀ uv ∈ WS, (∀ Y ∈ uv.1, unitLie k r Y) ∧ (∀ Y ∈ uv.2, unitLie k r Y) ∧
      uv.1.length + uv.2.length ≤ m := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hunit w, by simp, by simpa using hw⟩
  have good := good_set D hFm hK hKG hWS hWSl bd fun uv huv g' hg' =>
    hbd uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 g' hg'
  set P0 : Set (SS k r) := {p | D.inSS p ∧ ∀ uv ∈ WS, ∀ g' ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g'‖ ≤ bd p} with hP0
  have goodae : ∀ᵐ p ∂D.μSS, p ∈ P0 := good
  set hK' : SS k r → Mat k r → (Wq →L[ℂ] Wp) := fun p => if p ∈ P0 then rho D p F else fun _ => 0 with hK'def
  have hsel : ∀ p (u' v' : List (Mat k r)),
      dLR u' v' (hK' p) = if p ∈ P0 then dLR u' v' (rho D p F) else fun _ => 0 := by
    intro p u' v'
    by_cases hp : p ∈ P0
    · simp only [hK'def, if_pos hp]
    · simp only [hK'def, if_neg hp, dLR_zero]
  have hAL := int_chart_loc (xiP D) (fun p => norm_xiP D p) (continuous_xiP D).aestronglyMeasurable hK' m
    (fun p => by
      by_cases hp : p ∈ P0
      · simp only [hK'def, if_pos hp]; exact ckOn_rho D hp.1 hFm
      · simp only [hK'def, if_neg hp]; exact ckOn_zero _)
    hg0G hδp hcl
    (fun w hw Y hY => by
      refine (hDom1 (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hunit w) (by simp) (by simpa using hw) _
        (hKOm (hmemK Y hY))).congr ?_
      filter_upwards [goodae] with p hp
      rw [hsel, if_pos hp, dLR_rho D hp.1])
    (fun p => ‖bd p‖) hbdI.norm
    (fun w hw Y hY p => by
      rw [hsel]
      by_cases hp : p ∈ P0
      · rw [if_pos hp]; exact (hp.2 _ ⟨w, hw, rfl⟩ _ (hmemK Y hY)).trans (Real.le_norm_self _)
      · rw [if_neg hp, norm_zero]; exact norm_nonneg _)
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => JF D F (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show ∫ p, xiP D p • rho D p F _ ∂D.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [goodae] with p hp
    simp only [hK'def, if_pos hp]
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := ck_at_of_chart hg0G hδp hAL'
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩

end

theorem _root_.Formalism.FourierDecayAlt.P.bessel_words_of_domain : JWordsOfDom := by
  intro hDom k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  obtain ⟨hDom1, hDom2⟩ := hDom k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmulRApply
section
noncomputable section

open Finset Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.NFRO

open Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

def JetR {M : Type*} [AddCommGroup M] [Module ℝ M] (U : Set ℂ) (ζ0 : ℂ) (Λ : (ℂ → ℂ) → M) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (L : ι → ℂ →ₗ[ℝ] M),
    ∀ f, ContDiffOn ℝ ∞ f U → Λ f = ∑ i, L i (wd (w i) f ζ0)

theorem wn_cmono (ζ0 c : ℂ) (j l a b : ℕ) :
    wn a b (fun x => c * mono ζ0 j l x) ζ0 = c * wn a b (mono ζ0 j l) ζ0 := by
  have e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x := by funext x; ring
  have h1 : wn a b (fun x => c * mono ζ0 j l x) ζ0 =
      (c * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, iter_dZb_cmono, iter_dZ_cmono]
  have h2 : wn a b (mono ζ0 j l) ζ0 =
      (1 * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, e, iter_dZb_cmono, iter_dZ_cmono]
  rw [h1, h2]
  ring

section Zero

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_zero (hU : IsOpen U) (h0 : ζ0 ∈ U) {Λ : (ℂ → ℂ) → M} (hΛ : JetR U ζ0 Λ)
    (hP : ∀ (c : ℂ) (j l : ℕ), Λ (fun x => c * mono ζ0 j l x) = 0) : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = 0 := by
  classical
  obtain ⟨ι, _, w, L, h⟩ := hΛ
  let cnt : ι → ℕ × ℕ := fun i => ((w i).count false, (w i).count true)
  have hS : ∀ (c : ℕ × ℕ) (x : ℂ), ∑ i ∈ univ.filter (fun i => cnt i = c), L i x = 0 := by
    intro c x
    have hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y * ((c.1.factorial * c.2.factorial : ℕ) : ℂ) = x :=
      ⟨x / _, div_mul_cancel₀ x hne⟩
    have hsm : ContDiffOn ℝ ∞ (fun t => y * mono ζ0 c.1 c.2 t) U :=
      contDiffOn_const.mul (contDiff_mono ζ0 c.1 c.2).contDiffOn
    have hc := h _ hsm
    rw [hP] at hc
    have e1 : ∀ i, L i (wd (w i) (fun t => y * mono ζ0 c.1 c.2 t) ζ0) =
        if cnt i = c then L i x else 0 := by
      intro i
      rw [wd_eq hU hsm (w i) h0, wn_cmono, wn_mono]
      by_cases hi : cnt i = c
      · rw [if_pos hi, if_pos (by rw [← hi]), hy]
      · rw [if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), mul_zero, map_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter] at hc
    exact hc.symm
  intro f hf
  rw [h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]),
    ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt)
      (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e2 : ∀ i ∈ univ.filter (fun i => cnt i = c),
      L i (wn ((w i).count false) ((w i).count true) f ζ0) = L i (wn c.1 c.2 f ζ0) := by
    intro i hi
    have hi' : cnt i = c := (Finset.mem_filter.1 hi).2
    rw [← hi']
  rw [Finset.sum_congr rfl e2, hS c]

end Zero

section Deriv

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def smulR {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) : E →L[ℝ] (X →L[ℝ] E) :=
  ((ContinuousLinearMap.compL ℝ X ℂ E).flip c).comp (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

theorem smulR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) (e : E) (v : X) : smulR c e v = c v • e := by
  first
  | rfl
  | simp [smulR]

theorem jetR_iter (p : X →L[ℝ] ℂ) {U : Set ℂ} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : ∀ x ∈ V, p x ∈ U) {q : X} (hq : q ∈ V) (j : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (φ : X → E),
      ContDiffOn ℝ ∞ φ V → JetR U (p q) (fun f => iteratedFDeriv ℝ j (fun x => f (p x) • φ x) q) := by
  induction j with
  | zero =>
    intro E _ _ _ _ φ _
    let L0 : ℂ →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) E :=
      { toFun := fun c => (continuousMultilinearCurryFin0 ℝ X E).symm (c • φ q)
        map_add' := fun a b => by rw [add_smul, map_add]
        map_smul' := fun s a => by
          rw [RingHom.id_apply, smul_assoc, LinearIsometryEquiv.map_smul] }
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => L0, fun f _ => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | succ j ih =>
    intro E _ _ _ _ φ hφ
    let c2 : X →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp p
    have hφ' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ φ y) V := hφ.fderiv_of_isOpen hV (by simp)
    have hM1 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) p (φ y)) V :=
      (smulR (E := E) p).contDiff.comp_contDiffOn hφ
    have hM2 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) c2 (φ y)) V :=
      (smulR (E := E) c2).contDiff.comp_contDiffOn hφ
    obtain ⟨ι1, _, w1, L1, e1⟩ := ih (X →L[ℝ] E) _ hφ'
    obtain ⟨ι2, _, w2, L2, e2⟩ := ih (X →L[ℝ] E) _ hM1
    obtain ⟨ι3, _, w3, L3, e3⟩ := ih (X →L[ℝ] E) _ hM2
    let K : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (X →L[ℝ] E) →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) E :=
      (continuousMultilinearCurryRightEquiv' ℝ j X E).symm.toLinearEquiv.toLinearMap
    refine ⟨ι1 ⊕ ι2 ⊕ ι3, inferInstance,
      Sum.elim w1 (Sum.elim (fun i => w2 i ++ [false]) (fun i => w3 i ++ [true])),
      Sum.elim (fun i => K ∘ₗ L1 i) (Sum.elim (fun i => K ∘ₗ L2 i) (fun i => K ∘ₗ L3 i)), fun f hf => ?_⟩
    have hsm : ∀ {g : ℂ → ℂ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
        [IsScalarTower ℝ ℂ F] {ψ : X → F}, ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ ψ V →
        ContDiffAt ℝ j (fun y => g (p y) • ψ y) q := by
      intro g F _ _ _ _ ψ hg hψ
      exact (((hg.comp p.contDiff.contDiffOn hVU).smul hψ).contDiffAt (hV.mem_nhds hq)).of_le (inf_ge j)
    have hD : ∀ y ∈ V, fderiv ℝ (fun x => f (p x) • φ x) y =
        (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y) := by
      intro y hy
      have hfd : HasFDerivAt f (fderiv ℝ f (p y)) (p y) :=
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hVU y hy))).hasFDerivAt
      have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
        ((hφ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)).hasFDerivAt
      have hc : HasFDerivAt (fun x => f (p x)) ((fderiv ℝ f (p y)).comp p) y := hfd.comp y p.hasFDerivAt
      rw [(hc.fun_smul hφd).fderiv]
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smulR_apply, fderiv_wirt, add_smul,
        mul_smul, c2]
      simp [add_assoc]
    have hev : (fun y => fderiv ℝ (fun x => f (p x) • φ x) y) =ᶠ[𝓝 q]
        (fun y => (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y)) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) hD
    beta_reduce at e1 e2 e3 ⊢
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_add_apply ((hsm hf hφ').add (hsm (contDiffOn_dZ hU hf) hM1))
        (hsm (contDiffOn_dZb hU hf) hM2),
      fun_iteratedFDeriv_add_apply (hsm hf hφ') (hsm (contDiffOn_dZ hU hf) hM1),
      e1 f hf, e2 _ (contDiffOn_dZ hU hf), e3 _ (contDiffOn_dZb hU hf)]
    simp only [map_add, map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, wd_append]
    simp only [wd, Bool.false_eq_true, ↓reduceIte, add_assoc]
    rfl

end Deriv

section Closure

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_congr {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (e : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = Λ' f) :
    JetR U ζ0 Λ' := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, L, fun f hf => (e f hf).symm.trans (hL f hf)⟩

theorem jetR_map (Lm : M →ₗ[ℝ] N) {Λ : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) : JetR U ζ0 (fun f => Lm (Λ f)) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, fun i => Lm ∘ₗ L i, fun f hf => by simp only [hL f hf, map_sum, LinearMap.comp_apply]⟩

theorem jetR_add {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f + Λ' f) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  obtain ⟨ι', hι', w', L', hL'⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim L L', fun f hf => by
    simp only [hL f hf, hL' f hf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]⟩

theorem jetR_sub {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f - Λ' f) := by
  refine jetR_congr (jetR_add h (jetR_map (-LinearMap.id) h')) fun f _ => ?_
  simp [sub_eq_add_neg]

theorem jetR_sum {κ : Type*} (s : Finset κ) {Λ : κ → (ℂ → ℂ) → M} (h : ∀ j ∈ s, JetR U ζ0 (Λ j)) :
    JetR U ζ0 (fun f => ∑ j ∈ s, Λ j f) := by
  have h0 : JetR U ζ0 (fun _ : ℂ → ℂ => (0 : M)) :=
    ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun f _ => by simp⟩
  have hs := Finset.sum_induction Λ (JetR U ζ0) (fun a b ha hb => jetR_add ha hb) h0 h
  refine jetR_congr hs fun f _ => ?_
  simp [Finset.sum_apply]

theorem jetR_word (w : List Bool) (L : ℂ →ₗ[ℝ] M) : JetR U ζ0 (fun f => L (wd w f ζ0)) := by
  exact ⟨Unit, inferInstance, fun _ => w, fun _ => L, fun f _ => by simp⟩

def cl {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E) :
    ℂ →ₗ[ℝ] E where
  toFun c := (α * c) • e
  map_add' x y := by rw [mul_add, add_smul]
  map_smul' s c := by rw [RingHom.id_apply, mul_smul_comm, smul_assoc]

theorem cl_apply {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E)
    (c : ℂ) : cl α e c = (α * c) • e := rfl

end Closure

end Formalism.FourierDecayAlt.P.NFRO
end
end

