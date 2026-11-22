import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0108
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNormalisationModelLocalizationX

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchAwayFromRim.proof (hex : NormalModelExists.Statement)
    (hprop : NormalModelProper.Statement) (hlift : BranchLift.Statement)
    (hirr : NormalLocallyIrreducible.Statement) (hext : BranchContainsNormalPoint.Statement) :
    BranchAwayFromRim.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨N, hN, hcovN⟩ := hcov
  obtain ⟨M⟩ := hex n J hJ
  set Z' := zeroSetIn M.ideal with hZ'
  have hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hZc : IsClosed Z' := by
    have hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0} := by ext z; simp [Z', zeroSetIn]
    rw [hZ'eq]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
    intro w hw q hq
    have hq' : rename Sum.inl q ∈ M.ideal := by rw [← M.comap_eq] at hq; exact hq
    have := hw _ hq'
    rwa [eval_rename] at this

  choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim
  have hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius) := by
    intro c s hs t ht hst
    apply (γ c).injOn hs ht
    rw [← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]
  choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball

  choose a bd hbJ hab using M.birational
  set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg
  have hgJ : g ∉ J := by
    have := hJ
    intro hgm
    rcases hJ.mem_or_mem hgm with h1 | h2
    · exact hu h1
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hbJ i hi
  set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def
  have hh : h ∉ M.ideal := by
    intro hm
    apply hgJ
    rw [← M.comap_eq]
    exact hm
  have heval : ∀ w : Fin n ⊕ Fin M.m → ℂ,
      eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) *
        ∏ i, eval (firstCoords w) (bd i) := by
    intro w
    simp only [h, g, eval_rename, map_mul, map_prod]
    congr 1
    simp [GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]
  have hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w' := by
    intro w hw w' hw' hνw hne
    rw [heval] at hne
    have hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])
    funext s
    rcases s with j | i
    · exact congrFun hνw j
    · have e1 := hw _ (hab i)
      have e2 := hw' _ (hab i)
      simp only [map_sub, map_mul, eval_rename, eval_X] at e1 e2
      have c1 : w ∘ Sum.inl = firstCoords w := rfl
      have c2 : w' ∘ Sum.inl = firstCoords w := by rw [hνw]; rfl
      rw [c1] at e1
      rw [c2] at e2
      apply mul_left_cancel₀ (hb i)
      linear_combination e1 - e2

  by_contra hcon
  push Not at hcon
  set r := (γ b).radius with hr
  have hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r,
      (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖ := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact hcon _ hpos _ (by linarith)
  choose τ hτr hτx hτn using hseq
  have hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1} := by
    intro j
    refine ⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩
    rw [(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp (hτx j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  obtain ⟨xh, hxcl, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem
  have hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh) := hlim
  have hxZ : xh ∈ Z' := hZc.closure_subset_iff.mpr (fun w hw => hw.1) hxcl
  have h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j
  have hνx : firstCoords xh = x := by
    refine tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_
    refine hγlim.congr fun j => ?_
    exact ((hΓZ b _ (hτr _)).2).symm

  have hUN : firstCoords ⁻¹' N ∈ 𝓝 xh :=
    hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)
  obtain ⟨B, hBo, hxB, hBU, hpre, hdense⟩ :=
    hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN
  set P := (Z' ∩ B) \ {z | eval z h = 0} with hP

  have hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius := by
    rintro q ⟨⟨hqZ, hqB⟩, hqh⟩
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)
    obtain ⟨t, ht, hteq⟩ := hc
    refine ⟨c, t, ht, ?_⟩
    have hν : firstCoords (Γ c t) = firstCoords q := by rw [(hΓZ c t ht).2, hteq]
    refine hinj _ (hΓZ c t ht).1 q hqZ hν ?_
    rw [heval, hν, ← heval]
    exact hqh
  have hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius →
      q ∉ Γ c' '' Metric.ball 0 (γ c').radius := by
    rintro q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩
    have h1 : firstCoords (Γ c t) ∈ (γ c).image := ⟨t, ht, ((hΓZ c t ht).2).symm⟩
    have h2 : firstCoords (Γ c t) ∈ (γ c').image :=
      ⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩
    have h3 := hdisj c c' hcc' ⟨h1, h2⟩
    apply hqh
    show eval (Γ c t) h = 0
    rw [heval]
    rw [show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]

  have hPsub : P ⊆ Γ b '' Metric.ball 0 r := by
    have hsplit := isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c)
      (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_
    · rcases hsplit with hs | hs
      · intro q hq
        rw [hOeq b]
        exact ⟨hq.1.1, hs hq⟩
      · exfalso
        obtain ⟨j, hjB⟩ := (hlim'.eventually (hBo.mem_nhds hxB)).exists
        have hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r := ⟨_, hτr _, rfl⟩
        have hw0O : Γ b (τ (φ j)) ∈ O b := by
          have := hw0
          rw [hOeq b] at this
          exact this.2
        have hw0P := hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩
        obtain ⟨q, hqO, hqP⟩ := mem_closure_iff.mp hw0P (O b) (hOo b) hw0O
        obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp (hs hqP)
        have hqb : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩
        have hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
        exact hPdisj q hqP b c (Ne.symm hc) hqb hqc'
    · intro q hq
      obtain ⟨c, hc⟩ := hPcov q hq
      rw [hOeq c] at hc
      by_cases hcb : c = b
      · subst hcb
        exact Or.inl hc.2
      · exact Or.inr (Set.mem_biUnion hcb hc.2)
    · ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqP hqb hqv
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqv
      have h1 : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩
      have h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
      exact hPdisj q hqP b c (Ne.symm hc) h1 h2

  obtain ⟨σ0, hσ0, hσx⟩ := hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime
    M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1)
    (hBo.mem_nhds hxB) hPsub

  have hσ0' : ‖σ0‖ < r := mem_ball_zero_iff.mp hσ0
  set δ := (r - ‖σ0‖) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r := by
    intro t ht
    rw [mem_ball_zero_iff]
    have h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0 := by
      rw [dist_eq_norm]
      calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
    have h2 := Metric.mem_ball.mp ht
    linarith
  obtain ⟨O', hO'o, hO'eq⟩ := hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball
  have hxO' : xh ∈ O' := by
    have : xh ∈ Γ b '' Metric.ball σ0 δ := ⟨σ0, Metric.mem_ball_self hδpos, hσx⟩
    rw [hO'eq] at this
    exact this.2
  obtain ⟨j, hjO, hjδ⟩ :=
    ((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists
  have hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ := by
    rw [hO'eq]
    exact ⟨(hΓZ b _ (hτr _)).1, hjO⟩
  obtain ⟨t, ht, hteq⟩ := hjV
  have htτ : t = τ (φ j) := hΓinj b (hVsub ht) (hτr _) hteq
  have hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ := by
    rw [← htτ]
    have h2 := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h2
    calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
      _ < ‖σ0‖ + δ := by linarith
  have hn2 := hτn (φ j)
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInCurveComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchInCurveComponent.proof (h₁ : BranchInComponent.Statement) :
    BranchInCurveComponent.Statement := by
  intro n I q c hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hq : q ∈ zeroSet J := c.map_zero ▸ hmaps (Metric.mem_ball_self c.radius_pos)
  refine ⟨J, hJ, ?_, Filter.mem_of_superset (Metric.ball_mem_nhds _ c.radius_pos) hmaps⟩
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := inferInstance
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have he1 : (e : WithBot ℕ∞) ≤ 1 := by
    rw [← LocalDimDomain.proof n e J hJp he q hq, ← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.map_mono hIJ))
      (Ideal.Quotient.factor_surjective _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (by simpa using he)
    have hJq : J = RingHom.ker (eval q) :=
      (Ideal.Quotient.maximal_of_isField J Ring.KrullDimLE.isField_of_isDomain).eq_of_le
        (RingHom.ker_ne_top _) fun f hf ↦ RingHom.mem_ker.2 (hq f hf)
    have hr := c.radius_pos
    have ht : (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
      rw [mem_ball_zero_iff, pi_norm_const, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      linarith
    have hct : c.toFun (fun _ ↦ ((c.radius / 2 : ℝ) : ℂ)) = c.toFun 0 := by
      rw [c.map_zero]
      funext i
      have hmem : X i - C (q i) ∈ J := by
        rw [hJq, RingHom.mem_ker]
        simp
      simpa [sub_eq_zero] using hmaps ht _ hmem
    have h0 := congrFun (c.injOn ht (Metric.mem_ball_self hr) hct) 0
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
    linarith
  rw [he]
  have : e ≤ 1 := by exact_mod_cast he1
  have : e = 1 := by omega
  subst this
  rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMHeightAddDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hn P hP
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hmin : P ∈ minimalPrimes B
  · rw [Ideal.height_eq_zero_iff.mpr hmin, ringKrullDim_quotient_eq_of_mem_minimalPrimes hmin]
    simp

  have hfin := minimalPrimes.finite_of_isNoetherianRing (R := B)
  obtain ⟨y, hyP, hyq⟩ : ∃ y ∈ P, ∀ q ∈ minimalPrimes B, y ∉ q := by
    by_contra! h
    have hsub : (P : Set B) ⊆ ⋃ i ∈ (↑hfin.toFinset : Set (Ideal B)), (id i : Set B) := by
      intro z hz
      obtain ⟨q, hq, hzq⟩ := h z hz
      exact Set.mem_biUnion (by simpa using hq) hzq
    obtain ⟨q, hq, hPq⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun i hi _ _ => ((Set.Finite.mem_toFinset hfin).mp hi).1.1)).mp hsub
    have hq' : q ∈ minimalPrimes B := (Set.Finite.mem_toFinset hfin).mp hq
    have hqP : q ≤ P := hq'.2 ⟨hP, bot_le⟩ hPq
    exact hmin (le_antisymm hPq hqP ▸ hq')
  have hym : y ∈ maximalIdeal B := le_maximalIdeal hP.ne_top hyP
  obtain ⟨hynzd, hCM⟩ := hreg B y hym hyq
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hynzd hym
  obtain ⟨rs', -, -, hd'⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B ⧸ Ideal.span {y})
  have hlt : rs'.length < n := by
    have h1 : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hn, ← hdim, hd']
      push_cast
      rfl
    have h2 : rs'.length + 1 = n := by exact_mod_cast h1
    omega
  have hle : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hyP
  have hP' : (P.map (Ideal.Quotient.mk (Ideal.span {y}))).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hle
  have hIH := ih rs'.length hlt (B ⧸ Ideal.span {y}) hd' (P.map (Ideal.Quotient.mk (Ideal.span {y})))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hIH
  have hc := height_map_add_one_le_of_mem_nonZeroDivisors hynzd P hyP
  calc ringKrullDim B = ringKrullDim (B ⧸ Ideal.span {y}) + 1 := hdim.symm
    _ = ((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) + 1 := by
        rw [hIH]
    _ = (((P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        rw [WithBot.coe_add, WithBot.coe_one, add_right_comm]
    _ ≤ (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) := by
        gcongr
        exact_mod_cast hc

theorem CMHeightAddDim.proof (hreg : CMRegularElement.Statement.{u}) : CMHeightAddDim.Statement.{u} := by
  intro B _ _ J hJ
  obtain ⟨rs, -, -, hd⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hprime := CMHeightAddDim.height_add_ringKrullDim_quotient_of_isPrime hreg rs.length B hd
  refine le_antisymm ?_ ?_
  ·
    have : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
    have : Nonempty (PrimeSpectrum (B ⧸ J)) := inferInstance
    rw [show ringKrullDim (B ⧸ J) = Order.krullDim (PrimeSpectrum (B ⧸ J)) from rfl,
      Order.krullDim_eq_iSup_coheight_of_nonempty, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    refine iSup_le fun a => ?_
    obtain ⟨a, ha⟩ := a
    set Q := a.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q := fun z hz => by
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact Ideal.zero_mem _
    have hmap : a = Q.map (Ideal.Quotient.mk J) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective a).symm
    have hco : (Order.coheight (⟨a, ha⟩ : PrimeSpectrum (B ⧸ J)) : WithBot ℕ∞) = ringKrullDim (B ⧸ Q) := by
      rw [← ringKrullDim_quotient_eq_coheight a,
        ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE hJQ))]
    rw [WithBot.coe_add, hco, ← hprime Q]
    gcongr
    exact_mod_cast Ideal.height_mono hJQ
  ·
    obtain ⟨P, hPmin, hPle⟩ := Set.exists_min_image J.minimalPrimes Ideal.height
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B J) (Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes hJ))
    have : P.IsPrime := hPmin.1.1
    have hht : J.height = P.height := by
      rw [Ideal.height_eq_inf_minimalPrimes]
      exact le_antisymm (iInf₂_le P hPmin) (le_iInf₂ fun Q hQ => hPle Q hQ)
    rw [hht, ← hprime P]
    gcongr
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hPmin.1.2)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMQuotientUnmixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem map_mem_associatedPrimes_quotient {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩

theorem CMQuotientUnmixed.proof (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalisationModelLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem NormalisationModelLocalization.full : NormalisationModelLocalization.Statement :=
  NormalisationModelLocalization.proof

end GroundTheory.Heights₂.Heights
end

