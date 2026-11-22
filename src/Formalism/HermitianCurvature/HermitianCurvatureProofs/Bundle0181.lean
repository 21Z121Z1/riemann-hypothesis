import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0178
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0177

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_zero' {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] : B.hsVec (0 : W →L[ℂ] V) = 0 := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL 0 = 0
  exact map_zero _

theorem group_action_pairing_holds : GAPair := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr X Y F F' hX hY hF hF' hae
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs
  have hQm : MeasurableSet Qs := (MA.Qset_open _ _).measurableSet
  set W : (Fin S.G.r → ℂ) × ℂ → ℝ := bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') with hWdef
  have hW0 : ∀ x, 0 ≤ W x := fun x => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ x

  have hW : ∀ x ∈ Qs, W x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
    intro x hx
    have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
      rw [hTT]; exact le_of_lt hx.2
    rw [hWdef]
    unfold bcWeight
    rw [if_pos hle]
    unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
    rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
      have := l.isLt
      simp only [MA.Mdim]; omega
    have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
    have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
    rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
      pow_succ]
    field_simp

  have hval : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v), ∀ ρ,
      ((trJ S T v e J ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) =
        fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Db q.1))) := fun J hJ ρ =>
    toSm_val_of_mem (D.parOf S v) (trace_smoothness E Wp Wq S T v hplace e hFr J hJ ρ)

  have hR : ∀ ρ, MA.ip0 (trJ S T v e X ρ) (trJ S T v e Y ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e X ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e Y ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval X hX, hval Y hY]
    rw [dif_pos (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)

  have hXc : ContinuousOn (fun x => X (B.gq Db x)) Qs := (jgq_contDiffOn S T v hplace hX).continuousOn
  set O : Set ((Fin S.G.r → ℂ) × ℂ) := Qs ∩ (fun x => X (B.gq Db x)) ⁻¹' {0}ᶜ with hO
  have hOo : IsOpen O := hXc.isOpen_inter_preimage (MA.Qset_open _ _) isOpen_compl_singleton
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOQ : O ⊆ Qs := Set.inter_subset_left

  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db
    (B.AB S.G.k S.G.r) le_rfl
  have h54 : ∀ G : GFn S v, B.InCC (B.AB S.G.k S.G.r) 5 G → ∃ c, B.CCle (B.AB S.G.k S.G.r) 4 G c := by
    rintro G ⟨c, hck, hb⟩
    exact ⟨c, Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) hck, fun u w hu hw hl g hg => hb u w hu hw (by omega) g hg⟩
  obtain ⟨c₁, hc₁⟩ := h54 F hF
  obtain ⟨c₂, hc₂⟩ := h54 F' hF'
  obtain ⟨hN, hN', -⟩ := hB1 F F' c₁ c₂ hF hF' hc₁ hc₂
  unfold B.normSq jNormSq at hN hN'

  have hU : ∀ (Z G : GFn S v), Z ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) →
      (∫⁻ p, ENNReal.ofReal (W p * ‖B.hsVec (B.JF Db G (B.gq Db p))‖ ^ 2)) ≠ ⊤ →
      (∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∈ O → Z (B.gq Db x) = B.JF Db G (B.gq Db x)) →
      IntegrableOn (fun x => W x * ‖B.hsVec (Z (B.gq Db x))‖ ^ 2) O := by
    intro Z G hZ hNG hZG
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      ((((hcont Z hZ).mono hOQ).norm.pow 2).aestronglyMeasurable hOm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hNG)
    calc ∫⁻ x in O, ENNReal.ofReal (W x * ‖B.hsVec (Z (B.gq Db x))‖ ^ 2)
        = ∫⁻ x in O, ENNReal.ofReal (W x * ‖B.hsVec (B.JF Db G (B.gq Db x))‖ ^ 2) := by
          refine setLIntegral_congr_fun_ae hOm ?_
          filter_upwards [hZG] with x hx hxO
          rw [hx hxO]
      _ ≤ ∫⁻ x, ENNReal.ofReal (W x * ‖B.hsVec (B.JF Db G (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral O _
  have hUX := hU X F hX hN (by filter_upwards [hae] with x hx hxO; exact (hx (hOQ hxO)).1)
  have hUY := hU Y F' hY hN' (by filter_upwards [hae] with x hx hxO; exact (hx (hOQ hxO)).2 hxO.2)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))))) O := by
    intro ρ
    refine Integrable.mono' (hUX.add hUY) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        (((((heC ρ).inner (hcont X hX)).mul ((heC ρ).inner (hcont Y hY)).star).mono hOQ).aestronglyMeasurable hOm)
    · refine ae_restrict_of_forall_mem hOm fun x hxO => ?_
      have hx := hOQ hxO
      have he1 : ‖B.hsVec (e ρ x.2)‖ ≤ 1 := by
        have h1 : inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (e ρ x.2)) = (1 : ℂ) := by
          simpa using (hFr.2 x.2 hx.2).2.1 ρ ρ
        rw [inner_self_eq_norm_sq_to_K] at h1
        have h2' : ((‖B.hsVec (e ρ x.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
        have h2 : ‖B.hsVec (e ρ x.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
        nlinarith [norm_nonneg (B.hsVec (e ρ x.2))]
      have ha : ∀ J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J (B.gq Db x)))‖ ≤ ‖B.hsVec (J (B.gq Db x))‖ := fun J =>
        (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (J (B.gq Db x)))])
      have hn1 := ha X
      have hn2 := ha Y
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))‖ ≤
            ‖B.hsVec (X (B.gq Db x))‖ ^ 2 + ‖B.hsVec (Y (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))),
          norm_nonneg (B.hsVec (X (B.gq Db x))), norm_nonneg (B.hsVec (Y (B.gq Db x))),
          sq_nonneg (‖B.hsVec (X (B.gq Db x))‖ - ‖B.hsVec (Y (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (X (B.gq Db x))‖ ^ 2 + ‖B.hsVec (Y (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (X (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (Y (B.gq Db x))‖ ^ 2 := by ring

  have hQO : ∀ ρ, (∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x)))))) =
      ∫ x in O, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (X (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Y (B.gq Db x))))) := by
    intro ρ
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm hOQ fun x hx => ?_
    have hX0 : X (B.gq Db x) = 0 := by
      by_contra h
      exact hx.2 ⟨hx.1, h⟩
    rw [hX0, hsVec_zero', inner_zero_right, zero_mul, mul_zero]

  unfold MA.ipA
  simp_rw [hR]
  rw [Finset.sum_congr rfl fun ρ _ => hQO ρ]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold B.beta betaBig
  have hae2 : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ O →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (B.JF Db F' (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (B.JF Db F (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db, hae] with x hx hxe hxO
    by_cases hxQ : x ∈ Qs
    · have hX0 : X (B.gq Db x) = 0 := by
        by_contra h
        exact hxO ⟨hxQ, h⟩
      have hJ0 : B.JF Db F (B.gq Db x) = 0 := by rw [← (hxe hxQ).1]; exact hX0
      change ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (B.JF Db F' (B.gq Db x))) (B.hsVec (B.JF Db F (B.gq Db x))) = 0
      rw [hJ0, hsVec_zero', inner_zero_right, mul_zero]
    · rcases hx with hx | hx
      · exfalso
        apply hxQ
        refine ⟨hx.1, ?_⟩
        have h2 := hx.2
        rw [hTT] at h2
        exact h2
      · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae2]
  refine setIntegral_congr_ae hOm ?_
  filter_upwards [hae] with x hxe hxO
  rw [← Finset.mul_sum]
  congr 1
  have hXF := (hxe (hOQ hxO)).1
  have hYF := (hxe (hOQ hxO)).2 hxO.2
  have hXf := (hFr.2 x.2 (hOQ hxO).2).2.2 (X (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace X hX x (hOQ hxO))
  rw [← parseval (fun ρ => e ρ x.2) (X (B.gq Db x)) (Y (B.gq Db x)) hXf, hXF, hYF]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA.GA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section agree

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def agNN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), p.2.2))

def agN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), Matrix.of.symm (1 : B.Mat k r)))

theorem agNN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agNN p) := by
  obtain ⟨_, h2, _, h4⟩ := hp
  refine ⟨?_, h2, ?_, h4⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _

theorem agN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agN p) := by
  obtain ⟨_, h2, _, _⟩ := hp
  refine ⟨?_, h2, ?_, ?_⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact WeylGroupFacts.mem_n_one

theorem sgs_agNN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agNN p) g = (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 := by
  simp only [B.sgs, agNN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_agN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agN p) g = (Matrix.of p.1.2)⁻¹ * g := by
  simp only [B.sgs, agN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_split (p : B.SS k r) (g : B.Mat k r) :
    B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
  simp only [B.sgs, mul_assoc]

theorem agree_sgs (Bs : B.RealPlaceData k r Wp Wq) (f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hL₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (n * g) = psi k r Bs.z cStd n • f₁ g)
    (hR₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (g * n) = psi k r Bs.z' cStd n • f₁ g)
    (hU₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₁ (h * g * h') = (Bs.π h).comp ((f₁ g).comp (Bs.π' h')))
    (hL₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (n * g) = psi k r Bs.z cStd n • f₂ g)
    (hR₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (g * n) = psi k r Bs.z' cStd n • f₂ g)
    (hU₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₂ (h * g * h') = (Bs.π h).comp ((f₂ g).comp (Bs.π' h')))
    {p : B.SS k r} (hp : Bs.inSS p) {x : B.Mat k r} (hx : x ∈ JF.Om k r Bs.z Bs.z') (he : f₁ x = f₂ x) :
    f₁ (B.sgs p x) = f₂ (B.sgs p x) := by
  have hp' := hp
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have hx1 : (Matrix.of p.1.2)⁻¹ * x ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agN_inSS Bs hp) hx
  have hx2 : (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agNN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agNN_inSS Bs hp) hx
  have hn := WeylGroupFacts.mem_n_inv h2
  have hu := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1
  rw [sgs_split, hU₁ _ hx2 _ hu _ h3, hU₂ _ hx2 _ hu _ h3, hR₁ _ hx1 _ h4, hR₂ _ hx1 _ h4,
    hL₁ _ hx _ hn, hL₂ _ hx _ hn, he]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agreement_on_domain_holds : AgreeOm := by
  intro k r Wp Wq _ _ _ _ _ _ Bs J F U hJ hag g hg hgU
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hGq : Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U := by
    have e : Gf k r Bs.z Bs.z' (B.sgs p (B.gq Bs q)) = Gf k r Bs.z Bs.z' (B.gq Bs q) := by
      unfold Gf
      rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]
    rw [← e]; exact hgU
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hGq)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end agree

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smoothLog_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : ContDiffOn ℝ ∞ φ (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ => φ (Real.exp (Real.log x))) (Set.Ioi 0) :=
    (hφ : ContDiff ℝ ∞ (fun u : ℝ => φ (Real.exp u))).comp_contDiffOn
      (Real.contDiffOn_log.mono fun x hx => (ne_of_gt (Set.mem_Ioi.1 hx)))
  exact h1.congr fun x hx => by rw [Real.exp_log (Set.mem_Ioi.1 hx)]

section mem

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem phi_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ)
    {Dm : Set (Q.Mx k r)} (hD : ∀ g ∈ Dm, 0 < Gf k r Bs.z Bs.z' g) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    have hGc : Continuous (fun g : Q.Mx k r => Gf k r Bs.z Bs.z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
    refine ⟨U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}, fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • F g,
      hU.inter (isOpen_lt continuous_const hGc), ⟨hgU, hD g₀ hg₀.2⟩, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ))
          (U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp
          (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').contDiffOn fun g hg => hg.2)
      exact hc.smul (hF.mono Set.inter_subset_left)
    · intro g hgU hgG
      simp only [hFJ g hgU.1 hgG]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g
      simpa using this
    simp only [e, hL g hg n hn]
    rw [smul_comm]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g
      simpa using this
    simp only [e, hR g hg n hn]
    rw [smul_comm]
  · intro g hg h hh h' hh'
    have e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g :=
      gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g
    simp only [e, hU g hg h hh h' hh']
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end mem

theorem phi_operator_transfer_holds : JAPhiOp := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he φ hφ J hJ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  have hJ' : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) := hJ
  refine ⟨phi_mem_FFl (T v).base hφ (fun g hg => hg.1) hJ', ?_⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => J (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ'.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  set p : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q => ((φ (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) with hp_def
  have hp : p ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext p) (MA.Qset _ _)
    have hG : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) := by
      have hn := cutTr_normSq_contDiff
      fun_prop
    have hGp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT) ∈ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact mul_pos (Finset.prod_pos fun l _ => Complex.normSq_pos.2 (hx.1 l)) (sub_pos.2 hx.2)
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        ((φ ((∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp hG.contDiffOn hGp)
    refine hc.congr ?_
    intro x hx
    simp [MA.ext, hx, hp_def, MA.Gq]
  have hL : trJ S T v e (mulG S T v φ J) ρ = MA.toSm (D.parOf S v) (fun q => p q * u q) := by
    unfold trJ
    congr 1
    funext q
    simp only [mulG, GfP]
    rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, hp_def, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e J ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dif_pos hu]
  have hP : MA.toSm (D.parOf S v) p = ⟨p, hp⟩ := by
    unfold MA.toSm
    rw [dif_pos hp]
  rw [hL, hR, hP]
  have hm : (fun q => p q * u q) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := Subalgebra.mul_mem _ hp hu
  unfold MA.toSm
  rw [dif_pos hm]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

