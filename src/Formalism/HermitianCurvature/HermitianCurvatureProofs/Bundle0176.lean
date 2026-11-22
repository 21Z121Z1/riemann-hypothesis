import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0173
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordKeyIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem cutTr_Gf_gq (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hc : ∀ a, q.1 a ≠ 0)
    (hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) :
    Formalism.QuantumDeterminants.Gf k r D.z D.z' (B.gq D q) =
      (∏ l, Complex.normSq (q.1 l)) * (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') := by
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
  have hPe : P = ∏ a : Fin r, q.1 a := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
    rw [this]
    congr 1
    ext a
    simp
  have hP0 : P ≠ 0 := by
    rw [hPe]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
    unfold zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  show Formalism.QuantumDeterminants.Gf k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) = _
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul, hPe, map_prod]
  ring

theorem cutTr_hsVec_contDiff [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    ContDiff ℝ ∞ (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  have h : (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) =
      ⇑((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ) := rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

theorem cutTr_jgq_smooth (D : B.RealPlaceData k r Wp Wq) (J : B.Mat k r → (Wq →L[ℂ] Wp)) (Om : Set (B.Mat k r))
    (hJ : Q.SmoothLev k r 0 Om J) (hOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ Om) :
    ContDiffOn ℝ ∞ (fun q => J (B.gq D q)) (JF.QDom k r D.z D.z') := by
  have hg : ContDiffOn ℝ ∞ (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D n
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ (B.gq D q) ⟨Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 hG.1, hOm q hq⟩
  refine ⟨JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ ∞ (F' ∘ fun q => B.gq D q)
      (JF.QDom k r D.z D.z' ∩ (JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1).1)

end helpers

theorem cutTr_normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 := by
    funext z; exact Complex.normSq_eq_norm_sq z
  rw [this]
  exact contDiff_norm_sq ℝ

theorem cutoff_transport_to_model : CutTr := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he hJ c hc ε hε
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
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF (T v).base (f v) (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => B.JF (T v).base (f v) (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ.1 hOm).mono hQ
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
  have hL : trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) ρ =
      MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) * u q) := by
    unfold trJ
    congr 1
    funext q
    rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, LE.Cut.sc, hc, pow_one, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e (B.JF (T v).base (f v)) ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dif_pos hu]
  rw [hL]
  show _ = MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) *
    (trJ S T v e (B.JF (T v).base (f v)) ρ).1 q)
  rw [hR]

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toSm_val_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) :
    ((MA.toSm P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = u := by
  unfold MA.toSm; rw [dif_pos h]

theorem hsVec_sum_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → (W →L[ℂ] V)) :
    B.hsVec (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • B.hsVec (e ρ) := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • Formalism.FourierDecayAlt.P.JFxI.hsVecL (e ρ)
  rw [map_sum]
  simp only [map_smul]

theorem parseval {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (e : ι → (W →L[ℂ] V))
    (X Y : W →L[ℂ] V) (hX : X = ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) • e ρ) :
    inner ℂ (B.hsVec Y) (B.hsVec X) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) * conj (inner ℂ (B.hsVec (e ρ)) (B.hsVec Y)) := by
  conv_lhs => rw [hX]
  rw [hsVec_sum_smul, inner_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_smul_right, inner_conj_symm]

theorem jgq_contDiffOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    {J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
    (hJ : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ContDiffOn ℝ ∞ (fun x => J (B.gq (T v).base x)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hGl : ∀ x ∈ JF.QDom S.G.k S.G.r Db.z Db.z', B.gq Db x ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun x hx =>
    om_sub' (Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db x hx)
  have hgq : ContDiffOn ℝ ∞ (fun x => B.gq Db x) (JF.QDom S.G.k S.G.r Db.z Db.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Db n
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ.1 _ (hGl x₀ (hQ x₀ hx₀))
  refine ⟨JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U,
    hgq.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open _ _) hU, ⟨hQ x₀ hx₀, hgU⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun x => F (B.gq Db x))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT ∩ (JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U)) :=
    hF.comp (hgq.mono fun x hx => hx.2.1) fun x hx => hx.2.2
  exact hc.congr fun x hx => hJF _ hx.2.2 (hGl x hx.2.1).1

theorem beta_frame_identity_holds : BetaFrame := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hplace e hFr J₁ hJ₁ J₂ hJ₂ hN₁ hN₂
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

  have hR : ∀ ρ, MA.ip0 (trJ S T v e J₁ ρ) (trJ S T v e J₂ ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e J₁ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e J₂ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval J₁ hJ₁, hval J₂ hJ₂]
    rw [dif_pos (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)
  have hU : ∀ (J) (hJ : J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v)),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') (fun q => B.hsVec (J (B.gq Db q))) ≠ ⊤ →
      IntegrableOn (fun x => W x * ‖B.hsVec (J (B.gq Db x))‖ ^ 2) Qs := by
    intro J hJ hN
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      (((hcont J hJ).norm.pow 2).aestronglyMeasurable hQm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    exact lt_of_le_of_lt (setLIntegral_le_lintegral Qs _) (lt_top_iff_ne_top.2 hN)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))))) Qs := by
    intro ρ
    refine Integrable.mono' ((hU J₁ hJ₁ hN₁).add (hU J₂ hJ₂ hN₂)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        ((((heC ρ).inner (hcont J₁ hJ₁)).mul ((heC ρ).inner (hcont J₂ hJ₂)).star).aestronglyMeasurable hQm)
    · refine ae_restrict_of_forall_mem hQm fun x hx => ?_
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
      have hn1 := ha J₁
      have hn2 := ha J₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖ ≤
            ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))),
          norm_nonneg (B.hsVec (J₁ (B.gq Db x))), norm_nonneg (B.hsVec (J₂ (B.gq Db x))),
          sq_nonneg (‖B.hsVec (J₁ (B.gq Db x))‖ - ‖B.hsVec (J₂ (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by ring

  unfold MA.ipA
  simp_rw [hR]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold betaBig
  have hae : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ Qs →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (J₂ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (J₁ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db] with x hx hxQ
    rcases hx with hx | hx
    · exfalso
      apply hxQ
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [hTT] at h2
      exact h2
    · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hX := (hFr.2 x.2 hx.2).2.2 (J₁ (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace J₁ hJ₁ x hx)
  exact parseval (fun ρ => e ρ x.2) (J₁ (B.gq Db x)) (J₂ (B.gq Db x)) hX

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGFormJ
section
open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section betaJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congrJ_left (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D F g = JF D F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

theorem beta_congrJ_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D G g = JF D G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end betaJ

section formJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_congrJ_left (x y x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hx : ∀ a, JC.NiceCoef (T.bs j) ε (x a)) (hy : ∀ a, JC.NiceCoef (T.bs j) ε (y a))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x x' = D.formLev T s j w y x' := by
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => beta_congrJ_left (T.bs j) fun h hh => ?_
  rw [bc_core (D.RRlev T s j w) hR x hx a hh, bc_core (D.RRlev T s j w) hR y hy a hh]
  show (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (x b) g)) h =
    (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (y b) g)) h
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (hR a b).2.2 _ _ (fun g hg hgG => hJ b g ⟨hgG, hg⟩) h hh.2 hh.1

theorem formLev_congrJ_right (x' x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x' x = D.formLev T s j w x' y := by
  unfold D.formLev
  exact Finset.sum_congr rfl fun a _ => beta_congrJ_right (T.bs j) (hJ a)

theorem pairJ_congrJ_left (ε : ℝ) : ∀ (ys : List ℝ)
    (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, JC.NiceCoef (T.bs j) ε (x a)) → (∀ a, JC.NiceCoef (T.bs j) ε (y a)) →
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y x'
  | [], x, y, x', hx, hy, hJ => formLev_congrJ_left P0 T s j w x y x' ε hx hy hJ
  | _ :: ys, x, y, x', hx, hy, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_left ε ys (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _),
      pairJ_congrJ_left ε ys (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _)]

theorem pairJ_congrJ_right : ∀ (ys : List ℝ)
    (x' : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x' x = KB.pairJ (D.formLev T s j w) ys x' y
  | [], x', x, y, hJ => formLev_congrJ_right P0 T s j w x' x y hJ
  | _ :: ys, x', x, y, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_right ys _ (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) (fun _ => hJ _),
      pairJ_congrJ_right ys _ (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) (fun _ => hJ _)]

end formJ

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def YGSlice : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h' : C.LPt) (m ρ : ℕ)
    (e1 : r = D.ptSize h' + (m + 2) + ρ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ : G.Mat (m + 2) → V) (L : V →L[ℂ] E) (γ : B.Mat k ρ) (Kc : Set ℂ) (K a : ℝ),
    D.IsLocPt h' (D.ptSize h') → (0 : ℂ) ∉ Kc → ((m : ℝ) + 1) * ((m : ℝ) + 4) < a →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → G.detM Z ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc →
      L (Φ Z) = U.PhiFun k ρ (D.ptPerm h') (D.ptDiag h') (D.castV e1 z) (D.castV e1 z')
        (D.castF e1.symm F) Z γ) →
    ∀ q, okG m Kc q →
    Integrable (fun ξ : U.Xi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) =>
        U.psiStar k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.castV (by rw [ptSize_ptG]; omega) z)
          (D.castV (by rw [ptSize_ptG]; omega) z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) F
            (U.gaXi k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
      (U.muXi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) →
    L (yG U.betaU m Φ q) = D.sliceAt k r z z' F (ptG h' m q) (D.castM (by rw [ptSize_ptG]; omega) γ)

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

