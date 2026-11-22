import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0157
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0003
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAlStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissiblePeriodZero_of_classPeriodDecomposition_all : ∀ D : D7, (∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D := by
  first | exact @GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | exact GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | (intros; apply GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaTranslatesPrimeToQIntegral
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open Formalism.L2.Th1.F (herm altE cmTheta)
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.MomN

def latOne (L : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  L.lattice.comap (LinearMap.proj 0 : (Fin 1 → ℂ) →ₗ[ℤ] ℂ)

def setupOne (d : ℕ) (L : PeriodPair) : JMB.Setup 1 := ⟨d, hOne L (Fin 1), latOne L⟩

theorem hf_hOne (L : PeriodPair) (z w : Fin 1 → ℂ) : JMB.hf (hOne L (Fin 1)) z w = herm L (z 0) (w 0) := by
  simp [JMB.hf, hOne, herm, div_eq_mul_inv]
  ring

theorem opU_hOne (L : PeriodPair) (x : Fin 1 → ℂ) (F : ℂ → ℂ) (z : Fin 1 → ℂ) :
    JMB.opU (hOne L (Fin 1)) x (fun w => F (w 0)) z = Formalism.L2.Th1.F.opU L (x 0) F (z 0) := by
  simp only [JMB.opU, Formalism.L2.Th1.F.opU, hf_hOne, Pi.add_apply]
  congr 3
  ring

theorem area_pos (L : PeriodPair) : 0 < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L

theorem herm_conj (L : PeriodPair) (x y : ℂ) : herm L y x = conj (herm L x y) := by
  simp [herm, mul_comm]

theorem rankOne_base_weight_eq_cmTheta (d : ℕ) : JMB.w0 d = cmTheta 1 d := by
  simp [JMB.w0, JMB.rtd, cmTheta]

theorem opU_contDiff (L : PeriodPair) (s : ℂ) {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s F) := by
  unfold Formalism.L2.Th1.F.opU herm
  fun_prop

theorem jet_one {F : ℂ → ℂ} (hF : ContDiff ℂ ⊤ F) (k : ℕ) (v : Fin k → Fin 1 → ℂ) :
    iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => F (z 0)) 0 v = (∏ j, v j 0) * iteratedDeriv k F 0 := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).iteratedFDeriv_comp_right hF
    (0 : Fin 1 → ℂ) (i := k) (by exact_mod_cast le_top)
  have e : (fun z : Fin 1 → ℂ => F (z 0)) = F ∘ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) := rfl
  rw [e, h, iteratedDeriv_eq_iteratedFDeriv]
  have e2 : (fun j => v j 0) = fun j => (v j 0) • (1 : ℂ) := by funext j; simp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def]
  have := (iteratedFDeriv ℂ k F ((0 : Fin 1 → ℂ) 0)).map_smul_univ (fun j => v j 0) (fun _ => (1 : ℂ))
  simpa [smul_eq_mul] using this

section Lat

variable (d : ℕ) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst

theorem beta_mem {x y : ℂ} (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    ((Real.sqrt d / 2 : ℝ) : ℂ) * herm L x y ∈ JMB.OK d := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L x y hx hy
  obtain ⟨m, hm⟩ := Formalism.L2.Th1.F.altEInt L _ y (hst x hx) hy
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have e : herm L (cmTheta 1 d * x) y = cmTheta 1 d * herm L x y := by unfold herm; ring
  simp only [altE] at hk hm
  rw [e, Complex.mul_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk] at hm
  refine ⟨m - k, k, ?_⟩
  rw [rankOne_base_weight_eq_cmTheta]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im]
    push_cast
    linarith
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.add_im,
      Complex.intCast_re, Complex.intCast_im, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_re, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.theta_im, hk]
    push_cast
    ring

theorem setupOne_ok (hp : d.Prime) (h16 : d % 16 = 7) : (setupOne d L).Ok := by
  refine ⟨hp, h16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : hOne L (Fin 1) = Matrix.diagonal fun _ => (((Formalism.L2.Th1.F.area L : ℝ) : ℂ))⁻¹ := by
      ext i j
      simp [hOne, Matrix.one_apply, Matrix.diagonal_apply]
    show (hOne L (Fin 1)).PosDef
    rw [h, Matrix.posDef_diagonal_iff]
    intro _
    have := area_pos L
    rw [← Complex.ofReal_inv]
    exact_mod_cast inv_pos.2 this
  · have hi : Function.Injective (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) := by
      intro a b hab
      ext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      exact congrArg (fun w : L.lattice => (w : ℂ)) hab
    have hc : Continuous (fun x : (setupOne d L).La => (⟨x.1 0, x.2⟩ : L.lattice)) :=
      Continuous.subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _
    exact DiscreteTopology.of_continuous_injective hc hi
  · have htop : Submodule.span ℝ (L.lattice : Set ℂ) = ⊤ := IsZLattice.span_top
    let c : ℂ →ₗ[ℝ] (Fin 1 → ℂ) := LinearMap.pi fun _ => LinearMap.id
    rw [eq_top_iff]
    intro v _
    have hv : v = c (v 0) := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
    have h0 : v 0 ∈ Submodule.span ℝ (L.lattice : Set ℂ) := by rw [htop]; trivial
    have hmap : (Submodule.span ℝ (L.lattice : Set ℂ)).map c ≤ Submodule.span ℝ ((setupOne d L).La : Set (Fin 1 → ℂ)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Submodule.subset_span hw
    rw [hv]
    exact hmap (Submodule.mem_map_of_mem h0)
  · intro x hx
    show (JMB.w0 d • x) 0 ∈ L.lattice
    rw [Pi.smul_apply, smul_eq_mul, rankOne_base_weight_eq_cmTheta]
    exact hst _ hx
  · intro x hx y hy
    show ((Real.sqrt d / 2 : ℝ) : ℂ) * JMB.hf (hOne L (Fin 1)) x y ∈ JMB.OK d
    rw [hf_hOne]
    exact beta_mem d L hst hx hy
  · intro y hy
    have key : ∀ w ∈ L.lattice, ∃ m : ℤ, altE L (y 0) w = (m : ℝ) := by
      intro w hw
      obtain ⟨k, hk⟩ := hy (fun _ => w) hw
      refine ⟨-k, ?_⟩
      have e : JMB.hf (setupOne d L).Hm (fun _ => w) y = herm L w (y 0) := hf_hOne L _ _
      rw [e] at hk
      simp only [altE]
      rw [herm_conj L w (y 0), Complex.conj_im, hk]
      push_cast; ring
    exact Formalism.L2.Th1.H.mem_lattice_of_dual L _ (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)

end Lat

theorem mem_Qbar_phi (D : D7) (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact IsAlgebraic.algHom D.host.φ₀.toRatAlgHom (Algebra.IsAlgebraic.isAlgebraic x)

section Main

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem contDiff_base_even_theta_kernel : ContDiff ℂ ⊤ B.th0 :=
  (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B)).1.contDiff

def eOne (_B : Base D cc δ) : (Fin 1 → ℂ) → ℂ := fun z => _B.th0 (z 0)

theorem eOne_theta : (setupOne D.host.d B.L).IsTheta (eOne B) := by
  refine ⟨(contDiff_base_even_theta_kernel B).comp (by fun_prop), fun x hx => ?_⟩
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  have hc := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (GlobalTheory.FourthRootStd.hst B) (GlobalTheory.FourthRootStd.omega_mem B)
    (GlobalTheory.FourthRootStd.hθ B) (GlobalTheory.FourthRootStd.hθ' B) h8 (x 0) hx
  funext z
  have hfix := Formalism.L2.Th1.H.th0Char_mul_opU_th0_half_period_eq B.L B.ω₀ (GlobalTheory.FourthRootStd.omega_mem B) (GlobalTheory.FourthRootStd.half B) (x 0) hx (z 0)
  rw [← hc] at hfix
  have hU : JMB.opU (setupOne D.host.d B.L).Hm x (eOne B) z = Formalism.L2.Th1.F.opU B.L (x 0) B.th0 (z 0) :=
    opU_hOne B.L x B.th0 z
  have hb : (JMB.beta (setupOne D.host.d B.L).d (setupOne D.host.d B.L).Hm x x).re = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (x 0) := by
    have : JMB.hf (setupOne D.host.d B.L).Hm x x = herm B.L (x 0) (x 0) := hf_hOne B.L x x
    rw [JMB.beta, this, Complex.re_ofReal_mul]
    rfl
  simp only [JMB.opW]
  rw [hU, hb]
  exact hfix

theorem eOne_algJets (hc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {δ₀ : ℂ} (h0 : δ / δ₀ ∈ Qbar) :
    (setupOne D.host.d B.L).AlgJets δ₀ (eOne B) := by
  intro k ys hy
  have hcc : cc ≠ ⊥ := hc.1
  have hdir : ∀ j, δ₀⁻¹ * ys j 0 ∈ Qbar := by
    intro j
    obtain ⟨s, hs, hmem⟩ := hy j
    have h1 : (s : ℂ) * ys j 0 ∈ lamOf D cc δ := by
      have := (GlobalTheory.FourthRootStd.mem_iff B _).1 hmem
      simpa using this
    obtain ⟨x, -, hx⟩ := ((GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D).2.2.2.2 cc δ hcc).2 _ |>.1 h1
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : δ₀⁻¹ * ys j 0 = (δ / δ₀) * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
      have : ys j 0 = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) * (s : ℂ)⁻¹ := by
        field_simp
        rw [mul_comm]; exact hx
      rw [this]; ring
    rw [e]
    exact mul_mem (mul_mem h0 (mem_Qbar_phi D _)) (inv_mem (natCast_mem _ s))
  have hj := jet_one (contDiff_base_even_theta_kernel B) k (fun j => δ₀⁻¹ • ys j)
  show iteratedFDeriv ℂ k (fun z : Fin 1 → ℂ => B.th0 (z 0)) 0 (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [hj]
  refine mul_mem (prod_mem fun j _ => ?_) (GlobalTheory.T.iteratedDeriv_th0_zero_mem_Qbar D cc δ B hc hδ k)
  simpa using hdir j

end Main

theorem latInt_opU_of_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q →
    ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (s : ℂ) (n : ℕ), Nat.Coprime n q →
    (n : ℂ) * s ∈ B.L.lattice → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) (Formalism.L2.Th1.F.opU B.L s B.th0) := by
  intro D cc δ B hc hδ q _ hq2 hj hcop ι δ₀ θ Ω hPer s n hn hs
  obtain ⟨hp, h16, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hOk : (setupOne D.host.d B.L).Ok := setupOne_ok D.host.d B.L (GlobalTheory.FourthRootStd.hst B) hp h16
  have hd0 : δ / δ₀ ∈ Qbar := (GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hc hδ hPer.2.1 q hq2 hcop).1
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : q = 1 := by simpa using hn
      exact absurd this (Fact.out : q.Prime).one_lt.ne'
    · exact h
  have hprime : (setupOne D.host.d B.L).PrimeTo q (fun _ => s) := ⟨n, hnpos, hn, hs⟩
  let p0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let c0 : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
  have hLat : LatInt ι (Ω / ι δ₀) (setupOne D.host.d B.L).La.toAddSubgroup (eOne B) :=
    GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 1 → ℂ) _ (lamOf D cc δ) _ p0 B.th0 (contDiff_base_even_theta_kernel B)
      (fun x hx => ⟨1, Nat.coprime_one_left q, by
        rw [one_smul]; exact (GlobalTheory.FourthRootStd.mem_iff B _).1 hx⟩)
      (GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime D cc δ B hc hδ q hq2 hj hcop ι δ₀ θ Ω hPer)
  have hres := GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality q ι δ₀ θ Ω 1 (setupOne D.host.d B.L) (eOne B) (fun _ => s) hPer hOk
    (Or.inr ⟨hq2, hj⟩) (eOne_theta B) (eOne_algJets B hc hδ hd0) hprime hLat
  have hU : JMB.opU (setupOne D.host.d B.L).Hm (fun _ => s) (eOne B)
      = fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0) := by
    funext z; exact opU_hOne B.L _ B.th0 z
  rw [hU] at hres
  have hcd : ContDiff ℂ ⊤ (fun z : Fin 1 → ℂ => Formalism.L2.Th1.F.opU B.L s B.th0 (z 0)) :=
    (opU_contDiff B.L s (contDiff_base_even_theta_kernel B)).comp (by fun_prop)
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (Fin 1 → ℂ) ℂ _ _ (lamOf D cc δ) c0 _ hcd
    (fun x hx => ⟨1, Nat.coprime_one_left q, by
      rw [one_smul]
      show x ∈ B.L.lattice
      exact (GlobalTheory.FourthRootStd.mem_iff B _).2 hx⟩) hres

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoMTSOfGaInv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory

open Matrix MvPolynomial Formalism.L2.GlobalTheoryTheory.Br

set_option maxHeartbeats 1000000 in

theorem coMTS_of_gaInv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B' : GL (Fin (D.R.N D.R.m)) D.host.E), IsUnit (B w c).det → (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) * bZg u Tf.til.z0 (B w c) → ∀ (f : (D.mem u).C.Y D.R.m → ℂ) (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ), (∀ z, f z = fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) → Formalism.L2.GlobalTheoryTheory.Br.coMTS Tf B w c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) • P := by
  intro D u Ch chOf Tf B w c B' hBdet hB' f P hf
  have hg : ∃ g : GL (Fin (D.R.N D.R.m)) D.host.E, g = (Tf.til.ga c).1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hg
  rw [← hg] at hB'
  have hbZg := bZg_isUnitS Tf (B w c) hBdet
  have hU2 := atInf_inv_isUnit _ hbZg

  have hprod : ∀ τ, atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ *
      atInf (embT D) ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ =
      atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul]
    congr 1
    have e1 : ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
        (((g * B')⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    have e2 : ((g * B' : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = bZg u Tf.til.z0 (B w c) := by
      rw [Units.val_mul, hB', ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e1, Matrix.coe_units_inv, e2]
  subst hg
  have hT : trEvS Tf c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
      fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
        (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) P := by
    funext y
    simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, hf, Equiv.apply_symm_apply]
    congr 1
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, ← Matrix.mul_assoc, hprod]
  simp only [coMTS, LinearMap.coe_comp, Function.comp_apply]
  rw [hT, map_smul, fnInv_fnOf _ _ _ hU2]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsLocBasisClsP
section
noncomputable section

namespace GlobalTheory.ClsPLocBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem exists_isLocBasis_clsP : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP),
    ∃ B : GL (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B := by
  intro D u Ch chOf Tf w c
  have hL : Submodule.IsLattice D.host.E (Tf.clsP.lat c) :=
    Formalism.MainNotions.G.ChF.isLattice_of_hat Tf.clsP.lev.Lb (Tf.clsP.lat c) Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span
      (Tf.clsP.y c).1 (Tf.clsP.y_lat c)
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (D.what₂.places.resChar w) D.host.E (Tf.clsP.lat c) hL.fg hL.span_eq_top

end GlobalTheory.ClsPLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPtEmbOfCoordInt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.FormsRatOfInt

theorem intSpan_le_ratSpan (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam ≤ Formalism.L2.Forms.RatSpan D lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan Formalism.L2.Forms.RatSpan
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem exists_ptEmb_of_coord_int : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl), ∀ z ∈ (D.fm u).ptC, (∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) → ∃ y, (D.fm u).ptEmb y = z := by
  intro D u Ch chOf Tf B w z hz hint
  refine (Tf.valP.rat z).2 ⟨hz, fun c => ?_⟩
  have hB : IsUnit ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B w c))
  obtain ⟨Q, hQ, hq⟩ := Formalism.L2.GlobalTheoryTheory.Br.eW_repS Tf _ hB z hz c
  have hco : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c = Q := by
    simp only [Formalism.L2.GlobalTheoryTheory.Br.coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ hB)]
  have hQr : Q ∈ Formalism.L2.Forms.RatSpan D (D.fm u).sg := intSpan_le_ratSpan D w _ (hco ▸ hint c)
  obtain ⟨Q', hQ', he⟩ := GlobalTheory.LevelHecke.exists_ratSpan_fnOf_atInf (D.fm u).sg _ (shiftOf (sgT u))
    (((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹) hQr
  exact ⟨Q', hQ', hq.trans he⟩

end GlobalTheory.FormsRatOfInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PtCoMemIntSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PtCo

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem ptCo_one (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V) (hy : y ∈ (D.fm u).ptLat.L) (c : (D.fm u).clsP) :
    Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  obtain ⟨P, hP, hq⟩ := (Tf.valP.lat y).1 hy w c (B w c) (hB w c)
  rw [Matrix.coe_units_inv] at hq
  have e : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c = P := by
    simp only [Formalism.L2.GlobalTheoryTheory.Br.coPTS, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, LinearEquiv.coe_coe]
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (Matrix.isUnits_det_units (B w c)))]
  rw [e]
  exact hP

theorem ptCo_mem_intSpan : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E), (∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c)) → ∀ w, ∀ y ∈ (D.fm u).SP w, ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  intro D u Ch chOf Tf B hB w y hy c
  induction hy using Submodule.span_induction with
  | mem y hy => exact ptCo_one D u Ch chOf Tf B hB w y hy c
  | zero => rw [map_zero, map_zero, Pi.zero_apply]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, map_add, Pi.add_apply]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : D.what₂.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply]
    exact intSpan_smul' D w _ (r : D.what₂.LL) r.2 _ hy

end GlobalTheory.PtCo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPairStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  first | exact @GlobalTheory.PerRedTw.reduction_perDecTw | exact GlobalTheory.PerRedTw.reduction_perDecTw | (intros; apply GlobalTheory.PerRedTw.reduction_perDecTw <;> assumption)
end

