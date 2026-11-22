import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0180
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSPw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def conjL (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun X := A.comp (X.comp B)
  map_add' X Y := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c X := by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

def sumL {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) :
    (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ ρ, (((innerₛₗ ℂ (B.hsVec (f ρ))).comp Formalism.FourierDecayAlt.P.JFxI.hsVecL).smulRight (V ρ))

theorem sumL_apply {ι : Type} [Fintype ι] (f : ι → (Wq →L[ℂ] Wp)) (V : ι → (Wq →L[ℂ] Wp)) (Y : Wq →L[ℂ] Wp) :
    sumL f V Y = ∑ ρ, inner ℂ (B.hsVec (f ρ)) (B.hsVec Y) • V ρ := by
  unfold sumL
  rw [LinearMap.sum_apply]
  rfl

end SSPw

open SSPw in
theorem second_shift_pointwise_holds : SSn.Rep.Core.SSPointwise := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA l hl
  obtain ⟨hpl, hL, hS, hRel, hQQ⟩ := hA
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl

  have hcs0 := Formalism.FourierDecayAlt.P.TheSecStab.theSection_csec (k := P.k) (r := P.r) (by omega) Bs.z_mem Bs.z'_mem
    Bs.T_pos Bs.T'_pos
  set μ0 := TheSec.theSection P.k P.r Bs.z Bs.z' with hμ0
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hcs0.1 }
  have hyp0 : Gauge.GC.GTHyp P Bs0 X d := ⟨hpl, hk, hcs0, hL, hS, hRel, hQQ⟩
  obtain ⟨e0, he0, -⟩ := Gauge.GC.gauge_kappa_holds Wp Wq P Bs0 X d hyp0

  have hRT := Gauge.GC.radial_torus_local_holds Wp Wq P Bs0 hpl hk hcs0 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), Gauge.GC.SliceLoc P Bs0 (X.t Y a b) := fun Y a b =>
    Gauge.GC.second_shift_slice_derivative Wp Wq P Bs0 hpl _ (hRT Y a b)
  have hSL := (Gauge.GC.second_shift_slice_operator Wp Wq P Bs0 X d hyp0 hSl l hl).1

  have hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute (d.SS l).1 W := by
    intro f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact ((Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl).1

  have hRB0 : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := Gauge.GC.radBase_of P Bs0 hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he0.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB0 _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs0.μsec ζ) = e0 ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hdec : ∀ ζ : ℂ, ∃ hh : Q.Mx P.k P.r × Q.Mx P.k P.r, ζ ∈ Gauge.GC.Ann P →
      hh.1 ∈ UWset P.k P.r Bs.z ∧ hh.2 ∈ UWset P.k P.r Bs.z' ∧
        NF.muZ P.k P.r Bs.μsec ζ = hh.1 * NF.muZ P.k P.r μ0 ζ * hh.2 := by
    intro ζ
    by_cases hζ : ζ ∈ Gauge.GC.Ann P
    · have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
      have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
      obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hcs0.1
        hdom.2.1 hdom.2.2
      rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hq.2] at he
      exact ⟨(h, h'), fun _ => ⟨hh, hh', he⟩⟩
    · exact ⟨(1, 1), fun h => absurd h hζ⟩
  choose H hH using hdec
  let V : M.Ty P → ℂ → (Wq →L[ℂ] Wp) := fun ρ ζ =>
    ((d.SS l).1 (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r μ0 ζ)
  refine ⟨fun ζ => LinearMap.toContinuousLinearMap
    ((conjL (Bs.π (H ζ).1) (Bs.π' (H ζ).2)) ∘ₗ sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ) ∘ₗ
      conjL (Bs.π (H ζ).1⁻¹) (Bs.π' (H ζ).2⁻¹)), ?_⟩
  intro Φ c hc ζ hζ
  obtain ⟨hh, hh', hd⟩ := hH ζ hζ
  set h := (H ζ).1
  set h' := (H ζ).2
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hdom0 := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs0.1 hq
  have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'

  have hback : NF.muZ P.k P.r μ0 ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
    rw [hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
      Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
  have hΦ0 : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r μ0 ζ) =
      (Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)) := by
    rw [hback]
    exact Φ.2.2.2 (c, NF.muZ P.k P.r Bs.μsec ζ) hdom h⁻¹ hhi h'⁻¹ hhi'

  have hfwd : (((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec ζ) =
      (Bs.π h).comp (((((d.SS l).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r μ0 ζ)).comp (Bs.π' h')) := by
    rw [hd]
    exact ((d.SS l).1 Φ).2.2.2 (c, NF.muZ P.k P.r μ0 ζ) hdom0 h hh h' hh'
  have hkey := Gauge.GC.key_slice P Bs0 hpl hk e0 he0 Ψ hΨ (d.SS l).1 hSL hC Φ hc hc0 hζ
  rw [hfwd]
  change _ = (Bs.π h).comp ((sumL (fun ρ => e0 ρ ζ) (fun ρ => V ρ ζ)
    ((Bs.π h⁻¹).comp (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' h'⁻¹)))).comp
      (Bs.π' h'))
  rw [← hΦ0, sumL_apply]
  congr 2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAModelAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), ∀ u U : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P (MA.actA P (star a) u) U = MA.ipA P u (MA.actA P a U)

def SASection : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ U : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT,
        (∀ π, U π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) → ∃ K ∈ smoothFormsPositiveCone S T v, trJ S T v e K = U

def SAPairL : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J))

def SAFundQ : Prop :=
  ∀ (P : M.Par) (u w : M.Ty P → MA.SmQ P.r P.TT),
    (∀ U : M.Ty P → MA.SmQ P.r P.TT, (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P u U = MA.ipA P w U) → u = w

section lin

variable {P : M.Par}

open Formalism.FourierDecayAlt.P.MAx2.Adj

theorem ipA_add_left (u w U : M.Ty P → MA.SmQ P.r P.TT) (hU : ∀ π, U π ∈ MA.Test P.r P.TT) :
    MA.ipA P (u + w) U = MA.ipA P u U + MA.ipA P w U := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 ((u + w) π) (U π) = conj (MA.ip0 (U π) (u π + w π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (U π) (u π)) + conj (MA.ip0 (U π) (w π)) := by rw [inner_add_right_alt (hU π), map_add]
    _ = MA.ip0 (u π) (U π) + MA.ip0 (w π) (U π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_add_right (u X Y : M.Ty P → MA.SmQ P.r P.TT) (hX : ∀ π, X π ∈ MA.Test P.r P.TT)
    (hY : ∀ π, Y π ∈ MA.Test P.r P.TT) : MA.ipA P u (X + Y) = MA.ipA P u X + MA.ipA P u Y := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 (u π) ((X + Y) π) = conj (MA.ip0 (X π + Y π) (u π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (X π) (u π)) + conj (MA.ip0 (Y π) (u π)) := by rw [inner_add_left_alt (hX π) (hY π), map_add]
    _ = MA.ip0 (u π) (X π) + MA.ip0 (u π) (Y π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_smul_left (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P (c • u) U = c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_left_alt c (u π) (U π)

theorem ipA_smul_right (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P u (c • U) = conj c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_right_alt c (u π) (U π)

theorem ipA_conj (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P u U = conj (MA.ipA P U u) := by
  unfold MA.ipA
  rw [map_sum]
  exact Finset.sum_congr rfl fun π _ => inner_conj_symm_alt _ _

theorem sumAdj (u Ku : M.Ty P → MA.SmQ P.r P.TT) (hKu : ∀ π, Ku π ∈ MA.Test P.r P.TT) {α : Type*} (l : List α)
    (c : α → ℂ) (X Y : α → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ x ∈ l, (∀ π, X x π ∈ MA.Test P.r P.TT) ∧ MA.ipA P (X x) u = MA.ipA P Ku (Y x)) :
    (∀ π, (l.map fun x => c x • X x).sum π ∈ MA.Test P.r P.TT) ∧
      MA.ipA P u (l.map fun x => c x • X x).sum = MA.ipA P (l.map fun x => conj (c x) • Y x).sum Ku := by
  induction l with
  | nil =>
    refine ⟨fun π => ?_, ?_⟩
    · simpa using (test_zero : (0 : MA.SmQ P.r P.TT) ∈ MA.Test P.r P.TT)
    · simp [MA.ipA, inner_zero_left_alt, inner_zero_right_alt]
  | cons x l ih =>
    obtain ⟨hX, hXe⟩ := h x (by simp)
    obtain ⟨ihT, ihE⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨fun π => test_add (test_smul _ (hX π)) (ihT π), ?_⟩
    rw [ipA_add_right u (c x • X x) _ (fun π => test_smul (c x) (hX π)) ihT, ipA_add_left (conj (c x) • Y x) _ Ku hKu, ipA_smul_right,
      ipA_smul_left, ihE, ipA_conj u (X x), hXe, ← ipA_conj]

end lin

theorem jAStarOp_of_parts (hM : SAModelAdj) (hS : SASection) (hP : SAPairL) (hF : SAFundQ) : JAStarOp := by
  obtain ⟨C1, hS'⟩ := hS
  obtain ⟨C2, hP'⟩ := hP
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L he _ hL a ha ts hts hrep J hJ
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  apply hF (D.parOf S v)
  intro U hU
  obtain ⟨K, hK, hKU⟩ := hS' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he U hU
  subst hKU
  rw [hM _ L hTTpos hL a ha (trJ S T v e J) (trJ S T v e K) hU, (hrep K hK).2]
  exact (sumAdj (trJ S T v e J) (trJ S T v e K) hU ts (fun t => t.1) (fun t => trJ S T v e (applyL S v t.2 K))
    (fun t => trJ S T v e (adjL S v t.2 J))
    (fun t ht => hP' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he t.2 (hts t ht) K hK J hJ hU)).2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAVTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section model

variable (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r)

def capaVpM (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem capaVpM_zero (Y : ℂ) : capaVpM P L Y 0 = 1 := by
  simp [capaVpM]

theorem capaVpM_succ (Y : ℂ) (i : ℕ) (h : i < P.r) :
    capaVpM P L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * capaVpM P L Y i := by
  simp [capaVpM, List.take_add_one, h]

theorem capa_tvprod (Y : ℂ) : L.Tvprod Y = capaVpM P L Y P.r := by
  simp [R.LevelData.Tvprod, capaVpM, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem capa_Tvl_mul_0 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_Tvl_mul_1 (Y : ℂ) (l : Fin P.r) (V : Matrix (Fin 2) (Fin 2) (MA.A P (MA.DQ P))) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem capa_actA_pb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.pbA P (MA.DQ P) l) f = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

theorem capa_actA_cbi (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbiA P (MA.DQ P) l) f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (MA.sc P (MA.DQ P) _) f = _
  rw [actA_sc]
  rfl

end model

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem capa_vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r Y 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r Y i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (Q.vAB P.r Y i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r Y i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r Y i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 0) Φ =
        Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r Y (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc (Y • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

theorem capa_vabm_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L) (Y : ℂ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 0) Φ) =
          MA.actA P (capaVpM P L Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r Y i) 1) Φ) =
          MA.actA P (capaVpM P L Y i 1 0) (trR P Bs.μsec e Φ)) := by
  obtain ⟨-, hpb, -, -, hcb, hcbi, -⟩ := hL
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (vABm P.r Y 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (vABm P.r Y 0) 1) Φ = 0 := rfl
    have v0 : capaVpM P L Y 0 0 0 = 1 := by simp [capaVpM_zero]
    have v1 : capaVpM P L Y 0 1 0 = 0 := by simp [capaVpM_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (vABm P.r Y i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (vABm P.r Y i) 1) Φ with hΦB
    have hv : vABm (X := Wq →L[ℂ] Wp) P.r Y (i + 1) =
        (fun f => Y • (vABm P.r Y i).1 f - pbOp ⟨i, h⟩ ((vABm P.r Y i).1 f) -
          cbOp ⟨i, h⟩ ((vABm P.r Y i).2 f), fun f => cbiOp ⟨i, h⟩ ((vABm P.r Y i).1 f)) := by
      simp only [vABm, dif_pos h]
    have e0 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 0) Φ =
        Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA - Q.crd (cbOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (vABm P.r Y (i + 1)) 1) Φ = Q.crd (cbiOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 3
    have hcB : FamR P Bs Dc (Q.crd (cbOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 4
    have hciA : FamR P Bs Dc (Q.crd (cbiOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 5
    have hdif : FamR P Bs Dc (Y • ΦA - Q.crd (pbOp ⟨i, h⟩) ΦA) := famR_sub (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cbOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => star (c ⟨i, h⟩)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tci : trR P Bs.μsec e (Q.crd (cbiOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (star (c ⟨i, h⟩))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hdif hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hdif ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_pb hpl hk he hA, tc, tA, tB, capaVpM_succ P L Y i h, capa_Tvl_mul_0, hpb, hcb, actA_add, actA_mul,
        actA_mul, actA_neg, sub_eq_add_neg ((algebraMap ℂ (MA.A P (MA.DQ P))) Y), actA_add, actA_algebraMap, actA_neg,
        capa_actA_pb, capa_actA_cb, sub_eq_add_neg, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, capaVpM_succ P L Y i h, capa_Tvl_mul_1, actA_mul, hcbi, capa_actA_cbi]

end ind

theorem capelli_transition_holds : JDAVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ y
  have hA := (capa_vab_ind hpl hk he y P.r le_rfl Dc Φ hΦ).1
  have hAv := (capa_vabm_ind hpl hk he L hL y P.r le_rfl Dc Φ hΦ).1
  refine ⟨⟨hA.1, ?_⟩, ⟨hAv.1, ?_⟩⟩
  · rw [hA.2, R.LevelData.Ar, ← site_vector_eq_tensor_product P L hL y 0, sitesCommonSpace_v0_eq_Vp]
  · rw [hAv.2, R.LevelData.Avr, capa_tvprod]

theorem jDCapA_of_grp (hG : JDAGrp) : JDCapA := jDCapA_of_parts hG capelli_transition_holds residue_derivative_transition

end

end Formalism.FourierDecayAlt.P.CutMP
end

