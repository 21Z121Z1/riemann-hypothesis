import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatMulDivPowMemIntegralFiniteAdele
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

set_option maxHeartbeats 800000

namespace GlobalTheory.DivInt
open GlobalTheory.AdeleBaseChange Formalism.UG.P

theorem exists_nat_mul_div_pow_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  intro F E _ _ _ _ _ w z hz ℓ hℓ
  obtain ⟨ι, hι⟩ := exists_toAd F E
  obtain ⟨x, r, hr, hzr⟩ := exists_approx z
  obtain ⟨D, hD, hDx⟩ := exists_nat_mul_integral ({x} : Finset E)
  obtain ⟨o, ho⟩ := hDx x (Finset.mem_singleton_self x)
  have hDz : algebraMap E _ (D : E) * ι z ∈ intAd E := by
    rw [hzr, map_add, map_tmul_one hι, mul_add, ← map_mul, ← nsmul_eq_mul, ← ho]
    exact add_mem (algebraMap_int_mem o) (mul_mem (by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact algebraMap_int_mem _) (map_mem_int hι hr))
  refine ⟨D, hD, fun n => mem_int_of_map hι ?_⟩
  intro P
  rw [map_mul, map_tmul_one hι]
  change algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P ∈ P.adicCompletionIntegers E
  by_cases hP : P.under (𝓞 F) = w
  · have hv : Valued.v (algebraMap E (P.adicCompletion E) (ℓ : E)) = 1 := by
      rw [levelaf_valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      apply hℓ
      rw [← hP, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
      exact hm
    have h1 := hDz P
    change algebraMap E (P.adicCompletion E) (D : E) * ι z P ∈ P.adicCompletionIntegers E at h1
    have e : algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P =
        (algebraMap E (P.adicCompletion E) (ℓ : E))⁻¹ ^ n *
          (algebraMap E (P.adicCompletion E) (D : E) * ι z P) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, inv_pow]; ring
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [e, map_mul, map_pow, map_inv₀, hv, inv_one, one_pow, one_mul]
    exact h1
  · have h0 : ι z P = 0 := (prV_eq_zero_iff hι (P.under (𝓞 F)) z).1 (hz _ hP) P rfl
    rw [h0, mul_zero]
    exact zero_mem _

end GlobalTheory.DivInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdeleIsoComponentZeroOfInfinitelyDivisible
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ (x γ : WithZero (Multiplicative ℤ)) (hx : x ≠ 0) (hγ : γ < 1) :
    ∃ n : ℕ, γ ^ n < x := by
  by_cases h0 : γ = 0
  · exact ⟨1, by simp [h0, zero_lt_iff.2 hx]⟩
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hg : Multiplicative.toAdd g < 0 := by
    have : g < 1 := by exact_mod_cast hγ
    exact this
  refine ⟨(Multiplicative.toAdd a).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (g ^ ((Multiplicative.toAdd a).natAbs + 1)) < Multiplicative.toAdd a
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  have h1 := neg_abs_le (Multiplicative.toAdd a)
  have h2 : Multiplicative.toAdd g ≤ -1 := by omega
  have h3 := abs_nonneg (Multiplicative.toAdd a)
  nlinarith

theorem GlobalTheory.TwV.Xc.adIso_comp_zero_of_div : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ iE iA hrat hint ι hι z ℓ D hℓ hD hdiv P hP
  set y := ι (iA.symm z) with hy

  have hc : ∀ n : ℕ, iA.symm (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      = ((D : E') / (ℓ : E') ^ n) ⊗ₜ[F'] (1 : FiniteAdeleRing (𝓞 F') F') := by
    intro n
    rw [RingEquiv.symm_apply_eq, hrat]
    simp [map_div₀, map_pow, map_natCast]
  have hbound : ∀ n : ℕ, Valued.v (((D : E') / (ℓ : E') ^ n : E') : P.adicCompletion E') * Valued.v (y P) ≤ 1 := by
    intro n
    have hmem := hdiv n
    have h1 : iA.symm ((((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z) ∈ RInt F' E' := by
      rw [← hint, RingEquiv.apply_symm_apply]; exact hmem
    have h2 := (hι.2 _).1 h1 P
    rw [map_mul, hc, map_mul, hι.1, ← hy] at h2
    rw [← map_mul]
    simpa using h2
  have hval : ∀ c : E', Valued.v ((c : E') : P.adicCompletion E') = P.valuation E' c :=
    fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P c
  have hℓE : ((ℓ : 𝓞 E') : E') = (ℓ : E') := by simp
  have hlt : P.valuation E' (ℓ : E') < 1 := by
    rw [← hℓE]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 hP
  have hℓ0 : P.valuation E' (ℓ : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hℓ.ne'
  have hD0 : P.valuation E' (D : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hD.ne'
  by_contra hyP
  have hyv : Valued.v (y P) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hyP
  obtain ⟨n, hn⟩ := GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ
    (P.valuation E' (D : E') * Valued.v (y P)) (P.valuation E' (ℓ : E')) (mul_ne_zero hD0 hyv) hlt
  have hb := hbound n
  rw [hval, map_div₀, map_pow] at hb
  have hpos : (0 : WithZero (Multiplicative ℤ)) < P.valuation E' (ℓ : E') ^ n :=
    zero_lt_iff.2 (pow_ne_zero _ hℓ0)
  have : P.valuation E' (D : E') * Valued.v (y P) ≤ P.valuation E' (ℓ : E') ^ n := by
    have he : P.valuation E' (D : E') * Valued.v (y P)
        = P.valuation E' (D : E') / P.valuation E' (ℓ : E') ^ n * Valued.v (y P) * P.valuation E' (ℓ : E') ^ n := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero _ hℓ0)]
    rw [he]
    simpa using mul_le_mul' hb (le_refl (P.valuation E' (ℓ : E') ^ n))
  exact absurd hn (not_lt.2 this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem eFac_mul_pPow : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), E.iK ((pendT X E hfin hst hLT pos F).eS j La * ((pendT X E hfin hst hLT pos F).eT j La')⁻¹) * pPow X j La La' = 1 := by
  intro p _ X _ E hfin hst g hLT T pos F j La La'
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  show E.iK (Pend.eS _ j La * (Pend.eT _ j La')⁻¹) * pPow X j La La' = 1
  simp only [Pend.eS, Pend.eT]
  rw [pPow_eq_prod]
  rw [map_mul, map_inv₀, map_prod, map_prod]
  simp only [map_zpow₀, map_natCast]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun v _ => ?_)
  rw [← zpow_neg, ← zpow_add₀ hp, ← zpow_add₀ hp]
  show (p : ℂ_[p]) ^ _ = 1
  ring_nf
  simp

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GmOfMapEqActC
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem blk_frame_eq {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : PosTie X D pos Kc ι ρ) (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n)
    (M : GL (Fin n) D.host.E) (hU : StdU D M) (hF : FrIs fd ρ j La h M) :
    (fun v s => Matrix.GeneralLinearGroup.map (algebraMap X.G.Kf Kc)
        (gPosGL (X.Pj j) v s ((SecondKernelHermitian.glInv X j (SecondKernelHermitian.BOf fd j La) v)⁻¹))) =
      (fun v s => Matrix.GeneralLinearGroup.map ι (hAt (X.Pj j) h (posJ X D pos j) (fun _ => 1) (atR D M) v s)) := by
  have hblk := GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU
  cases j with
  | zero =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X 0 (SecondKernelHermitian.BOf fd 0 La) v)⁻¹ = SecondKernelHermitian.frGL fd 0 La v := inv_inv _
    have hdet : IsUnit (fd.frM 0 La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) = fd.frM 0 La v := by
      unfold SecondKernelHermitian.frGL
      rw [dif_pos hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm
  | succ j =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X (j + 1) (SecondKernelHermitian.BOf fd (j + 1) La) v)⁻¹ = SecondKernelHermitian.frGL fd (j + 1) La v := inv_inv _
    have hdet : IsUnit (fd.frM (j + 1) La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) = fd.frM (j + 1) La v := by
      unfold SecondKernelHermitian.frGL
      rw [dif_pos hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem gmOf_map_eq_actC : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → ∀ (G : (X.Pj j).Xsp) (V : XR (X.Pj j) ℂ), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι V → MvPolynomial.map (algebraMap X.G.Kf Kc) (gmOf fd j La G) = MvPolynomial.map ι (actC X D pos j h M V) := by
  intro p _ X D pos Kc _ _ ι ρ hT fd j La n h M hU hF G V hGV
  unfold gmOf actC
  rw [natAct_eq, map_natActR, map_natActR, ← hGV, blk_frame_eq X D pos Kc ι ρ hT fd j La h M hU hF]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterFiniteIdeleEqProdValuesZpow
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.HeckeFinVal

open Neutral.B1 Formalism.L2.Host PI.HeckeProdW

theorem idele_ext {L : Type} [Field L] [NumberField L] {a c : Ideles L}
    (h1 : ∀ w, pw w a = pw w c) (h2 : ∀ v, pv v a = pv v c) : a = c :=
  Units.ext (Prod.ext (funext fun w => h1 w) (Subtype.ext (funext fun v => h2 v)))

theorem loc_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.UnrAt P) (x : (P.adicCompletion L)ˣ) : ∃ k : ℤ, χ.loc P x = χ.val P ^ k := by
  have hx0 : Valued.v (x : P.adicCompletion L) ≠ 0 := by simp
  set m : ℤ := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hxm : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log hx0).symm
  set ϖ : (P.adicCompletion L)ˣ := atFin P (unif P) with hϖ
  have hϖv : Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  refine ⟨-m, ?_⟩
  have hu : IsUnitAt P (x * ϖ ^ m) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxm, hϖv, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h3 := hP _ hu
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact h3

theorem eq_prod_val_zpow : ∀ {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (b : Neutral.B1.Ideles L), Formalism.L2.Host.IsFinIdele b → (∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) →
    (∀ P ∈ T, χ.UnrAt P) → ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P := by
  intro L _ _ χ T b hb hout hunr
  classical
  let u : ∀ P : HeightOneSpectrum (𝓞 L), (P.adicCompletion L)ˣ := fun P =>
    ⟨pv P b, pv P b⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by rw [← map_mul, inv_mul_cancel, map_one]⟩
  have hdec : b = ∏ P ∈ T, localIdele L P (u P) := by
    refine idele_ext (fun w => ?_) (fun v => ?_)
    · rw [map_prod]
      rw [Finset.prod_eq_one fun P _ => pw_local w P (u P)]
      exact hb w
    · rw [map_prod]
      by_cases hv : v ∈ T
      · rw [Finset.prod_eq_single v]
        · rw [pv_local_self]
        · intro P _ hPv
          exact pv_local_ne P v (Ne.symm hPv) _
        · intro h; exact absurd hv h
      · rw [Finset.prod_eq_one fun P hP => pv_local_ne P v (fun e => hv (e ▸ hP)) _]
        exact hout v hv
  have hk : ∀ P ∈ T, ∃ k : ℤ, χ.loc P (u P) = χ.val P ^ k := fun P hP => loc_eq_val_zpow χ P (hunr P hP) (u P)
  choose! n hn using hk
  refine ⟨n, ?_⟩
  rw [hdec, map_prod]
  exact Finset.prod_congr rfl fun P hP => hn P hP

end GlobalTheory.HeckeFinVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseAtCompan

theorem mem_reL_symm {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin b → E))
    (x : Fin a → E) : x ∈ reL h.symm L ↔ reV h E x ∈ L := by
  subst h
  show x ∈ reL rfl L ↔ reV rfl E x ∈ L
  rw [reL_rfl, reV_rfl]

theorem mem_mvL_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (co : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (y : Fin N → E) : (co : Matrix (Fin N) (Fin N) E) *ᵥ y ∈ mvL co Λ ↔ y ∈ Λ := by
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : toLE co z = toLE co y := e
    rwa [(toLE co).injective e'] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem smul_mem_of_mem_compan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {R : Ranks} (sp : Spaces R F E) {σ : E →ₐ[F] E} (hσ : (σ : E →+* E) = (sp.cm.sig : E →+* E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (a : 𝓞 E)
    (y : Fin n → E) (hy : y ∈ compan (sp := sp) J a S.Lb) : (T : E) • y ∈ S.Lb := by
  let M : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {y | (T : E) • y ∈ S.Lb}
      add_mem' := fun {x z} hx hz => by
        show (T : E) • (x + z) ∈ S.Lb
        rw [smul_add]; exact add_mem hx hz
      zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        show (T : E) • (c • x) ∈ S.Lb
        rw [smul_comm]; exact S.Lb.smul_mem c hx }
  have hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hσ] at hz
    exact S.Lb_dual z hz
  have hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) := by
    intro x hx
    apply Submodule.subset_span
    have := S.Lb_int x hx
    rwa [hσ] at this
  exact hd (sup_le hL Submodule.smul_le_right hy)

theorem isBaseAt_inv_of_latCo : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  intro D X0 u w hg i hi T bad S co a hT hstd
  have hr := rankN D (i + 1) hi
  set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC
  have h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩
  have hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1)) := by
    rw [← hstd, GlobalTheory.TwU.latCo, h1]
  have hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [← mem_mvL_iff co C y, hm]
    unfold StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]
  have hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb :=
    smul_mem_of_mem_compan D.sp rfl S a
  refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_
  · rw [mem_reL_symm, hCi]
    exact free_re (rankN D (i + 1) hi) co _ x
  · have hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal :=
      natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT
    refine (loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm
    · intro x hx
      rw [mem_reL_symm hr] at hx ⊢
      exact le_sup_left (a := S.Lb) hx
    · intro y hy
      rw [mem_reL_symm hr] at hy ⊢
      rw [map_smul]
      exact hTC _ hy

end GlobalTheory.BaseAtCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelic
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]

set_option maxHeartbeats 1000000 in

theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dif_pos ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeSelfDualEvenRankAtSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerSiteSelfDual

theorem isSDLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {n N : ℕ} (h : n = N)
    {L : Submodule (𝓞 E) (Fin n → E)} {M : Submodule (𝓞 E) (Fin N → E)} (hL : HEq L M) (hM : Formalism.BasicNotions.IsSDLat E N M) :
    Formalism.BasicNotions.IsSDLat E n L := by
  subst h
  cases hL
  exact hM

set_option maxHeartbeats 2000000 in

theorem even_and_isSDLat_kerN : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j ≤ D.R.m → ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → Even (((sysS H X std).Pj j).m + 1) ∧ IsSDLat D.host.E (((sysS H X std).Pj j).m + 1) ((J.fd std).kerN j La) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hk, -⟩ := hD j hj La hLa
  refine ⟨hr ▸ Formalism.MainNotions.product_zeroth_first_parts.N_even D.R j, isSDLat_of_heq hr hk ?_⟩
  exact GlobalTheory.KerSelfDual.isSDLat_latK_of_stdL ((J.St j hj).K (J.chart std j hj La)).lev (J.A.crd j hj) J.a
    (J.pins.crd_orth j hj) (J.base j hj _) (J.pt std j hj La)

end GlobalTheory.KerSiteSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_adelic_point_step_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  first | exact @GlobalTheory.TwV.Joint.isPt_pt_zero | exact GlobalTheory.TwV.Joint.isPt_pt_zero | (intros; apply GlobalTheory.TwV.Joint.isPt_pt_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_bases_span_at_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  first | exact @GlobalTheory.TwV.Joint.basesAt_span | exact GlobalTheory.TwV.Joint.basesAt_span | (intros; apply GlobalTheory.TwV.Joint.basesAt_span <;> assumption)
end

