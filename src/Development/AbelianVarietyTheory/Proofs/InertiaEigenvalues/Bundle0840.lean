import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.TupleChars

variable {D : D7}

open GlobalTheory.StepLaw (ResAt UnrOff)

theorem idemSum_mul_idemAt {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) : (idem Q + cA D (idem Q)) * idemAt PP = 0 := by
  rw [idem, map_sum, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_eq_zero fun i hi => h.mul_eq_zero (hQ hi) hPP (by rintro rfl; exact hn hi),
    Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact h.mul_conj hPP (hQ hi), add_zero]

theorem idemSum_mul_of_off {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) {e : AE D} (he : IsIdemAt e PP) {x : AE D} (hx : e * (x - 1) = x - 1) :
    (idem Q + cA D (idem Q)) * x = idem Q + cA D (idem Q) := by
  have k := idemSum_mul_idemAt h hQ hPP hn
  rw [idemAt_eq he] at k
  linear_combination (-(idem Q + cA D (idem Q))) * hx + (x - 1) * k

theorem resAt_of_isResAt {χ : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {c : (kP PP)ˣ →* Circle} (h : IsResAt χ PP c) :
    ResAt χ PP (Circle.toUnits.comp c) := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  rw [h x (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm]
  rfl

theorem resAt_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet P)
    (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2 (idemSum_mul_of_off h hQ hPP hn he hx)]
  simp

theorem resAt_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (PP : Pl D.host.E) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2]
  simp

theorem resAt_twist {t : Twist D Circle} (ht : t.Good) {P : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : t.Q ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) : ResAt t.chi PP (t.locC PP) := by
  by_cases hq : PP ∈ t.Q
  · have e : t.locC PP = t.resC PP := by simp only [Twist.locC, if_pos hq]
    rw [e]
    exact resAt_of_isResAt (ht.res PP hq)
  · have e : t.locC PP = 1 := by simp only [Twist.locC, if_neg hq]
    rw [e]
    exact resAt_of_unram ht.unram h hQ hPP hq

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  simp [infPart, Algebra.TensorProduct.algebraMap_apply]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem infPart_eq_one {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x : AE D}
    (h : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  have k := congrArg (infPart D) h
  rw [map_mul, map_sub, map_one, infPart_placeIdem hε, zero_mul] at k
  linear_combination -k

theorem unrOff_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet Q)
    (hQ : Q ⊆ P) : UnrOff χ P := by
  intro v ε hε hv x h1 h2 h3
  refine hχ x (infPart_eq_one hε h1) h2 h3 ?_
  have k : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v', ε', hε', he⟩ := (h.isIdemAt hPP).1
    have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v' ε' (h.isIdemAt hPP) hε' he
    rw [he, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε fun e => hv PP (hQ hPP) (hu.trans e), map_zero]
  linear_combination (-(idem Q + cA D (idem Q))) * h1 + ((x : AE D) - 1) * k

theorem unrOff_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (P : Finset (Pl D.host.E)) :
    UnrOff χ P := fun _ _ hε _ x h1 h2 h3 => hχ x (infPart_eq_one hε h1) h2 h3

theorem tuple_chars : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q →
    (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧
      GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
    GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  intro D S T B hB ν hν hA
  classical
  obtain ⟨P, hPg, hQP, hP⟩ := hA.1.split
  have hsub : allP B ν.Q ⊆ P := Finset.union_subset hPg hQP
  have hdeP : B.de.Q ⊆ P := fun x hx => hQP (Finset.mem_union_left _ hx)
  have hνP : ν.Q ⊆ P := fun x hx => hQP (Finset.mem_union_right _ hx)
  have hη : UnramEverywhere D B.eta := hB.eta.2.1
  have key : ∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) := by
    intro PP hPP
    have hPPP := hsub hPP
    have hνr := resAt_twist hν hP hνP hPPP
    by_cases hg : PP ∈ B.G.Pg
    · have hde : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hA.1.disj hg (Finset.mem_union_left _ h)
      have hdl : B.de.locC PP = 1 := by simp only [Twist.locC, if_neg hde]
      rw [resP, if_pos hg, hdl, mul_one]
      exact ResAt.mul (resAt_of_isResAt (hB.tame PP hg)) hνr
    · rw [resP, if_neg hg]
      exact ResAt.mul (ResAt.mul (resAt_of_unram hB.unram hP hPg hPPP hg) (resAt_twist hB.de hP hdeP hPPP)) hνr
  have u1 : UnrOff (B.mu * ν.chi) (allP B ν.Q) :=
    UnrOff.mul (UnrOff.mul (unrOff_of_unram hB.unram (hP.mono hPg) (by intro x hx; simp [allP, hx]))
      (unrOff_of_unram hB.de.unram hB.de.split (by intro x hx; simp [allP, hx])))
      (unrOff_of_unram hν.unram hν.split (by intro x hx; simp [allP, hx]))
  refine ⟨fun PP hPP => ⟨key PP hPP, ?_⟩, u1, u1.mul (unrOff_of_unramEverywhere hη _).inv⟩
  have := (key PP hPP).mul (resAt_of_unramEverywhere hη PP).inv
  rwa [inv_one, mul_one] at this

end GlobalTheory.ExportSeries.TupleChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelic
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

open GlobalTheory.IdemSupport

theorem idempotentFlip_mul_conjFlip_eq_one {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0)
    (hxy : x * y = 1) : (e * x + c * y + (1 - e - c)) * (c * x + e * y + (1 - c - e)) = 1 := by
  linear_combination (x*y - x - y + 1) * he + (x*y - x - y + 1) * hc + (x^2 + y^2 - 2*x - 2*y + 2) * hec + (e + c) * hxy

theorem complementIdempotent_mul_idempotentFlip {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0) :
    (1 - (e + c)) * (e * x + c * y + (1 - e - c)) = 1 - (e + c) := by
  linear_combination (1 - x) * he + (1 - y) * hc + (2 - x - y) * hec

theorem orthogonal_mul_idempotentFlip_sub_one_eq_zero {R : Type} [CommRing R] {e x y c f : R} (h1 : f * e = 0) (h2 : f * c = 0) :
    f * (e * x + c * y + (1 - e - c) - 1) = 0 := by
  linear_combination (x - 1) * h1 + (y - 1) * h2

theorem natCast_mul_incA_inv {D : D7} {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hm), map_one]

theorem cA_incA_natCast_inv {D : D7} (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [cA_incA, star_inv₀, star_natCast]

theorem cA_flipElt {D : D7} (e : AE D) (m : ℕ) :
    cA D (flipElt e m) = cA D e * (m : AE D) + e * incA D ((m : D.host.E)⁻¹) + (1 - cA D e - e) := by
  unfold flipElt
  rw [map_add, map_add, map_mul, map_mul, map_sub, map_sub, map_one, map_natCast, cA_incA_natCast_inv, cA_cA]

theorem flipElt_mul_cA {D : D7} {e : AE D} (he : e * e = e) (hec : e * cA D e = 0) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * cA D (flipElt e m) = 1 := by
  rw [cA_flipElt]
  exact idempotentFlip_mul_conjFlip_eq_one he (by rw [← map_mul, he]) hec (natCast_mul_incA_inv hm)

theorem flipElt_sub_one_mul {D : D7} {e f : AE D} (m : ℕ) (h1 : f * e = 0) (h2 : f * cA D e = 0) :
    f * (flipElt e m - 1) = 0 := by
  unfold flipElt
  exact orthogonal_mul_idempotentFlip_sub_one_eq_zero h1 h2

def scalGL {R : Type} [CommRing R] (n : ℕ) (a b : R) (h : a * b = 1) : GL (Fin n) R :=
  ⟨a • (1 : Matrix (Fin n) (Fin n) R), b • (1 : Matrix (Fin n) (Fin n) R),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, mul_comm, h, one_smul]⟩

theorem cT_scalar {R : Type} [CommRing R] (σ : R →+* R) (n : ℕ) (a : R) :
    Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) = σ a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp only [if_true, mul_one]
  · simp only [if_neg (Ne.symm hij), if_neg hij, mul_zero, map_zero]

theorem scalGL_mem_UJ {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : R)
    (h : a * b = 1) (hb : σ a = b) : scalGL n a b h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) * J * (a • (1 : Matrix (Fin n) (Fin n) R)) = J
  rw [cT_scalar, hb, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

def scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) : GA D V :=
  ⟨scalGL V.rank a (cA D a) ha, scalGL_mem_UJ _ _ a (cA D a) ha rfl⟩

theorem mt_scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a ha) = a • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

theorem scalar_sub_one_entry {R : Type} [CommRing R] {n : ℕ} {f a : R} (h : f * (a - 1) = 0) (i j : Fin n) :
    f * (a • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, mul_one]; exact h
  · rw [if_neg hij, mul_zero, sub_zero, mul_zero]

theorem oneAt_scalU {D : D7} (V : HSp D) {a : AE D} (ha : a * cA D a = 1) (l : ℕ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → algebraMap (AF D.host.F) (AE D) ε * (a - 1) = 0) :
    OneAt V l (scalU V a ha) := by
  intro v ε hε hlv i j
  rw [mt_scalU]
  exact scalar_sub_one_entry (h v ε hε hlv) i j

theorem flip_central_exists : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V T m eT hT hm
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have he : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT hT subset_rfl
  have hec : eT * cA D eT = 0 := hT.2
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, he]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  have hinv := flipElt_mul_cA he hec hm
  refine ⟨scalU V _ hinv, ?_, ?_, mt_scalU V _ hinv⟩
  · have hinf : infPart D eT = 0 := by
      rw [hsum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (delta_of_isIdemAt hΦ (hes PP hPP)).1
    refine mem_GfC_of_suppF V (f := eT + cA D eT) ?_ ((suppF_iff V _ _).2 ?_)
    · rw [map_add, hinf, (parts_cA eT).1, hinf, map_zero, add_zero]
    · rw [mt_scalU, smul_smul]
      unfold flipElt
      rw [complementIdempotent_mul_idempotentFlip he hcc hec]
  · intro l hl
    refine oneAt_scalU V hinv l fun v ε hε hlv => ?_
    have h0 : algebraMap (AF D.host.F) (AE D) ε * eT = 0 := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      have hd := delta_of_isIdemAt hΦ (hes PP hPP)
      refine hΦ.ext' (by rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = PP
      · subst hQ
        by_cases hQv : Q.under (𝓞 D.host.F) = v
        · exfalso
          apply hl Q hPP
          have h1 := hlv
          rw [← hQv] at h1
          change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal at h1
          rwa [map_natCast] at h1
        · rw [(place_comp hΦ hε).2.2 Q hQv, zero_mul]
      · rw [hd.2.2 Q hQ, mul_zero]
    have h0' : algebraMap (AF D.host.F) (AE D) ε * cA D eT = 0 := by
      rw [← cA_algebraMap ε, ← map_mul, h0, map_zero]
    exact flipElt_sub_one_mul m h0 h0'

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldCurve
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.DeepCoeff

open GlobalTheory.WeierstrassCurve GlobalTheory.UnifCoord GlobalTheory.PeriodicWeierstrass PeriodPair GlobalTheory.CompRat.Weber GlobalTheory.FieldSize GlobalTheory.WeberFixed

def preimageField (τ : ℂ ≃+* ℂ) (K : IntermediateField ℚ ℂ) : IntermediateField ℚ ℂ :=
  K.comap ((τ : ℂ →+* ℂ).toRatAlgHom)

theorem exists_coeff_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l l₂ : Level H) (c : Coeff l) (n p : ℕ), p.Prime → ¬ p ∣ n → Nat.Coprime l.M n → l₂.M = l.M * n → l₂.A = 1 → l.GoodAt p → CurveOver H c.F l.M → ∃ c' : Coeff l₂, c.F ≤ c'.F ∧ CurveOver H c'.F l₂.M ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → (∀ x ∈ c'.F, τ x ∈ c'.F) ∧ ∀ A : ValuationSubring ℂ, (p : ℂ) ∈ A.nonunits → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → ∀ x ∈ c'.F, τ x = x := by
  intro E _ _ _ H l l₂ c n p hp hpn hco hM hA hgood hcurve
  obtain ⟨L, hL⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H
  have h3 := l₂.three_le
  have hN : 0 < l₂.M := by omega
  have hN0 : (l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨hfin, halg, hperm⟩ := weberSet_finite_algebraic_permuted L l₂.M hN (g₂_ne_zero H L hL) (g₃_ne_zero H L hL)
  have hζ : IsPrimitiveRoot (zeta l₂.M) l₂.M := Complex.isPrimitiveRoot_exp _ hN.ne'
  let S : Set ℂ := insert (zeta l₂.M) (weberSet L l₂.M)
  have := (hfin.insert (zeta l₂.M)).to_subtype
  have hS : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro x (rfl | hx)
    · exact (hζ.isIntegral hN).tower_top
    · exact (halg (GlobalTheory.WeberField.invariant_isAlgebraic H L hL) x hx).isIntegral
  have := c.fin
  let F := c.F ⊔ IntermediateField.adjoin ℚ S
  have hl : c.F ≤ F := le_sup_left
  have hr : ∀ x ∈ S, x ∈ F := fun x hx => le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ S hx)
  have hrt : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hle : ∀ K : IntermediateField ℚ ℂ, c.F ≤ K → S ⊆ K → F ≤ K := fun K h₁ h₂ =>
    sup_le h₁ (IntermediateField.adjoin_le_iff.2 h₂)
  refine ⟨⟨F, inferInstance, fun τ a => hl (c.conj τ a), ?_, ?_⟩, hl, fun τ hτ => ?_, fun τ hτ => ⟨?_, ?_⟩⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
    exact hr _ (.inl rfl)
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact hl hrt
    · rw [hA, show zeta 1 = 1 by simp [zeta]]
      exact one_mem F
  · exact fixesCurve_of_weber E H L _ hN hL τ (hτ _ (hl hrt)) (hτ _ (hr _ (.inr (.inl rfl))))
      fun s hs => hτ _ (hr _ (.inr (.inr ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)))
  · have hj := weber_fixed H L hL (hcurve τ hτ) _ (.inl rfl)
    refine hle (preimageField τ F) (fun x hx => ?_) ?_
    · show τ x ∈ F
      rw [hτ x hx]
      exact hl hx
    rintro x (rfl | rfl | ⟨z, hz, hz', rfl⟩)
    · show τ (zeta l₂.M) ∈ F
      have : NeZero l₂.M := ⟨hN.ne'⟩
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (zeta l₂.M)) (by rw [← map_pow, hζ.pow_eq_one, map_one])
      rw [← hk]
      exact pow_mem (hr _ (.inl rfl)) _
    · show τ _ ∈ F
      rw [hj]
      exact hr _ (.inr (.inl rfl))
    · show τ _ ∈ F
      obtain ⟨t, h₁, h₂, h₃⟩ := hperm τ hj (z / l₂.M) (by rwa [mul_div_cancel₀ _ hN0]) hz'
      rw [h₃]
      have e : l₂.M * t / l₂.M = t := mul_div_cancel_left₀ _ hN0
      exact hr _ (.inr (.inr ⟨_, h₁, by rwa [e], by rw [e]⟩))
  · intro A hpA hin
    have hfix : FixesCurve H τ l₂.M := hM ▸ GlobalTheory.T.fixesCurve_mul_coprime E H l.M n p A τ hp hpA hpn hco hgood (hcurve τ hτ) hin
    let K : IntermediateField ℚ ℂ :=
      ((τ : ℂ →+* ℂ).eqLocusField (RingHom.id ℂ)).toIntermediateField fun q => by
        show τ (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q
        simp
    refine hle K hτ ?_
    rintro x (rfl | hx)
    · exact zeta_fixed H (by omega) hfix
    · exact weber_fixed H L hL hfix x hx

end GlobalTheory.DeepCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorComponentsOfAdelicInvariantFunction
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompFactor

set_option maxHeartbeats 1000000 in

theorem exists_factor_comp : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∃ v : U.Comp → c.F, ∀ h : GA D V, w h = v (dict h).1 := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio _ _ _ hW hD _ w _ h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h h', ik (dict h).1 = ik (dict h').1 → w h = w h' := by
    intro h h' hi
    obtain ⟨γ, hγ, hΛ, hm, -⟩ := hD.2 h
    obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
    have hξ : -(-D.host.xi0) ≠ 0 := by
      rw [← (hW (dict h).1).2]
      exact neg_ne_zero.2 (U.X _).ξ0_ne
    obtain ⟨δ, hδ, u, hu, hc, eu⟩ := GlobalTheory.CompRead.exists_rat_finCong_of_index F V io hio.emb _ _ hi _ _ _ _
      (SetLike.ext' (hΛ.trans (Set.image_id _))) (SetLike.ext' (hΛ'.trans (Set.image_id _))) (φ _) (φ _) _ hξ
      (htr _) (htr _) hm hm'
    rw [← h2 γ' hγ' h', eu, h3 u hu hc, h2 δ hδ, h2 γ hγ]
  have hv : ∀ k : U.Comp, ∃ a : c.F, ∀ h, (dict h).1 = k → w h = a := by
    intro k
    by_cases hex : ∃ h, (dict h).1 = k
    · obtain ⟨h, hi⟩ := hex
      exact ⟨w h, fun h' hi' => key h' h (congrArg ik (hi'.trans hi.symm))⟩
    · exact ⟨0, fun h hi => absurd ⟨h, hi⟩ hex⟩
  choose v hv using hv
  exact ⟨v, fun h => hv _ h rfl⟩

end GlobalTheory.CompFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumberStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_element_local_components_level_number : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  first | exact @GlobalTheory.LevelFieldApprox.exists_approx | exact GlobalTheory.LevelFieldApprox.exists_approx | (intros; apply GlobalTheory.LevelFieldApprox.exists_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlipStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P → (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  first | exact @GlobalTheory.IdemFlip.idemSum_sub_and_flip | exact GlobalTheory.IdemFlip.idemSum_sub_and_flip | (intros; apply GlobalTheory.IdemFlip.idemSum_sub_and_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJointHarmonicOfLoweringStableSubmoduleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHarmonic_of_lowering_stable_submodule : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  first | exact @GlobalTheory.LowerHarm.lower_to_harmonic | exact GlobalTheory.LowerHarm.lower_to_harmonic | (intros; apply GlobalTheory.LowerHarm.lower_to_harmonic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  first | exact @GlobalTheory.exists_nHw_of_fockS_stable | exact GlobalTheory.exists_nHw_of_fockS_stable | (intros; apply GlobalTheory.exists_nHw_of_fockS_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChangeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  first | exact @GlobalTheory.HeckeBorelChange.hkRelFr_frBor | exact GlobalTheory.HeckeBorelChange.hkRelFr_frBor | (intros; apply GlobalTheory.HeckeBorelChange.hkRelFr_frBor <;> assumption)
end

