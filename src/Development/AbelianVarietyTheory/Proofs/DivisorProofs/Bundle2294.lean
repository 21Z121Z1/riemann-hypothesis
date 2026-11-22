import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogShortThetaSeriesDenominatorBoundLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovIntNum

section Size

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sum_abs_laOf (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H) :
    ∑ k, |((laOf Dw a n τ k : ℤ) : ℝ)| =
      ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) +
        ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin Dw.p, |((laOf Dw a n τ (Fin.castAdd Dw.q i) : ℤ) : ℝ)| = (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_pos hi, Fin.val_castAdd]
    simp only [Int.cast_add, Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  have h2 : ∀ i : Fin Dw.q, |((laOf Dw a n τ (Fin.natAdd Dw.p i) : ℤ) : ℝ)| =
      (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ¬ ((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    have hidx : Dw.q - 1 - (((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) - Dw.p) = (Fin.rev i : ℕ) := by
      simp only [Fin.val_natAdd, Fin.val_rev]; omega
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_neg hi, hidx]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast]
    have h3 : (0 : ℝ) ≤ (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : (∑ i : Fin Dw.q, (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)) = ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ) :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hr]
  push_cast
  ring

theorem DF_eq_sum (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) :
    (DF Dw a : ℝ) = ∑ τ : Psi H, ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) := by
  classical
  let P : (E →+* ℂ) → Prop := fun τ => τ (H.rt : E) = H.rt0
  have h := Fintype.sum_subtype_add_sum_subtype P (fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ))
  beta_reduce at h
  have e1 : (∑ τ : {τ // P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ) := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Datum.mult, if_pos τ.2]
  let e : {τ : E →+* ℂ // ¬ P τ} ≃ {τ // P τ} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun σ => ⟨conjEmb σ.1, GlobalTheory.AllWt.conj_not_mem (H := H) σ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun σ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have e2 : (∑ τ : {τ // ¬ P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    show _ = ∑ i : Fin Dw.q, (a (conjEmb (conjEmb τ.1), i) : ℝ)
    rw [GlobalTheory.AllWt.conjEmb_conjEmb, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_neg τ.2]
  unfold DF
  push_cast
  calc (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = _ := h.symm
    _ = (∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) +
          ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
        convert congrArg₂ (· + ·) e1 e2 using 2 <;> first | rfl | exact Finset.sum_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl | congr 1
    _ = _ := by
        rw [← Finset.sum_add_distrib]

theorem sizeK_eq (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    sizeK Dw a n = (DF Dw a : ℝ) + (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  unfold sizeK
  simp only [sum_abs_laOf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [DF_eq_sum, Finset.sum_add_distrib]
  ring

end Size

end GlobalTheory.CovIntNum

namespace GlobalTheory.CovIntNum

theorem intZ_log_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n →
    0 < intZ D (T.Q.Dw j) Y.d.l₂ n a ∧
    Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n := by
  refine ⟨67, by norm_num, ?_⟩
  intro D T j Y e o Lb a n h
  obtain ⟨-, -, -, -, -, -, hLb, hM, hsz, -, -, -, hn, -, -, -⟩ := h
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := D.host.hyp
  have hM3 : 3 ≤ Y.d.l₂.M := Y.d.l₂.three_le
  have hZ : (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      (Y.d.l₂.M : ℝ) ^ (Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a) *
        ((NumberField.discr D.host.E).natAbs : ℝ) ^ DF (T.Q.Dw j) a := by
    rw [intZ_eq]
    push_cast [-Nat.cast_natAbs]
    ring
  have hD1 : (1 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have hlD : Real.log ((NumberField.discr D.host.E).natAbs : ℝ) ≤ D.R.f * (7 * Lb) := by
    have h1 := log_discr_natAbs_le D.host.E
    have h2 : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
    have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    rw [h2] at h1
    nlinarith
  have hMpos : (0 : ℝ) < Y.d.l₂.M := by exact_mod_cast (by omega : 0 < Y.d.l₂.M)
  have hq0 : (0 : ℝ) < D.host.q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast hdp.pos
  have hZpos : (0 : ℝ) < (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) := by rw [hZ]; positivity
  refine ⟨by exact_mod_cast hZpos, ?_⟩
  have hlogZ : Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      ((Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a : ℕ) : ℝ) *
          Real.log Y.d.l₂.M +
        (DF (T.Q.Dw j) a : ℝ) * Real.log ((NumberField.discr D.host.E).natAbs : ℝ) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [hlogZ]

  have hSe := sizeK_eq (T.Q.Dw j) a n
  have hcard : Fintype.card (Psi T.Q.H) = Module.finrank ℚ D.host.E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.LamF.card_psiSet T.Q.H
  rw [hcard] at hSe
  have hlD0 := Real.log_nonneg hD1
  generalize Real.log ((NumberField.discr D.host.E).natAbs : ℝ) = lD at hlD hlD0 ⊢
  obtain ⟨t, rfl⟩ := hn
  have ht : (t + t) / 2 = t := by omega
  rw [ht] at hSe
  generalize Module.finrank ℚ D.host.E / 2 = m at hSe ⊢
  generalize sizeK (T.Q.Dw j) a (t + t) = S at hSe ⊢
  generalize DF (T.Q.Dw j) a = dF at hSe ⊢
  push_cast at hSe ⊢

  have hf : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hlM0 : 0 ≤ Real.log Y.d.l₂.M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y.d.l₂.M))
  have hdF0 : (0 : ℝ) ≤ dF := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * t := by positivity
  have hS0 : 0 ≤ S := by rw [hSe]; positivity
  have hX : (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF ≤ 2 * S := by rw [hSe]; linarith
  have hdFS : (dF : ℝ) ≤ S := by rw [hSe]; linarith
  have h1 : ((m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF) * Real.log Y.d.l₂.M ≤
      (2 * S) * (30 * Lb) := mul_le_mul hX hM hlM0 (by linarith)
  have h2 : (dF : ℝ) * lD ≤ (D.R.f * S) * (7 * Lb) :=
    (mul_le_mul hdFS hlD hlD0 hS0).trans (le_of_eq (by ring))
  have hLS : 0 ≤ Lb * S := mul_nonneg (by linarith) hS0
  have hA : Lb * S ≤ D.R.f * (Lb * S) := le_mul_of_one_le_left hLS hf1
  have h3 : (2 * S) * (30 * Lb) + (D.R.f * S) * (7 * Lb) ≤ 67 * ((D.R.f : ℝ) * Lb) * S := by linarith
  have hx1 : (1 : ℝ) ≤ D.R.f * D.R.r * Lb :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hLb
  have h5 : (D.R.f : ℝ) * Lb ≤ D.R.f * D.R.r * Lb :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr1) (by linarith)
  have h4 : (D.R.f : ℝ) * Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := h5.trans (le_self_pow₀ hx1 (by norm_num))
  have h6 : 67 * ((D.R.f : ℝ) * Lb) * S ≤ 67 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * S :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  linarith

end GlobalTheory.CovIntNum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

theorem rp_eq_one (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (k : GA D V) (hk : k ∈ GfC V) : rp k = 1 := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  have h1 : infMat D.sp.cm.sig V.gram (θ ρ) k = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hk)
    show (Units.val (infHom V k)).map (θ ρ) = 1
    rw [h2]
    simp
  rw [hrp, h1, Pi.one_apply, GlobalTheory.Mem.VolExists.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem rp_realElt (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (b : ∀ ρ, Upq V ρ) :
    rp (realElt θ V fun ρ => realMat V A ρ (b ρ)) = b := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D ρ))).2.2 (A ρ) (hA ρ)
  have e : UpqT.mat (b ρ) * A ρ = A ρ * (C * (UpqT.mat (b ρ) * A ρ)) := by
    rw [← Matrix.mul_assoc (A ρ), h1, Matrix.one_mul]
  rw [hrp, GlobalTheory.RealBoxMeasure.infMat_realElt θ hθ V _ (fun τ => GlobalTheory.RealBoxMeasure.realMat_mem V hV A hA τ _) ρ,
    GlobalTheory.RealBoxMeasure.realMat_of V A hA ρ _ _ e, ← e]

theorem exists_fin (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (h : GA D V) :
    ∃ k : GA D V, rp k = 1 ∧ finE V k = finE V h := by
  refine ⟨(realElt θ V fun ρ => realMat V A ρ (rp h ρ))⁻¹ * h, ?_, ?_⟩
  · rw [map_mul, map_inv, rp_realElt V θ A rp hV hθ hA hrp, inv_mul_cancel]
  · rw [map_mul, map_inv, GlobalTheory.RealBoxMeasure.finE_realElt, inv_one, one_mul]

theorem meas_level (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ))
    (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ)) (hc : Continuous rp)
    (hrp : IsRealPart V θ A rp) (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  have hBm : MeasurableSet (rp ⁻¹' B) := hc.measurable hB
  have H := GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ V hV K μ hμ A hA m hm
    ((rp ⁻¹' B).indicator 1) (measurable_one.indicator hBm) (fun g k hk => by
      have : rp (g * k) = rp g := by rw [map_mul, rp_eq_one V θ A rp hV hA hrp k hk.1, mul_one]
      exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, this, Set.mem_preimage]) rfl) hK.measurableSet
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at H
  rw [← lintegral_indicator_one hB, show {h | finE V h ∈ K ∧ rp h ∈ B} = rp ⁻¹' B ∩ {h : GA D V | finE V h ∈ K} from
    Set.ext fun h => and_comm, H]
  refine lintegral_congr fun b => ?_
  exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, rp_realElt V θ A rp hV hθ hA hrp]) rfl

theorem meas_translate_le : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  intro D V θ A m rp K K₀ μ hV hθ hA hm hc hrp _ hi hK hμ g _ B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let S : (K₀ ⧸ K.subgroupOf K₀) → Set (GA D V) := fun q =>
    {h | (∃ hh : finE V (g⁻¹ * h) ∈ K₀, (QuotientGroup.mk ⟨_, hh⟩ : K₀ ⧸ K.subgroupOf K₀) = q) ∧ rp h ∈ B}
  have hS : ∀ q, μ (S q) ≤ Measure.pi m B := by
    intro q
    rcases (S q).eq_empty_or_nonempty with h0 | ⟨h₀, ⟨hh₀, hq₀⟩, -⟩
    · rw [h0, measure_empty]; exact zero_le
    obtain ⟨k, hk1, hk2⟩ := exists_fin V θ A rp hV hθ hA hrp h₀
    rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB, ← measure_preimage_mul μ k⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
    refine measure_mono ?_
    rintro h ⟨⟨hh, hq⟩, hb⟩
    have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hq₀.trans hq.symm))
    show finE V (k⁻¹ * h) ∈ K ∧ rp (k⁻¹ * h) ∈ B
    refine ⟨?_, ?_⟩
    · have h2 : finE V (k⁻¹ * h) = (finE V (g⁻¹ * h₀))⁻¹ * finE V (g⁻¹ * h) := by
        simp only [map_mul, map_inv, hk2]; group
      rw [h2]; exact h1
    · rwa [map_mul, map_inv, hk1, inv_one, one_mul]
  calc μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ μ (⋃ q, S q) :=
        measure_mono fun h hh => Set.mem_iUnion.2 ⟨_, ⟨hh.1, rfl⟩, hh.2⟩
    _ ≤ ∑ q, μ (S q) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _q : K₀ ⧸ K.subgroupOf K₀, Measure.pi m B := Finset.sum_le_sum fun q _ => hS q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end GlobalTheory.CovTop.VolBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanRed

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem redE_dualMap (e : ℕ) :
    redE (R ⧸ I ^ (e + 1)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) = thick R I e ≫ redE R := by
  show spMap _ ≫ spMap _ = Spec.map _ ≫ spMap _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem red_lift_eq_eSec (y : epsR R ⟶ G) (hy : IsTangent y) (e : ℕ)
    (ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (h1 : ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) :
    redE (R ⧸ I ^ (e + 1)) ≫ ye = eSec (thickObj R I e G) := by
  rw [← cancel_mono (fstG I e G).left, Category.assoc, h1, ← Category.assoc, redE_dualMap, Category.assoc]
  have hy' : redE R ≫ y.left = η[G].left := hy
  rw [hy']
  exact (UnitValue.eSec_fGl (G := G) e).symm

theorem levels_of_tanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) (gm : GtPt D.toPre (epsR R))
    (h : TanRel U y gm) (e : ℕ) :
    eSec (thickObj R I e G) ≫ (U.gt e).pG.left = (thick R I e ≫ redE R) ≫ gm.b.left ∧
    ∀ χ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) C, Good D.toPre.P.L z C →
      val ((U.gt e).t χ) (eSec (thickObj R I e G)) z C = val (gm.s χ) (thick R I e ≫ redE R) z C := by
  obtain ⟨ye, h1, h2, h3⟩ := h e
  have hr := red_lift_eq_eSec y hy e ye h1
  refine ⟨?_, fun χ z C hC => ?_⟩
  · rw [← hr, Category.assoc, h2, ← Category.assoc, redE_dualMap]
  · rw [← hr, ← redE_dualMap]
    exact (val_pull hC _ _ _).symm.trans ((val_corr hC (h3 χ) _).trans (val_pull hC _ _ _))

theorem gtTan_of_tanRel [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (U : UnifPre I D A G)
    (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) (hy : IsTangent y) (h : TanRel U y gm) : GtTan gm := by
  have hL := D.toPre.P.isLB
  have hz := levels_of_tanRel U y hy gm h
  have hb : redE R ≫ gm.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
  have hob : o.b.left = redE R ≫ gm.b.left := by
    rw [hb, ho.1]
    exact (congrArg (· ≫ η[D.toPre.P.A].left)
      ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
  have e₁ := TorusCoord.comp_eq_of_left gm.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
  refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
    (DVR.pullGen_isGen _ _ _ _ (gm.isGen χ) _) fun e z J hJ => ?_⟩
  · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
  · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine Eq.trans ?_ ((hz e).2 χ z J hJ)
    have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
    rw [val_pull hJ, Category.id_comp] at this
    exact this.symm

theorem main : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)),
    IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U y gm₀ hy h => gtTan_of_tanRel U.toUnifPre y gm₀ hy h

end GlobalTheory.MBLow.TanRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  first | exact @GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | exact GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | (intros; apply GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
section
noncomputable section

section Family

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg GlobalTheory.KeyFourth
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyCover

set_option maxHeartbeats 1000000 in

theorem nonempty_keySec_of_family (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (hpq : 1 ≤ Dw.p + Dw.q) (hF : FnAlgClosed Xo c) : Nonempty (KeySec Xo c) := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_chart_units k₁ k₂ k₄ e hpq h
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyCover

end Family

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.KeyCover

end GlobalTheory.KeyCover
end
end

