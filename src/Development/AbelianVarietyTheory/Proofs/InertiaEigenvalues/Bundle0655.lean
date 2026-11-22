import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfExistsMulEqPowSmulOfModLPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfInvLim

theorem dvd_mul_entry {R : Type} [CommRing R] {d : ℕ} (c : R) (A B : Matrix (Fin d) (Fin d) R)
    (h : ∀ i j, c ∣ B i j) (i j : Fin d) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem exists_mul_eq_smul_one : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣
      (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) →
    ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ d M τ Y hY hQ
  have hinj : Function.Injective (inclW l) :=
    WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  set A := Y.map (inclW l) with hA
  set c := inclW l τ ^ M with hc
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  set Z := c • A⁻¹ with hZ
  have hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a) := by
    intro i j
    refine GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_
    obtain ⟨Q, hQn⟩ := hQ n
    have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j
    have h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) =
        Q.map (inclW l) - Z := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [h2] at h1
    refine ⟨Q i j, ?_⟩
    rw [pow_zero, one_mul, one_mul, dvd_sub_comm]
    simpa [Matrix.sub_apply] using h1
  choose Y' hY' using hZent
  refine ⟨Matrix.of fun i j => Y' i j, ?_⟩
  have hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z := by
    ext i j; simp [hY' i j]
  have key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) =
      (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l) := by
    rw [Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]
    ext i j
    simp [Matrix.one_apply, hc, Matrix.smul_apply]
    split_ifs <;> simp
  refine Matrix.ext fun i j => hinj ?_
  exact congrFun (congrFun (congrArg Matrix.of.symm key) i) j

end GlobalTheory.AinfInvLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfRightInverseUpToPowModLPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfRinv

theorem rinv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  intro l _ d d' n M τ Y Y' A Q hτ hY hYY' hdiv
  set f : Ainf l →+* WCb l := inclW l with hf
  let I : Ideal (WCb l) := Ideal.span {((l : WCb l)) ^ n}
  let π : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  let fW := (f.mapMatrix : Matrix (Fin d) (Fin d) (Ainf l) →+* Matrix (Fin d) (Fin d) (WCb l))
  let πM := (π.mapMatrix : Matrix (Fin d) (Fin d) (WCb l) →+* Matrix (Fin d) (Fin d) (WCb l ⧸ I))
  have hsm : ∀ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : R),
      (φ.mapMatrix : Matrix (Fin d) (Fin d) R →+* Matrix (Fin d) (Fin d) S) (c • 1) = φ c • 1 := by
    intro R S _ _ φ c; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  set t : WCb l := f τ ^ M with ht
  have hfτ : fW (τ ^ M • 1) = t • 1 := by rw [hsm, map_pow]

  have h1 : fW Y * fW Y' = t • 1 := by rw [← map_mul, hYY', hfτ]
  obtain ⟨u, hu⟩ := hY
  have hYw : fW Y = (u : Matrix (Fin d) (Fin d) (WCb l)) := hu.symm
  have h2 : fW Y' * fW Y = t • 1 := by
    have e : fW Y' = (↑u⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) * (fW Y * fW Y') := by
      rw [← Matrix.mul_assoc, hYw, Units.inv_mul, Matrix.one_mul]
    rw [e, h1, hYw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  set s : WCb l ⧸ I := π t with hs
  have hsu : IsUnit s := (hτ.pow M).map π
  have hmod : πM (fW Y * fW (A * Q) - t • 1) = 0 := by
    ext i j
    simp only [πM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hdiv i j))
  rw [map_sub, map_mul, hsm] at hmod
  have hYZ := sub_eq_zero.mp hmod
  have h2b : πM (fW Y') * πM (fW Y) = s • 1 := by rw [← map_mul, h2, hsm]
  have hZ : πM (fW (A * Q)) = πM (fW Y') := by
    have : s • πM (fW (A * Q)) = s • πM (fW Y') := by
      calc s • πM (fW (A * Q)) = (πM (fW Y') * πM (fW Y)) * πM (fW (A * Q)) := by
              rw [h2b, Matrix.smul_mul, Matrix.one_mul]
        _ = πM (fW Y') * (s • 1) := by rw [Matrix.mul_assoc, hYZ]
        _ = s • πM (fW Y') := by rw [Matrix.mul_smul, Matrix.mul_one]
    exact (hsu.smul_left_cancel).mp this
  have hfin : πM (fW (A * (Q * Y) - τ ^ M • 1)) = 0 := by
    rw [← Matrix.mul_assoc, map_sub, map_sub, map_mul, map_mul, hZ, h2b, hfτ, hsm, sub_self]
  intro i j
  have hij : π (f ((A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j)) = 0 := by
    have := congrFun (congrFun hfin i) j
    simpa [πM, fW, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hij)
  obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) n w (fun _ => ⟨(A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j, by rw [one_mul, ← hw, sub_self]; exact dvd_zero _⟩)
  refine ⟨a, GlobalTheory.Prism.inclW_injective ?_⟩
  rw [one_mul] at ha
  rw [map_mul, map_pow, map_natCast, ← ha]
  exact hw

end GlobalTheory.AinfRinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientConditionsAtGood
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubGood

theorem ambAll_goodPoints : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambBlock (D := D) i (X.r i) (X.ρ i) π := by
  intro hF D L X hG hJa hJc hX i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg2 := GlobalTheory.T.admG2_of_decomposition hF D L hG hJa hJc i (X.r i) (X.ρ i) π (hX.good i) h0 h1 hZ hd
  have hWT := GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp D i (X.r i) (X.ρ i) π (X.dc i) hg2 hd
  exact ⟨hWT.2, hWT.1, GlobalTheory.T.ambientFiltration_every_declaration D i (X.r i) (X.ρ i) π (X.dc i), GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i (X.r i) (X.ρ i) π hd⟩

end GlobalTheory.HubGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatingLatticesTransitionMatrixModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.TransLim

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR
  have key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S,
      (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T := fun n =>
    GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val)
      (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)
  choose Y hY using key
  refine ⟨Y, fun n => ?_⟩
  let π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n} := Ideal.Quotient.mk _
  have hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)),
      (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π := by
    intro a b M M'
    constructor
    · intro h
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)
    · intro h i j
      rw [Matrix.sub_apply]
      refine (Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
  have hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]; exact (hz _ _).1 (hR n)
  have hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)
  have hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hY n]
  have hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π := by
    rw [← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    have h1 := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)
    simp only [map_pow, map_natCast] at h1
    convert h1 using 1
    simp [zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]
  obtain ⟨u, hu⟩ := hT0
  have hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1 := by
    rw [← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]
  have hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]
  have hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π := by
    have := congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE
    simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
  rw [← Matrix.map_mul] at hF
  exact (hz _ _).2 hF

end GlobalTheory.BKLim.TransLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem
section
open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

theorem Stable.scale_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {c : k} (hc : c ≠ 0)
    (α β γ : ℂ) (a r b s : k)
    (h : α • (fun _ => (1 : ℂ)) + β • ballFn a r + γ • ballFn b s ∈ S) :
    α • (fun _ => (1 : ℂ)) + β • ballFn (c * a) (c * r) + γ • ballFn (c * b) (c * s) ∈ S := by
  have hv : 0 < valuation k c := zero_lt_iff.2 (by simpa using hc)
  have key : ∀ a r x : k, ballFn (c * a) (c * r) x = ballFn a r ((c⁻¹ * x + 0 : k) : OnePoint k) := by
    intro a r x
    have h1 : x - c * a = c * (c⁻¹ * x + 0 - a) := by field_simp; ring
    rw [ballFn_coe, ballFn_coe, h1, map_mul, map_mul]
    congr 1
    rw [mul_le_mul_iff_right₀ hv]
  refine hS.1 _ h c⁻¹ 0 (inv_ne_zero hc) _ (by simp) fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, key]

theorem ballFn_eq_ballFn_zero {a r : k} (h : valuation k a ≤ valuation k r) : ballFn a r = ballFn 0 r := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    rw [ballFn_coe, ballFn_coe, sub_zero]
    congr 1
    refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_sub_le hx h⟩
    have := (valuation k).map_add_le hx h
    rwa [sub_add_cancel] at this

theorem ballFn_congr_radius (a : k) {r s : k} (h : valuation k r = valuation k s) : ballFn a r = ballFn a s := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rw [ballFn_coe, ballFn_coe, h]

theorem Stable.ballFn_mem_and_one_mem_of_sub_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (ϖ : k)
    (hϖ : valuation k ϖ = uniformizer k) (h : ballFn 0 ϖ - ballFn 1 ϖ ∈ S) :
    ballFn (0 : k) 1 ∈ S ∧ (fun _ => (1 : ℂ)) ∈ S := by
  classical
  have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
  have hle : ∀ x : k, valuation k x ≤ valuation k ϖ ↔ valuation k x < 1 := fun x => by
    rw [hϖ]; exact le_uniformizer_iff
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (hϖ.symm.trans (map_zero _))
  have hdiff : ∀ a : k, valuation k a ≤ 1 → ballFn 0 ϖ - ballFn a ϖ ∈ S := by
    intro a ha
    rcases ha.lt_or_eq with ha | ha
    · rw [ballFn_eq_ballFn_zero ((hle a).2 ha), sub_self]
      exact S.zero_mem
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have h1 := hS.scale_mem ha0 0 1 (-1) 0 ϖ 1 ϖ (by simpa [sub_eq_add_neg] using h)
      have h2 : valuation k (a * ϖ) = valuation k ϖ := by rw [map_mul, ha, one_mul]
      rw [ballFn_congr_radius _ h2, ballFn_congr_radius _ h2] at h1
      simpa [sub_eq_add_neg] using h1
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_eq_sum_ballFn (r := ϖ) (R := 1) h0 (by simpa using hlt.le)
  simp only [map_one] at hT1 hT2 hT3
  set q : ℂ := (T.card : ℂ) with hqdef
  have hsum : ballFn (0 : k) 1 = ∑ a ∈ T, ballFn a ϖ := by
    rw [hT3 (ballFn 0 1) rfl (fun x hx => by rw [ballFn_coe, if_neg (by simpa using hx)]) (fun x b hb => ?_)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [ballFn_coe, if_pos (by simpa using hT1 a ha), one_smul]
    · have hb1 : valuation k b ≤ 1 := hb.trans hlt.le
      rw [ballFn_coe, ballFn_coe, sub_zero, sub_zero, map_one]
      congr 1
      refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_add_le hx hb1⟩
      have := (valuation k).map_sub_le hx hb1
      rwa [add_sub_cancel_right] at this
  set e : OnePoint k → ℂ := fun _ => 1 with he
  have R1 : (0 : ℂ) • e + (1 : ℂ) • ballFn (0 : k) 1 + (-q) • ballFn (0 : k) ϖ ∈ S := by
    have h1 := S.neg_mem (S.sum_mem fun a (ha : a ∈ T) => hdiff a (hT1 a ha))
    rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, ← hqdef] at h1
    convert h1 using 1
    module
  have R2 := hS.scale_mem h0 _ _ _ _ _ _ _ R1
  have R3 : (1 - q) • e + q • ballFn (0 : k) 1 + (-1 : ℂ) • ballFn (0 : k) ϖ ∈ S := by
    refine hS.2 _ R1 _ ?_ ?_ fun x hx => ?_
    · simp [ballFn_coe, he]; ring
    · simp [ballFn_coe, he]
    · have hx0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
      simp only [Pi.add_apply, Pi.smul_apply, ballFn_coe, sub_zero, map_one, hϖ, le_uniformizer_iff, map_inv₀, he, smul_eq_mul,
        inv_le_one₀ hx0, inv_lt_one₀ hx0]
      rcases lt_trichotomy (valuation k x) 1 with h1 | h1 | h1
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]
      · simp [h1]
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]; ring
  have R4 := hS.scale_mem h0 _ _ _ _ _ _ _ R3
  simp only [mul_zero, mul_one] at R2 R4
  rw [← he] at R2 R4
  have hq1 : (1 - q) ≠ 0 := by
    rw [sub_ne_zero, hqdef]
    exact_mod_cast (hT2 hlt).ne
  have hq2 : (1 + q) ≠ 0 := by
    rw [hqdef]
    exact_mod_cast (by omega : 1 + T.card ≠ 0)
  have h2 : ballFn (0 : k) (ϖ * ϖ) ∈ S := by
    have h3 := S.sub_mem (S.add_mem (S.sub_mem R4 R3) (S.smul_mem q R1)) (S.smul_mem (q + 1 - q ^ 2) R2)
    have h4 : -((1 - q) * (1 - q) * (1 + q)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hq1 hq1) hq2)
    refine (S.smul_mem_iff h4).1 ?_
    convert h3 using 1
    module
  have hu0 : ballFn (0 : k) 1 ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 one_ne_zero
  have hu1 : ballFn (0 : k) ϖ ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 h0
  refine ⟨hu0, (S.smul_mem_iff hq1).1 ?_⟩
  convert S.add_mem (S.sub_mem R3 (S.smul_mem q hu0)) hu1 using 1
  module

end GlobalTheory.LocGL.ProjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnSubMemOfRadial
section
open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

theorem exists_jump_point {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (f : k → ℂ) {r : k} (hr : r ≠ 0) (h : ∀ x, valuation k x ≤ valuation k r → f x = f 0) {y : k} (hy : f y ≠ f 0) :
    ∃ b : k, f b ≠ f 0 ∧ ∀ x, valuation k x < valuation k b → f x = f 0 := by
  classical
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hr' : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  have hex : ∃ n : ℕ, ∃ x, valuation k x * uniformizer k ^ n ≤ valuation k r ∧ f x ≠ f 0 := by
    have hy0 : 0 < valuation k y := zero_lt_iff.2 (by rintro h0; rw [map_eq_zero] at h0; exact hy (by rw [h0]))
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k))
      (Units.mk0 (valuation k r / valuation k y) (div_pos hr' hy0).ne')
    refine ⟨n, y, ?_, hy⟩
    rw [Units.val_mk0, lt_div_iff₀ hy0, mul_comm] at hn
    exact hn.le
  obtain ⟨b, hb, hb'⟩ := Nat.find_spec hex
  refine ⟨b, hb', fun x hx => ?_⟩
  by_contra hne
  rcases hm : Nat.find hex with _ | m
  · rw [hm, pow_zero, mul_one] at hb
    exact hb' (h b hb)
  · refine Nat.find_min hex (m := m) (by omega) ⟨x, ?_, hne⟩
    rw [hm] at hb
    have hb0 : 0 < valuation k b := zero_le'.trans_lt hx
    have h1 : valuation k x / valuation k b ≤ uniformizer k := le_uniformizer_iff.2 ((div_lt_one₀ hb0).2 hx)
    rw [div_le_iff₀ hb0] at h1
    calc valuation k x * uniformizer k ^ m ≤ uniformizer k * valuation k b * uniformizer k ^ m := by gcongr
      _ = valuation k b * uniformizer k ^ (m + 1) := by rw [pow_succ]; ac_rfl
      _ ≤ _ := hb

theorem ballFn_sub_mem_of_radial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (F : OnePoint k → ℂ) (hF : F ∈ S)
    (hrad : ∀ u x : k, valuation k u = 1 → F ((u * x : k) : OnePoint k) = F (x : OnePoint k))
    (h0 : ∃ r : k, r ≠ 0 ∧ ∀ x : k, valuation k x ≤ valuation k r → F (x : OnePoint k) = F ((0 : k) : OnePoint k))
    (hi : ∃ R : k, ∀ x : k, valuation k R < valuation k x → F (x : OnePoint k) = F ∞)
    (hne : F ((0 : k) : OnePoint k) ≠ F ∞) (ϖ : k) (hϖ : valuation k ϖ = uniformizer k) :
    ballFn 0 ϖ - ballFn 1 ϖ ∈ S := by
  classical
  obtain ⟨r, hr, h0⟩ := h0
  obtain ⟨R, hi⟩ := hi
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hy : ∃ y : k, valuation k R < valuation k y := by
    by_cases hR : R = 0
    · exact ⟨1, by simp [hR]⟩
    · have hR' : 0 < valuation k R := zero_lt_iff.2 (by simpa using hR)
      refine ⟨R / ϖ, ?_⟩
      rw [map_div₀, hϖ, lt_div_iff₀ hπ]
      exact mul_lt_of_lt_one_right hR' uniformizer_lt_one
  obtain ⟨y, hy⟩ := hy
  obtain ⟨b, hb, hb'⟩ := exists_jump_point (fun x : k => F x) hr h0 (y := y) (by
    show F y ≠ F (0 : k)
    rw [hi y hy]; exact hne.symm)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
  have hvb : 0 < valuation k b := zero_lt_iff.2 (by simpa using hb0)
  let g : k → ℂ := fun x => F ((b * x : k) : OnePoint k)
  have g1 : ∀ x, valuation k x < 1 → g x = F (0 : k) := fun x hx => hb' _ (by
    rw [map_mul]; exact mul_lt_of_lt_one_right hvb hx)
  have g2 : ∀ x, valuation k x = 1 → g x = F b := fun x hx => by
    show F ((b * x : k) : OnePoint k) = _
    rw [mul_comm]; exact hrad x b hx
  have g3 : ∀ x z, x ≠ 0 → valuation k z = valuation k x → g z = g x := fun x z hx hz => by
    have hvx : valuation k x ≠ 0 := by simpa using hx
    have := hrad (z / x) (b * x) (by rw [map_div₀, hz, div_self hvx])
    show F ((b * z : k) : OnePoint k) = F ((b * x : k) : OnePoint k)
    rw [← this]; congr 2; field_simp
  have hG : (fun x : OnePoint k => x.elim (F ∞) g) ∈ S :=
    hS.1 F hF b 0 hb0 _ rfl fun x => by rw [add_zero]; rfl
  have hG' : (fun x : OnePoint k => x.elim (F ∞) fun x => g (x - 1)) ∈ S :=
    hS.1 F hF b (-b) hb0 _ rfl fun x => by
      show F ((b * (x - 1) : k) : OnePoint k) = _
      congr 2; ring
  have hc : F (0 : k) - F b ≠ 0 := sub_ne_zero.2 hb.symm
  rw [← S.smul_mem_iff hc]
  convert S.sub_mem hG hG' using 1
  funext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe x =>
    show (F (0 : k) - F b) * (ballFn 0 ϖ x - ballFn 1 ϖ x) = g x - g (x - 1)
    rw [ballFn_coe, ballFn_coe, hϖ, sub_zero]
    simp only [le_uniformizer_iff]
    by_cases h1 : valuation k x < 1
    · have h2 : valuation k (x - 1) = 1 := by
        rw [Valuation.map_sub_swap]; exact (valuation k).map_one_sub_of_lt h1
      rw [if_pos h1, if_neg (by rw [h2]; exact lt_irrefl _), g1 x h1, g2 _ h2]; ring
    · by_cases h2 : valuation k (x - 1) < 1
      · have h3 : valuation k x = 1 := by
          have := (valuation k).map_one_add_of_lt h2
          rwa [add_sub_cancel] at this
        rw [if_neg h1, if_pos h2, g1 _ h2, g2 _ h3]; ring
      · have hx0 : x ≠ 0 := by rintro rfl; exact h1 (by simp)
        have h3 : valuation k (x - 1) = valuation k x := by
          rcases (not_lt.1 h1).eq_or_lt with h4 | h4
          · refine le_antisymm ?_ (h4 ▸ not_lt.1 h2)
            exact (valuation k).map_sub_le le_rfl (by rw [map_one]; exact h4.le)
          · exact (valuation k).map_sub_eq_of_lt_left (by rwa [map_one])
        rw [if_neg h1, if_neg h2, g3 x _ hx0 h3]; ring

end GlobalTheory.LocGL.ProjLine
end

