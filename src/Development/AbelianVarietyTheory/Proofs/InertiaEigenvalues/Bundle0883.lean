import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0877
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIff
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.CellDec.RowPos
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_val (v : HeightOneSpectrum (𝓞 E)) (x : GA E n) (i j : Fin n) :
    (compV E n v x).val i j = pLoc E v (pFin E (x.val i j)) := rfl

theorem row_unip_mul {R : Type} [CommRing R] {m : ℕ} {U : GL (Fin (m + 1)) R}
    (hU : U ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (K : GL (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (U * K).val (Fin.last m) i = K.val (Fin.last m) i := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hU
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro j _ hj
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sub_single_apply {m : ℕ} (y : Fin (m + 1) → Af E) (i : Fin (m + 1)) (v : HeightOneSpectrum (𝓞 E)) :
    (((y - Pi.single (Fin.last m) (1 : Af E)) : Fin (m + 1) → Af E) i) v = y i v - if i = Fin.last m then 1 else 0 := by
  change pLoc E v ((y - Pi.single (Fin.last m) (1 : Af E) : Fin (m + 1) → Af E) i) = pLoc E v (y i) - _
  rw [Pi.sub_apply, map_sub]
  congr 1
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]

theorem val_sub_ite_le_one {v : HeightOneSpectrum (𝓞 E)} {x : v.adicCompletion E} (hx : Valued.v x ≤ 1) (p : Prop)
    [Decidable p] : Valued.v (x - if p then 1 else 0) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans (max_le hx ?_)
  split_ifs
  · rw [map_one]
  · rw [map_zero]; exact zero_le'

end GlobalTheory.CellDec.RowPos

open GlobalTheory.CellDec GlobalTheory.CellDec.RowPos in

theorem GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  intro E _ _ m T ϖ hϖ J hJ g hg l hl
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hgv : ∀ v i, (pFin E ((u * k).val (Fin.last m) i)) v = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i
    change pLoc E v _ = _
    rw [← compV_val, map_mul, row_unip_mul (compV_mem_unipB v hu)]
  have htv : ∀ v i, (pFin E ((tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) v =
      ((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (pFin E ((u * k).val (Fin.last m) i)) v := by
    intro v i
    change pLoc E v _ = _ * pLoc E v _
    rw [← compV_val, ← compV_val, map_mul (compV E (m + 1) v), compV_tl, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul]
  refine forall_congr' fun i => ?_
  rw [GroundTheory.Global.mem_idealFiniteAdeles, GroundTheory.Global.mem_idealFiniteAdeles]
  refine forall_congr' fun v => ?_
  rw [sub_single_apply, sub_single_apply]
  beta_reduce
  rw [htv]
  by_cases hv : v ∈ T
  · rw [l.2 v hv]
    simp
  · rw [hJ v hv]
    have hK := (GlobalTheory.AdelicU.mem_GLint_iff.1 (mem_US.1 hk v hv)).1 (Fin.last m) i
    have hK' : Valued.v ((compV E (m + 1) v k).val (Fin.last m) i) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hK
    have hϖ1 : Valued.v ((ϖ v : v.adicCompletion E)) ≤ 1 := by
      rw [hϖ v]; exact le_of_lt (by decide)
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hl v)
    have hp : Valued.v (((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ≤ 1 := by
      rw [ha, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' hϖ1 a
    rw [hgv, neg_zero, WithZero.exp_zero]
    refine ⟨fun _ => val_sub_ite_le_one hK' _, fun _ => val_sub_ite_le_one ?_ _⟩
    rw [map_mul]
    exact mul_le_one' hp hK'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponent
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CellDec.lastRow_sub_notMem_latt : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  intro E _ _ m T ϖ hϖ J hJ g hg l w hlw hmem
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hwT : w ∉ T := fun h => by rw [l.2 w h] at hlw; simp at hlw
  set a := l.1 w (Fin.last m) with ha
  set K := GlobalTheory.CellDec.compV E (m+1) w k with hKdef
  have hK : K ∈ GlobalTheory.LFun.KGL w (m+1) := GlobalTheory.CellDec.mem_US.1 hk w hwT
  obtain ⟨-, hK2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have hU := (GlobalTheory.SmGL.mem_unipB _).1 (GlobalTheory.CellDec.compV_mem_unipB w hu)
  have hent : ∀ i, (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
      ((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i := by
    intro i
    have h1 : (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
        (GlobalTheory.CellDec.compV E (m+1) w (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k))).val (Fin.last m) i := rfl
    rw [h1, map_mul, map_mul, GlobalTheory.CellDec.compV_tl, Units.val_mul, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hU.2, one_mul]
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hb : ∀ i, Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i -
      (if i = Fin.last m then 1 else 0)) ≤ 1 := by
    intro i
    have h2 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hmem i) w
    rw [hJ w hwT, neg_zero, WithZero.exp_zero] at h2
    convert h2 using 2
    rw [← hent i]
    by_cases hi : i = Fin.last m
    · subst hi; simp
    · simp [hi]
  have hϖv : Valued.v ((ϖ w : w.adicCompletion E)) = WithZero.exp (-1 : ℤ) := hϖ w
  have hrow : ∀ i, Valued.v (K.val (Fin.last m) i) < 1 := by
    intro i
    have hle : Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) ≤ 1 := by
      by_cases hi : i = Fin.last m
      · have := hb i
        rw [if_pos hi] at this
        calc _ = Valued.v ((((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i - 1) + 1) := by
              rw [sub_add_cancel]
          _ ≤ max _ _ := Valuation.map_add _ _ _
          _ ≤ 1 := max_le this (by simp)
      · simpa [hi] using hb i
    have e : K.val (Fin.last m) i = ((ϖ w ^ (-a) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
        (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) := by
      rw [← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    rw [e, Valuation.map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖv, ← WithZero.exp_zsmul]
    have hlt : WithZero.exp ((-a) • (-1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; simp; omega
    calc _ ≤ WithZero.exp ((-a) • (-1 : ℤ)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hone : ∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (w.adicCompletion E) => M (Fin.last m) (Fin.last m))
      (Units.mul_inv K)
    simpa [Matrix.mul_apply] using this
  have hlt : Valued.v (∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Valuation.map_mul]
    have hj : Valued.v ((K⁻¹).val j (Fin.last m)) ≤ 1 := hK2 j (Fin.last m)
    calc _ ≤ Valued.v (K.val (Fin.last m) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hrow j
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelsWith
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in
theorem models_with (h : R.IsModels) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, h.HX, h.HV, h.HE, h.HW, h.gE, h.gW, h.jX, h.jV, h.νY, h.νY', h.ν0, h.νX, h.νV, h.νW, h.BV,
    h.order⟩

set_option maxHeartbeats 4000000 in
theorem fam_with (h : R.IsFam) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsFam :=
  ⟨h.tie, h.Sb, h.roots, h.pl_onto, h.degR, h.degL, h.muVal, h.etaVal⟩

theorem chain_with (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (a : R.chain_ptY)
    (b : R.chain_ptX) (c : R.chain_ItY) (d : R.chain_ItX) (ioY ioX Th) (e : ({ R with ioY := ioY } : RealDat D A Ks).chain_ioY)
    (f : ({ R with ioX := ioX } : RealDat D A Ks).chain_ioX)
    (g : ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain :=
  ⟨hωY, hωX, hvY, hvX, a, b, c, d, e, f, g⟩

theorem exists_th (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record) (hF : R.IsFam) (hM : R.IsModels) (ioY ioX) :
    ∃ Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th :=
  GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks { R with ioY := ioY, ioX := ioX } hL
    (fam_with hF ioY ioX R.Th R.thF R.thG) (models_with hM ioY ioX R.Th R.thF R.thG) hr

set_option maxHeartbeats 800000 in

theorem exists_chain (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record)
    (hF : R.IsFam) (hM : R.IsModels) (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (t₀ : T)
    (hY : ∀ k, k + 1 < D.R.m → IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) (R.ItY k))
    (hX : IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) R.ItX) :
    ∃ ioY ioX Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain := by
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hW := GlobalTheory.T.chainSteps_levelCharacter_conditions_hold D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hIY : R.chain_ItY := fun t k hk =>
    GlobalTheory.Chain.ItAllTuples.pItY_of_one h₁ h₂ D G Pl0 T A Ks R hP hL hM hωY hωX hvY hvX k hk t₀ _ (hY k hk) t
  have hIX : R.chain_ItX := GlobalTheory.T.lastStep_intertwiner_one_tuple_all_tuples D G Pl0 T A Ks R hL hM hωX hvX t₀ _ hX
  have hpY : R.chain_ptY := fun t k hk P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (hωY t k hk).std hM.inf _ _ _ _ (hS.1 t ⟨k, by omega⟩ hk).2.theta P
  have hpX : R.chain_ptX := (GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hL hF hM hωX hvX).1
  exact (GlobalTheory.Chain.InnerLift.exists_ioY_of_pair R (GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses h₁ h₂ h₃ h₄ D) hP hS.1 hW.1 hM hIY).elim fun ioY hioY =>
    (GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hL hF hM hωX hvX hpX hIX).elim fun ioX hioX =>
    (exists_th hL hr hF hM ioY ioX).elim fun Th hTh =>
    ⟨ioY, ioX, Th, chain_with hωY hωX hvY hvX hpY hpX hIY hIX ioY ioX Th hioY hioX hTh⟩

set_option maxHeartbeats 4000000 in

theorem exists_thP (h₃ : GlobalTheory.Published.CuspRapidDecay) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (hM : R.IsModels) (hω : R.thP_ωP)
    (hv : R.thP_vP) (t₀ : T)
    (hI : ∀ i, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) (R.ioP i)) :
    ∃ thF thG, ({ R with thF := thF, thG := thG } : RealDat D A Ks).IsThP := by
  have hp : R.thP_pt_theta := (GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R hL hF hM hω hv).1
  have hio : R.thP_ioP := fun i => GlobalTheory.IoAllTuples.ioP_of_isIoW_at D G Pl0 T A Ks R hL hF hM hω hv i t₀ _ (hI i)
  obtain ⟨thF, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity h₃ D G Pl0 T A Ks R hL hF hM hω hv hp hio
  obtain ⟨thG, h3⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks { R with thF := thF } hL
    (fam_with hF R.ioY R.ioX R.Th thF R.thG) (models_with hM R.ioY R.ioX R.Th thF R.thG) h1
  exact ⟨thF, thG, hω, hv, hp, hio, h1, h2, h3⟩

end GlobalTheory.ConjExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem lastRow_uGL_mul (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GroundTheory.Automorphic.FourierWhittaker.uGL X * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GroundTheory.Automorphic.FourierWhittaker.coe_uGL, Matrix.mul_apply,
    GroundTheory.Automorphic.FourierWhittaker.uMat_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), dif_neg (not_lt.2 (Fin.le_last c)), zero_mul]
  · simp

theorem jswWhit_fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) :
    GlobalTheory.JSW.whit (fT φ Φ) g = sqrtC Φ (yInf g) * GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv (yInf g))) := by
  simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [fT_of_lastRow (lastRow_uGL_mul X g), mul_assoc (GroundTheory.Automorphic.FourierWhittaker.uGL X) g]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem indN_eq_re (N : ℕ) (y : Fin (m + 1) → Af E) : indN N y = ((indN N y).re : ℂ) := by
  unfold indN; split_ifs <;> simp

theorem indN_re_nonneg (N : ℕ) (y : Fin (m + 1) → Af E) : 0 ≤ (indN N y).re := by
  unfold indN; split_ifs <;> simp

theorem wt_coe (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    (((wt N x g : ℝ≥0) : ℝ) : ℂ) = indN N (yFin g) * (detPow E (m + 1) x g : ℂ) := by
  have h0 : 0 ≤ detPow E (m + 1) x g := norm_nonneg _
  rw [wt, Real.coe_toNNReal _ (mul_nonneg (indN_re_nonneg N _) h0), Complex.ofReal_mul, ← indN_eq_re]

theorem sqrtC_mul_conj {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (u : Fin (m + 1) → Cinf E) :
    sqrtC Φ u * conj (sqrtC Φ u) = Φ u := by
  rw [sqrtC, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hΦ u).1]
  exact Complex.ext (by simp) (by simp [(hΦ u).2])

theorem psi_lastRow_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) =
      fT φ Φ g * conj (fT φ' Φ g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, fT, fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change φ (g * (infGL E (m + 1)) (secInv (yInf g))) * conj (φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

theorem uInt_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ' Φ N x g =
      GlobalTheory.JSW.whit (fT φ Φ) g * conj (GlobalTheory.JSW.whit (fT φ' Φ) g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, jswWhit_fT, jswWhit_fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change GlobalTheory.JSW.whit φ (g * (infGL E (m + 1)) (secInv (yInf g))) *
    conj (GlobalTheory.JSW.whit φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

omit [IsTotallyComplex E] in

theorem NE_eq_ratMirU_zero : GlobalTheory.CellDec.NE E (m + 1) = ratMirU E (m + 1) 0 := by
  have h : GlobalTheory.SmGL.unipB E (Fin (m + 1)) = mirU E (m + 1) 0 := by
    ext γ
    rw [GlobalTheory.SmGL.mem_unipB, mem_mirU_zero]
  rw [GlobalTheory.CellDec.NE, ratMirU, h]

omit [IsTotallyComplex E] in
theorem isMir_of_mem_mirU_zero {γ : GL (Fin (m + 1)) E} (hγ : γ ∈ mirU E (m + 1) 0) : IsMir m γ := by
  intro i k h
  refine hγ i k (Nat.zero_le _) ?_
  rcases h with h | h
  · have := k.2; change (k : ℕ) ≤ i; omega
  · have := k.2; omega

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

theorem enorm_uInt_self {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ = ‖GlobalTheory.JSW.whit (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) := by
  rw [uInt_eq hΦ, enorm_mul, enorm_mul, RCLike.enorm_conj, pow_two]
  congr 1
  have h0 : (((wt N x g : ℝ≥0) : ℝ) : ℂ) = ((wt N x g : ℝ≥0) : ℂ) := rfl
  rw [h0, enorm_eq_nnnorm]
  congr 1
  ext
  simp

theorem zint_unfold : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  rw [GlobalTheory.T.rankinSelbergThetaIntegral_unfold_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin, e2,
    Complex.ofReal_one, one_mul, e1]
  exact hEq

end GlobalTheory.ZUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLintStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelbergThetaIntegral_smoothSpan_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral | exact GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral | (intros; apply GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalKernel_normSq_mul_latticeIndex_eq_one : ∀ (D : D7) (T : HSp D) (N : ℕ) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.FinZeta.Gv T v → ℂ), GlobalTheory.FinZeta.IsLocKer T N (GlobalTheory.LFun.val χ) v φ → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → ∀ a : GlobalTheory.FinZeta.Gv T v, ‖φ a‖ ^ 2 * (latIndex T (GlobalTheory.FinZeta.embV T v a) : ℝ) ^ N = 1 := by
  first | exact @GlobalTheory.LocKerMod.sq_norm_mul_latIndex | exact GlobalTheory.LocKerMod.sq_norm_mul_latIndex | (intros; apply GlobalTheory.LocKerMod.sq_norm_mul_latIndex <;> assumption)
end

