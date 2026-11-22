import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstTwistedSumFockVectorsPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeisenbergCombinationProjectsOntoVacuum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApplyScalar
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.Central

def centralFns (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : HChar E) :
    Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
  add_mem' hF hG z g := by simp [hF z g, hG z g, mul_add]
  zero_mem' _ _ := by simp
  smul_mem' c F hF z g := by simp [hF z g, mul_left_comm]

theorem apply_scalar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (ω : HChar E) (hω : π.HasCentChar ω) (φ : Sm E a) (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π)
    (z : Neutral.B1.Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  have hc := CuspSub.hasCentral_iff.2 hω
  have hle : GlobalTheory.JSW.mspan π ≤ centralFns E a ω := by
    refine sInf_le ⟨fun ψ hψ z g => hc.apply hψ z g, fun F hF h z g => ?_, fun F hF f _ z g => ?_,
      fun F hF r f z g => ?_⟩
    · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
      rw [mul_assoc]; exact hF z _
    · change GlobalTheory.JSW.smoothInf f F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.smoothInf f F g
      rw [← GlobalTheory.JSW.smoothInf_left]
      have e : (fun x => F (GeneralLinearGroup.scalar (Fin a) z * x)) = ((ω.1 z : ℂˣ) : ℂ) • F :=
        funext fun x => hF z x
      rw [e, GlobalTheory.JSW.smoothInf_smul]; rfl
    · change GlobalTheory.JSW.colConv r f F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.colConv r f F g
      simp only [GlobalTheory.JSW.colConv, mul_assoc]
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hF z]; ring
  rcases hφ with h | h
  · exact hc.apply h z g
  · exact hle h z g

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (ω : HChar E), π.HasCentChar ω → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π) → ∀ (z : Neutral.B1.Ideles E) (g : GA E a), φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
  fun E _ _ _ a π ω hω φ hφ z g => apply_scalar E a π ω hω φ hφ z g

end GlobalTheory.JSW.Central
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

section H

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
theorem secRow_eq_rowMat {R : Type} [CommRing R] (y : Fin (m + 1) → R) :
    secRow y = GlobalTheory.RSTheta.rowMat (Fin.last m) y := by
  ext i j
  simp only [secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by simpa using e)))]

omit [NumberField E] [IsTotallyComplex E] in

theorem secInv_eq_inv_rowGL {y : Fin (m + 1) → Cinf E} (hy : y ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m)) :
    secInv y = (GlobalTheory.RSTheta.rowGL (Fin.last m) y)⁻¹ := by
  have hu := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hy
  have hd : IsUnit (secRow y).det := by rw [secRow_eq_rowMat, GlobalTheory.RSTheta.det_rowMat]; exact hu
  rw [secInv, dif_pos hd]
  congr 1
  apply Units.ext
  rw [GlobalTheory.RSTheta.val_rowGL hu, ← secRow_eq_rowMat]
  rfl

theorem continuous_yInf : Continuous (yInf : GA E (m + 1) → Fin (m + 1) → Cinf E) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp
    (Units.continuous_val.matrix_elem (Fin.last m) i)

omit [NumberField E] [IsTotallyComplex E] in
theorem continuous_sqrtC {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) : Continuous (sqrtC Φ) :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (Complex.continuous_re.comp hΦ))

theorem lastRow_mul_of_row {h g : GA E (m + 1)}
    (hr : ∀ l, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply, hr]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem blkU_lastRow {r : ℕ} (hr : r ≤ m) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) (l : Fin (m + 1)) :
    ((blkU x : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change (1 + posM Subtype.val x : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, -⟩
  have h1 : (t.1.1 : ℕ) = m := by rw [e1]; simp
  have h2 := t.2.1
  omega

omit [IsTotallyComplex E] in
theorem ratGL_lastRow {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) (l : Fin (m + 1)) :
    ((ratGL E (m + 1) γ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change algebraMap E (Ad E) (γ.val (Fin.last m) l) = _
  rw [hγ (Fin.last m) l (Or.inl (by simp))]
  by_cases h : Fin.last m = l
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

theorem continuous_fT {φ : GA E (m + 1) → ℂ} (hφ : Continuous φ) {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) : Continuous (fT φ Φ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv (yInf g))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp continuous_yInf.continuousAt)
    exact (hφ.continuousAt.comp h1).mul ((continuous_sqrtC hΦ).comp continuous_yInf).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [fT, sqrtC, hq]

end H

theorem good_fT : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  intro E _ _ _ m φ hφ hl hv Φ hΦ hs ψ
  refine ⟨continuous_fT hφ hΦ hs, ?_, ?_, ?_⟩
  · intro γ hγ g
    rw [fT_of_lastRow (lastRow_mul_of_row (ratGL_lastRow hγ)), mul_assoc, hl, fT]
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have e : (fun x : UnipotentBlockColumnIndex (m + 1) r m → Ad E => fT φ Φ (blkU x * g)) = fun x =>
        sqrtC Φ (yInf g) * φ (blkU x * (g * infGL E (m + 1) (secInv (yInf g)))) := by
      funext x
      rw [fT_of_lastRow (lastRow_mul_of_row (blkU_lastRow hrm x)), mul_comm, mul_assoc]
    rw [e, avg_const_mul, hv r hr hrm, mul_zero]

end GlobalTheory.ZUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumRegroupFinerLevelCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_regroup_finerLevel_cosets : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G), Function.Injective ι → ∀ {J J₀ : Subgroup G}, J₀ ≤ J →
    ∀ {F : Finset G}, (∀ u ∈ F, u ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J₀) →
    ∀ {I₀ : Type} [Fintype I₀] (y₀ : I₀ → G), Bridge.IsReps ι J₀ y₀ → ∀ {I : Type} [Fintype I] (y : I → G), Bridge.IsReps ι J y →
    ∀ (Φ : G → ℂ), (∀ γ g, Φ (ι γ * g) = Φ g) → (∀ k ∈ J₀, ∀ g, Φ (g * k) = Φ g) →
    ∑ i, ((Nat.card (Bridge.stab ι J₀ (y₀ i)) : ℂ))⁻¹ * Φ (y₀ i) =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ∑ u ∈ F, Φ (y i * u) := by
  first | exact @GlobalTheory.ClassRefineBridge.sum_isReps_refine | exact GlobalTheory.ClassRefineBridge.sum_isReps_refine | (intros; apply GlobalTheory.ClassRefineBridge.sum_isReps_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.SpanProps

theorem avg_eq_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {F : GA E a → ℂ}
    (hcont : Continuous F) (hleft : ∀ γ g, F (ratGL E a γ * g) = F g) (hc : IsCuspidal F)
    (r : ℕ) (hr : 0 < r) (hra : r ≤ a - 1) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F (blkU x * g)) = 0 := by
  have hra' : r < a := by omega
  have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => hleft _ g) g
  have hper2 : Per (ratN E a r) (fun x => F (blkU (blkIxHomeo r x) * g)) :=
    ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
      simp only [map_add]
      exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
  have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
    (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
  rw [← key]
  have hfun : (fun x => F (blkU (blkIxHomeo r x) * g)) = fun x => F (unip x * g) :=
    funext fun x => by rw [← blkU_comp_equiv]; rfl
  rw [hfun] at hper2 ⊢
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
  have hc' := hc r hr hra' μ 𝓕 hμ hF g
  rw [hint, h1] at hc'
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc'
  exact hc'

end GlobalTheory.JSW.SpanProps

theorem GlobalTheory.JSW.mspanR_cont_left_avg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  intro E _ _ _ m π ω hω hc F hF
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil] at h0
  refine ⟨h0.cont, h0.left, fun r hr hrm g => ?_⟩
  exact GlobalTheory.JSW.SpanProps.avg_eq_zero (a := m + 1) h0.cont h0.left h0.cusp r hr hrm g
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstTwistedSumFockVectorsPrincipalDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (F : Finset (Bridge.Gf S)) (hF : ∀ u ∈ F, u ∈ B.levJ ψ),
    (∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) →
    ∃ κ : ℂ, ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ F.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P := by
  first | exact @GlobalTheory.LevTransl.sum_om_fock_princ | exact GlobalTheory.LevTransl.sum_om_fock_princ | (intros; apply GlobalTheory.LevTransl.sum_om_fock_princ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeisenbergCombinationProjectsOntoVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergCombination_projects_onto_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ v : WO S T → ℂ, IsThetaFunO ψ S T v → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) v) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) ∧ (c.sum fun u z => z • heisO ψ S T u v) = v ∧ ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) → ∃ a : ℂ, (c.sum fun u z => z • heisO ψ S T u x) = a • v := by
  first | exact @GlobalTheory.VacDensity.proj | exact GlobalTheory.VacDensity.proj | (intros; apply GlobalTheory.VacDensity.proj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentationComponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.CoefDuty GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representation_component : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (a : NAt hL D cf nch tp), OPin a → (∀ (I : Ident a.nt.D) cp, IsComp I a.nt.rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g a.nt.D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom a.nt.D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ b, ρ.asAlgebraHom b x ∈ W) ∧ ρ.asAlgebraHom a.nt.D.ntypes.e0 x = x) → GoodFTAll D := by
  first | exact @GlobalTheory.GoodPin.goodFTAll_pinned | exact GlobalTheory.GoodPin.goodFTAll_pinned | (intros; apply GlobalTheory.GoodPin.goodFTAll_pinned <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockReadingTranslatedFormMemComplexFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockReading_translatedForm_mem_complexForms : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  first | exact @GlobalTheory.FockReadForms.fockRead_mem_formsC | exact GlobalTheory.FockReadForms.fockRead_mem_formsC | (intros; apply GlobalTheory.FockReadForms.fockRead_mem_formsC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.VacPairSchur

set_option synthInstance.maxHeartbeats 400000 in
theorem actO_fin : ∀ (D : D7) (S T : HSp D) (u : GA D T), u ∈ GinfC T → ∀ w : WO S T, w.map (infPart D) = 0 → actO S T 1 u w = w := by
  intro D S T u hu w hw
  have hf : (Formalism.L2.Theta.mt T u).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hu)
    exact h
  have hm : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_one, hm, Matrix.mul_one]
  ext i j
  refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
  · have h0 : ∀ k, infPart D (w k j) = 0 := fun k => by
      have := congrFun (congrFun hw k) j
      simpa using this
    rw [Matrix.mul_apply, map_sum]
    simp [h0]
  · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T u i k) = if i = k then 1 else 0 := fun k => by
      have := congrFun (congrFun hf i) k
      simpa [Matrix.one_apply] using this
    rw [Matrix.mul_apply, map_sum]
    simp [h1]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem pT_heisO (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) {w : WO S T}
    (hw : w.map (infPart D) = 0) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T w f) P = heisO ψ S T w (pureTensorO ψ θ S T sS sT BS BT f P) := by
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T w)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2
  · exact h.symm
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
    rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw]
    rfl

theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1
  funext w
  rw [mul_comm]
  rfl

theorem thetaInner_heisenberg (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b)
    (w : WO S T) : thetaIP μ 𝓕 (heisO ψ S T w a) (heisO ψ S T w b) = thetaIP μ 𝓕 a b := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]

theorem om_heisO_fin {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {u : GA D T} (hu : u ∈ GinfC T) {w : WO S T} (hw : w.map (infPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (1, u) (heisO ψ S T w f) = heisO ψ S T w (om (1, u) f) := by
  rw [hom.om_heis 1 u w f hf, actO_fin D S T u hu w hw]

theorem pT_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : ℂ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (a • f + f') P =
      a • pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P :=
  GlobalTheory.VacCoefAtPlace.pure_lin (P := IsThetaFunO ψ S T) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun _ b _ _ h h' => by
      simp only [aPlusAll]
      rw [GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul b h) h',
        GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ b h]) a hf hf' P

theorem onb_min {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsONBasis G s B (min p k) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  refine ⟨ε, fun a => ?_, h2, h3⟩
  rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
  · exact Or.inl ⟨e, lt_min ha a.2⟩
  · exact Or.inr ⟨e, (min_le_left _ _).trans ha⟩

theorem cs (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    ‖thetaIP μ 𝓕 a b‖ ^ 2 ≤ (thetaIP μ 𝓕 a a).re * (thetaIP μ 𝓕 b b).re := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have ii : ∀ {c : WO S T → ℂ}, IsThetaFunO ψ S T c → Integrable (fun x => star (c x) * c x) (μ.restrict 𝓕) :=
    fun {c} hc => (GlobalTheory.Size.integrableOn_mul_conj hψ hcv.1 hcv.2.1 hc hc).congr
      (ae_of_all _ fun x => mul_comm _ _)
  exact GlobalTheory.norm_integral_star_mul_sq_le (μ.restrict 𝓕) a b ha.cont.aestronglyMeasurable
    hb.cont.aestronglyMeasurable (ii ha) (ii hb)

theorem pair_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ u ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv u hu P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g := by
    intro a f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hf hf' P, map_add, map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul a (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g' := by
    intro a f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hb : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_fin hom hu hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hb hi

end GlobalTheory.VacPairSchur
end
end

