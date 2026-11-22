import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0891
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.UnfoldRows

open Matrix

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem single_last_vecMul {m : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (Pi.single (Fin.last m) 1 : Fin (m + 1) → R) ᵥ* M = M (Fin.last m) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem algebraMap_comp_single {m : ℕ} :
    (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) = Pi.single (Fin.last m) 1 := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem lastRow_eq {m : ℕ} (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val := by
  rw [algebraMap_comp_single, single_last_vecMul]
  rfl

theorem det_posM_eq_one {R : Type} [CommRing R] {a : ℕ} {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a}
    (hp : ∀ t, (p t).1 < (p t).2) (x : ι → R) : (1 + posM p x).det = 1 := by
  have hz : ∀ i j : Fin a, j ≤ i → posM p x i j = 0 := by
    intro i j hij
    simp only [posM, Matrix.sum_apply, Matrix.single_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl, -⟩
    exact absurd (hp t) (not_lt.2 hij)
  have hT : (1 + posM p x).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, hz i j (le_of_lt hij), add_zero]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.add_apply, Matrix.one_apply_eq, hz i i le_rfl, add_zero]

theorem detAbs_of_det_one {a : ℕ} (u : GA E a) (hu : (u : Matrix (Fin a) (Fin a) (Ad E)).det = 1) :
    GlobalTheory.RSnm.detAbs u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := Units.ext (by rw [GeneralLinearGroup.val_det_apply, hu, Units.val_one])
  simp [GlobalTheory.RSnm.detAbs, h]

theorem rows_main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  intro E _ _ _ m
  refine ⟨?_, lastRow_eq, ?_, ?_, ?_⟩
  · intro γ g
    rw [lastRow_eq, GlobalTheory.ThetaUnfold.vecMul_ratGL_mul]
  · intro γ hγ
    rw [single_last_vecMul]
    funext k
    have := hγ (Fin.last m) k (Or.inl (by simp))
    rw [this]
    by_cases h : k = Fin.last m
    · subst h; simp
    · simp [Matrix.one_apply, Pi.single_apply, h, Ne.symm h]
  · intro r l y g
    have hp : ∀ t : UnipotentBlockColumnIndex (m + 1) r l, t.1.1 < t.1.2 := fun t => by
      have := t.2; exact Fin.lt_def.2 (by omega)
    refine ⟨?_, ?_⟩
    · funext j
      change ((blkU y).val * g.val) (Fin.last m) j = g.val (Fin.last m) j
      rw [blkU, posU_val, add_mul, one_mul, Matrix.add_apply, add_eq_left]
      simp only [posM, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Matrix.single_mul_apply_of_ne]
      intro h
      have h1 := t.2.1
      have h2 := t.1.2.isLt
      have h3 := t.2.2.1
      rw [← h] at h1
      simp only [Fin.val_last] at h1
      omega
    · rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
      rw [blkU, posU_val]
      exact det_posM_eq_one (p := Subtype.val) hp y
  · intro X g
    rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
    rw [GroundTheory.Automorphic.FourierWhittaker.coe_uGL, GroundTheory.Automorphic.FourierWhittaker.det_uMat]

end GlobalTheory.UnfoldRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), GlobalTheory.Pst.IsPst P ρ → ∀ (σ : ↥(Ine (F := E) A)) (q : (↥LL.1)[X]), q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = (GlobalTheory.Pst.wdPst P ι Bw h hj ρ).charPol (GlobalTheory.WeilDeligne.ineIncl h σ) → ∀ x ∈ GlobalTheory.Pst.Dpst P ρ, Polynomial.aeval (GlobalTheory.Pst.stRep P ρ (GlobalTheory.Pst.weilToGK Bw h (GlobalTheory.WeilDeligne.ineIncl h σ))) q x = 0 := by
  first | exact @GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero | exact GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero | (intros; apply GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  first | exact @GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | exact GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst | (intros; apply GlobalTheory.PcrisPst.aeval_eq_zero_of_kills_Dpst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AugmentationLengthColengthBound
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.PartialBlock

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self coe_blockGL blockMat_apply diagonal_blockGL)

variable {E : Type} [Field E] [NumberField E]

theorem good_top {ψ : AddChar (Ad E) ℂ} {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) :
    Good ψ k φ := by
  refine ⟨hφ, fun γ _ g => hl γ g, ?_, hv⟩
  intro j hj y g
  have he : IsEmpty (UnipotentBlockColumnIndex (k + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  have hd : dot (eLast (k + 1) j) (0 : UnipotentBlockColumnIndex (k + 1) j j → Ad E) = 0 := by simp [dot]
  rw [hd, AddChar.map_zero_eq_one, one_mul]
  unfold blkU
  rw [posU_zero, one_mul]

theorem good_partialCoeff {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0)
    {m : ℕ} (hm : m ≤ k) : Good (GlobalTheory.StdCharConductor.psi E) m (partialCoeff φ (m + 1)) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [partialCoeff_self]; exact good_top hφ hl hv
  | of_succ m hm ih =>
    rw [← GlobalTheory.WhitCols.colT_partialCoeff hφ (fun γ _ g => hl γ g) (by omega : m + 1 < k + 1)]
    exact GlobalTheory.CuspRep.Generic.good_colT (GlobalTheory.StdCharConductor.stdPsi_psi E) (by omega) ih

theorem blkU_entry {R : Type} [CommRing R] {a r m : ℕ} (y : UnipotentBlockColumnIndex a r m → R) (i k : Fin a) :
    (blkU y : GL (Fin a) R).val i k = (1 : Matrix (Fin a) (Fin a) R) i k +
      if h : (i : ℕ) < r ∧ r ≤ (k : ℕ) ∧ (k : ℕ) ≤ m then y ⟨(i, k), h⟩ else 0 := by
  rw [← posM_block_entry]; rfl

def blkEquiv {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : UnipotentBlockColumnIndex n r m ≃ UnipotentBlockColumnIndex (m + 1) r m where
  toFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  invFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def blkHom {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : (UnipotentBlockColumnIndex (m + 1) r m → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex n r m → Ad E) where
  toFun x := fun t => x (blkEquiv h r t)
  invFun y := fun i => y ((blkEquiv h r).symm i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem blkHom_mem_iff {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    blkHom h r x ∈ ratV E (UnipotentBlockColumnIndex n r m) ↔ x ∈ ratV E (UnipotentBlockColumnIndex (m + 1) r m) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c ((blkEquiv h r).symm i), funext fun i => congrFun hc ((blkEquiv h r).symm i)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkEquiv h r t), rfl⟩

theorem blockGL_blkU {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    (blockGL h (blkU x) : GL (Fin n) (Ad E)) = blkU (blkHom h r x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_blockGL, blockMat_apply, blkU_entry]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dif_pos hi, dif_pos hj, blkU_entry]
      congr 1
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dif_pos hi, dif_neg hj, dif_neg (by omega), Matrix.one_apply_ne hne, add_zero]
  · rw [dif_neg hi, dif_neg (by omega), add_zero, Matrix.one_apply]

omit [NumberField E] in
theorem isMir_blockGL {n m : ℕ} (h : m + 1 ≤ n) {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) :
    IsMir m (blockGL h γ : GL (Fin n) E) := by
  intro i j hij
  rw [coe_blockGL, blockMat_apply]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dif_pos hi, dif_pos hj, hγ _ _ hij]
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dif_pos hi, dif_neg hj, Matrix.one_apply_ne hne]
  · rw [dif_neg hi, Matrix.one_apply]

theorem good_restrict {ψ : AddChar (Ad E) ℂ} {n m : ℕ} (h : m + 1 ≤ n) {F : GA E n → ℂ} (hF : Good ψ m F) :
    Good ψ m (fun g : GA E (m + 1) => F (blockGL h g)) := by
  refine ⟨hF.cont.comp (GlobalTheory.RSnm.continuous_blockGL h), ?_, ?_, ?_⟩
  · intro γ hγ g
    have e : (blockGL h (ratGL E (m + 1) γ) : GA E n) = ratGL E n (blockGL h γ) := (diagonal_blockGL h γ).symm
    simp only [map_mul]
    rw [e, hF.left _ (isMir_blockGL h hγ)]
  · intro j hj y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) j) (0 : UnipotentBlockColumnIndex (m + 1) j j → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have hP := per_blk (r := r) (m := m) hF.cont (fun c g => hF.left _ (isMir_blkU c) g) (blockGL h g)
    rw [← hF.van r hr hrm (blockGL h g), ← avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (blkHom h r)
      (blkHom_mem_iff h r) _ hP]
    simp only [map_mul, blockGL_blkU]

theorem good_partialCoeff_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  intro E _ _ k m hmk φ hφ hl hv
  exact good_restrict _ (good_partialCoeff hφ hl hv (by omega))

end GlobalTheory.PartialBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPadded
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

section Block

variable {R S : Type} [CommRing R] [CommRing S] {j n : ℕ}

theorem blockGL_cornerGL (hj : j ≤ n) (s : R →ₙ+* S) (g : GL (Fin j) R) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (cornerGL j s g) =
      cornerGL n s (GroundTheory.Automorphic.FourierWhittaker.blockGL hj g) := by
  ext a b
  change GroundTheory.Automorphic.FourierWhittaker.blockMat hj
      ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b =
    (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) +
      s (GroundTheory.Automorphic.FourierWhittaker.blockMat hj (g : Matrix (Fin j) (Fin j) R) a b)
  rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
        Fin.ext_iff]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.one_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.one_apply]
    · simp [ha, hab, Matrix.one_apply]

theorem blockGL_diagPow (hj : j ≤ n) (ϖ : Rˣ) (v : Fin j → ℕ) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (diagPow ϖ v) = diagPow ϖ (GlobalTheory.RSnmUnf.padNat (n := n) v) := by
  ext a b
  rw [GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  simp only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp [ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.diagonal_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]
    · simp [ha, hab, Matrix.diagonal_apply]

theorem padNat_eq_zero_iff {m n : ℕ} (hmn : m ≤ n) (v : Fin m → ℕ) :
    GlobalTheory.RSnmUnf.padNat (n := n) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [GlobalTheory.RSnmUnf.padNat, i.isLt] using this
  · rintro rfl
    exact GlobalTheory.RSnmUnf.padNat_zero

end Block

theorem blockGL_tl {E : Type} [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  have hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n := m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
    rw [padNat_eq_zero_iff (by omega)]
  unfold tl
  rw [hsupp, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, Finsupp.mapRange_apply]
  rw [finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]
  rfl

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargementStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  first | exact @GlobalTheory.PstModel.charPol_upRep_of_isPstAt | exact GlobalTheory.PstModel.charPol_upRep_of_isPstAt | (intros; apply GlobalTheory.PstModel.charPol_upRep_of_isPstAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.ConjLocCsd

theorem plMap_conj_eq {R : Ranks} (Hs : Host R) (w w' : HeightOneSpectrum (𝓞 Hs.E)) (h : IsConjPl Hs w w') :
    CT.plMap (Hs.conj : Hs.E ≃+* Hs.E) w = w' := by
  ext y
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E)
  set x := (RingOfIntegers.mapRingEquiv j).symm y with hx
  have hy : RingOfIntegers.mapRingEquiv j x = y := by rw [hx, RingEquiv.apply_symm_apply]
  have hyx : (y : Hs.E) = Hs.conj (x : Hs.E) := by rw [← hy]; rfl
  rw [← hy, CT.mem_plMap, hy]
  exact h x y hyx

theorem main : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  intro R Hs μ hμ w w' hc
  have hcsd := hμ.1 w w' hc
  obtain rfl := plMap_conj_eq Hs w w' hc
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E) with hj
  set i := CT.compEquiv j w with hi
  have hcont : Continuous i := CT.continuous_compEquiv j w
  have halg : ∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x) := fun x => CT.compEquiv_algebraMap j w x
  refine ⟨i, hcont, halg, ?_⟩
  obtain ⟨ξ, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary Hs.E μ⁻¹ w
  set ψ₁ : (w.adicCompletion Hs.E)ˣ →* ℂˣ := (μ.loc (CT.plMap j w)).comp (Units.map i.toRingHom.toMonoidHom) with hψ₁
  have h1 : IsComp μ⁻¹ w ψ₁ := by
    refine ⟨?_, fun x => ?_⟩
    · have hc' : Continuous (Units.map i.toRingHom.toMonoidHom) := Units.continuous_map hcont
      exact (ParLaws.isSmoothChar_loc μ (CT.plMap j w)).preimage hc'
    · have hu : Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap Hs.E (w.adicCompletion Hs.E)).toMonoidHom x)
          = Units.map (algebraMap Hs.E ((CT.plMap j w).adicCompletion Hs.E)).toMonoidHom (Units.map (Hs.conj : Hs.E ≃+* Hs.E).toRingHom.toMonoidHom x) := by
        apply Units.ext
        exact halg (x : Hs.E)
      rw [hψ₁, MonoidHom.comp_apply, hu]
      have := hcsd x
      exact this
  have h2 : IsComp μ⁻¹ w ((μ⁻¹).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
  have he : ψ₁ = (μ⁻¹).loc w := (huniq _ h1).trans (huniq _ h2).symm
  intro x
  have := congrArg (fun f => f x) he
  simpa [hψ₁, HChar.loc_inv] using this

end GlobalTheory.ConjLocCsd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateCompletionIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_completion_iso : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (κ : w.adicCompletion D.host.E ≃+* w'.adicCompletion D.host.E), Continuous κ →
    (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E)))
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w'.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
    (∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a)) →
    ∃ (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
      GlobalTheory.WeilDeligne.WD.mk b = (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)).lpDual ∧
      GlobalTheory.WeilDeligne.WD.mk b' = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w') (GlobalTheory.LocLanglands.cls σ') ∧
      b.N = b'.N ∧ ∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ' := by
  first | exact @GlobalTheory.ConjDualParam.main | exact GlobalTheory.ConjDualParam.main | (intros; apply GlobalTheory.ConjDualParam.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtensionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c → ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]), (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  first | exact @GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt | exact GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt | (intros; apply GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt <;> assumption)
end

