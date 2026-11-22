import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0880
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0122
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0881
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellDec.TlComm

theorem tl_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  intro E _ _ n S ϖ l p hp
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (Matrix.GeneralLinearGroup.map c p = 1 ∨ Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1) = 1) →
      Matrix.GeneralLinearGroup.map c (p * GlobalTheory.CellDec.tl n ϖ l.1) =
        Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1 * p) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GlobalTheory.JSW.GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v ∈ S
    · refine Or.inr ?_
      rw [GlobalTheory.CellDec.tl, finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, GlobalTheory.SmGL.val_diagT]
      have hl : l.1 v = 0 := l.2 v hv
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq]
        show ((ϖ v ^ ((Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l.1) v) : (v.adicCompletion E)ˣ) :
          v.adicCompletion E) = 1
        rw [Finsupp.mapRange_apply, hl, Pi.zero_apply, zpow_zero, Units.val_one]
      · simp [Matrix.diagonal_apply, hij, Matrix.one_apply]
    · exact Or.inl (hp v hv)

end GlobalTheory.CellDec.TlComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

open Matrix

namespace GlobalTheory.CellDecNat

theorem glExt {E : Type} [Field E] [NumberField E] {n : ℕ} {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

theorem tl_eq_jsw_tl (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ))
    (h : ∀ w i, ((l' w i : ℕ) : ℤ) = l w i) : GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  classical
  unfold GlobalTheory.CellDec.tl GlobalTheory.JSW.tl
  have hm : (List.map (fun w => finGL E n (locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w)))) l'.support.toList).prod =
      finGL E n (List.map (fun w => locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w))) l'.support.toList).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hm]
  congr 1
  apply glExt
  intro w
  rw [map_list_prod, List.map_map,
    List.prod_map_eq_pow_single w _ (fun v hv _ => by simp only [Function.comp_apply]; exact pLoc_locGL_of_ne (Ne.symm hv) _)]
  simp only [Function.comp_apply, pLoc_locGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : ∀ i, (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w = ((l' w i : ℕ) : ℤ) := fun i => by
    rw [Finsupp.mapRange_apply, h]
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hw : w ∈ l'.support
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 hw), pow_one]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, zpow_natCast]
      simp [GlobalTheory.JSW.diagPow]
    · simp [Matrix.diagonal_apply_ne _ hij, GlobalTheory.JSW.diagPow]
  · rw [List.count_eq_zero_of_not_mem (by simpa using hw), pow_zero]
    have h0 : l' w = 0 := by simpa using hw
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, h0]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
end GlobalTheory.CellDecNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_decomposition_lattice_integral_unfolding : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ GlobalTheory.JSW.mirS E T m, GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (m + 1)) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  first | (exact @GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (exact GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (intros; apply GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.ClassSumPrinc

theorem ratF_injective {D : D7} (S : HSp D) : Function.Injective (Bridge.ratF S) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
  have h1 : GlobalTheory.ClassRegroup.finPt S (γ : GA D S) = 1 := by
    show (GlobalTheory.ClassRegroup.finEquiv S).symm ((finHom S).rangeRestrict (γ : GA D S)) = 1
    have : (finHom S).rangeRestrict (γ : GA D S) = 1 := hγ
    rw [this, map_one]
  exact Subtype.ext (GlobalTheory.ClassRegroup.eq_one_of_finPt S γ.2 h1)

end GlobalTheory.ClassSumPrinc

namespace GlobalTheory.ClassSumPrinc

theorem symm_finPt {D : D7} (S : HSp D) {k : GA D S} (hk : k ∈ GfC S) :
    (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S k) : GfC S) : GA D S) = k := by
  have : (GlobalTheory.ClassRegroup.finEquiv S) ⟨k, hk⟩ = finPt S k := rfl
  rw [← this, MulEquiv.symm_apply_apply]

theorem inner_sum {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T)
    {Fs : Finset (Bridge.Gf S)} (hF : ∀ u ∈ Fs, u ∈ B.levJ ψ) {κ : ℂ}
    (hκ : ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ Fs.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P)
    {F : Bridge.Gf S → Links.PolF D T.rank S.rank} (hlaw : B.HasLaw ψ F) {x : GA D S} (hx : x ∈ GfC S) (g : GA D T) :
    ∑ u ∈ Fs, series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
        (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      κ * series B.F ω (B.vecFlat ψ) x (F (finPt S x)) g := by
  have hu : ∀ u (hu : u ∈ Fs), series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
      (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      ω (x, g) (((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1)
          (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))) 0 := by
    intro u hu
    have e1 : F (finPt S x * u) = ((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) • F (finPt S x) := by
      have := hlaw 1 (finPt S x) ⟨u, hF u hu⟩
      rw [map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at this
      exact this
    have e2 : (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) =
        x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) := by
      have e3 := map_mul (GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x) u
      rw [e3, Subgroup.coe_mul, symm_finPt S hx]
    rw [series_apply, e2]
    simp only [e1, map_smul]
    have e4 : ω (x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), g) =
        ω (x, g) * ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have e5 := LinearMap.congr_fun e4 (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))
    rw [Module.End.mul_apply] at e5
    simp only [e5]
  rw [← Finset.sum_attach Fs, Finset.sum_congr rfl fun u _ => hu u.1 u.2]
  rw [← Finset.sum_apply, ← map_sum, hκ, map_smul, Pi.smul_apply, smul_eq_mul, series_apply]

theorem classSum_princ_eq : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  intro D S T B hB hS ψ hψ hQ ω hω m h₀ hC₀ I _ h hC
  obtain ⟨hle, -⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  obtain ⟨Fs, hF, hFu⟩ := GlobalTheory.T.finite_coset_representatives_level B hB ψ hQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum B hB hS ψ hψ hQ ω hω Fs hF hFu
  refine ⟨κ, fun F hFm => ?_⟩
  have hinv := GlobalTheory.T.classSumTerms_invariant_principalLevel B hB hS ψ hψ hQ ω hω F hFm
  have hlaw := ((B.mem_formsC).1 hFm).2
  funext g
  rw [Base.classSum_apply, Base.classSum_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_apply]
  have key := GlobalTheory.T.classSum_regroup_finerLevel_cosets (Bridge.ratF S) (ratF_injective S) hle hF hFu (fun i => finPt S (h₀ i)) hC₀.reps
    (fun i => finPt S (h i)) hC.reps
    (fun y => series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g)
    (fun γ y => (hinv g).1 γ y) (fun k hk y => (hinv g).2 k hk y)
  simp only [symm_finPt S (hC₀.fin _), inner_sum B ψ ω hF hκ hlaw (hC.fin _)] at key
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, show (GlobalTheory.FlatVecSum.princ B).F = B.F from rfl]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ClassSumPrinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  first | (exact @GlobalTheory.JSW.WhitCont.continuous_whit) | (exact GlobalTheory.JSW.WhitCont.continuous_whit) | (intros; apply GlobalTheory.JSW.WhitCont.continuous_whit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsMulStableWeberValues
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat
open GlobalTheory.FinalJoin

namespace GlobalTheory.CompMul

theorem sec_mul_of_weberIn : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l : Level Q.H) (Xo : Moduli (Q.Dw j) l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK (Q.Dw j) V io → 1 ≤ (Q.Dw j).p + (Q.Dw j).q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → ∀ N : ℕ, 0 < N → l.M' ∣ N → (WeberIn Q.H c.F N ∨ CurveOver Q.H c.F N) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D Q hQ j hj l Xo c σ V r hr U dict io g e F ik φ th x₀ h1 h2 h3 h4 h5 h6 h7 h8 N hN hd hW
  exact GlobalTheory.T.exists_section_mul_adelic_function_level_cover D Q.H (Q.Dw j) l Xo c σ V r hr U dict io g e F ik φ th x₀ h1 h2 h3 h4 h5 h6 h7 h8
    (GlobalTheory.T.geometricallyIrreducible_components_weberValues D Q hQ j hj l Xo c N hN hd hW)

end GlobalTheory.CompMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariantStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  first | exact @GlobalTheory.JSW.mspanR_left_invariant | exact GlobalTheory.JSW.mspanR_left_invariant | (intros; apply GlobalTheory.JSW.mspanR_left_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_add (F G : GA E a → ℂ) (g : GA E a) : chart (F + G) g = chart F g + chart G g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_smul (z : ℂ) (F : GA E a → ℂ) (g : GA E a) : chart (z • F) g = z • chart F g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_zero (g : GA E a) : chart (0 : GA E a → ℂ) g = 0 := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem kSpan_diff : ∀ F ∈ kSpan E a, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    obtain ⟨L, hL, -⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g u
    exact hL.differentiableAt.differentiableWithinAt
  | zero => intro g; rw [chart_zero]; exact differentiableOn_const 0
  | add F G _ _ hF hG => intro g; rw [chart_add]; exact (hF g).add (hG g)
  | smul z F _ hF => intro g; rw [chart_smul]; exact (hF g).const_smul z

theorem differentiableAt_one_of_mem {F : GA E a → ℂ} (hF : F ∈ kSpan E a) (g : GA E a) :
    DifferentiableAt ℝ (chart F g) (oneL E a) :=
  (kSpan_diff F hF g).differentiableAt (isOpen_invSet.mem_nhds isUnit_one)

theorem kSpan_lie : ∀ F ∈ kSpan E a, ∀ Y : Lie E a, lieD Y F ∈ kSpan E a := by
  intro F hF Y
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    have e : lieD Y (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) = fun g : GA E a =>
        ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν := by
      funext g
      obtain ⟨L, hL, hZ⟩ := GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator E a G X ν k γ hk hG g 1
      have e1 : toL (1 : GL (Fin a) (Cinf E)).val = oneL E a := rfl
      rw [lieD, ← e1, hL.fderiv, hZ Y]
      simp
    rw [e]
    exact GlobalTheory.T.rapidKernel_integral_conjLieDerivative_mem_span E a G X ν k γ Y hk hG
  | zero =>
    have e : lieD Y (0 : GA E a → ℂ) = 0 := by
      funext g; simp [lieD, chart_zero]
    rw [e]; exact zero_mem _
  | add F G hF' hG' hF hG =>
    have e : lieD Y (F + G) = lieD Y F + lieD Y G := by
      funext g
      simp only [lieD, chart_add, Pi.add_apply]
      rw [fderiv_add (differentiableAt_one_of_mem hF' g) (differentiableAt_one_of_mem hG' g)]
      rfl
    rw [e]; exact add_mem hF hG
  | smul z F hF' hF =>
    have e : lieD Y (z • F) = z • lieD Y F := by
      funext g
      simp only [lieD, chart_smul, Pi.smul_apply]
      rw [fderiv_const_smul (differentiableAt_one_of_mem hF' g)]
      rfl
    rw [e]; exact Submodule.smul_mem _ z hF

theorem kSpan_le_Sm : kSpan E a ≤ Sm E a := GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable E a _ kSpan_diff kSpan_lie

theorem kSpan_decays_growth : ∀ F ∈ kSpan E a, GlobalTheory.ShortVecDecay.Decays F ∧ Growth F := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    exact ⟨GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator E a G X ν k γ hk hG.decays, GlobalTheory.T.moderateGrowth_rapidKernelOperator E a G X ν k γ hk hG.growth⟩
  | zero => exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩
  | add F G _ _ hF hG => exact ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  | smul z F _ hF => exact ⟨hF.1.smul z, hF.2.smul z⟩

theorem word_mem_kSpan (l : List (Lie E a)) (φ : Sm E a) (hφ : φ.1 ∈ kSpan E a) :
    (GlobalTheory.GLFin.word l φ).1 ∈ kSpan E a := by
  induction l with
  | nil => simpa [GlobalTheory.GLFin.word] using hφ
  | cons Y l ih => rw [word_cons]; exact kSpan_lie _ ih Y

theorem Good.kernel {G : GA E a → ℂ} (hG : Good G) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    Good (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) := by
  have hm : (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) ∈ kSpan E a :=
    Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, k, γ, G, hk, hG, rfl⟩
  exact ⟨kSpan_le_Sm hm, fun l => kSpan_decays_growth _ (word_mem_kSpan l _ hm)⟩

variable (E a) in

def goodSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Good F}
  add_mem' := Good.add
  zero_mem' := good_zero
  smul_mem' c _ h := h.smul c

theorem mspanR_le_goodSub {π : CuspSub E a} (hπ : π.IsUnitary) : GlobalTheory.JSW.mspanR π ≤ goodSub E a :=
  sInf_le ⟨fun φ hφ => good_of_mem hπ hφ, fun F hF h => GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate E a F h hF,
    fun F hF X _ ν _ k γ hk => Good.kernel (G := F) hF hk⟩

theorem norm_le_of_short_vector_mspanR : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  intro E _ _ _ a π hπ φ hφ l
  have hg : Good φ.1 := hφ.elim (good_of_mem hπ) fun h => mspanR_le_goodSub hπ h
  obtain ⟨h, hl⟩ := hg
  exact (hl l).1

end GlobalTheory.MSpanDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArchimedeanBumpIdealRowOrbitStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w a) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  first | (exact @GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (exact GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL) | (intros; apply GlobalTheory.BumpOrbit.exists_bump_ideal_rowGL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidueStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes → ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  first | exact @GlobalTheory.GeoTie.ReadExist.exists_isReading | exact GlobalTheory.GeoTie.ReadExist.exists_isReading | (intros; apply GlobalTheory.GeoTie.ReadExist.exists_isReading <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoefficientContinuousNormInvarianStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∀ γ g, F (ratGL E a γ * g) = F g) →
    Continuous (GlobalTheory.JSW.whit F) ∧ ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖ := by
  first | exact @GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | exact GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul | (intros; apply GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul <;> assumption)
end

