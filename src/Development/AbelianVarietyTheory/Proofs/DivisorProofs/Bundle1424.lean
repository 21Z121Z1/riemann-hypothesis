import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOne
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem coneChain_step_bounds {a : ℕ} {t ρ K : ℝ} (ht : 0 < t) (hKt : t⁻¹ ≤ K) (hK0 : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hup : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hdown : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ k : ℕ, ∀ i j : Fin a, (j : ℕ) = i + k → r j ≤ K ^ k * r i ∧ r i ≤ ρ ^ k * r j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by simpa using hij)
    subst hji
    simp
  | succ k ih =>
    intro i j hij
    have hja := j.isLt
    have hk : (i : ℕ) + k < a := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hk⟩ rfl
    have hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have hu := hup _ j hmj
    have hd := hdown _ j hmj
    set m : Fin a := ⟨(i : ℕ) + k, hk⟩
    have hrj : r j ≤ t⁻¹ * r m := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    constructor
    · calc r j ≤ t⁻¹ * r m := hrj
        _ ≤ K * r m := mul_le_mul_of_nonneg_right hKt (hr m).le
        _ ≤ K * (K ^ k * r i) := mul_le_mul_of_nonneg_left h1.1 hK0
        _ = K ^ (k + 1) * r i := by ring
    · calc r i ≤ ρ ^ k * r m := h1.2
        _ ≤ ρ ^ k * (ρ * r j) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) * r j := by ring

theorem coneCoord_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  intro a t ht
  obtain ⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K := ⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K ^ a, one_le_pow₀ hK1, ?_⟩
  intro r ρ hr hup hprod hρ hdown i
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hC0 : 0 ≤ K ^ a * ρ ^ a := mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  have step := coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown
  have pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q := by
    intro p q
    rcases le_total (q : ℕ) p with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := p.isLt; omega
      calc r p ≤ K ^ k * r q := (step k q p hk).1
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc K ^ k ≤ K ^ a := pow_le_pow_right₀ hK1 hka
            _ = K ^ a * 1 := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ) (pow_nonneg hK0 _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := q.isLt; omega
      calc r p ≤ ρ ^ k * r q := (step k p q hk).2
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc ρ ^ k ≤ ρ ^ a := pow_le_pow_right₀ hρ hka
            _ = 1 * ρ ^ a := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (pow_nonneg hρ0 _)
  have hne : (Finset.univ : Finset (Fin a)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have ex_le : ∃ j, r j ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r)
      (fun _ _ => one_pos) (fun j _ => hcon j) hne
    simp [hprod] at this
  have ex_ge : ∃ j, 1 ≤ r j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ))
      (fun j _ => hr j) (fun j _ => hcon j) hne
    simp [hprod] at this
  obtain ⟨j, hj⟩ := ex_le
  obtain ⟨l, hl⟩ := ex_ge
  constructor
  · calc r i ≤ K ^ a * ρ ^ a * r j := pair i j
      _ ≤ K ^ a * ρ ^ a * 1 := mul_le_mul_of_nonneg_left hj hC0
      _ = K ^ a * ρ ^ a := by ring
  · rw [inv_eq_one_div, div_le_iff₀ (hr i)]
    have := pair l i
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCoeffOfSeparating
section
namespace GlobalTheory.ContinuousRepresentationCoefficients

theorem continuous_coeff_of_separating {X V ι : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (L : ι → V →ₗ[ℂ] ℂ)
    (hL : ∀ v, (∀ i, L i v = 0) → v = 0) (f : X → V) (hf : ∀ i, Continuous fun x => L i (f x))
    (ℓ : Module.Dual ℂ V) : Continuous fun x => ℓ (f x) := by
  have hmem : ℓ ∈ Submodule.span ℂ (Set.range L) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have h0 : v = 0 := hL v fun i => by
      simpa using (Submodule.mem_iInf _).1 hv i
    simp [h0]
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => simpa using continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact (continuous_const (y := c)).mul hx

theorem continuous_translate {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (φ : GlobalTheory.CuspRep.Sm E a) (g : GlobalTheory.CuspRep.GA E a) :
    Continuous fun k : GlobalTheory.CuspRep.Kinf E a =>
      ((GlobalTheory.CuspRep.cptRep E a k φ : GlobalTheory.CuspRep.Sm E a) : GlobalTheory.CuspRep.GA E a → ℂ) g := by
  have h1 : ContinuousOn (GlobalTheory.CuspRep.chart φ.1 g) (GlobalTheory.CuspRep.invSet E a) :=
    (φ.2 g).continuousOn
  have hu : ∀ k : GlobalTheory.CuspRep.Kinf E a,
      IsUnit (Matrix.of (k.1 : GlobalTheory.CuspRep.Lie E a)) := fun k => (Unitary.toUnits k).isUnit
  have h2 : Continuous fun k : GlobalTheory.CuspRep.Kinf E a => (k.1 : GlobalTheory.CuspRep.Lie E a) :=
    continuous_subtype_val
  have h3 := h1.comp_continuous h2 hu
  refine h3.congr fun k => ?_
  have h4 : (hu k).unit = Unitary.toUnits k := Units.ext rfl
  show GlobalTheory.CuspRep.chart φ.1 g (k.1 : GlobalTheory.CuspRep.Lie E a) = _
  unfold GlobalTheory.CuspRep.chart
  rw [dif_pos (hu k), h4]
  rfl

theorem isContRep_sub {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E a))
    (hW : ∀ (k : GlobalTheory.CuspRep.Kinf E a), ∀ w ∈ W, GlobalTheory.CuspRep.cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] :
    GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (GlobalTheory.CuspRep.cptRep E a) W hW) := by
  intro ℓ w
  refine continuous_coeff_of_separating
    (fun g : GlobalTheory.CuspRep.GA E a =>
      (LinearMap.proj g : (GlobalTheory.CuspRep.GA E a → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (GlobalTheory.CuspRep.Sm E a).subtype ∘ₗ W.subtype) ?_ _ ?_ ℓ
  · intro v hv
    exact Subtype.ext (Subtype.ext (funext hv))
  · intro g
    exact continuous_translate w.1 g

end GlobalTheory.ContinuousRepresentationCoefficients
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (GlobalTheory.T.integralCrystallineBlockData_of_reductionPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMultiplicityCarriers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.SpanW

theorem iSup_wp3_eq_range_eH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → ∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hS hGS hCD hME hcar i
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk2.irr
  obtain ⟨h, -, -, -, hsum, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF i
  rw [← hsum]
  apply le_antisymm
  · refine iSup_le fun p => iSup₂_le fun c _ => ?_
    rw [hWc]
    exact le_iSup (fun c => Wcc R.toRealDat R.SF i c) c
  · refine iSup_le fun c => ?_
    by_cases h0 : Wcc R.toRealDat R.SF i c = ⊥
    · rw [h0]; exact bot_le
    · have hE0 : EEc R.toRealDat R.SF c ≠ ⊥ :=
        GlobalTheory.T.eigensystem_goodForms_thetaTarget_occurs_on_rows R.toRealDat F.lv2 hOk2 hCore hS hGS hCD hME R.SF hSF i c h0
      obtain ⟨p, hp⟩ := hcar c (by rw [hE]; exact hE0)
      rw [← hWc]
      exact le_trans (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp) (le_iSup (fun p => R.Wp3 i p) p)

end GlobalTheory.SpanW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfinite
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatSplit

theorem ratU_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n,
    ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧
      ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  intro E _ _ _ n γ hγ
  obtain ⟨g0, hg0⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈ (ratGL E n).range)
  have hval : γ.1.val = g0.val.map (algebraMap E (Ad E)) := by rw [← hg0]; rfl

  have hU : g0 ∈ UE E n := by
    have h2 : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
    show cT (IsCMField.complexConj E).toRingEquiv.toRingHom g0.val * 1 * g0.val = 1
    have hinj : Function.Injective (algebraMap E (Ad E)) := by
      intro x y hxy
      have τ := (Classical.arbitrary (InfinitePlace E)).embedding
      exact τ.injective (by rw [← coord_algebraMap τ x, ← coord_algebraMap τ y, hxy])
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul,
      FinPtLoc.map_cT (algebraMap E (Ad E)) _ (conjAd E) (fun x => (conjAd_algebraMap x).symm),
      Matrix.map_one _ (map_zero _) (map_one _), ← hval, h2]
  refine ⟨⟨g0, hU⟩, ?_, ?_⟩
  · set a : finU E n := finPt ⟨g0, hU⟩ with ha
    have haval : ((a : UA E n) : GA E n) = finGL E n (ratF E n g0) := by
      rw [ha, FinPtLoc.finPt_eq]
    have hb : (a : UA E n)⁻¹ * γ ∈ infU E n := by
      show GeneralLinearGroup.map (pFin E) (((a : UA E n)⁻¹ * γ : UA E n) : GA E n) = 1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, haval, pFin_finGL, ← hg0]
      have : GeneralLinearGroup.map (pFin E) (ratGL E n g0) = ratF E n g0 := by
        apply Units.ext; ext i j; rfl
      rw [this, inv_mul_cancel]
    have hγs : γ = (a : UA E n) * ((⟨_, hb⟩ : infU E n) : UA E n) := by
      simp
    rw [hγs, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (γ.1.val i j)) = v.embedding (g0.val i j)
    rw [hval, Matrix.map_apply, coord_algebraMap]

end GlobalTheory.BCT.RatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameter
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section
namespace GlobalTheory.HoweD
open scoped Matrix
open GlobalTheory.RealLift.OneParam GlobalTheory.RealLift.CharTrace

theorem prod_charD {ι : Type} [Fintype ι] [DecidableEq ι] {R S : ι → ℕ} (χ : (∀ w, Mat (R w) (S w)) → ℂ)
    (hmul : ∀ g h : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → (∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)) →
      χ (g * h) = χ g * χ h)
    (hc : ContinuousOn χ {g | ∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)})
    (hne : ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g ≠ 0) :
    ∃ n : ι → ℤ, ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g = ∏ w, (g w).det ^ n w := by
  have upd : ∀ w (a : Mat (R w) (S w)), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) → ∀ v,
      (Function.update (1 : ∀ w, Mat (R w) (S w)) w a v)ᴴ * Jm (R v) (S v) * Function.update (1 : ∀ w, Mat (R w) (S w)) w a v = Jm (R v) (S v) := by
    intro w a ha v
    by_cases hv : v = w
    · subst hv; simpa using ha
    · rw [Function.update_of_ne hv]; exact mem_one
  have key : ∀ w, ∃ n : ℤ, ∀ a : Mat (R w) (S w), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) →
      χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a) = a.det ^ n := by
    intro w
    refine charUpq (R w) (S w) (fun a => χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a)) ?_ ?_ ?_
    · intro a b ha hb
      have e : Function.update (1 : ∀ w, Mat (R w) (S w)) w (a * b) =
          Function.update (1 : ∀ w, Mat (R w) (S w)) w a * Function.update (1 : ∀ w, Mat (R w) (S w)) w b := by
        funext v
        by_cases hv : v = w
        · subst hv; simp
        · simp [Function.update_of_ne hv]
      rw [e]
      exact hmul _ _ (upd w a ha) (upd w b hb)
    · exact hc.comp (show Continuous (Function.update (1 : ∀ w, Mat (R w) (S w)) w) from continuous_const.update w continuous_id).continuousOn
        fun a ha => upd w a ha
    · intro a ha; exact hne _ (upd w a ha)
  choose n hn using key
  refine ⟨n, fun g hg => ?_⟩
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (fun _ => mem_one) (fun _ => mem_one)
    rw [mul_one] at e
    have hz := hne 1 (fun _ => mem_one)
    exact mul_left_cancel₀ hz (e.symm.trans (mul_one _).symm)
  have pc : ∀ (s : Finset ι) v, (s.piecewise g 1 v)ᴴ * Jm (R v) (S v) * s.piecewise g 1 v = Jm (R v) (S v) := by
    intro s v
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hg v
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact mem_one
  have ind : ∀ s : Finset ι, χ (s.piecewise g 1) = ∏ w ∈ s, (g w).det ^ n w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      have e : (insert a s).piecewise g 1 = Function.update (1 : ∀ w, Mat (R w) (S w)) a (g a) * s.piecewise g 1 := by
        funext v
        by_cases hv : v = a
        · subst hv; simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hv, Function.update_of_ne hv]
      rw [e, hmul _ _ (upd a (g a) (hg a)) (pc s), hn a (g a) (hg a), ih, Finset.prod_insert ha]
  simpa using ind Finset.univ

theorem deriv_charD :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines σ J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC ν hmul hcont hne
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  set U : Set (∀ w : InfinitePlace F, Mat (R w) (S w)) := {h | ∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)} with hU
  set Λ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → Matrix β β (AE F E) :=
    fun h => 1 + liftM τ ξ (fun w => C w * h w * C' w - 1) with hΛ
  have Λπ : ∀ h w, (Λ h).map (piInf (τ w)) = C w * h w * C' w := fun h w => by
    rw [hΛ, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have Λat : ∀ h, At (evI F) (Λ h - 1) := fun h => by
    rw [hΛ, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have Λmul : ∀ h h', Λ (h * h') = Λ h * Λ h' := fun h h' => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : Λ h * Λ h' - Λ (h * h') = (Λ h - 1) * Λ h' + (Λ h' - 1) - (Λ (h * h') - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (Λat h) _) (Λat h')) (Λat _)
    · rw [Matrix.map_mul, Λπ, Λπ, Λπ, Pi.mul_apply]
      calc C w * h w * C' w * (C w * h' w * C' w) = C w * h w * (C' w * C w) * h' w * C' w := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have Λone : Λ 1 = 1 := eq_of_at hCM τ (Λat 1) fun w => by
    rw [Λπ, Pi.one_apply, Matrix.mul_one, hC' w, Matrix.map_one _ (map_zero _) (map_one _)]
  have ΛU : ∀ h ∈ U, (Λ h)ᵀ * J * (Λ h).map (cA σ) = J := fun h hh => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (Λ h)ᵀ * J * (Λ h).map (cA σ) - J =
          (Λ h - 1)ᵀ * J * (Λ h).map (cA σ) + J * (Λ h - 1).map (cA σ) := by
        have e1 : (Λ h - 1).map (cA σ) = (Λ h).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (Λat h)) _) _)
        (at_mul_left (at_map_cA σ (Λat h)) _)
    · have hc : ((Λ h).map (cA σ)).map (piInf (τ w)) = (C w * h w * C' w).map star := by
        rw [← Λπ h w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, Λπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unit (hC w).1 (hC' w) ((form_iff (h w)).1 (hh w))
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  set hinv : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ∀ w : InfinitePlace F, Mat (R w) (S w) :=
    fun h w => Jm (R w) (S w) * (h w)ᴴ * Jm (R w) (S w) with hhinv
  have inv_mul : ∀ h ∈ U, hinv h * h = 1 := fun h hh => by
    funext w
    rw [Pi.mul_apply, hhinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm (R w) (S w)) (h w), hh w,
      jm_mul_self, Pi.one_apply]
  have mul_inv : ∀ h ∈ U, h * hinv h = 1 := fun h hh => by
    funext w
    have := congrFun (inv_mul h hh) w
    rw [Pi.mul_apply, Pi.one_apply] at this ⊢
    exact mul_eq_one_comm.1 this
  have Λinv1 : ∀ h ∈ U, Λ h * Λ (hinv h) = 1 := fun h hh => by rw [← Λmul, mul_inv h hh, Λone]
  have Λinv2 : ∀ h ∈ U, Λ (hinv h) * Λ h = 1 := fun h hh => by rw [← Λmul, inv_mul h hh, Λone]
  let G : U → UG (cA σ) J := fun h => ⟨⟨Λ h, Λ (hinv h), Λinv1 h h.2, Λinv2 h h.2⟩, ΛU h h.2⟩
  have LevelValuationRings : ∀ h, At (evI F) (((G h).1 : Matrix β β (AE F E)) - 1) := fun h => Λat h
  have Gmul : ∀ h h' : U, ∀ hm : (h : ∀ w : InfinitePlace F, Mat (R w) (S w)) * h' ∈ U, G ⟨_, hm⟩ = G h * G h' :=
    fun h h' hm => Subtype.ext (Units.ext (Λmul h h'))
  have Λc : Continuous Λ := continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
    (((continuous_const.matrix_mul (continuous_apply w)).matrix_mul continuous_const).sub continuous_const)))
  have hinvc : Continuous hinv := continuous_pi fun w =>
    (continuous_const.matrix_mul (continuous_apply w).matrix_conjTranspose).matrix_mul continuous_const
  have Gc : Continuous G := by
    have hu : Continuous fun h : U => ((G h).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨Λc.comp continuous_subtype_val, (Λc.comp hinvc).comp continuous_subtype_val⟩
    exact hu.subtype_mk _
  classical
  let χ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ℂ := fun h => if hh : h ∈ U then ν (G ⟨h, hh⟩) else 0
  have χG : ∀ h : U, χ h = ν (G h) := fun h => by simp only [χ, dif_pos h.2]
  have memU : ∀ h h' : ∀ w : InfinitePlace F, Mat (R w) (S w), h ∈ U → h' ∈ U → h * h' ∈ U := fun h h' hh hh' w =>
    mem_mul (hh w) (hh' w)
  obtain ⟨n, hn⟩ := prod_charD (R := R) (S := S) χ
    (fun g h hg hh => by
      rw [χG ⟨g, hg⟩, χG ⟨h, hh⟩, χG ⟨g * h, memU g h hg hh⟩, Gmul ⟨g, hg⟩ ⟨h, hh⟩]
      exact hmul _ _ (LevelValuationRings _) (LevelValuationRings _))
    (by
      rw [continuousOn_iff_continuous_restrict]
      convert hcont.comp_continuous Gc LevelValuationRings using 1
      funext h
      exact χG h)
    (fun g hg => by rw [χG ⟨g, hg⟩]; exact hne _ (LevelValuationRings _))
  refine ⟨fun w => (n w : ℂ), fun γ hγ Y hY => ?_⟩
  set e : ℝ → ∀ w : InfinitePlace F, Mat (R w) (S w) := fun t w => NormedSpace.exp (t • Y w) with he
  have hγw : ∀ t w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = C w * e t w * C' w :=
    fun t w => by
      rw [he]; simp only
      rw [← hY t w, Matrix.mul_assoc, hC' w, Matrix.mul_one]
  have heU : ∀ t, e t ∈ U := fun t w => by
    rw [form_iff]
    set g := ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hg
    have hgU : gᵀ * (b • J.map (piInf (τ w))) * g.map star = b • J.map (piInf (τ w)) := by
      have hu : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))ᵀ * J *
          ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ) = J := (γ (Multiplicative.ofAdd t)).2
      have := congrArg (fun X => X.map (piInf (τ w))) hu
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have hc : (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ)).map (piInf (τ w)) = g.map star := by
        rw [hg, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [hc] at this
      rw [Matrix.mul_smul, Matrix.smul_mul, this]
    have hee : e t w = C' w * g * C w := by
      rw [hg, hγw, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have t1 : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC' w, Matrix.transpose_one]
    have t2 : (C w).map star * (C' w).map star = 1 := by
      rw [← map_star_mul, hC' w]; exact Matrix.map_one _ (star_zero _) (star_one _)
    rw [hee, ← (hC w).1]
    calc (C' w * g * C w)ᵀ * ((C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star) * (C' w * g * C w).map star
        = (C w)ᵀ * (gᵀ * (((C' w)ᵀ * (C w)ᵀ) * (b • J.map (piInf (τ w))) * ((C w).map star * (C' w).map star)) *
            g.map star) * (C w).map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, hgU]
  have hγe : ∀ t, γ (Multiplicative.ofAdd t) = G ⟨e t, heU t⟩ := fun t => by
    refine Subtype.ext (Units.ext (eq_of_at hCM τ ?_ fun w => ?_))
    · have e1 : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t) =
          (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) - (Λ (e t) - 1) := by abel
      show At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t))
      rw [e1]
      exact at_sub (hγ.2 _) (Λat _)
    · show ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = (Λ (e t)).map (piInf (τ w))
      rw [hγw, Λπ]
  have hval : ∀ t : ℝ, ν (γ (Multiplicative.ofAdd t)) =
      Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace) := fun t => by
    rw [hγe t, ← χG, hn _ (heU t), Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [he]; simp only
    rw [GlobalTheory.DetSqrtCover.det_exp, ← Complex.exp_int_mul, Matrix.trace_smul]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace))
      (∑ w, (n w : ℂ) * (Y w).trace) 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (∑ w, (n w : ℂ) * (Y w).trace)).cexp
    simpa using h0
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)

end GlobalTheory.HoweD
end
end

