import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanAutomorphismConjugatesOfNumberFieldIndepende
section
namespace GlobalTheory.ConjSpan

theorem exists_ringEquiv_fix_ne (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : Transcendental ℚ z) : ∃ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) ∧ τ z ≠ z := by
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq (fun q => by simp)
  have hzK : Transcendental K z := fun h => hz (h.restrictScalars ℚ)
  have hind : AlgebraicIndepOn K id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hzK
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let n : MvPolynomial B K ≃ₐ[K] MvPolynomial B K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => - MvPolynomial.X i)
      (MvPolynomial.aeval fun i => - MvPolynomial.X i) (by ext; simp) (by ext; simp)
  let e := hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv, ?_, ?_⟩
  · intro x
    have hx : σ x = algebraMap K ℂ x := rfl
    rw [hx, IsScalarTower.algebraMap_apply K (Algebra.adjoin K (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have h2 : IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X ⟨z, hzB'⟩))
        = hB.1.aevalEquiv (- MvPolynomial.X ⟨z, hzB'⟩) := by
      simp [e, n]
    rw [this, map_neg, map_neg, h1]
  rw [h2]
  intro h
  have hz0 : z = 0 := by linear_combination (-1/2 : ℂ) * h
  exact hz (hz0 ▸ isAlgebraic_zero)

theorem exists_eq_of_forall_fixed (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (z : ℂ)
    (hz : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (σ x) = σ x) → τ z = z) : ∃ c : K, σ c = z := by
  by_cases ha : IsAlgebraic ℚ z
  · have := GlobalTheory.FixedAlgebraic.mem_of_forall_ringEquiv_fixed σ.fieldRange z ha (fun τ hτ => hz τ
      (fun x => hτ _ ⟨x, rfl⟩))
    simpa using this
  · obtain ⟨τ, hτ, hne⟩ := exists_ringEquiv_fix_ne K σ z ha
    exact absurd (hz τ hτ) hne

theorem span_conj_eq_top : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (ι : Type) [Fintype ι]
    (e : ι → ℂ), (∀ c : ι → K, ∑ i, σ (c i) * e i = 0 → c = 0) →
    Submodule.span ℂ {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} = ⊤ := by
  intro K _ _ σ ι _ e he
  classical
  let R : Submodule ℂ (ι → ℂ) :=
    { carrier := {z | ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0}
      add_mem' := by
        intro a b ha hb φ hφ
        simp only [Set.mem_setOf_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib, ha φ hφ,
          hb φ hφ, add_zero]
      zero_mem' := by intro φ hφ; simp
      smul_mem' := by
        intro c a ha φ hφ
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
          ha φ hφ, mul_zero] }
  have hRmem : ∀ z, z ∈ R ↔ ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) → ∑ i, z i * φ (e i) = 0 :=
    fun z => Iff.rfl
  have key : ∀ n, ∀ z ∈ R, (Finset.univ.filter (fun i => z i ≠ 0)).card = n → z = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro z hz hcard
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    set z' := (z i0)⁻¹ • z with hz'
    have hz'R : z' ∈ R := R.smul_mem _ hz
    have hz'i0 : z' i0 = 1 := by simp [z', hi0]
    have hsupp : (Finset.univ.filter (fun i => z' i ≠ 0))
        = Finset.univ.filter (fun i => z i ≠ 0) := by
      ext i; simp [z', hi0]
    have hfix : ∀ ψ : ℂ ≃+* ℂ, (∀ x, ψ (σ x) = σ x) → ∀ i, ψ (z' i) = z' i := by
      intro ψ hψ
      have hw : (fun i => ψ (z' i)) - z' ∈ R := by
        refine R.sub_mem ?_ hz'R
        rw [hRmem]
        intro φ hφ
        have h1 := (hRmem z').1 hz'R (φ.trans ψ.symm) (by
          intro x
          rw [RingEquiv.trans_apply, hφ, RingEquiv.symm_apply_eq, hψ])
        have h2 := congrArg ψ h1
        simpa [map_sum, map_mul] using h2
      have hlt : (Finset.univ.filter (fun i => ((fun i => ψ (z' i)) - z') i ≠ 0)).card < n := by
        rw [← hcard, ← hsupp]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨i0, by simp [hz'i0], by simp [hz'i0]⟩
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, ne_eq] at hi ⊢
          intro h
          apply hi
          simp [h]
      have h3 := ih _ hlt _ hw rfl
      intro i
      have h4 := congrFun h3 i
      simpa [sub_eq_zero] using h4
    choose c hc using fun i => exists_eq_of_forall_fixed K σ (z' i) (fun τ hτ => hfix τ hτ i)
    have hc0 := he c (by
      have h5 := (hRmem z').1 hz'R (RingEquiv.refl ℂ) (fun x => rfl)
      simpa [hc] using h5)
    have h6 : z' i0 = 0 := by rw [← hc i0, hc0]; simp
    rw [hz'i0] at h6
    exact one_ne_zero h6
  by_contra hS
  obtain ⟨f, hf0, hf⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hS) inferInstance
  let z : ι → ℂ := fun i => f (fun j => if i = j then 1 else 0)
  have hzR : z ∈ R := by
    rw [hRmem]
    intro φ hφ
    have hmem : (fun i => φ (e i)) ∈ Submodule.span ℂ
        {v : ι → ℂ | ∃ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) ∧ v = fun i => φ (e i)} :=
      Submodule.subset_span ⟨φ, hφ, rfl⟩
    have h7 : f (fun i => φ (e i)) = 0 := by
      have h8 := Submodule.mem_map_of_mem (f := f) hmem
      rw [hf, Submodule.mem_bot] at h8
      exact h8
    rw [LinearMap.pi_apply_eq_sum_univ] at h7
    simpa [z, smul_eq_mul, mul_comm] using h7
  have hz0 := key _ z hzR rfl
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.pi_apply_eq_sum_univ]
  have : ∀ i, f (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hz0 i
  simp [this]

end GlobalTheory.ConjSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.SplitIntLift

theorem exists_lift {R K O : Type} [CommRing R] [CommRing K] [CommRing O] {n : ℕ} (S : Subring R) (π : R →+* K)
    (ι : O →+* K) (p : S) (hinj : ∀ x, π x = 0 → (p : R) * x = 0) (hl : ∀ o, ∃ s : S, π s = ι o)
    (h : GL (Fin n) O) (β g : GL (Fin n) R)
    (hg : (Matrix.GeneralLinearGroup.map π β)⁻¹ * Matrix.GeneralLinearGroup.map π g * Matrix.GeneralLinearGroup.map π β =
      Matrix.GeneralLinearGroup.map ι h) :
    ∃ (Y : Matrix (Fin n) (Fin n) S) (u : S), (∀ i j, π (Y i j) = ι (h.1 i j)) ∧ u * Y.det = p ∧
      (p : R) • g.1 = (p : R) • (β.1 * Y.map S.subtype * (β⁻¹).1) := by
  choose Y hY using fun i j => hl (h.1 i j)
  obtain ⟨u, hu⟩ := hl (h⁻¹).1.det
  have eY : (Matrix.of Y).map (π.comp S.subtype) = h.1.map ι := Matrix.ext hY
  refine ⟨Matrix.of Y, p * u, hY, Subtype.ext ?_, ?_⟩
  · have e1 : π ((Matrix.of Y).det : S) = ι h.1.det := by
      rw [RingHom.map_det ι, RingHom.mapMatrix_apply, ← eY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    have := hinj (u * ((Matrix.of Y).det : S) - 1) (by
      rw [map_sub, map_mul, hu, e1, ← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one, map_one, sub_self])
    push_cast
    linear_combination this
  · have e2 : Matrix.GeneralLinearGroup.map π g = Matrix.GeneralLinearGroup.map π β * Matrix.GeneralLinearGroup.map ι h *
        Matrix.GeneralLinearGroup.map π β⁻¹ := by
      rw [← hg, map_inv]; group
    have e3 : g.1.map π = (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1).map π := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
      exact (congrArg Units.val e2).trans (congrArg (fun z => β.1.map π * z * (β⁻¹).1.map π) eY.symm)
    ext i j
    have := hinj (g.1 i j - (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1) i j) (by
      rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e3 i) j)
    rw [mul_sub, sub_eq_zero] at this
    exact this

open GlobalTheory.LevSplit GlobalTheory.ParahoricLift Formalism.L2.NTheta GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7}

theorem rdE_finSw {v : FinPl D} (φ : SplitProj D v) (a : Formalism.L2.Theta.AE D) : rdE φ (finSw D a) = rdA φ a :=
  GlobalTheory.SplitProjChart.rdE_toEAf φ a

theorem finSw_surjective (z : Formalism.IndefR.Lev.EAf D) : ∃ w, finSw D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from (0, a)) ⊗ₜ x, rfl⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, RingHom.map_add _ _ _⟩

theorem cut_inj {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e)
    (x : Formalism.IndefR.Lev.EAf D) (hx : rdE φ x = 0) : finSw D e * x = 0 := by
  obtain ⟨w, rfl⟩ := finSw_surjective x
  rw [rdE_finSw] at hx
  rw [← RingHom.map_mul, ((GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.2.1 w).1 hx, RingHom.map_zero]

theorem int_lift {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e) (o : OI v) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, rdE φ s = algebraMap (OI v) (Fv D.host.F v) o := by
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  obtain ⟨a, ha⟩ := h1 (algebraMap (OI v) (Fv D.host.F v) o)
  refine ⟨⟨finSw D (e * a), swapAE_int ((h4 a).2 ⟨o, ha.symm⟩)⟩, ?_⟩
  show rdE φ (finSw D (e * a)) = _
  rw [rdE_finSw, RingHom.map_mul, he.2.2, one_mul, ha]

set_option maxHeartbeats 1000000 in

theorem lift_of_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  intro D V β Λ N hB P v φ e hP0 he0 red hred h κ hs hκ0
  have he : IsIdemAt e P := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ P hP0).2.2 e he0).1
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  have hg : (Matrix.GeneralLinearGroup.map (rdE φ) β)⁻¹ * Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) *
      Matrix.GeneralLinearGroup.map (rdE φ) β = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h := by
    rw [← hκ0]
    have : Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) =
        Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
      Units.ext (Matrix.ext fun i j => rdE_finSw φ (Formalism.L2.Theta.mt V κ i j))
    rw [this]
    rfl
  obtain ⟨Y, u, hY, hu', hκ⟩ := exists_lift (Formalism.L2.Herm.intAf D.host.F D.host.E) (rdE φ)
    (algebraMap (OI v) (Fv D.host.F v)) p (fun x hx => hp ▸ cut_inj he0 x hx) (int_lift he0) h β (finE V κ) hg
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨(T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ]
    refine Matrix.ext fun i j => ?_
    obtain ⟨hi, hr⟩ := hred (Y i j) (Y i j).2
    exact hr.symm.trans (congrArg red (Subtype.ext (hY i j)))
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

end GlobalTheory.DownLift.SplitIntLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem symplO_nsmul_left_eq (S T : HSp D) (k : ℕ) (l x : WO S T) :
    symplO S T (k • l) x = symplO S T l (k • x) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, GlobalTheory.PlaceModel.symplO_zero_left, GlobalTheory.PlaceModel.symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, ih]

theorem coef_isSBHalf_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf
  classical
  have ha' := GlobalTheory.SplitScalar.isSplitIdem_conj ha
  have hd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hstc : ∀ u ∈ latH S T ΛS ΛT, cA D a • u ∈ latH S T ΛS ΛT := fun u hu =>
    GlobalTheory.SplitScalar.idem_smul_mem ha'.1 u hu
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  have hinv : ∀ u ∈ latH S T ΛS ΛT, heisO ψ S T (k • u) f = f := fun u hu =>
    hUf _ (hkU u hu) (GlobalTheory.SplitScalar.latO_fin ((latH S T ΛS ΛT).nsmul_mem hu k))
  have hsupp : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT := by
    intro ℓ hℓ x hx hne
    by_contra hn
    obtain ⟨l, hl, hlh, hlne⟩ := GlobalTheory.SplitScalar.exists_dual_half ha hd hstc
      (GlobalTheory.SplitScalar.isHalf_nsmul hx k) hn
    have h1 := hℓ (k • l) (GlobalTheory.SplitScalar.isHalf_nsmul hlh k) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x)
    rw [GlobalTheory.SplitScalar.heisO_comm, hinv l hl, map_smul, smul_eq_mul, symplO_nsmul_left_eq] at h1
    apply hlne
    have h2 : (ψ (symplO S T l (k • x)) - 1) * ℓ (heisO ψ S T x f) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  have hcoef : ∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f) := by
    intro ℓ hℓ
    refine ⟨fun t ht => ?_, k, hk, fun u hu huh t => ?_, fun t ht => ?_⟩
    · by_contra hn
      exact ht (by simp only [coef, if_neg hn])
    · by_cases htt : IsHalf a t
      · have h2 : IsHalf a (t + k • u) := GlobalTheory.SplitScalar.isHalf_add htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
        simp only [coef, if_pos htt, if_pos h2]
        rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
          (GlobalTheory.SplitScalar.half_orth ha htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu]
      · have h2 : ¬ IsHalf a (t + k • u) := fun h => htt (by
          have := GlobalTheory.SplitScalar.isHalf_sub h (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
          rwa [add_sub_cancel_right] at this)
        simp only [coef, if_neg htt, if_neg h2]
    · have htt : IsHalf a t := by
        by_contra hn
        exact ht (by simp only [coef, if_neg hn])
      refine hsupp ℓ hℓ t htt ?_
      simpa only [coef, if_pos htt] using ht
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.DiagLiftFix.half_finite_mod (S := S) (T := T) hS.1.fg hT.1.fg ha.1 (k * k)
    (Nat.mul_pos hk hk)
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk x, ← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hP : ((fun t : WO S T => k • t) ⁻¹' R).Finite := hR.preimage tf.injOn
  refine ⟨⟨k, hk, fun u hu _ => hinv u hu, hsupp⟩, hcoef, hP.toFinset.filter (fun x => IsHalf a x),
    fun x hx => (Finset.mem_filter.1 hx).2, fun x hx => ?_⟩
  by_cases hkx : k • x ∈ latH S T ΛS ΛT
  · right
    obtain ⟨r, hr, u, hu, e⟩ := hRm (k • x)
      ⟨hkx, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_nsmul hx k)⟩
    have huh : IsHalf a u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2
    have hxu : IsHalf a (x - k • u) := GlobalTheory.SplitScalar.isHalf_sub hx (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
    refine ⟨x - k • u, Finset.mem_filter.2 ⟨hP.mem_toFinset.2 ?_, hxu⟩, ?_⟩
    · show k • (x - k • u) ∈ R
      rwa [smul_sub, e, smul_smul, add_sub_cancel_right]
    · conv_lhs => rw [show x = (x - k • u) + k • u by abel]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
        (GlobalTheory.SplitScalar.half_orth ha hxu (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu.1]
  · left
    intro ℓ hℓ
    by_contra hne
    exact hkx (hsupp ℓ hℓ x hx hne)

end GlobalTheory.DownLift.SplitCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorSchroedingerImageAtLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.BadPlace

set_option maxHeartbeats 2000000 in

theorem vec_read_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (P : Pl D.host.E), P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ k, SuppF (Wc D i) f k → ∃ (ea : AE D) (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) (c : ℂ), IsIdemSum ea (R.Pg ∪ R.Q t) ∧ IsSplitIdem D e ∧ e * ea = e ∧ f = e + cA D e ∧ IsStdChar D R.ψ (-1) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ IsLatVac (heisO R.ψ (Vc D i) (Wc D i)) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (R.vacP i) ∧ IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) 1 (R.vacP i) Tm ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) ∧ IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) ∧ R.vP i t = Tm (datP R i t ea) ∧ R.ωP i t (1, k) (R.vP i t) = c • Tm (fun x => datP R i t ea (actO (Vc D i) (Wc D i) 1 k⁻¹ x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t P hP e f hPI k hk
  obtain ⟨⟨hψ, hvac⟩, ea, hIS, hth⟩ := hL.thP.vP i t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hvP : R.vP i t = Tm (datP R i t ea) := hall Tm hTm
  have lV := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βV i)
  have lW := GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hL.lev.βW i)
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lV
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) := GlobalTheory.AdTh.RecPair.selfDual_of_coe lW
  have hIS' := hIS
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := hIS'
  have hPm : P ∈ R.Pg ∪ R.Q t := Finset.mem_union.2 hP
  obtain ⟨rfl, rfl⟩ := GlobalTheory.Hk3.SplitMatch.idem_unique (hes P hPm) hPI
  have h1 : ∀ PP ∈ R.Pg ∪ R.Q t, IsSplitIdem D (es PP) := fun PP hPP => (hes PP hPP).1
  have h2 : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ QQ ∈ R.Pg ∪ R.Q t, QQ ≠ PP → es PP * es QQ = 0 := by
    intro PP hPP QQ hQQ hne
    refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP) (h1 QQ hQQ)).resolve_left fun h => hne ?_
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [(hes PP hPP).2 x hx, (hes QQ hQQ).2 x hx, h]
  have hee : es P * ea = es P := by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hPm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hIS).conj
  have hinf : infPart D (cA D ea) = 0 := ho.infPart_eq
  have hSB : IsSBHalf (cA D ea) (latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) fun _ => True) (datP R i t ea) :=
    GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      (R.Pg ∪ R.Q t) (fun y => omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr R.Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr (R.Q t) _ (R.xiR t) _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)]
  have hSB2 := GlobalTheory.SplitLinear.isSBHalf_actO hSV.1 hSW.1 1 k⁻¹ hSB
  have hcc : cA D ea * cA D (cA D ea) = 0 := by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, hc]
  have ha : cA D ea * cA D ea = cA D ea := ho.idem
  have r1 : cA D ea * cA D (es P) = cA D (es P) := by rw [← map_mul, mul_comm, hee]
  have r2 : ea * cA D (es P) = 0 := by
    have e1 : cA D (es P) = cA D (es P) * cA D ea := by rw [← map_mul, hee]
    rw [e1, ← mul_assoc, mul_comm ea, mul_assoc, hc, mul_zero]
  have r3 : cA D ea * es P = 0 := by
    have := congrArg (cA D) r2
    rwa [map_mul, GlobalTheory.SplitOnto.cA_cA, map_zero] at this
  have r4 : ea * es P = es P := by rw [mul_comm, hee]
  have key : (cA D ea + cA D (cA D ea)) * (es P + cA D (es P)) = es P + cA D (es P) := by
    rw [GlobalTheory.SplitOnto.cA_cA]
    linear_combination r1 + r2 + r3 + r4
  have hsupp : SuppAt (cA D ea) (Wc D i) k := fun a b => by
    rw [← hk a b, ← mul_assoc, key]
  have hLaw := GlobalTheory.SplitLinear.law_orth (hF i t).datum hSV hSW ho hcc hvac.theta hvac.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one _ _) hsupp (GlobalTheory.VecInv.isDetAt_detAt _ ha _ 1) (GlobalTheory.VecInv.isDetAt_detAt _ ha _ k)
  have hω := hLaw _ hSB
  rw [← hvP] at hω
  simp only [inv_one] at hω
  exact ⟨ea, Tm, _, hIS, (hes P hPm).1, hee, rfl, hψ, hSV, hSW, hvac.theta, hvac.lat, hTm, hSB, hSB2, hvP, hω⟩

end GlobalTheory.BadPlace

end
end

