import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZero
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcZero

theorem eq_of_hcVal_eq_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν μ : Fin N → ℕ)
    (hν : Antitone ν) (hμ : Antitone μ) (hc : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩)
    (hv : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) : μ = ν := by
  have hZ : ∀ j, hcVal ℤ (fun i => (μ i : ℤ)) j = hcVal ℤ (fun i => (ν i : ℤ)) j := by
    intro j
    apply Int.cast_injective (α := k)
    have h1 := hcVal_map (Int.castRingHom k) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom k) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [← h1, ← h2]
    exact hv j
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (∑ i, ν i + N)
  haveI := Fact.mk hp
  apply eq_of_hcVal_eq p hp (ZMod p) N ν μ hν hμ
  · intro h
    refine ⟨(hc h).1, (hc h).2, ?_⟩
    have : ν ⟨0, h⟩ ≤ ∑ i, ν i := Finset.single_le_sum (fun i _ => Nat.zero_le (ν i)) (Finset.mem_univ _)
    omega
  · intro j
    have h1 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (μ i : ℤ)) j
    have h2 := hcVal_map (Int.castRingHom (ZMod p)) (fun i => (ν i : ℤ)) j
    simp only [eq_intCast, Int.cast_natCast] at h1 h2
    rw [h1, h2, hZ j]

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.map φ (rowAct R (n := N) g f) = rowAct S (n := N) (g.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum, Matrix.map_apply]

theorem map_mem_span_map {S A : Type} [CommRing S] [CommRing A] (ψ : S →+* A) {σ : Type}
    (X : Set (MvPolynomial σ S)) (P : MvPolynomial σ S) (hP : P ∈ Submodule.span S X) :
    MvPolynomial.map ψ P ∈ Submodule.span A (MvPolynomial.map ψ '' X) := by
  induction hP using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem isGLSubmodule_of_stable (k : Type) [Field k] [Infinite k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k))
    (hG : ∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) : GlobalTheory.Published.IsGLSubmodule k N lam M := by
  intro A _ _ g f hf
  let S := MvPolynomial (Fin N × Fin N) k
  let Y : Matrix (Fin N) (Fin N) S := Matrix.mvPolynomialX (Fin N) (Fin N) k
  let P : MvPolynomial (Fin N × Fin N) S :=
    rowAct S (n := N) Y.transpose (MvPolynomial.map (algebraMap k S) f)
  have hP : P ∈ Submodule.span S (MvPolynomial.map (algebraMap k S) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    refine GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero k _ _ M Y.det (Matrix.det_mvPolynomialX_ne_zero _ _) P ?_
    intro y hy
    let m0 : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => y (i, j)
    have hm0 : Y.map (MvPolynomial.eval y) = m0 := by
      ext i j; simp [Y, m0, Matrix.mvPolynomialX]
    have hdet : m0.det ≠ 0 := by
      rw [← hm0]; rw [RingHom.map_det] at hy; exact hy
    let g0 : GL (Fin N) k := Matrix.nonsingInvUnit m0 (isUnit_iff_ne_zero.mpr hdet)
    have h1 := hG g0 f hf
    have hu : detPow k N g0 lam.detShift ≠ 0 := Units.ne_zero _
    rw [sqAct, Submodule.smul_mem_iff M hu] at h1
    have e1 : MvPolynomial.map (MvPolynomial.eval y) P = rowAct k (n := N) (m0.transpose) f := by
      simp only [P]
      rw [map_rowAct_eq, MvPolynomial.map_map]
      have : (MvPolynomial.eval y).comp (algebraMap k S) = RingHom.id k := by
        ext a; simp [S]
      rw [this, MvPolynomial.map_id, Matrix.transpose_map, hm0]
    rw [e1]
    exact h1
  let ψ : S →+* A := MvPolynomial.eval₂Hom (algebraMap k A) fun v => (g : Matrix (Fin N) (Fin N) A) v.1 v.2
  have e2 : MvPolynomial.map ψ P =
      rowAct A (n := N) (g : Matrix (Fin N) (Fin N) A).transpose (MvPolynomial.map (algebraMap k A) f) := by
    simp only [P]
    rw [map_rowAct_eq, MvPolynomial.map_map]
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    have h4 : (Y.transpose).map ψ = (g : Matrix (Fin N) (Fin N) A).transpose := by
      ext i j
      simp only [Y, ψ, Matrix.mvPolynomialX, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom]
      exact MvPolynomial.eval₂_X _ _ _
    rw [h3, h4]
  have h5 := map_mem_span_map ψ _ P hP
  rw [Set.image_image] at h5
  have h6 : (fun x : MvPolynomial (Fin N × Fin N) k => MvPolynomial.map ψ (MvPolynomial.map (algebraMap k S) x)) =
      ⇑(MvPolynomial.map (σ := Fin N × Fin N) (algebraMap k A)) := by
    have h3 : ψ.comp (algebraMap k S) = algebraMap k A := by
      ext a; simp [ψ, S]
    funext x
    rw [MvPolynomial.map_map, h3]
  rw [h6, e2] at h5
  rw [sqAct]
  exact Submodule.smul_mem _ _ h5

end GlobalTheory.AlcZero

namespace GlobalTheory.AlcZero

theorem hw_mem_of_lt_charZero (k : Type) [Field k] [CharZero k] (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν)
    (hlast : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0)
    (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : Good M) (hM' : Good M') (hlt : M < M')
    (hle : M' ≤ dualWeyl k N N ν) : hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  have dom := GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ v hvw
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).1
  have hhw := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := GlobalTheory.T.traceRowOperatorPower_dualWeyl_field_smul k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by
    rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ := by
    intro h
    refine ⟨hlast h, ?_⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := eq_of_hcVal_eq_charZero k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := GlobalTheory.T.dualWeyl_highestWeight_space_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

theorem nablaSq_simple_charZero : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)),
    M ≤ nablaSq k N lam → (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) →
      M = ⊥ ∨ M = nablaSq k N lam := by
  intro k _ _ N lam M hM hG
  haveI : Infinite k := Infinite.of_injective _ Nat.cast_injective
  have hN := factNatW N lam
  by_contra hc
  push_neg at hc
  have hMg : Good M := good_of_isGLSubmodule k N lam M (isGLSubmodule_of_stable k N lam M hG)
  have key := hw_mem_of_lt_charZero k N lam.natW hN.1 hN.2.2
  have h1 := (key ⊥ M (good_top_bot k N N).2 hMg (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) hMg (good_nablaSq k N lam) (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.AlcZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) := by
  first | exact @GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | exact GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | (intros; apply GlobalTheory.SplitExConj.exists_splitPlace_conj_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeightStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_model_of_algWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  first | exact @GlobalTheory.AutQuot.Model.exists_model | exact GlobalTheory.AutQuot.Model.exists_model | (intros; apply GlobalTheory.AutQuot.Model.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HorizPt

def strHom {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top

theorem fromSpec_str {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (strHom q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem charZero {X : Scheme.{0}} (q : X ⟶ Sp ℤ) [Flat q] {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁
  have h₃ : (algebraMap ℤ Γ(X, U)).Flat := by
    rwa [Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]
  have := RingHom.flat_algebraMap_iff.1 h₃
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  intro F _ _ Y N W z g hz hg hzg
  have := N.ar.isIntegral
  have := N.ar.flat
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(N.X, U) := charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(N.X, U) := (strHom N.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(N.X, U) :=
    RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(N.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ N.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ N.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := N.pb.lift_fst _ _ hw
  refine ⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

end GlobalTheory.TrueGeo.HorizPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TwistAny

open Formalism.L2.NR

theorem exists_isRepOf_tw : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    rw [HChar.loc_mul, hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := rfl
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.TwistAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  first | exact @GlobalTheory.Mem.Col2.HAt.dn_move_exists | exact GlobalTheory.Mem.Col2.HAt.dn_move_exists | (intros; apply GlobalTheory.Mem.Col2.HAt.dn_move_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelGroup_with_character_at_type_places : ∀ (D : D7) (T : TwR D.LL0 D.nd) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ)
    (QP DP : Finset (PlE D.host)) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)),
    (∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (P' ∈ QP ∨ P' ∈ DP ∨ ∃ kv, P' = NX.pG D kv) →
      (sp P).v = (sp P').v → P = P') →
    (∀ P ∈ QP, P ∉ DP) → (∀ kv, NX.pG D kv ∉ QP ∧ NX.pG D kv ∉ DP) → (∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv') →
    QP ⊆ Q → DP ⊆ T.pD i →
    (∀ P ∈ QP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal ψ P 1 (u * u') = NX.tameVal ψ P 1 u * NX.tameVal ψ P 1 u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal ψ P 1 u = NX.tameVal ψ P 1 u') →
    (∀ P ∈ DP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) (u * u') =
          NX.tameVal (T.delta i) P (if b then 1 else -1) u * NX.tameVal (T.delta i) P (if b then 1 else -1) u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) u = NX.tameVal (T.delta i) P (if b then 1 else -1) u') →
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* (FractionRing (T.Ok i k))ˣ),
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      NX.HypOutsideF J χ (badVT D T i Q) ∧
      (∀ κ : GAf D.host.E D.R.nV, κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV ∧
        (∀ kv, NX.InLevG (sp (NX.pG D kv)).v D.R.r (NX.locM (sp (NX.pG D kv)) κ)) ∧
        (∀ P ∈ QP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ)) ∧
        (∀ P ∈ DP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ))) ∧
      ∀ κ (h : κ ∈ J), ((χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ)) *
        (∏ P ∈ QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) *
        (∏ P ∈ DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
          (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) := by
  first | exact @GlobalTheory.LevGChar.levGroup_exists | exact GlobalTheory.LevGChar.levGroup_exists | (intros; apply GlobalTheory.LevGChar.levGroup_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocCompSplit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem exists_locComp_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsAdmissible σ.ρ ∧ π.IsLocComp w σ ∧ (IsUnramU π.V w ↔ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w n)) := by
  intro E _ _ _ n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hsym : ∀ x : locU n w, e.symm (cLoc w (x : UA E n)) = x := fun x => by
    rw [← he, e.symm_apply_apply]
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) σ₀.V :=
    σ₀.ρ.comp e.symm.toMulEquiv.toMonoidHom
  have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
  let σ : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
    { V := σ₀.V
      ρ := ρ
      smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
      irred := GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ₀.ρ e.symm.toMulEquiv σ₀.irred }
  have hf' : ∀ (x : locU n w) v, f (σ₀.ρ x v) = RU E n x (f v) := hf
  refine ⟨σ, GlobalTheory.CuspMult.isAdmissible_comp_equiv σ₀.ρ e.symm hadm, ⟨σ.irred, f, hf0, hfm, fun x v => ?_⟩, ?_, ?_⟩
  · change f (ρ (cLoc w (x : UA E n)) v) = _
    rw [hρ, hsym, hf']
  · rintro ⟨φ, hφ, h0, hK⟩
    let F : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hsup := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ₀.V σ₀.V π.rep (locU n w).subtype σ₀.ρ σ₀.ρ
      π.isIrreducible_rep σ₀.irred σ₀.irred (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ₀.ρ σ₀.irred
      (fun h : σ₀.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
      (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
      {k | cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w n} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hK k k.2 hk))
      (hsup ▸ Submodule.mem_top)
    intro hb
    have hmem : v ∈ fixed ρ (GlobalTheory.LFun.KGL w n) := fun g => by
      have h1 : σ₀.ρ (e.symm g.1) v = v := hv _ (by
        have h2 : cLoc w ((e.symm g.1 : locU n w) : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
          rw [hcl]
          exact g.2
        exact h2)
      simpa [hρ] using h1
    have hb' : fixed ρ (GlobalTheory.LFun.KGL w n) = ⊥ := hb
    rw [hb'] at hmem
    exact hv0 ((Submodule.mem_bot _).1 hmem)
  · intro hsph
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hinj : Function.Injective f := by
      have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ₀.irred).2 (LinearMap.ker f) (fun g u hu => by
        rw [LinearMap.mem_ker] at hu ⊢
        rw [hf', hu, map_zero])
      rcases hk with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · exact absurd (LinearMap.ker_eq_top.1 h) hf0
    refine ⟨f v, hfm v, fun h => hv0 (hinj (h.trans (map_zero f).symm)), fun x hx hk => ?_⟩
    have h1 : σ₀.ρ (⟨x, hx⟩ : locU n w) v = v := by
      have h2 : ρ (cLoc w x) v = v := by simpa using hv ⟨_, hk⟩
      rwa [hρ, hsym (⟨x, hx⟩ : locU n w)] at h2
    have h3 := hf' ⟨x, hx⟩ v
    rw [h1] at h3
    exact h3.symm

end GlobalTheory.DefU
end
end

