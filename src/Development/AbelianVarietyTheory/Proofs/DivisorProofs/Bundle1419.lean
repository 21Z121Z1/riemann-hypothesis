import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjective
section
open scoped TensorProduct Matrix Classical

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

theorem polMap_index_injective (W Λ : Type) [Fintype W] :
    Function.Injective (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
  have key : ∀ (f : W → (Λ →₀ ℕ)) (w : W) (l : Λ),
      (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) (w, l) = f w l := by
    intro f w l
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply (Prod.mk_right_injective w) _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Prod.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (W × Λ) →₀ ℕ => F (w, l)) h

theorem polMap_tprod_monomial (W Λ : Type) [Fintype W] [DecidableEq W] (f : W → (Λ →₀ ℕ)) :
    polMap W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial Λ ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMap_injective (W Λ : Type) [Fintype W] [DecidableEq W] :
    Function.Injective (polMap W Λ) := by
  let B := Basis.piTensorProduct (fun _ : W => basisMonomials Λ ℂ)
  have hli : LinearIndependent ℂ (polMap W Λ ∘ B) := by
    have h := (basisMonomials (W × Λ) ℂ).linearIndependent.comp _ (polMap_index_injective W Λ)
    have e : polMap W Λ ∘ B = (basisMonomials (W × Λ) ℂ) ∘
        (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMap_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMap W Λ ∘ₗ Finsupp.linearCombination ℂ B = Finsupp.linearCombination ℂ (polMap W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometries
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTransport

section General

variable {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

theorem conv_map (j : G ≃ₜ* G') (μ : Measure G) (f g : G → ℂ) :
    GlobalTheory.AutomorphicL2Unitary.conv (μ.map j) (f ∘ j.symm) (g ∘ j.symm) = GlobalTheory.AutomorphicL2Unitary.conv μ f g ∘ j.symm := by
  funext y
  rw [show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl]
  simp only [GlobalTheory.AutomorphicL2Unitary.conv, Function.comp_apply]
  rw [integral_map_equiv]
  congr 1
  funext x
  change f (j.symm (j x)) * g (j.symm ((j x)⁻¹ * y)) = _
  rw [map_mul, map_inv, j.symm_apply_apply]

theorem typeIdem_map {Q Q' W : Type} [Group Q] [Group Q'] [AddCommGroup W] [Module ℂ W]
    (j : G ≃ₜ* G') (μ : Measure G) {K : Subgroup G} {K' : Subgroup G'} (hK : ∀ g, j g ∈ K' ↔ g ∈ K)
    (r : K →* Q) (r' : K' →* Q') (φ : Q' →* Q) (τ : Representation ℂ Q W)
    (hr : ∀ (k : K) (k' : K'), (k' : G') = j k → φ (r' k') = r k) :
    GlobalTheory.Orb.typeIdem (μ.map j) r' (τ.comp φ) = GlobalTheory.Orb.typeIdem μ r τ ∘ j.symm := by
  funext y
  have hv : (μ.map j).real K' = μ.real K := by
    rw [Measure.real, Measure.real, show (μ.map j) = μ.map j.toHomeomorph.toMeasurableEquiv from rfl,
      MeasurableEquiv.map_apply]
    congr 2
    ext x
    exact hK x
  have hy : ∀ y, y ∈ K' ↔ j.symm y ∈ K := fun y => by
    rw [← hK, j.apply_symm_apply]
  simp only [GlobalTheory.Orb.typeIdem, Function.comp_apply]
  by_cases hg : j.symm y ∈ K
  · rw [dif_pos ((hy y).2 hg), dif_pos hg, hv]
    simp only [Representation.character, MonoidHom.comp_apply,
      hr ⟨j.symm y, hg⟩ ⟨y, (hy y).2 hg⟩ (j.apply_symm_apply y).symm]
  · rw [dif_neg (mt (hy y).1 hg), dif_neg hg]

theorem isIrreducible_comp_mulEquiv {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  let e : Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        have h := U.apply_mem_toSubmodule (φ.symm g) hv
        simpa using h⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder

end General

def glCast {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] : GL (Fin n') k ≃* GL (Fin n) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (finCongr hr)).toMulEquiv

theorem glCast_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n') k) (a b : Fin n) :
    (glCast hr k g : Matrix (Fin n) (Fin n) k) a b = (g : Matrix (Fin n') (Fin n') k) (Fin.cast hr.symm a) (Fin.cast hr.symm b) :=
  rfl

theorem glCast_symm_apply {n n' : ℕ} (hr : n' = n) (k : Type) [CommRing k] (g : GL (Fin n) k) (a b : Fin n') :
    ((glCast hr k).symm g : Matrix (Fin n') (Fin n') k) a b = (g : Matrix (Fin n) (Fin n) k) (Fin.cast hr a) (Fin.cast hr b) :=
  rfl

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} {v : HeightOneSpectrum (𝓞 F)}
  (hr : n' = n) (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hK : ∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v)
  (s : SplitAt σ J L v) (s' : SplitAt σ J' L' v)
  (he : ∀ g (a b : Fin n'), (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr))
include he

include hK in

theorem mem_iwahori_iff (g : GLoc σ J v) : j g ∈ s'.iwahori ↔ g ∈ s.iwahori := by
  rw [s'.mem_iwahori, s.mem_iwahori, hK]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · have := h (a.cast hr.symm) (b.cast hr.symm) hab
    rwa [he, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_eq_self] at this
  · rw [he]
    exact h _ _ hab

theorem map_diag (t : Fin n → (Fv F v)ˣ) : j (s.diag t) = s'.diag fun i => t (i.cast hr) := by
  apply s'.equiv.injective
  ext a b
  rw [he]
  simp only [SplitAt.diag, ContinuousMulEquiv.apply_symm_apply, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply,
    Fin.cast_inj]

include hK in

theorem mem_iwahoriCoset_iff (t : Fin n → (Fv F v)ˣ) (g : GLoc σ J v) :
    j g ∈ s'.iwahoriCoset (fun i => t (i.cast hr)) ↔ g ∈ s.iwahoriCoset t := by
  simp only [SplitAt.iwahoriCoset, DoubleCoset.mem_doubleCoset, ← map_diag hr j s s' he]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨j.symm a, (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using ha), j.symm b,
      (mem_iwahori_iff hr j hK s s' he _).1 (by simpa using hb), j.injective ?_⟩
    simp [e, map_mul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨j a, (mem_iwahori_iff hr j hK s s' he _).2 ha, j b, (mem_iwahori_iff hr j hK s s' he _).2 hb, by
      simp [map_mul]⟩

include hK in
theorem cosetFn_transfer (t : Fin n → (Fv F v)ˣ) :
    s'.cosetFn (fun i => t (i.cast hr)) = s.cosetFn t ∘ j.symm := by
  funext y
  obtain ⟨g, rfl⟩ := j.surjective y
  change (s'.iwahoriCoset _).indicator 1 (j g) = (s.iwahoriCoset t).indicator 1 (j.symm (j g))
  rw [j.symm_apply_apply]
  by_cases h : g ∈ s.iwahoriCoset t
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_iwahoriCoset_iff hr j hK s s' he t g).2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (mem_iwahoriCoset_iff hr j hK s s' he t g).1 h)]

end Local

end GlobalTheory.LatTransport

namespace GlobalTheory.LatTransport

section Types

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n' : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
  {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (hr : n' = n)

def moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) : TypeData σ J' L' where
  S := T.S
  frame := fr
  W := T.W
  τ := fun v => (T.τ v).comp (glCast hr (ResF v.1)).toMonoidHom
  irred := fun v => isIrreducible_comp_mulEquiv _ _ (T.irred v)

theorem noFixed_moveTypes (T : TypeData σ J L) (fr : ∀ v : T.S, SplitAt σ J' L' v) (h : NoFixed T) :
    NoFixed (moveTypes hr T fr) := by
  refine ⟨h.1, fun a ha0 han => ?_⟩
  obtain ⟨v, hv⟩ := h.2 a ha0 (by omega)
  refine ⟨v, fun y hy => hv y fun g hg => ?_⟩
  have := hy ((glCast hr (ResF v.1)).symm g) (fun i k hik => ?_)
  · change T.τ v (glCast hr _ ((glCast hr _).symm g)) y = y at this
    rwa [MulEquiv.apply_symm_apply] at this
  · rw [glCast_symm_apply, hg _ _ hik]
    simp [Matrix.one_apply, Fin.cast_inj]

end Types

set_option maxHeartbeats 1000000 in

theorem isTestFin_transport : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  intro D V V' hr j hj
  have h := fun v => GlobalTheory.T.splitFrames_transport_localLatticeIsometry D V V' hr v (j v) (hj v)
  refine ⟨fun v g => (h v).1 g, fun T U => ?_⟩
  choose fr hfr1 hfr2 using fun v => (h v).2
  refine ⟨moveTypes hr T (fun v => fr v (T.frame v)), ⟨U.u, fr U.u U.frame, U.ϖ, U.unif⟩,
    noFixed_moveTypes hr T _, fun μf ff hf => ?_⟩
  obtain ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩ := hf
  have hid : ∀ v : T.S, (moveTypes hr T fun v => fr v (T.frame v)).idem (fun v => (μf v).map (j v)) v =
      T.idem μf v ∘ (j v).symm := fun v =>
    typeIdem_map (j v) (μf v) ((h v).1 ·) (T.frame v).red (fr v (T.frame v)).red (glCast hr (ResF v.1)).toMonoidHom
      (T.τ v) fun k k' e => Units.ext (Matrix.ext fun a b => by
        show (glCast hr (ResF v.1) ((fr v (T.frame v)).red k')).1 a b = ((T.frame v).red k).1 a b
        rw [glCast_apply, hfr2 v (T.frame v) k k' e]
        simp)
  refine ⟨hu, fun v => ?_, ⟨fun i => t (i.cast hr), ?_, ?_⟩,
    fun v hv hv' => comp_mem_SB (h3 v hv hv') (j v).symm.toHomeomorph, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h1 v
    refine ⟨φ ∘ (j v).symm, comp_mem_SB hφ (j v).symm.toHomeomorph, ?_⟩
    have e1 := conv_map (j v) (μf v) (conv (μf v) (T.idem μf v) φ) (T.idem μf v)
    have e2 := conv_map (j v) (μf v) (T.idem μf v) φ
    have e3 := (congrArg (fun X => conv ((μf v).map (j v)) X (T.idem μf v ∘ (j v).symm)) e2).trans e1
    rewrite [hid v]
    exact (congrArg (· ∘ (j v).symm) e).trans e3.symm
  · obtain ⟨a, ha, rfl⟩ := ht
    exact ⟨fun i => a (i.cast hr), fun x y hxy => ha hxy, rfl⟩
  · show ff U.u ∘ (j U.u).symm = _
    rw [h2]
    exact (cosetFn_transfer hr (j U.u) ((h U.u).1 ·) U.frame _ (hfr1 U.u U.frame) t).symm
  · exact ((IsTestFin.isFinFamily ⟨hu, h1, ⟨t, ht, h2⟩, h3, h4⟩).transfer j (.of_forall fun v g => (h v).1 g)).2

end GlobalTheory.LatTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

theorem withBot_lt_of_add_one_le_nat {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) :=
  withBot_lt_of_add_one_lt (lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self n))

theorem topSelf_pull_eq_zero_of_not_dominant : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver q → topologicalKrullDim X ≤ D → topologicalKrullDim Y ≤ D → ∀ (π : Y ⟶ X), π (genericPoint Y) ≠ genericPoint X → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = 0 := by
  intro k _ X Y _ _ p q D hq hX hY π hπ B hB
  letI := GlobalTheory.algebraΓOfHom q
  have hs : strHom k Y = q := GlobalTheory.strHom_eq (f := q) fun _ => rfl
  have hη : genericPoint X ∈ (closure ({π (genericPoint Y)} : Set X))ᶜ := fun h =>
    hπ (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := dim_closure_add_one_le (genericPoint_specializes (π (genericPoint Y)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint X} : Set X)) = topologicalKrullDim X := by
    rw [(genericPoint_spec X).def]
    exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  have h3 := withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hX))
  have h := interNum_pull_eq_zero k 0 D Y X (hs ▸ hq) (by rwa [Nat.zero_add]) π h3
    (fun i => i.elim0) (fun i => i.elim0) (fun _ => B) (fun _ => hB)
  rw [topSelf_def, ← interNum_comp_equiv k _ (fun _ => pull_isLB hB π)
    (Equiv.emptySum (Fin 0) (Fin D)), ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.PullVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositiveRealPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealPlaceNorms

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField NumberField.InfinitePlace.Completion

theorem aeval_mulVec_of_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (z : ℂ)
    (h : A *ᵥ v = z • v) (p : ℂ[X]) : (aeval A p) *ᵥ v = p.eval z • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    have hk : (A ^ k) *ᵥ v = z ^ k • v := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hk, smul_smul, eval_monomial]

theorem pos_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {v : Fin n → ℂ}
    (hv : v ≠ 0) {c : ℂ} (h : M *ᵥ v = c • v) : 0 < c := by
  have h1 := hM.dotProduct_mulVec_pos hv
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hv
  rw [Complex.lt_def] at h1 h2 ⊢
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at a1 a2 b1 b2 ⊢
  rw [← b2] at a1 a2
  have hi : c.im = 0 := by
    have : c.im * (star v ⬝ᵥ v).re = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right b1.ne'
  refine ⟨?_, hi.symm⟩
  rw [hi] at a1
  have : 0 < c.re * (star v ⬝ᵥ v).re := by linarith
  exact (pos_iff_pos_of_mul_pos this).2 b1

theorem map_aeval {E : Type} [Field E] {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X]) (τ : E →+* ℂ) :
    (aeval γ m).map τ = aeval (γ.map τ) (m.map τ) := by
  rw [← RingHom.mapMatrix_apply, aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

section Fld

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)

theorem pos_at_embedding {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X])
    (hpos : ∀ τ : E →+* ℂ, ((aeval γ m).map τ).PosDef) (hdvd : Q.1 ∣ γ.charpoly)
    (x : plus Q) (hx : (x : Fld Q) = AdjoinRoot.mk Q.1 m) (φ : plus Q →+* ℂ) : 0 < φ x := by
  letI : Algebra (plus Q) ℂ := φ.toAlgebra
  haveI : Module.Finite (plus Q) (Fld Q) :=
    Module.Finite.of_restrictScalars_finite (maximalRealSubfield E) (plus Q) (Fld Q)
  haveI : Module.IsTorsionFree (plus Q) ℂ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (plus Q) (Fld Q) := DivisionSemiring.to_moduleIsTorsionFree
  let ρ : Fld Q →ₐ[plus Q] ℂ := IsAlgClosed.lift
  have hρx : ρ (x : Fld Q) = φ x := ρ.commutes x
  let τ : E →+* ℂ := (ρ : Fld Q →+* ℂ).comp (algebraMap E (Fld Q))
  have hev : ∀ p : E[X], (p.map τ).eval (ρ (AdjoinRoot.root Q.1)) = ρ (AdjoinRoot.mk Q.1 p) := by
    intro p
    rw [eval_map, ← AdjoinRoot.aeval_eq, aeval_def]
    exact (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) (ρ : Fld Q →+* ℂ) (AdjoinRoot.root Q.1)).symm
  set z := ρ (AdjoinRoot.root Q.1)
  have hroot : ((γ.map τ).charpoly).eval z = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    have h0 : (AdjoinRoot.mk Q.1 Q.1 : Fld Q) = 0 := AdjoinRoot.mk_self
    rw [Matrix.charpoly_map, hg, Polynomial.map_mul, eval_mul, hev, h0]
    exact mul_eq_zero_of_left (map_zero ρ) _
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hγv : (γ.map τ) *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hv0
    exact hv0.symm
  have hM : ((aeval γ m).map τ) *ᵥ v = φ x • v := by
    rw [map_aeval, aeval_mulVec_of_eigen _ v z hγv, hev, ← hx, hρx]
  exact pos_of_posDef (hpos τ) hv hM

end Fld

theorem exists_mul_self_of_pos {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (t : K)
    (ht : 0 < w.embedding t) : ∃ a : w.Completion, a * a = algebraMap K w.Completion t := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.1 ht
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  have hre : w.embedding t = ((w.embedding t).re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  have key : ∃ a : w.Completion, extensionEmbedding w a = (Real.sqrt (w.embedding t).re : ℂ) := by
    by_cases hw : w.IsReal
    · refine ⟨(ringEquivRealOfIsReal hw).symm (Real.sqrt (w.embedding t).re), ?_⟩
      rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    · exact surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  obtain ⟨a, ha⟩ := key
  refine ⟨a, (extensionEmbedding w).injective ?_⟩
  rw [map_mul, ha, ← Complex.ofReal_mul, Real.mul_self_sqrt h1.le, ← hre]
  simp

theorem exists_norm_at_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X],
    (∀ τ : E →+* ℂ, ((aeval γ.val m).map τ).PosDef) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r),
    Q.1 ∣ γ.val.charpoly →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) =
      (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) →
    ∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q,
        z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ _ _ m hpos r Q hdvd hfix v
  let x : plus Q := ⟨AdjoinRoot.mk Q.1 m, hfix⟩
  obtain ⟨ψ, h1, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp (maximalRealSubfield E) (plus Q)
  have hroot : ∀ w : {w : InfinitePlace (plus Q) // w.comap (algebraMap (maximalRealSubfield E) (plus Q)) = v},
      ∃ a : w.1.Completion, a * a = algebraMap (plus Q) _ x := fun w =>
    exists_mul_self_of_pos w.1 x (pos_at_embedding Q γ.val m hpos hdvd x rfl w.1.embedding)
  choose a ha using hroot
  obtain ⟨b, hb'⟩ := (hb v).2 a
  have hb2 : b * b = 1 ⊗ₜ x := (hb v).1 (funext fun w => by
    have hw : ψ v w b = a w := congrFun hb' w
    simp only
    rw [map_mul, hw, ha, h1])
  refine ⟨inclPlus Q _ b, ?_⟩
  rw [GlobalTheory.TraceClasses.involBase_inclPlus, ← map_mul, hb2]
  rfl

end GlobalTheory.RealPlaceNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZero
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprod
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem twOrb_restr_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hfin hcpt hev
  rw [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  simp only [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  exact GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) (GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ) _ _
    (GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hcpt (hev.mono fun v h => ⟨h.1, h.2.1, h.2.2.1⟩))
    (fun v t ht y k hk => GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant _ _ _ _ (hcomm v) (hidx v) t ht y k hk)
    (fun v => (hfin v).subset fun q hq => GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hq)
    (hev.mono fun v h => ⟨by rw [h.1]; exact GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified _ _ _ (hθK v) h.2.1 h.2.2.1, fun y hy => by
        obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hy
        rw [h.1] at hne
        have hm : (y * k)⁻¹ * pf v δ * θv v (y * k) ∈ K v := by
          by_contra hc; exact hne (Set.indicator_of_notMem hc _)
        obtain ⟨t, ht, k', hk', he⟩ := h.2.2.2 (y * k) hm
        exact ⟨t, ht, k' * k⁻¹, mul_mem hk' (inv_mem hk), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩⟩)

end GlobalTheory.EulerAbs
end

