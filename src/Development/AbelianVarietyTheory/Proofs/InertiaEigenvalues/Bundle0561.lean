import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0546
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleChangeScalarsBack
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntiOfKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
section
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Polynomial
open Formalism.MainNotions.N (GRep)

namespace GlobalTheory.FullCharpoly

section Lat
variable {G LL O V W : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
  {ρ : Representation LL G V} {σ : Representation LL G W}

def mapLat (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) (L : Lattice (O := O) ρ) :
    Lattice (O := O) σ where
  T := L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, L.stable g x hx, he g x⟩
  fg := L.fg.map _
  free := by
    have := L.free
    exact Module.Free.of_equiv ((e.restrictScalars O).submoduleMap L.T)
  span := by
    have h : ((L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W) : Submodule O W) : Set W) =
        (e : V →ₗ[LL] W) '' (L.T : Set V) := rfl
    rw [h, Submodule.span_image, L.span, Submodule.map_top, LinearEquiv.range]

variable {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]

theorem quot_equiv_iff (L₁ L₂ : Lattice (O := O) ρ) (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    (∃ e : (E ⧸ LinearMap.ker p) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
      ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩) ↔
    ∃ q : ↥L₁.T →ₗ[O] M, Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧
      ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := p.quotKerEquivOfSurjective hp
    refine ⟨(Φ.toLinearMap.comp e.symm.toLinearMap).comp (L₂.T.comap L₁.T.subtype).mkQ, ?_, ?_, ?_⟩
    · exact Φ.surjective.comp (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    · intro g y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk y))
      have h1 : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
        rw [hx, LinearEquiv.apply_symm_apply]
      have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
      rw [h3, ← he g x y h1, LinearEquiv.symm_apply_apply, ← hx]
      simp only [Φ, LinearMap.quotKerEquivOfSurjective_apply_mk]
      exact hact g x
    · intro y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype]
  · rintro ⟨q, hq, hqe, hqk⟩
    have hker : LinearMap.ker q = L₂.T.comap L₁.T.subtype := by
      ext y
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, hqk]
    let ψ : M ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype) :=
      (q.quotKerEquivOfSurjective hq).symm.trans (Submodule.quotEquivOfEq _ _ hker)
    have hψ : ∀ y, ψ (q y) = Submodule.Quotient.mk y := by
      intro y
      simp only [ψ, LinearEquiv.trans_apply]
      rw [(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk q hq y).symm]
      rfl
    have hΦ : ∀ x, p.quotKerEquivOfSurjective hp (Submodule.Quotient.mk x) = p x :=
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp
    refine ⟨(p.quotKerEquivOfSurjective hp).trans ψ, fun g x y h => ?_⟩
    simp only [LinearEquiv.trans_apply, hΦ] at h ⊢
    have hxy : p x = q y := ψ.injective (h.trans (hψ y).symm)
    have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
    rw [hact, hxy, ← hqe, h3, hψ]

end Lat

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {lam : O} {jT : ZMod n → ℤ → ℤ} {cT : G → Polynomial LL}

def ofFull (F : tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := F.V
  cadd := IsModuleTopology.toContinuousAdd LL F.V
  csmul := by have := IsModuleTopology.toContinuousSMul LL F.V; infer_instance
  ρ := F.ρ
  cont := F.full.1

def sumFull {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := ∀ j, (F j).V
  cadd := IsModuleTopology.toContinuousAdd LL _
  csmul := by have := IsModuleTopology.toContinuousSMul LL (∀ j, (F j).V); infer_instance
  ρ := tableLineDegreeTwo.piRep F
  cont := fun x => continuous_pi fun j => (F j).full.1 (x j)

def toFull (A : GRep G Qp LL O) (h : tableLineDegreeTwo.IsFull PD emb lam jT cT A.ρ) : tableLineDegreeTwo.FullRep PD emb lam jT cT where
  V := A.V
  ρ := A.ρ
  full := h

private theorem mapLattice_quotient_of_equivariant_equiv {G LL O V W M : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    {ρ : Representation LL G V} {σ : Representation LL G W} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x))
    (L₁ L₂ : Lattice (O := O) ρ) (q : ↥L₁.T →ₗ[O] M) (hq : Function.Surjective q)
    (hqe : ∀ g x, q (latRep L₁ g x) = π g (q x)) (hqk : ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T) :
    ∃ q' : ↥(mapLat e he L₁).T →ₗ[O] M, Function.Surjective q' ∧
      (∀ g x, q' (latRep (mapLat e he L₁) g x) = π g (q' x)) ∧
      ∀ x, q' x = 0 ↔ (x : W) ∈ (mapLat e he L₂).T := by
  let s : ↥L₁.T ≃ₗ[O] ↥(mapLat e he L₁).T := (e.restrictScalars O).submoduleMap L₁.T
  have hsx : ∀ x, (s x : W) = e x := fun x => rfl
  refine ⟨q.comp s.symm.toLinearMap, hq.comp s.symm.surjective, ?_, ?_⟩
  · intro g y
    obtain ⟨x, rfl⟩ := s.surjective y
    have hs : latRep (mapLat e he L₁) g (s x) = s (latRep L₁ g x) := by
      apply Subtype.ext
      rw [latRep_apply, hsx, hsx, latRep_apply, he]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hqe g x
  · intro y
    obtain ⟨x, rfl⟩ := s.surjective y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hqk, hsx]
    change (x : V) ∈ L₂.T ↔ e x ∈ L₂.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have hzx : z = (x : V) := e.injective hze
      rwa [← hzx]

omit [IsTopologicalRing LL] in

theorem admissible_quotient_ker_iff_full_lattices {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]
    (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    tableLineDegreeTwo.AdmQ PD emb lam jT cT act (LinearMap.ker p) ↔
      ∃ (μ : ℕ) (F : Fin μ → GRep G Qp LL O) (A : GRep G Qp LL O)
      (e : A.V ≃ₗ[LL] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := O) A.ρ) (q : ↥L₁.T →ₗ[O] M),
      (∀ j, tableLineDegreeTwo.IsFull PD emb lam jT cT (F j).ρ) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧ ∀ x, q x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨m, F, L₁, L₂, hle, e, he⟩
    obtain ⟨q, hq, hqe, hqk⟩ := (quot_equiv_iff L₁ L₂ act π p hp hact).1 ⟨e, he⟩
    exact ⟨m, fun j => ofFull (F j), sumFull F, LinearEquiv.refl LL _, L₁, L₂, q,
      fun j => (F j).full, fun g x j => rfl, hle, hq, hqe, hqk⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, he, hle, hq, hqe, hqk⟩
    let F' : Fin μ → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun j => toFull (F j) (hF j)
    let e' : A.V ≃ₗ[LL] (∀ j, (F' j).V) := e
    have he' : ∀ g x, e' (A.ρ g x) = tableLineDegreeTwo.piRep F' g (e' x) := fun g x => funext fun j => he g x j
    obtain ⟨q', hq', hqe', hqk'⟩ := mapLattice_quotient_of_equivariant_equiv π e' he' L₁ L₂ q hq hqe hqk
    exact ⟨μ, F', mapLat e' he' L₁, mapLat e' he' L₂, Submodule.map_mono hle,
      (quot_equiv_iff _ _ act π p hp hact).2 ⟨q', hq', hqe', hqk'⟩⟩

omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in

theorem resPoly_eq {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (χ : ℕ → G →* Oˣ) (t : ℕ) :
    tableLineDegreeTwo.resPoly ρ χ t = fun g => LinearMap.charpoly (ρ g) *
      ∏ c : Fin t, (X - C (algebraMap O LL (χ (c.val + 1) g))) := by
  funext g
  simp only [tableLineDegreeTwo.resPoly]
  congr 1
  symm
  refine Finset.prod_bij (fun (c : Fin t) _ => c.val + 1) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    exact Fin.ext (by simpa using hab)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro c _
    simp [tableLineDegreeTwo.charL]

end Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem isFull_iff_polyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) :
    tableLineDegreeTwo.IsFull (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) A.ρ ↔ PolyFull S jT A := by
  unfold tableLineDegreeTwo.IsFull PolyFull
  rw [resPoly_eq]
  simp only [tableLineDegreeTwo.Over, AlgHom.ext_iff, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨A.cont, h.1, h.2.1, h.2.2⟩⟩

theorem admissibleQuotient_iff_admissible_module : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ), (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) → ∀ (E M : Type) [AddCommGroup E] [Module S.O E] [AddCommGroup M] [Module S.O M] (act : S.G → E → E) (π : Representation S.O S.G M) (p : E →ₗ[S.O] M), Function.Surjective p → (∀ g x, p (act g x) = π g (p x)) → (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) act (LinearMap.ker p) ↔ S.admitted π) := by
  intro l _ P S jT hj E M _ _ _ _ act π p hp hact
  refine (admissible_quotient_ker_iff_full_lattices act π p hp hact).trans (Iff.trans ?_ (admissibleModule_iff_lattice_quotients S hj π).symm)
  constructor
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).1 (hF j), h⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).2 (hF j), h⟩

end GlobalTheory.FullCharpoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  first | exact @GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | exact GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | (intros; apply GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisCoboundaryEventuallyMemPrimePowLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  first | exact @GlobalTheory.CocycleCont.cont_at_one | exact GlobalTheory.CocycleCont.cont_at_one | (intros; apply GlobalTheory.CocycleCont.cont_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.Dyadic

theorem bound_mod_two_of_hypothesis : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hS := GlobalTheory.SelFun.oneMatrix_of_galoisCohomology h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hgw := GlobalTheory.T.residual_selmer_finrank_eq_dual h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hk4 := GlobalTheory.ScalarFrob.firstHalf h5 h6 h7 h4 D N X bkP
  refine GlobalTheory.StepTwo.TwoBound.thmC_of_parts D N X bkP (GlobalTheory.ChosenPrimes.stepAB h1 D N X) (fun i => GlobalTheory.ChooseForms.chooseH h8 D N X bkP i fun s hs =>
    ⟨GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s hs, GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s hs, hgw i s hs⟩) fun i s hs => ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.StepTwo.StartInd.start_of_resBound D N X bkP i s hs (GlobalTheory.ScalarFrob.firstPlace h5 h6 h7 D N X bkP i s hs) (GlobalTheory.ResOrder.resBound h4 D N X bkP i s hs (hk4 i s hs)
      (GlobalTheory.ResRecip.reciprocity h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP i s hs (hk4 i s hs)) (hgw i s hs))
  · exact GlobalTheory.Growth.grow h4 D N X bkP hS i s hs
  · exact GlobalTheory.NewPrime.step h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP hS i s hs

end GlobalTheory.StepTwo.Dyadic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinApproxRootImageIndepStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_approxRoot_image_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  first | exact @GlobalTheory.BSP.approx_root_indep | exact GlobalTheory.BSP.approx_root_indep | (intros; apply GlobalTheory.BSP.approx_root_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominatorsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_bounded_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  first | (exact @GlobalTheory.BKLim.beta_bdd_denominators) | (exact GlobalTheory.BKLim.beta_bdd_denominators) | (intros; apply GlobalTheory.BKLim.beta_bdd_denominators  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  first | exact @GlobalTheory.BKLim.beta_unique | exact GlobalTheory.BKLim.beta_unique | (intros; apply GlobalTheory.BKLim.beta_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinChangeOfBasisNoPoleAtEStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_changeOfBasis_no_pole_at_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m N c₂ : ℕ) (s : Matrix (Fin d) (Fin m) (bk.S)) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), (∀ r i, (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)))) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → X = (s * Matrix.diagonal fun i => bk.E ^ n i) * Q + bk.E ^ (2 * N) • R → (l : bk.S) ^ c₂ • (s * Matrix.diagonal fun i => bk.E ^ n i) = X * Q' → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) := by
  first | exact @GlobalTheory.seed_nopole | exact GlobalTheory.seed_nopole | (intros; apply GlobalTheory.seed_nopole <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CocycleFrob

theorem σA_frob {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff l g, WittVector.map_coeff, WittVector.map_coeff,
    GlobalTheory.RingIface.sigA_coeff l g, frobenius_def, frobenius_def, map_pow]

theorem cancel_left {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (Y X₁ X₂ : Matrix n n R) (c : R) (hc : c ≠ 0) (hY : Y.det ≠ 0) (h : c • (Y * X₁) = c • (Y * X₂)) :
    X₁ = X₂ := by
  have h1 : Y * X₁ = Y * X₂ := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have h2 := congrArg (fun Z => Y.adjugate * Z) h1
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hY this

theorem frob_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA g) G → IsDiscMap WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  intro l _ K bk τ hτ d M N Y A A' hAA hφ hdet g G Φ _ hΦ w hw P hP e he
  obtain ⟨-, -, -, h0, h1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  obtain ⟨-, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have ht' : bk.iA (Per.σA g τ) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    have h2 := hστ g
    rw [hinj h, map_zero] at h2
    exact not_isUnit_zero h2
  have hE : bk.iA (bk.ev bk.E) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    exact bk.E_ne_zero (bk.ev_injective ((hinj h).trans (map_zero _).symm))
  have hu : bk.iA (w : Ainf l) ≠ 0 := fun h => by
    have := congrArg bk.iA w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this

  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := hΦ.ext
  have hσE : ∀ k : ℕ, bk.iA (Per.σA g (bk.ev bk.E ^ k)) = (bk.iA (bk.ev bk.E) * bk.iA w) ^ k := fun k => by
    rw [map_pow, hw, map_pow, map_mul]

  have hφ1 : bk.iA (bk.ev bk.E) ^ N • (Y.map WittVector.frobenius).map bk.iA =
      bk.iA (bk.ev bk.E) ^ M • (Y.map bk.iA * (A.map bk.ev).map bk.iA) := by
    have := congrArg (fun X => X.map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_mul, map_pow] at this
    exact this

  have hφ2 : (bk.iA (bk.ev bk.E) * bk.iA w) ^ N • ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ M • ((Y.map (Per.σA g)).map bk.iA * ((A.map bk.ev).map (Per.σA g)).map bk.iA) := by
    have := congrArg (fun X => (X.map (Per.σA g)).map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_mul] at this
    rw [hσE, hσE] at this
    have hc : ((Y.map WittVector.frobenius).map (Per.σA g)) = ((Y.map (Per.σA g)).map WittVector.frobenius) := by
      exact Matrix.ext fun i j => σA_frob g (Y i j)
    rw [hc] at this
    exact this

  have he1 : (bk.iA (bk.ev bk.E) * bk.iA w * bk.iA (Per.σA g τ)) ^ M • ((Y.map WittVector.frobenius).map bk.iA * e.map Φ) =
      (bk.iA (bk.ev bk.E) * bk.iA τ) ^ M • (P.map bk.iA * ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA) := by
    have := congrArg (fun X => X.map Φ) he
    simp only [Matrix.map_smul' _ _ _ (map_mul Φ), Matrix.map_mul, map_pow, hΦA] at this
    have m1 : ∀ Z : Matrix (Fin d) (Fin d) (Ainf l), (Z.map bk.iA).map Φ = (Z.map WittVector.frobenius).map bk.iA :=
      fun Z => Matrix.ext fun i j => hΦA (Z i j)
    rw [m1, m1, m1, hP, ← σA_frob, hτ.1, map_mul, hw, map_mul, map_mul, map_mul] at this
    exact this
  have hA2 : ((A.map bk.ev).map (Per.σA g)).map bk.iA * ((A'.map bk.ev).map (Per.σA g)).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (fun X => ((X.map bk.ev).map (Per.σA g)).map bk.iA) hAA
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_smul' _ _ _ (map_mul bk.ev), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [map_pow bk.ev, hσE] at this
    exact this
  have hv : bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA w = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hiS : bk.iS bk.E = bk.iA (bk.ev bk.E) := rfl
  rw [hiS, Matrix.map_smul' _ _ _ (map_mul bk.iA), map_pow]
  generalize (Y.map WittVector.frobenius).map bk.iA = ΦY at hφ1 he1
  generalize ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA = ΦGY at hφ2 he1
  generalize (Y.map (Per.σA g)).map bk.iA = GY at hφ2 he
  generalize Y.map bk.iA = YY at hφ1 he hdet
  generalize (A.map bk.ev).map bk.iA = AA at hφ1 ⊢
  generalize ((A.map bk.ev).map (Per.σA g)).map bk.iA = GA at hφ2 hA2
  generalize ((A'.map bk.ev).map (Per.σA g)).map bk.iA = GA' at hA2 ⊢
  generalize P.map bk.iA = PP at he he1
  generalize e.map Φ = Φe at he1 ⊢
  generalize bk.iA (bk.ev bk.E) = E' at *
  generalize bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = v at *
  generalize bk.iA (w : Ainf l) = u at *
  generalize bk.iA (Per.σA g τ) = t' at *
  generalize bk.iA τ = t at *
  have key : (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe))) =
      (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) :=
    calc (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe)))
        = (u ^ N * (E' * u * t') ^ M) • ((E' ^ M • (YY * AA)) * Φe) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (u ^ N * (E' * u * t') ^ M) • ((E' ^ N • ΦY) * Φe) := by rw [hφ1]
      _ = (E' * u) ^ N • ((E' * u * t') ^ M • (ΦY * Φe)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * u) ^ N • ((E' * t) ^ M • (PP * ΦGY)) := by rw [he1]
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ N • ΦGY)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ M • (GY * GA))) := by rw [hφ2]
      _ = (E' ^ M * (E' * u) ^ M) • ((t ^ M • (PP * GY)) * GA) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' ^ M * (E' * u) ^ M) • ((t' ^ M • (YY * e)) * GA) := by rw [he]
      _ = (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
  have hu' : u ≠ 0 := fun h => by rw [h, mul_zero] at hv; exact zero_ne_one hv
  have hc : E' ^ (2 * M) * u ^ M * t' ^ M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hu')) (pow_ne_zero _ ht')
  have hX := cancel_left YY _ _ _ hc hdet key
  calc E' ^ (2 * N) • e = (v ^ (2 * N) * (E' * u) ^ (2 * N)) • e := by
        congr 1
        rw [show v ^ (2 * N) * (E' * u) ^ (2 * N) = E' ^ (2 * N) * (v * u) ^ (2 * N) by ring, hv, one_pow, mul_one]
    _ = v ^ (2 * N) • (e * ((E' * u) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)))) := by
        rw [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = v ^ (2 * N) • ((e * GA) * GA') := by rw [← hA2, Matrix.mul_assoc]
    _ = v ^ (2 * N) • ((u ^ N • (AA * Φe)) * GA') := by rw [hX]
    _ = (v ^ N • AA) * Φe * GA' := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        congr 1
        rw [show v ^ (2 * N) * u ^ N = v ^ N * (v * u) ^ N by ring, hv, one_pow, mul_one]

end GlobalTheory.BSP.CocycleFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPreframe_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.pre_bounded_poles | exact GlobalTheory.BKLim.pre_bounded_poles | (intros; apply GlobalTheory.BKLim.pre_bounded_poles <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_two_homs_E_regular_associated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧ BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  first | exact @GlobalTheory.BSP.hf_E_pair | exact GlobalTheory.BSP.hf_E_pair | (intros; apply GlobalTheory.BSP.hf_E_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatumStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crysOnCond_of_every_datum : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F := by
  first | exact @GlobalTheory.crysOnCond_all | exact GlobalTheory.crysOnCond_all | (intros; apply GlobalTheory.crysOnCond_all <;> assumption)
end

