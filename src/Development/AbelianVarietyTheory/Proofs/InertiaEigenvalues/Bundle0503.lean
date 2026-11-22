import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSSRepMapOfAbsIrrDistinct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInertiaImpliesPotSemistableProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteInertiaImpliesPotSemistable_proof : UnrStep := by
  first | exact @GlobalTheory.PMon.unrStep_holds | exact GlobalTheory.PMon.unrStep_holds | (intros; apply GlobalTheory.PMon.unrStep_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfFiniteDimensional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

noncomputable section
namespace GlobalTheory.ConsCompare

section Factors
open GlobalTheory.AdmLoc
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

theorem finiteLength_of_finiteDimensional (k : Type) [Field k] [Algebra k A] (M : Type) [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] : IsFiniteLength A M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

theorem exists_semisimple_sameFactors : ∀ (d : ℕ) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M], Module.finrank k M = d →
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S) (_ : IsScalarTower k A S)
      (_ : FiniteDimensional k S), IsSemisimpleModule A S ∧ SameFactors A M S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ _ hd
  have hfl := finiteLength_of_finiteDimensional (A := A) k M
  rcases subsingleton_or_nontrivial M with h0 | h0
  · exact ⟨M, _, _, _, inferInstance, inferInstance, (isSemisimpleModule_iff A M).2
      (have := (Submodule.subsingleton_iff A).2 h0; Subsingleton.instComplementedLattice),
      SameFactors.refl hfl⟩
  · haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
    obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left bot_ne_top
    have hlt : Module.finrank k N < d := by
      rw [← hd]
      exact Submodule.finrank_lt (s := N.restrictScalars k) fun h => hN.1 (by simpa using h)
    obtain ⟨S, _, _, _, _, _, hS, hf⟩ := ih _ hlt N rfl
    haveI : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
    exact ⟨S × (M ⧸ N), _, _, _, inferInstance, inferInstance,
      isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun b : Bool =>
        cond b (LinearMap.range (LinearMap.inl A S (M ⧸ N))) (LinearMap.range (LinearMap.inr A S (M ⧸ N))))
        (by rintro (_ | _) <;> exact IsSemisimpleModule.range _)
        (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr),
      (SameFactors.sub_prod_quot hfl N).trans
        (hf.prod (SameFactors.refl (finiteLength_of_finiteDimensional k _)))⟩

theorem cpOn_eq_of_sameFactors (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M']
    [IsScalarTower k A M'] [FiniteDimensional k M'] (h : SameFactors A M M') : cpOn k a M = cpOn k a M' := by
  obtain ⟨s, t, h1, h2, h3, h4, f, hf⟩ := h
  rw [cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

variable {Γ : Type} [Group Γ]

def repOf (k Γ S : Type) [Field k] [Group Γ] [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] : Representation k Γ S :=
  (Algebra.lsmul k k S : MonoidAlgebra k Γ →ₐ[k] Module.End k S).toMonoidHom.comp (MonoidAlgebra.of k Γ)

theorem isSS_repOf {S : Type} [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] [IsSemisimpleModule (MonoidAlgebra k Γ) S] :
    IsSS (repOf k Γ S) := fun W hW => by
  let W₁ : Submodule (MonoidAlgebra k Γ) S :=
    { W.toAddSubmonoid with
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_on with
        | of g => exact hW g v hv
        | add a b ha hb => rw [add_smul]; exact W.add_mem ha hb
        | smul c a ha => rw [smul_assoc]; exact W.smul_mem c ha }
  obtain ⟨W₂, h⟩ := exists_isCompl W₁
  refine ⟨W₂.restrictScalars k, fun g v hv => W₂.smul_mem (MonoidAlgebra.of k Γ g) hv, ?_⟩
  exact (Submodule.isCompl_restrictScalars_iff k (s := W₁)).2 h

theorem sameSS_of_charpoly_eq (hBN : GlobalTheory.ConstituentsCompare.BrauerNesbitt) {V W : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    (h : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g)) : GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ := by
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : ∀ g, LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : ∀ g, LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  obtain ⟨S, _, _, _, _, _, hS, hf⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule rfl
  obtain ⟨S', _, _, _, _, _, hS', hf'⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ σ.asModule rfl
  obtain ⟨e, he⟩ := GlobalTheory.brauerNesbitt_abstract_of_matrix hBN (repOf k Γ S) (repOf k Γ S') isSS_repOf isSS_repOf
    fun g => ((cpOn_eq_of_sameFactors _ hf).symm.trans ((e1 g).symm.trans ((h g).trans (e2 g)))).trans
      (cpOn_eq_of_sameFactors _ hf')
  let e' : S ≃ₗ[MonoidAlgebra k Γ] S' :=
    { e.toAddEquiv with
      map_smul' := fun a v => by
        show e (a • v) = a • e v
        induction a using MonoidAlgebra.induction_on with
        | of g => exact he g v
        | add a b ha hb => rw [add_smul, add_smul, map_add, ha, hb]
        | smul c a ha => rw [smul_assoc, smul_assoc, map_smul, ha] }
  exact (hf.trans (SameFactors.of_equiv hf.finiteLength_right e')).trans hf'.symm

end Factors

section Distinct
open Matrix

end Distinct

section BaseChange
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A B : Type} [Group Γ] [CommRing A] [CommRing B] {n r t : ℕ}

variable [Algebra A B]

variable [IsDomain A] [IsDomain B]

variable [IsLocalRing A] [IsLocalRing B]

end BaseChange

end GlobalTheory.ConsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsModSquaresOfUnramifiedQuadraticStatement
section
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  first | exact @GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | exact GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | (intros; apply GlobalTheory.UnitLemma.UQ.finite_units_mod_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDimStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcrisLetter_deRhamComponent_eq_dim : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  first | exact @GlobalTheory.Per.LetterDim.tied_letter_component_finrank | exact GlobalTheory.Per.LetterDim.tied_letter_component_finrank | (intros; apply GlobalTheory.Per.LetterDim.tied_letter_component_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulMinpolyNatDegreeLeOfPowEqNegStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  first | exact @GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg | exact GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg | (intros; apply GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummandJumps

open Module

theorem finsum_count_neg (U : Multiset ℤ) (m : ℤ → ℤ) (h : ∀ a, m a = (U.count a : ℤ)) :
    ∑ᶠ (a : ℤ) (_ : a < 0), m a = (Multiset.card (U.filter (· < 0)) : ℤ) := by
  classical
  have h1 : ∀ a : ℤ, ∑ᶠ (_ : a < 0), m a = (((U.filter (· < 0)).count a : ℕ) : ℤ) := fun a => by
    rw [finsum_eq_if, h, Multiset.count_filter]
    split_ifs <;> simp
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := (U.filter (· < 0)).toFinset),
    ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  intro a ha
  have ha' : (U.filter (· < 0)).count a ≠ 0 := fun h0 => ha (by simp only [h0, Nat.cast_zero])
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha'))

section General

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem finsum_multV_neg {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (U : ZMod n → Multiset ℤ)
    (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    ∑ᶠ (τ : K →ₐ[Qp] LL), ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => finsum_count_neg (U i) _ (hU i (e i) (he i))

end General

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.TopSteps.FinSummandDim in

theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), tableLineDegreeTwo.BlochKatoJumpDimension (P.PD S.K) (LL := ↥S.LL.1) (O := S.O) (IK S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P S hB hC hV hH
  obtain ⟨⟨-, -, -, hemb, -⟩, -⟩ := S.hyp
  have : IsTopologicalAddGroup (tw S hC).V := IsModuleTopology.topologicalAddGroup ↥S.LL.1 (tw S hC).V
  have h := hB.1 (tw S hC).V (tw S hC).ρ (tw S hC).cont (tw_crysWith S hC).1
  exact fSummand_of_dim S hC hV hH (h.trans (congrArg _
    (finsum_multV_neg (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandJumps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrime
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChiTame

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  intro D i k v hne s hs
  have hwg : D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) := D.naut.plGw_over k v
  have hpl := D.nd.plOm.2 (D.naut.plGw k v)
  have hI : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := GlobalTheory.TameGenPowers.wild_mem_Ine hs
  have hcop : (D.nd.l i).Coprime (D.host.g k) :=
    (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 hne
  have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
    have h2 := (hpl _).2 hwg
    simpa using h2
  have hvl : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
    intro hl
    have h2 := (hpl _).2 hl
    exact GlobalTheory.WildKill.not_lt_one_of_coprime _ hcop hgv (by simpa using h2)
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k _ hwg (by rw [hl]; exact hvl)
    _ hpl s hI
  obtain ⟨n, hn⟩ := D.ntw.psiL_ord i s
  have h1 : ((Units.map (D.ntw.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i))) s ^ (D.host.g k - 1) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow, ht, map_one]
  have hpow : D.nd.chi i 1 s ^ ((D.host.g k - 1) * D.nd.l i ^ n) = 1 := by
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, mul_pow, pow_mul, h1, one_pow, one_mul, pow_mul', hn, one_pow]
  have := D.nd.trO i
  exact GlobalTheory.WildSetSQ.char_eq_one_of_wild (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.O_adic i) (D.nd.chi i 1)
    (D.nd.chi_cont i 1) s hs _
    (GlobalTheory.WildKill.not_lt_one_of_coprime _
      (Nat.Coprime.mul (GlobalTheory.WildSetSQ.coprime_pred _ (D.host.g_prime k).one_lt.le)
        (Nat.Coprime.pow_left n hcop)) hgv) hpow

end GlobalTheory.ChiTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.FontaineTied

theorem fontCore_all_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) :=
  fun l _ P AI hT K => GlobalTheory.Per.FontaineAll.fontCore_of_tied l P AI hT K

end GlobalTheory.Per.FontaineTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttachedStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobDual_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → FrobDual i s := by
  first | exact @GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt | exact GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt | (intros; apply GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.Hom

section Bounds

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_sum_le {s : Type} (t : Finset s) (f : s → K⟦X⟧) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k n, ‖coeff n (f k)‖ ≤ C) (n : ℕ) : ‖coeff n (∑ k ∈ t, f k)‖ ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf k n) ih)

theorem bdd_matMul {μ ν ρ : Type} [Fintype ν] {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply]
  refine norm_coeff_sum_le _ (fun k => Y i k * Z k j)
    (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (fun k m => ?_) n
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun p => by rw [mul_one]; exact (ha i k p).trans (le_max_left _ _))
    (fun p => by rw [mul_one]; exact (hb k j p).trans (le_max_left _ _)) m

theorem bdd_frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (frob K l f)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun n => ?_⟩
  rw [coeff_frob]
  split_ifs
  · exact hc _
  · simpa using (norm_nonneg _).trans (hc 0)

theorem bdd_map_frob (l : ℕ) [Fact l.Prime] {μ ν : Type} {Y : Matrix μ ν K⟦X⟧}
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y.map (frob K l)) i j)‖ ≤ c := by
  obtain ⟨c, hc⟩ := hY
  refine ⟨max c 0, fun i j n => ?_⟩
  rw [Matrix.map_apply, coeff_frob]
  split_ifs
  · exact (hc _ _ _).trans (le_max_left _ _)
  · simp

end Bounds

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_mem (l e : ℕ) {s : Type} [Finite s] (f : s → K⟦X⟧)
    (hf : ∀ x, f x ∈ invE l e (A O K)) : ∃ N : ℕ, ∀ x, E K l e ^ N * f x ∈ A O K := by
  classical
  cases nonempty_fintype s
  choose n hn using fun x => mem_away.1 (hf x)
  refine ⟨Finset.univ.sup n, fun x => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ x))
  rw [hc, pow_add, mul_assoc]
  exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn x)

theorem bdd_of_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c := ⟨1, hf⟩

theorem map_frob_smul_one (l : ℕ) [Fact l.Prime] {μ : Type} [DecidableEq μ] (h : K⟦X⟧) :
    (h • (1 : Matrix μ μ K⟦X⟧)).map (frob K l) = frob K l h • (1 : Matrix μ μ K⟦X⟧) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mxInv_mul_mat (F : Hom P Q) (τ : ZMod a) :
    Q.mxInv τ * F.mat τ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
  calc Q.mxInv τ * F.mat τ = Q.mxInv τ * (F.mat τ * P.mx τ) * P.mxInv τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
    _ = (F.mat (τ - 1)).map (frob K l) * P.mxInv τ := by
        rw [F.comm, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]

theorem frob_ldiv_eq (F : Hom P Q) (τ : ZMod a) {h : K⟦X⟧} {Y : Matrix ι κ K⟦X⟧}
    (hY : Y * F.mat (τ - 1) = h • (1 : Matrix ι ι K⟦X⟧)) :
    P.mx τ * Y.map (frob K l) * Q.mxInv τ * F.mat τ = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
  have hφ : Y.map (frob K l) * (F.mat (τ - 1)).map (frob K l) = frob K l h • (1 : Matrix ι ι K⟦X⟧) := by
    rw [← map_frob_smul_one l h, ← hY]
    exact (Matrix.map_mul (f := ((frob K l : K⟦X⟧ →ₐ[K] K⟦X⟧) : K⟦X⟧ →+* K⟦X⟧))).symm
  rw [Matrix.mul_assoc, mxInv_mul_mat, ← Matrix.mul_assoc,
    Matrix.mul_assoc (P.mx τ) (Y.map (frob K l)), hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, P.mx_mul_mxInv]

end Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem exists_pow_E_mul_frob_mem_ldivSet (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NeZero a] (κ : Type) [Fintype κ] [DecidableEq κ]
    (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : Hom P Q) :
    ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  obtain ⟨N₁, hN₁⟩ := exists_pow_E_mul_mem (O := O) l e (fun p : ZMod a × ι × ι => P.mx p.1 p.2.1 p.2.2)
    fun p => P.mx_mem _ _ _
  obtain ⟨N₂, hN₂⟩ := exists_pow_E_mul_mem (O := O) l e
    (fun p : ZMod a × κ × κ => Q.mxInv p.1 p.2.1 p.2.2) fun p => Q.mxInv_mem _ _ _
  refine ⟨N₁ + N₂, fun τ h ⟨hb, Y, hY, hYF⟩ => ⟨?_, ?_⟩⟩
  · exact bdd_mul (bdd_of_mem_A (pow_mem (E_mem l e (A O K)) _)) (bdd_frob l hb)
  · refine ⟨(E K l e ^ N₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ N₂ • Q.mxInv τ),
      bdd_matMul (bdd_matMul ⟨1, fun i j n => ?_⟩ (bdd_map_frob l hY)) ⟨1, fun i j n => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₁ (τ, i, j) n
    · rw [Matrix.smul_apply, smul_eq_mul]; exact hN₂ (τ, i, j) n
    · simp only [Matrix.smul_mul, Matrix.mul_smul]
      rw [frob_ldiv_eq F τ hYF, smul_smul, smul_smul, pow_add]
      congr 1
      ring

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.frob_mem_ldivSet_target : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.ldivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.ldivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  exact GlobalTheory.BK.Hom.exists_pow_E_mul_frob_mem_ldivSet l e a ι κ P Q F
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVectorStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  first | exact @GlobalTheory.FrobIntO.frobenius_integrality_vec_O | exact GlobalTheory.FrobIntO.frobenius_integrality_vec_O | (intros; apply GlobalTheory.FrobIntO.frobenius_integrality_vec_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  first | exact @GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | exact GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow | (intros; apply GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow <;> assumption)
end

