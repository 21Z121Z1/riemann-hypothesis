import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalHomOfNatCast
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.SelmerSameChar

theorem isLocalHom_of_natCast {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    (f : O →+* B) (l : ℕ) (h0 : (l : O) ≠ 0) (h : ¬ IsUnit (l : B)) : IsLocalHom f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hu : ¬ IsUnit (f ϖ) := fun hu => h (by
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [← map_natCast f, hn, map_mul, map_pow]
    exact (u.isUnit.map f).mul (hu.pow n))
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal O := hn
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [map_mul] at hx
  exact hu (isUnit_of_mul_isUnit_right hx)

theorem isIntegral_of_finite {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂) {O₀ O : Type}
    [CommRing O₀] [Algebra ℤ_[l₁] O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O]
    [Module.Finite ℤ_[l₂] O] (f : O₀ →+* O) : f.IsIntegral := by
  subst h
  cases Subsingleton.elim i₁ i₂
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l₁] O₀) f ?_
  rw [padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O)]
  exact algebraMap_isIntegral_iff.2 inferInstance

variable (D : D7)

theorem sT_congr (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) {O : Type} [CommRing O] [IsDomain O]
    {f f' : D.ntw.O0 i →+* O} (hf : Function.Injective f) (hf' : Function.Injective f')
    {ψ ψ' : Formalism.MainNotions.N.GE D.nd →* Oˣ} (h1 : f = f') (h2 : ψ = ψ') :
    sT D.loc D.ntwbr i s Q f hf ψ = sT D.loc D.ntwbr i s Q f' hf' ψ' := by
  subst h1 h2
  rfl

theorem toOk_local (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (toOk D.ntw i k) := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  refine isLocalHom_of_natCast _ (D.ntw.l i) (Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero) fun hu => ?_
  have := D.ntw.Ok_fin i k
  have := RingHom.IsIntegral.isLocalHom (f := algebraMap (D.ntw.O i) (D.ntw.Ok i k))
    (algebraMap_isIntegral_iff.2 inferInstance) (D.ntw.Ok_inj i k)
  rw [← map_natCast (algebraMap (D.ntw.O i) (D.ntw.Ok i k))] at hu
  exact D.ntw.O_l i (isUnit_of_map_unit _ _ hu)

theorem sTLoc_eq : ∀ (D : D7) (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) ψ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sTLoc D a s = GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw (D.ntw.twOf a) k) ψ := by
  intro D a s k ψ h
  obtain ⟨O₁, _, _, _, f, gA, gB, χ, iA, iB, lA, lB, cA, cB, eA, eB⟩ :=
    GlobalTheory.Proof.dvr_of_reflects_facts.common _ _ _ _ (D.ntw.twist₂ a) (toOk D.ntw _ k) (twO_inj D.ntw a)
      (isIntegral_of_finite (D.ntw.twOf_l a) _) (toOk_inj D.ntw _ k) (toOk_local D _ k) _ _ h
  have hf : Function.Injective f := Function.Injective.of_comp (f := gA) (by
    rw [← RingHom.coe_comp, cA]; exact twO_inj D.ntw a)
  exact (sT_congr D _ s _ _ (iA.comp hf) cA.symm eA.symm).trans
    ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gA iA χ).trans
      ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gB iB χ).symm.trans
        (sT_congr D _ s _ (iB.comp hf) _ cB eB)))

end GlobalTheory.SelmerSameChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_δ_of_I_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A),
    B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  intro l hl R _ B d hI
  by_contra hu
  obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {B.D.δ d})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hδd : B.D.δ d ∈ m := hdm (Ideal.mem_span_singleton_self _)
  have hJ : JJ B ≤ m := by
    have h1 : JJ B ≤ (⊥ : Ideal B.A).jacobson := @IsAdicComplete.le_jacobson_bot _ _ _ B.complete
    exact h1.trans (sInf_le ⟨bot_le, hm⟩)
  have hlm : (l : B.A) ∈ m := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hdm' : d ∈ m := hJ (Ideal.mem_sup_right (by rw [hI]; exact Ideal.mem_span_singleton_self _))
  have hmem := B.l_mem
  rw [hI, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton_sup] at hmem
  obtain ⟨a, y, hy, hle⟩ := hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hl2 : 2 ≤ l := hl.out.two_le
  have hφ : B.D.φ d ∈ m ^ 2 := by
    rw [B.D.φ_eq]
    refine Ideal.add_mem _ ?_ ?_
    · have : d ^ l = d ^ 2 * d ^ (l - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hdm' 2)
    · rw [pow_two]; exact Ideal.mul_mem_mul hlm hδd
  have hy2 : c * B.D.φ d ∈ m ^ (1 + 1) := Ideal.mul_mem_left _ _ hφ
  have hδy : B.D.δ (c * B.D.φ d) ∈ m := by
    simpa using GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l B.A B.D m hlm 1 _ hy2
  have hδad : B.D.δ (a * d) ∈ m := by
    rw [B.D.δ_mul]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hδd
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hdm' _ hl.out.pos)
    · exact Ideal.mul_mem_left _ _ hδd
  have hsum : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : B.A) * (a * d) ^ k * (c * B.D.φ d) ^ (l - k) ∈ m :=
    Ideal.sum_mem _ fun k hk =>
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hdm') _ (Finset.mem_Ioo.1 hk).1))
  have hδl : B.D.δ (l : B.A) ∈ m := by
    rw [← hle, B.D.δ_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hδad hδy) hsum
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B.A B.D m hm.ne_top hlm).2 hδl

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension
section
noncomputable section

namespace GlobalTheory.NT

open NumberField IsDedekindDomain

theorem isUnramifiedAt_of_unramIn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (h : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver 𝔭.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) P := by
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have := 𝔭.isMaximal
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := (Ideal.over_def P 𝔭.asIdeal).symm
  have : (P.under (𝓞 K)).IsMaximal := by rw [hu]; infer_instance
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨P, inferInstance, inferInstance, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2.symm

example : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P :=
  fun h P => isUnramifiedAt_of_unramIn h P

end GlobalTheory.NT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevelCocycle

theorem ioL_actQ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (g : G)
    (x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    GlobalTheory.BKFinLevel.ioL L ϖ r (actQ L _ hI g x) = actD L g (GlobalTheory.BKFinLevel.ioL L ϖ r x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [actQ, Submodule.mapQ_apply, GlobalTheory.BKFinLevel.ioL_mk, actD, actT]
    congr 1
    simp only [LinearMap.coe_restrictScalars, map_smul]
    rfl

theorem ioL_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ r hI c hc
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  simp only [hc.2 g h, map_add, ioL_actQ]

end GlobalTheory.BKFinLevelCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.RedLocConst

theorem mem_span_smul_top' {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem redT_mem_Z1Q : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL (ϖ ^ r) with hcdef
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hc).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = ϖ ^ r • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = ϖ ^ r • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

end GlobalTheory.RedLocConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLatticeStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (ϖ : X.O0 i), Irreducible ϖ → ∀ y : ↥(DecV N v) → Fin D.R.r → X.O0 i, (∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (y g a)) → (∀ g h a, y (g * h) a - (y g a + (Tdual i s g.1).mulVec (y h) a) ∈ IsLocalRing.maximalIdeal (X.O0 i)) → ((∃ y', IsFCoc bkP i v hv ρ y' ∧ ∀ g a, y' g a - y g a ∈ IsLocalRing.maximalIdeal (X.O0 i)) ↔ ∀ d, IsFCoc bkP i v hv (Tgl i s) d → ∃ f : ↥(DecV N v) → Formalism.BasicNotions.KmodO (X.O0 i), IsLocallyConstant f ∧ ∀ g h, (Submodule.Quotient.mk ((algebraMap (X.O0 i) (FractionRing (X.O0 i)) ϖ)⁻¹ * algebraMap (X.O0 i) (FractionRing (X.O0 i)) (d g ⬝ᵥ (Tdual i s g.1).mulVec (y h))) : Formalism.BasicNotions.KmodO (X.O0 i)) = ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) • f h - f (g * h) + f g) := by
  first | exact @GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | exact GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | (intros; apply GlobalTheory.BKLatticeCochain.lift_iff_orthogonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CycBridge

theorem locChi_epsU_eq_cycLL : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.locChi D.nbr i w hw (epsU D.nd i) = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) :=
  fun D i w hw => MonoidHom.ext (GlobalTheory.CycBridge.locChi_epsU D i w hw)

end GlobalTheory.CycBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K0_eq_and_good_of_ne : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  exact GlobalTheory.HubLoc.localField_unramified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.Proof.LocalGlobalAssembly

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GlobalTheory.PtCore.GoodPtRow D := by
  intro D _ _ hZ a π hπ
  have hπ' : π ∈ ZgoodN D.nd D.naut a := (D.Zgood_tie a π).1 hπ
  obtain ⟨-, Sig, hX, hg⟩ := id hπ'
  have hHG : HG D.nd D.naut a := ⟨π, hπ'⟩
  have h1 := ((hZ a hHG).1 π hπ' Sig hX).2

  have hE : eigC D.nd D.naut a π ≠ ⊥ := by
    obtain ⟨P, hP, -⟩ := hX
    intro h
    apply D.naut.typeV_ne a P
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | D.naut.ptV a P = some π}) => D.naut.typeV a P) P hP le_rfl
  have hM : MjSig D.nd D.naut a Sig ≠ ⊥ := by
    intro h
    apply hE
    rw [← h1, h, Submodule.map_bot]
  obtain ⟨σ, hW, hσ⟩ : ∃ σ, HasParamW D.nd D.naut a σ Sig ∧ D.what₂.isot (D.nd.j a) σ ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    apply hM
    unfold MjSig
    exact le_bot_iff.1 (iSup₂_le fun σ hW => (hc σ hW).le)
  have hgr : D.nd.goodRow σ := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW.2.2).2 hg
  exact ⟨σ, Sig, ⟨hgr, hσ⟩, hW, hX⟩

end GlobalTheory.Proof.LocalGlobalAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.Proof.CoefField

theorem exists_coefField {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ K : IntermediateField ℚ_[l] (Qbar l), (∀ z, z ∈ K ↔ ∃ x, ι x = z) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ x : FractionRing O, ‖ι x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let φ : O →+* Qbar l := ι.comp (algebraMap O (FractionRing O))
  have hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hι
  have hQ : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Qbar l) q ∈ ι.fieldRange := by
    intro q
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    rw [map_div₀]
    refine div_mem ?_ ?_
    · exact ⟨_, hι a⟩
    · exact ⟨_, hι b⟩
  let K : IntermediateField ℚ_[l] (Qbar l) := ι.fieldRange.toIntermediateField hQ
  have hK : ∀ z, z ∈ K ↔ ∃ x, ι x = z := fun z => Iff.rfl
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  let S : Set (Qbar l) := φ '' (s : Set O)
  have hint : ∀ x ∈ S, IsIntegral ℚ_[l] x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨p, hp, hy⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] ℚ_[l]), hp.map _, ?_⟩
    have := congrArg φ hy
    rw [map_zero, Polynomial.hom_eval₂] at this
    have e : (algebraMap ℚ_[l] (Qbar l)).comp (algebraMap ℤ_[l] ℚ_[l]) = φ.comp (algebraMap ℤ_[l] O) :=
      RingHom.ext fun z => (hφ z).symm
    rw [Polynomial.eval₂_map, e]
    exact this
  haveI : Finite S := (s.finite_toSet.image φ).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : K ≤ IntermediateField.adjoin ℚ_[l] S := by
    have hO : ∀ y : O, φ y ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro y
      have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Algebra.smul_def, map_mul, hφ]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀]
    exact div_mem (hO a) (hO b)
  refine ⟨K, hK, ?_, fun x => (GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι x).symm⟩
  have hge : IntermediateField.adjoin ℚ_[l] S ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have heq : K = IntermediateField.adjoin ℚ_[l] S := le_antisymm hle hge
  rw [heq]
  exact hfd

theorem coefField_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  intro R H what₂ N A i
  exact exists_coefField (A.iotaQ i) (A.iotaQ_alg i)

end GlobalTheory.Proof.CoefField

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.PointEigen

theorem genAt_iff_splitOut (D : D7) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.nd.l i) (D.nd.Q i) v k ↔ (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.nd.l i) := by
    rw [D.nd.S_def]; rfl
  unfold SplitOut GenAt
  rw [hS]
  tauto

theorem ptSys_mem_eigSet : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i),
    ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  intro D M A i x
  refine ⟨fun v k h => ?_, ?_⟩
  · simp only [ptSys, if_neg h]
  · obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hw, k1, k2⟩ := (genAt_iff_splitOut D i v k).1 hg
    simp only [ptSys, if_pos hg]
    exact (A.ptV i P x).1 hP v k s ϖ hw hc hu k1 k2 y hy

end GlobalTheory.PointEigen
end

