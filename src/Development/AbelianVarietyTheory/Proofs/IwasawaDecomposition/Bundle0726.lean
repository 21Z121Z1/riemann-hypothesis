import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcluded
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 2000000

namespace GlobalTheory.GoodPlaceAtState

theorem natCast_mem_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
  rw [← Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  refine Ideal.subset_span ⟨(n : 𝓞 K), h, ?_⟩
  simp

theorem natCast_mem_of_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal) : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have := natCast_mem_conjPl (Formalism.DivisionValues.conjPl w) n h
  rwa [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this

end GlobalTheory.GoodPlaceAtState

theorem GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  intro K B f T w P x v hs hv
  have hc := x.m.z.pins.char
  have hA := hc.allPl
  have hL := hc.base.lev
  have hlow : ∀ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro k hk
    apply hv
    refine (lowSet_finite (Dof x)).mem_toFinset.2 ⟨(Dof x).host.g k, ?_, ((Dof x).host.g_prime k).ne_zero, hk⟩
    fin_cases k <;> simp [lowAll]
  have hdiv : ∀ PP, PP ∈ x.m.z.R.toRealDat.Sb → ∃ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hm : PP ∈ x.m.z.R.Pg := by rw [← hA]; exact hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    exact ⟨k, Formalism.L2.Host.PiBar.overP _ hk⟩

  unfold GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace
  refine ⟨⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hs, fun hm => ?_, fun Q hQ he => ?_⟩, fun hm => ?_⟩
  · obtain ⟨k, hk⟩ := hdiv v hm
    exact hlow k hk
  · obtain ⟨k, hk⟩ := hdiv Q hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
    rw [he] at hk
    exact hlow k (GlobalTheory.GoodPlaceAtState.natCast_mem_of_conjPl v _ hk)
  · rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    · exact hlow 0 h
    · exact hlow 1 h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectio
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.SplitPull

theorem apply_eq_zero_of_isotropic {X : Type} [AddCommGroup X] {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) {d : X} (hd : x d d = 0) (z : X) : x d z = 0 := by
  by_contra h
  have h1 := hp ((-(x d z * (x z z + 1))) • d + z)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hd, hs z d] at h1
  have h2 : 1 ≤ x d z * x d z := mul_self_pos.2 h
  have h3 := hp z
  nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ x z z + 1 by omega)]

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
  {r : X →ₗ[O] X₁} {s : X₁ →ₗ[O] X}

def pullHom (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_pull (h : ∀ a, r (s a) = a) (β : LinearMap.BilinForm ℤ X₁) : pull s (pull r β) = β :=
  LinearMap.ext₂ fun a b => by simp [h]

theorem pull_injective (h : ∀ a, r (s a) = a) : Function.Injective (pull r) :=
  Function.LeftInverse.injective (pull_pull h)

theorem eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) (hv : ∀ y, pull r β y y = 0 → x y y = 0) :
    pull r (pull s x) = x := by
  have key : ∀ a z, x (s (r a)) z = x a z := fun a z => by
    have := apply_eq_zero_of_isotropic hs hp (hv (a - s (r a)) (by simp [h])) z
    rw [map_sub, LinearMap.sub_apply] at this
    omega
  refine LinearMap.ext₂ fun a b => ?_
  rw [pull_apply, pull_apply, key, hs, key, hs]

variable [Module.Finite O X] [Module.Finite O X₁]

theorem inFace_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    InFace bar ψ lab (pull r β) (pull r x) ↔ InFace bar ψ lab β x := by
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have e : pull r β + pull r x = pull r (β + x) := rfl
  unfold InFace
  rw [e]
  simp only [evalZ_pull _ hr, pull_apply]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ x y y)).symm
    (and_congr (hr.forall (p := fun y => β y y = 0 → x y y = 0)).symm Iff.rfl))
  rw [← pull_pull h x]
  exact pull_mem s hx

theorem InFace_eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hx : InFace bar ψ lab (pull r β) x) : ∃ x₁, pull r x₁ = x :=
  ⟨_, eq_pull h hx.1.1 hx.2.1 hx.2.2.1⟩

theorem isIndec_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    IsIndec bar ψ lab (pull r β) (pull r x) ↔ IsIndec bar ψ lab β x := by
  have hne : ∀ y : LinearMap.BilinForm ℤ X₁, pull r y ≠ 0 ↔ y ≠ 0 := fun y =>
    (pull_injective h).ne_iff' (rfl : pull r 0 = 0)
  refine and_congr (inFace_pull_iff h) (and_congr (hne x) ⟨fun H y z hy hz y0 z0 e => ?_, fun H y z hy hz y0 z0 e => ?_⟩)
  · exact H _ _ ((inFace_pull_iff h).2 hy) ((inFace_pull_iff h).2 hz) ((hne y).2 y0) ((hne z).2 z0) (by rw [← e]; rfl)
  · obtain ⟨y, rfl⟩ := InFace_eq_pull h hy
    obtain ⟨z, rfl⟩ := InFace_eq_pull h hz
    exact H y z ((inFace_pull_iff h).1 hy) ((inFace_pull_iff h).1 hz) ((hne y).1 y0) ((hne z).1 z0)
      (pull_injective h e)

theorem isMarked_pull_iff' (h : ∀ a, r (s a) = a) (i : ℕ) (β : LinearMap.BilinForm ℤ X₁) :
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  classical
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have hsum : ∀ S : Finset (LinearMap.BilinForm ℤ X₁), ∑ x ∈ S.map ⟨pull r, pull_injective h⟩, x = pull r (∑ x ∈ S, x) :=
    fun S => by
      rw [Finset.sum_map]
      exact (map_sum (pullHom r) (fun x => x) S).symm
  unfold IsMarked
  rw [evalZ_pull _ hr]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ β y y)).symm
    (and_congr ⟨fun H k β' e => H k (pull r β') (by rw [← e]; rfl), fun H k β' e => H k (pull s β') ?_⟩
      (and_congr Iff.rfl ⟨?_, ?_⟩)))
  · rw [← pull_pull h β]
    exact pull_mem s hx
  · rw [← pull_pull h β, ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    have hS' : (S.preimage (pull r) (pull_injective h).injOn).map ⟨pull r, pull_injective h⟩ = S := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ?_⟩
      obtain ⟨y, rfl⟩ := InFace_eq_pull h ((hS x).1 hx).1
      exact ⟨y, hx, rfl⟩
    refine ⟨S.preimage (pull r) (pull_injective h).injOn, fun x => ?_, k, hk, pull_injective h ?_⟩
    · rw [Finset.mem_preimage, hS, isIndec_pull_iff h]
    · rw [← hsum, hS', ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    refine ⟨S.map ⟨pull r, pull_injective h⟩, fun x => ?_, k, hk, ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (isIndec_pull_iff h).2 ((hS y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := InFace_eq_pull h hx.1
        exact ⟨y, (hS y).2 ((isIndec_pull_iff h).1 hx), rfl⟩
    · rw [hsum, ← e]; rfl

theorem isMarked_pull_iff : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁,
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β :=
  fun _ _ _ _ _ i _ _ _ _ _ _ _ _ _ _ h β => isMarked_pull_iff' h i β

end GlobalTheory.PolFan.Mark.SplitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntForms
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPrim_eq_one_of_smul_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (β : LinearMap.BilinForm ℤ X) (hβ : β ∈ balForms bar X), IsPrim bar (⟨β, hβ⟩ : balForms bar X) →
  ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar X _ _ β hβ hp k β' hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exfalso
    have h0 : (⟨β, hβ⟩ : balForms bar X) = 0 := Subtype.ext (by simpa using hk.symm)
    rw [h0] at hp
    exact not_isPrim_zero hp
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hval : ∀ y z, (k : ℤ) * β' y z = β y z := by
    intro y z
    rw [← hk]
    simp
  have hb : β' ∈ balForms bar X := by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.1 y z
    · apply mul_left_cancel₀ hk0
      rw [hval, hval]
      exact hβ.2 a y z
  refine hp k ⟨β', hb⟩ (Subtype.ext ?_)
  simp [← hk]

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.RayPrimeOfNorm

theorem isRayPrime_of_norm_eq : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  intro D i jE hp ⟨π, hK, hnorm, hm⟩
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : IsScalarTower ℚ D.host.E Qb := IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ Qb) (jE.comp (algebraMap ℚ D.host.E))) x
  let σ : Qb →ₐ[ℚ] Qb := (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).liftNormal Qb
  have hσ : ∀ x : D.host.E, σ (jE x) = jE (D.host.conj x) := fun x =>
    AlgHom.liftNormal_commutes (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) Qb x
  refine ⟨hp, jE (π : D.host.E), (IntermediateField.mem_map _).2 ⟨_, hK, rfl⟩, ?_, ?_, σ, ?_⟩
  · exact (RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom
  · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hm0 : (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = 0
    · rw [hm0, div_zero]; exact isIntegral_zero
    · have e : (jE (π : D.host.E) - 1) / (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = jE (y : D.host.E) := by
        rw [div_eq_iff hm0]
        have e1 := congrArg (fun z : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E z)) hy
        simp only [map_mul, map_sub, map_one, map_natCast] at e1
        push_cast at e1 ⊢
        exact e1.symm
      rw [e]
      exact (RingOfIntegers.isIntegral_coe y).map jE.toIntAlgHom
  · rw [hσ, ← map_mul, hnorm, map_natCast]

end GlobalTheory.RayPrimeOfNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointCondThird
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.JointConditionThird

theorem jointCond_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalDatumCompatibility D' := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  refine GlobalTheory.DesignBC.jointCond_of_definite _ fun j h1 h2 => ?_
  have h := (w.st x.o.Z).B.toPre.V_posDef j h1 h2
  intro τ
  exact Or.inl (h τ)

end GlobalTheory.HeightCounting.Up.JointConditionThird
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jumpsCard_of_built (hH : HtCard) {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} (b : NBuilt hL D')
    (fr : OmFrame b.D) (hp : PhtOn b.A.wd fr fun _ _ _ _ => True) : JumpsCard D'.nd D'.naut := by
  obtain ⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  intro i a r w τ hw hτ hdR
  have hdA := ((Au.wdOf i a r w).2.2.2.1).mp hdR
  have e1 := (Au.wdOf i a r w).2.2.2.2 τ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have e2 := hp.card _ (L.Y.naut.iotaQC i) a r τ w trivial (fun x => (hτ x).symm) hdA
  show Multiset.card (L.Y.jumpsW i r τ) = a
  rw [e1, e2]

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

theorem jumpsCard_atMem : HtCard → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => JumpsCard (w.D Z).nd (w.D Z).naut := by
  intro hH hL
  refine evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  obtain ⟨fr, -, hp⟩ := (e : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd).pht
  exact jumpsCard_of_built hH c.a.nt.toNBuilt fr hp

end GlobalTheory.HeightCounting.JumpsAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.WitTr

set_option maxHeartbeats 8000000 in

theorem kerT_entC_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (divTr (D := w.D Z) N h Y) (latTr (D := w.D Z) N h Gy) (kerTr w Z N h ker), EntC k' := by
  intro B f T w Z t Y Gy ker k N h hE
  exact ⟨DivTr.ktTr w Z N h k, DivTr.entC_tr w Z N h k hE⟩

end GlobalTheory.Mem.Top.Bl.WitTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  copy_cases h D D'
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  cases C; cases cf'
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_basis : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (a : ∀ σ : E →+* ℂ, Fin (Dw.mult σ + 1) → GL (Fin n) Γ(Z.X, U)), (∀ σ (r : Fin (Dw.mult σ + 1)), LatCover.StepAt Z B g L σ r hU m (a σ r)) → ∀ (c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)), (∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l) → (∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, c σ i l = ((a σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, U)) l j) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l) := by
  first | exact @GlobalTheory.LocM.LatCover.exists_frame_of_rows | exact GlobalTheory.LocM.LatCover.exists_frame_of_rows | (intros; apply GlobalTheory.LocM.LatCover.exists_frame_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_injective : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (σ : E →+* ℂ) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ (Dw.mult σ) hU m a → ∀ x : Z.X, x ∈ U → Dw.mult σ ≤ n := by
  first | exact @GlobalTheory.LocM.LatCover.mult_le_rank | exact GlobalTheory.LocM.LatCover.mult_le_rank | (intros; apply GlobalTheory.LocM.LatCover.mult_le_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberRankStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_fiber_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l := by
  first | exact @GlobalTheory.LocM.LatCover.exists_coordEquiv | exact GlobalTheory.LocM.LatCover.exists_coordEquiv | (intros; apply GlobalTheory.LocM.LatCover.exists_coordEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepFrameFiberStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_frame_fiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  first | exact @GlobalTheory.LocM.LatNorm.stepAt_of_frame | exact GlobalTheory.LocM.LatNorm.stepAt_of_frame | (intros; apply GlobalTheory.LocM.LatNorm.stepAt_of_frame <;> assumption)
end

