import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0055
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0002
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0037
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResEmbEx
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem res_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) :=
  _root_.UpperTheory.Reformulated.B.Qk69.res_algClosed A

private theorem res_surj {Ω : Type} [Field Ω] [CharZero Ω] (hΩ : ∀ x : Ω, IsAlgebraic ℤ x) (A : ValuationSubring Ω) {κ : Type} [Field κ]
    [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (e : κ →+* IsLocalRing.ResidueField A) : Function.Surjective e := by
  letI := e.toAlgebra
  haveI : Algebra.IsIntegral κ (IsLocalRing.ResidueField A) := ⟨fun z => by
    obtain ⟨z', rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨P₀, h0, hP₀⟩ := hΩ (z' : Ω)
    have hP : aeval (z' : Ω) P₀.primPart = 0 := by
      have h1 := congrArg (aeval (z' : Ω)) P₀.eq_C_content_mul_primPart
      rw [hP₀, map_mul, aeval_C] at h1
      have h2 : algebraMap ℤ Ω P₀.content ≠ 0 := by
        simpa [Polynomial.content_eq_zero_iff] using h0
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    have hA : aeval z' P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply Ω z' P₀.primPart
      change aeval (z' : Ω) _ = _ at h1
      rw [hP] at h1
      exact Subtype.val_injective h1.symm
    have hR : aeval (IsLocalRing.residue A z') P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply (IsLocalRing.ResidueField A) z' P₀.primPart
      rw [hA, map_zero] at h1
      exact h1
    have hQ : P₀.primPart.map (algebraMap ℤ κ) ≠ 0 := by
      intro h
      have hdvd : C (p : ℤ) ∣ P₀.primPart := (C_dvd_iff_dvd_coeff _ _).2 fun n => by
        have h1 := congrArg (fun q => q.coeff n) h
        simp only [coeff_map, coeff_zero] at h1
        have h2 := congrArg e h1
        simp only [eq_intCast, map_intCast, map_zero] at h2
        exact (CharP.intCast_eq_zero_iff _ p _).1 h2
      exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit (P₀.isPrimitive_primPart _ hdvd)
    refine IsAlgebraic.isIntegral ⟨_, hQ, ?_⟩
    rw [aeval_def, eval₂_map, Subsingleton.elim ((algebraMap κ (IsLocalRing.ResidueField A)).comp (algebraMap ℤ κ))
      (algebraMap ℤ (IsLocalRing.ResidueField A))]
    exact hR⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := IsLocalRing.ResidueField A)).2

theorem UpperTheory.Gal.InertialTypesAlt.resEmbEx :
    ResEmbEx := by
  intro E Ω _ _ _ _ _ A v hv
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI := res_algClosed A
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A,
      ∀ x, e₀ (DiscreteGroups.sglob.DzType.kappaP v x) = DiscreteGroups.sglob.DzType.kappaQ A x := by
    refine ⟨RingHom.liftOfSurjective _ (DiscreteGroups.sglob.DzType.kappa_surj_O v) ⟨DiscreteGroups.sglob.DzType.kappaQ A, fun x hx => ?_⟩,
      fun x => ?_⟩
    · rw [DiscreteGroups.sglob.DzType.kappa_ker_O, ← DiscreteGroups.sglob.DzType.kappa_ker_A A v hv] at hx
      exact hx
    · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[v.adicCompletion E]
  haveI : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[v.adicCompletion E] p⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := charP_of_injective_ringHom e₀.injective p
  letI := e₀.toAlgebra
  let e : AlgebraicClosure 𝓀[v.adicCompletion E] →ₐ[𝓀[v.adicCompletion E]] IsLocalRing.ResidueField A := IsAlgClosed.lift
  have hres : ResEmb A v (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A) := by
    intro x y z hy hz
    have h1 : IsLocalRing.residue 𝒪[v.adicCompletion E] y = DiscreteGroups.sglob.DzType.kappaP v x := by
      rw [DiscreteGroups.sglob.DzType.kappaP, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hy)
    have h2 : IsLocalRing.residue A z = DiscreteGroups.sglob.DzType.kappaQ A x := by
      rw [DiscreteGroups.sglob.DzType.kappaQ, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hz)
    rw [h1, h2, ← he₀]
    exact e.commutes _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hΩ : ∀ x : Ω, IsAlgebraic ℤ x := by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hs := res_surj hΩ A p (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
  let e' := RingEquiv.ofBijective (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
    ⟨RingHom.injective _, hs⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField 𝓀[v.adicCompletion E]
  refine ⟨⟨_, hres⟩, θ.comp (e'.symm : IsLocalRing.ResidueField A →* _), fun x y hx hy h => ?_⟩
  exact e'.symm.injective (hθ _ _ (by simpa using hx) (by simpa using hy) h)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStepSplit
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.stepSplit :
    StableOf → ResEmbCompat → LblIso → ∀ P₀, StepAt P₀ id := by
  intro hS hC hI P₀ K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp n hn π P hW A Θ hΘ v w hsplit hunr e e' he he' τ τ' hτ hτ' a hP ha
  refine ⟨a, Relation.ReflTransGen.refl, ?_⟩
  obtain ⟨-, hSL⟩ := hS K M hp n hn π P hW
  obtain ⟨r, j, h1, h2, h3⟩ := hC K M Ω A v w e e' he he'
  have hs : UpperTheory.ConvolutionTheory.GM.Split M v := hsplit
  let i : v.adicCompletion K ≃+* w.1.adicCompletion M :=
    RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs w⟩
  have hi : ∀ x, i x = completionMap v w.1 x := fun _ => rfl
  have hic : Continuous i := continuous_completionMap v w.1
  have hal : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x) := fun x => by
    rw [hi, completionMap_algebraMap, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  obtain ⟨f, hf⟩ := hSL v w.1 i hic hal τ τ' hτ hτ'
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 K)).ne'
  have hle : ∀ x y : w.1.adicCompletion M, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion M)) Valued.v x y
  have hle' : ∀ x y : v.adicCompletion K, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v x y
  have hv : ∀ x : v.adicCompletion K, valuation _ (i x) ≤ 1 ↔ valuation _ x ≤ 1 := fun x => by
    have a1 := hle (i x) (i 1)
    have a2 := hle' x 1
    rw [map_one (valuation (v.adicCompletion K))] at a2
    rw [map_one i, map_one (valuation (w.1.adicCompletion M))] at a1
    rw [a1, a2, ← map_one i, hi, hi, valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0
  have hcond : ∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y) :=
    fun x y hy => by rw [h2, h1 x y hy]
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom :=
    MonoidHom.ext fun x => congrArg Θ (h3 x)
  exact hI _ _ i hv j hcond (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ f hf a (by rw [hθ]; exact ha)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSubqMap
section
namespace UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

section SlopeTestRemainingChoices

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori
open GlobalTheory.Parabolic (mem_fixed)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = N} {W V Z : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

private theorem isSmooth_sub (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    IsSmooth S.toRepresentation := fun y => by
  have : {g : GL (Fin N) k | S.toRepresentation g y = y} =
      {g : GL (Fin N) k | parInd (stdBlocks d hd) ρ g y.1 = y.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_parInd _ _ y.1

private theorem levelZeroMap_surjective {S : Subrepresentation (parInd (stdBlocks d hd) ρ)}
    {π : Representation ℂ (GL (Fin N) k) V} (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) : Function.Surjective (levelZeroMap f) := by
  intro v
  obtain ⟨u0, hu0⟩ := hf v.1
  obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (isSmooth_sub S) DepthZero.isCompact_KOne₁
    f.toLinearMap u0 fun h hh => by
      show f (S.toRepresentation h u0) = f u0
      rw [f.isIntertwining, hu0]
      exact mem_fixed.1 v.2 h hh
  exact ⟨⟨u, hu⟩, Subtype.ext (e.trans hu0)⟩

private def evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    fixed S.toRepresentation (KOne k (Fin N)) →ₗ[ℂ] W where
  toFun u := (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOne_redK (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (κ : KO k (Fin N)) (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S (levelZero S.toRepresentation (redK k (Fin N) κ) u) =
      (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 κ := by
  show ((levelZero S.toRepresentation (redK k (Fin N) κ) u).1.1 : IndSp (stdBlocks d hd) ρ).1.1 1 = _
  rw [levelZero_apply]
  show ((parInd (stdBlocks d hd) ρ (κ : GL (Fin N) k) u.1.1 : IndSp (stdBlocks d hd) ρ)).1.1 1 = _
  rw [parInd_apply, one_mul]

private theorem val_mul_of_mem (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) (x : GL (Fin N) k) {c : GL (Fin N) k}
    (hc : c ∈ KOne k (Fin N)) :
    (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 (x * c) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 x := by
  have h : S.toRepresentation c u.1 = u.1 := mem_fixed.1 u.2 c hc
  have h2 : parInd (stdBlocks d hd) ρ c u.1.1 = u.1.1 := congrArg Subtype.val h
  exact congrArg (fun F : IndSp (stdBlocks d hd) ρ => F.1.1 x) h2

private theorem leviKOne_le_leviK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} {d : Fin s → ℕ} :
    leviKOne k (fun a => Fin (d a)) ≤ leviK k (fun a => Fin (d a)) := by
  intro l hl
  unfold leviKOne at hl
  unfold leviK
  rw [Subgroup.mem_pi] at hl ⊢
  exact fun a ha => GlobalTheory.StepData.KOne_le_KO (hl a ha)

private theorem evalOne_mem_fixed (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S u ∈ fixed ρ (leviKOne k fun a => Fin (d a)) := by
  rw [mem_fixed]
  intro l hl
  have hpar := leviEmb_mem_parab k (stdBlocks d hd) l
  have hlaw := parInd_law (stdBlocks d hd) ρ (u.1.1 : IndSp (stdBlocks d hd) ρ) ⟨_, hpar⟩ 1
  have hK : leviEmb k (stdBlocks d hd) l ∈ KOne k (Fin N) := jLevi_le_KOne _ ⟨l, hl, rfl⟩
  have h4 := val_mul_of_mem S u 1 hK
  rw [one_mul] at h4
  simp only [mul_one, leviProj_leviEmb, deltaHalf_of_mem_leviK (leviKOne_le_leviK hl)] at hlaw
  show ρ l ((u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  rw [h4] at hlaw
  simpa using hlaw.symm

private theorem val_of_redK_mem (hPF : ParaFactor) (F : IndSp (stdBlocks d hd) ρ)
    (hF : ∀ x, ∀ c ∈ KOne k (Fin N), F.1.1 (x * c) = F.1.1 x)
    (κ₀ : KO k (Fin N)) (hκ : redK k (Fin N) κ₀ ∈ parab 𝓀[k] (stdBlocks d hd)) :
    ∃ x : leviK k fun a => Fin (d a),
      redLevi k _ x = leviProj 𝓀[k] (stdBlocks d hd) ⟨redK k (Fin N) κ₀, hκ⟩ ∧
      F.1.1 κ₀ = ρ (x : Levi k fun a => Fin (d a)) (F.1.1 1) := by
  have hg : (κ₀ : GL (Fin N) k) ∈ parahoric k (stdBlocks d hd) := (coe_mem_levelPre κ₀).2 hκ
  obtain ⟨p, x, -, hpx, hred, c, hc, hgp⟩ := (hPF k (stdBlocks d hd)).1 ⟨κ₀, hg⟩
  have h3 := parInd_law (stdBlocks d hd) ρ F p 1
  rw [mul_one, hpx, deltaHalf_of_mem_leviK x.2, Units.val_one, one_smul] at h3
  have h4 : (κ₀ : GL (Fin N) k) = p * c := hgp
  refine ⟨x, hred, ?_⟩
  rw [h4, hF _ c hc]
  exact h3

set_option maxHeartbeats 1000000 in

private theorem evalOne_parab (hPF : ParaFactor)
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) (h : parab 𝓀[k] (stdBlocks d hd))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    Φ (evalOne S (levelZero S.toRepresentation (h : GL (Fin N) 𝓀[k]) u)) =
      κ (leviProj 𝓀[k] (stdBlocks d hd) h) (Φ (evalOne S u)) := by
  rcases h with ⟨h, hmem⟩
  obtain ⟨κ₀, rfl⟩ := redK_surjective h
  obtain ⟨x, hx1, hx2⟩ := val_of_redK_mem hPF (u.1.1 : IndSp (stdBlocks d hd) ρ)
    (fun y c hc => val_mul_of_mem S u y hc) κ₀ hmem
  exact (congrArg Φ ((evalOne_redK S κ₀ u).trans hx2)).trans
    ((hΦ x _).trans (congrArg (fun g => κ g (Φ (evalOne S u))) hx1))

private theorem eq_zero_of_evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N)))
    (hu : ∀ γ : GL (Fin N) 𝓀[k], evalOne S (levelZero S.toRepresentation γ u) = 0) : u = 0 := by
  have hF : (u.1.1 : IndSp (stdBlocks d hd) ρ) = 0 :=
    UpperTheory.TNZ.step_indDetK k s N d hd W ρ _ 0 fun κ hκ => by
      have := hu (redK k (Fin N) ⟨κ, hκ⟩)
      rw [evalOne_redK] at this
      exact this
  exact Subtype.ext (Subtype.ext hF)

private theorem main (hPF : ParaFactor) {π : Representation ℂ (GL (Fin N) k) V}
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (hinj : ∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0)
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (sec : fixed π (KOne k (Fin N)) →ₗ[ℂ] fixed S.toRepresentation (KOne k (Fin N)))
    (hs : ∀ g x, sec (levelZero π g x) = levelZero S.toRepresentation g (sec x))
    (hinv : Function.Injective sec)
    (hfix : fixed π (KOne k (Fin N)) ≠ ⊥) :
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x) := by
  obtain ⟨x0, hx0mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  let y0 : fixed π (KOne k (Fin N)) := ⟨x0, hx0mem⟩
  have hsx : sec y0 ≠ 0 := by
    intro h0
    apply hx0
    have h1 := hinv (h0.trans (map_zero sec).symm)
    exact congrArg Subtype.val h1
  have hγ : ∃ γ, evalOne S (levelZero S.toRepresentation γ (sec y0)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsx (eq_zero_of_evalOne S _ hc)
  obtain ⟨γ, hγ⟩ := hγ
  refine ⟨Φ ∘ₗ (evalOne S ∘ₗ sec), ?_, ?_⟩
  · intro h0
    apply hγ
    apply hinj _ (evalOne_mem_fixed S _)
    have h1 := LinearMap.congr_fun h0 (levelZero π γ y0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs] at h1
    exact h1
  · intro p x
    have h3 := evalOne_parab hPF hΦ S p (sec x)
    calc (Φ ∘ₗ (evalOne S ∘ₗ sec)) (levelZero π p x)
        = Φ (evalOne S (levelZero S.toRepresentation p (sec x))) :=
          congrArg (fun w => Φ (evalOne S w)) (hs _ _)
      _ = _ := h3

end SlopeTestRemainingChoices

end UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Gal.InertialTypesAlt.SubquotientMaps in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.subqMap :
    FinSec → UpperTheory.Gal.TypesAndIwahori.ParaFactor → SubqMap := by
  intro hSec hPF k _ _ _ _ N s d hd W V Z _ _ _ _ _ _ ρ π κ Φ hΦ hinj hsq hfix
  obtain ⟨S, f, hf⟩ := hsq
  have : Finite (GL (Fin N) 𝓀[k]) := inferInstance
  obtain ⟨sec, hs, hfs⟩ := hSec (GL (Fin N) 𝓀[k])
    (fixed S.toRepresentation (KOne k (Fin N))) (fixed π (KOne k (Fin N)))
    (levelZero S.toRepresentation) (levelZero π) (levelZeroMap f).toLinearMap
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _ (levelZeroMap f) g x) (levelZeroMap_surjective f hf)
  exact main hPF hΦ hinj S sec hs (Function.LeftInverse.injective hfs) hfix
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameRead
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.TameReduction

section Res

variable {Ω : Type} [Field Ω]

private noncomputable def toRes (A : ValuationSubring Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp
    { toFun := fun x => ⟨algebraMap F Ω (x : F), ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.map (algebraMap F Ω).toIntAlgHom)⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem toRes_eq_zero_iff (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F] [Algebra F Ω] (x : 𝓞 F) :
    toRes A F x = 0 ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := by
  unfold toRes
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact A.valuation_lt_one_iff _

private theorem exists_emb {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) {K : Type} [Field K] (red : 𝓞 F →+* K)
    (hs : Function.Surjective red) (hk : RingHom.ker red = v.asIdeal) :
    ∃ ι : K →+* IsLocalRing.ResidueField A, ∀ x, ι (red x) = toRes A F x := by
  refine ⟨RingHom.liftOfSurjective red hs ⟨toRes A F, fun x hx => ?_⟩, fun x => ?_⟩
  · rw [hk] at hx
    rw [RingHom.mem_ker, toRes_eq_zero_iff]
    exact (hv x).2 hx
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem residue_eq_toRes {A : ValuationSubring Ω} {F : Type} [Field F] [NumberField F] [Algebra F Ω]
    (z : A) (x : 𝓞 F) (h : A.valuation ((z : Ω) - algebraMap F Ω (x : F)) < 1) :
    IsLocalRing.residue A z = toRes A F x := by
  unfold toRes
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (A.valuation_lt_one_iff _).2 h

end Res

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem res_read {g n : ℕ} [Fact g.Prime] (hn : 0 < n) (D : UpperTheory.Zero.LLC.Ext h g n) (R : Ine (F := E) A →* D.Kˣ) (hR : D.Res R)
    (t : Ine (F := E) A) : ∃ (t' : Ine (F := D.E') A) (x : 𝓞 D.E'),
      (∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z) ∧
      Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - algebraMap D.E' (D.w'.adicCompletion D.E') (x : D.E')) < 1 ∧
      ((R t : D.Kˣ) : D.K) = D.red x := by
  obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _ (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' ⟨t', ht'⟩).le
  have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
  refine ⟨⟨t', ht'⟩, x, fun z => by rw [← e]; rfl, hx, ?_⟩
  have := hR t ⟨t', ht'⟩ x (Units.mk0 _ hne) e.symm rfl hx
  rw [this]; rfl

end UpperTheory.Gal.InertialTypesAlt.TameReduction

open UpperTheory.Gal.InertialTypesAlt.TameReduction in
theorem UpperTheory.Gal.InertialTypesAlt.tameRead :
    TameRead := by
  intro E Ω _ _ _ _ _ A v h g _ m hm D R hR
  obtain ⟨ι, hι⟩ := exists_emb D.h' D.red D.surj D.ker
  refine ⟨ι, fun t ϖ hϖ z hz => ?_⟩
  obtain ⟨t', x, ht, hx, hr⟩ := res_read hm D R hR t
  have hg := DiscreteGroups.sglob.DzType.natCast_mem_of_normV D.w' g m hm D.card
  have h1 := UpperTheory.Zero.LLC.tameRecAll D.E' Ω g A D.w' D.h' hg D.unr D.a' D.ha' ϖ (by rw [D.card]; exact hϖ) t' x hx
  rw [hr, hι]
  refine (residue_eq_toRes z x ?_).symm
  rw [hz, ht]
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensTr
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PUnifTower
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unifTower :
    LiftsFix → PlaceEx → UnrOfIne → UnifTower := by
  intro hF hP hU E Ω _ _ _ n X Y hXY
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A _ v w hv hw g hg
    have hvw : v = w := by
      apply HeightOneSpectrum.ext
      ext x
      rw [← hv x, hw x]
    rw [← hvw]
    exact hg
  | @head X Z hs hZY ih =>
    intro A hI v w hv hw g hg
    obtain ⟨_, _, _, _, _⟩ := hs
    obtain ⟨u, hu, -⟩ := hP X.K Z.K Ω A v hv n Z.π
    have hfix : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht z
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY z
      have := hI t ht y
      rwa [hy] at this
    have hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2 := by
      have h3 := (hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg
      rwa [map_natCast] at h3
    refine ih A (fun t ht => ?_) u w hu hw g hgu
    exact hI (AlgEquiv.restrictScalars X.K t) ht
end

