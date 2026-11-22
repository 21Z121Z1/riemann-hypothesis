import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FundamentalSequenceContinuityAll
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.CupFlip

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

theorem continuous_act (A : GRep G Qp LL O) : Continuous fun p : G × A.V => A.ρ p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A.V
  let b := Module.finBasis LL A.V
  have e : (fun p : G × A.V => A.ρ p.1 p.2) =
      fun p => ∑ i, (b.repr p.2 i) • A.ρ p.1 (b i) := by
    funext p
    have h := congrArg (A.ρ p.1) (b.sum_repr p.2)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun v : A.V => b.coord i v :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (h1.comp continuous_snd).smul ((A.cont (b i)).comp continuous_fst)

theorem continuous_pair (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) :
    Continuous fun p : A.V × A'.V => P p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A'.V
  exact IsModuleTopology.continuous_bilinear_of_finite_left P

theorem continuous_cup (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) {a : G → A.V}
    {b : G → A'.V} (ha : Continuous a) (hb : Continuous b) : Continuous (cupL A'.ρ P a b) :=
  (continuous_pair A A' P).comp ((ha.comp continuous_fst).prodMk
    ((continuous_act A').comp (continuous_fst.prodMk (hb.comp continuous_snd))))

end Top

section Cup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} {P : V →ₗ[LL] V' →ₗ[LL] LL}

omit [TopologicalSpace G] in

theorem char_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (g : G) (x : V) (y : V') : charRep (cycLL PD LL) g (P x y) = P (ρ g x) (ρ' g y) := by
  rw [hd]
  rfl

theorem d2_cup (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (cupL ρ' P a b) = 0 := by
  funext ⟨g, h, k⟩
  show charRep (cycLL PD LL) g (P (a h) (ρ' h (b k))) - P (a (g * h)) (ρ' (g * h) (b k)) +
    P (a g) (ρ' g (b (h * k))) - P (a g) (ρ' g (b h)) = 0
  rw [char_pair PD hd, ha, hb, map_mul, Module.End.mul_apply]
  simp only [map_add, LinearMap.add_apply]
  ring

theorem d1_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) (fun g => P (a g) (b g)) =
      -cupL ρ' P a b - cupL ρ P.flip b a := by
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P (a h) (b h)) - P (a (g * h)) (b (g * h)) + P (a g) (b g) =
    -P (a g) (ρ' g (b h)) - P (ρ g (a h)) (b g)
  rw [char_pair PD hd, ha, hb]
  simp only [map_add, LinearMap.add_apply]
  ring

variable [TopologicalSpace LL]

theorem cob_of_flip [IsTopologicalRing LL]
    (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P (a g) (b g))
    (h : CobL PD (cupL ρ P.flip b a)) : CobL PD (cupL ρ' P a b) := by
  obtain ⟨u, hu, e⟩ := h
  refine ⟨-u - fun g => P (a g) (b g), hu.neg.sub hc, ?_⟩
  rw [map_sub, map_neg, e, d1_pair PD hd ha hb]
  abel

theorem cob_of_left (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} {x : V} (ha : ∀ g, a g = ρ g x - x)
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P x (b g)) :
    CobL PD (cupL ρ' P a b) := by
  refine ⟨fun g => P x (b g), hc, ?_⟩
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P x (b h)) - P x (b (g * h)) + P x (b g) =
    P (a g) (ρ' g (b h))
  rw [char_pair PD hd, ha, hb]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  ring

end Cup

theorem cup_flip : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 ((D.loc l).PD K) A.ρ A'.ρ P → IsDual1 ((D.loc l).PD K) A'.ρ A.ρ P.flip ∧ ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, Continuous (cupL A'.ρ P a b) ∧ ReciprocityTheory.Def.d2 (charRep (cycLL ((D.loc l).PD K) LL)) (cupL A'.ρ P a b) = 0 ∧ (CobL ((D.loc l).PD K) (cupL A'.ρ P a b) ↔ CobL ((D.loc l).PD K) (cupL A.ρ P.flip b a)) ∧ ((a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ) → CobL ((D.loc l).PD K) (cupL A'.ρ P a b)) := by
  intro D l _ K LL _ _ _ O _ _ hO A A' P hP
  have : IsTopologicalRing LL := hO.2.2.2.1
  have hd := hP.1
  have hdf : ∀ g y x, P.flip (A'.ρ g y) (A.ρ g x) =
      ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) * P.flip y x := fun g y x => hd g x y
  refine ⟨⟨hdf, hP.2.2.1, hP.2.1, hP.2.2.2.symm⟩, fun a ha b hb => ?_⟩
  obtain ⟨hac, hacoc⟩ := ha
  obtain ⟨hbc, hbcoc⟩ := hb
  have hc : Continuous fun g => P (a g) (b g) := (continuous_pair A A' P).comp (hac.prodMk hbc)
  have hflip : CobL ((D.loc l).PD K) (cupL A.ρ P.flip b a) →
      CobL ((D.loc l).PD K) (cupL A'.ρ P a b) := cob_of_flip _ hd hacoc hbcoc hc
  refine ⟨continuous_cup A A' P hac hbc, d2_cup _ hd hacoc hbcoc, ⟨fun h => ?_, hflip⟩, ?_⟩
  · refine cob_of_flip _ (P := P.flip) hdf hbcoc hacoc hc ?_
    rwa [LinearMap.flip_flip]
  · rintro (h | h)
    · obtain ⟨x, hx⟩ := LinearMap.mem_range.1 h
      exact cob_of_left _ hd (x := x) (fun g => by rw [← hx]; rfl) hbcoc
        ((continuous_pair A A' P).comp (continuous_const.prodMk hbc))
    · obtain ⟨y, hy⟩ := LinearMap.mem_range.1 h
      exact hflip (cob_of_left _ (P := P.flip) hdf (x := y) (fun g => by rw [← hy]; rfl) hacoc
        ((continuous_pair A' A P.flip).comp (continuous_const.prodMk hac)))

end GlobalTheory.CompanionTheory.CupFlip
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TopCoh

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

theorem coboundary_of_characters (hT : LocalTateDualityK) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (hK : FiniteDimensional ℚ_[l] K) (n : ℕ) (hn : 0 < n)
    (hχ : Continuous fun g => ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (z : Formalism.GaloisCohomology.GK l K × Formalism.GaloisCohomology.GK l K → M) (hz : Continuous z)
    (hcoc : ∀ g h k, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • z (h, k) - z (g * h, k) +
      z (g, h * k) - z (g, h) = 0)
    (hchar : ∀ ψ : M →+ ZMod (l ^ n), ∃ f : Formalism.GaloisCohomology.GK l K → ZMod (l ^ n), Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) :
    ∃ f : Formalism.GaloisCohomology.GK l K → M, Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M := scalRep M (cycK l K n)
  have hrho : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp
      ((hχ.comp continuous_fst).prodMk continuous_snd)
  have hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _)) := ⟨hz, hcoc⟩
  have hb := (hT l K hK n M rho hn hrho).2.2.2.2
  have hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0 := by
    refine LinearMap.ext fun φ => ?_
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    let φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ.1
    obtain ⟨f, hf, hd⟩ := hchar φ'.toAddMonoidHom
    exact ⟨f, hf, funext fun p => hd p.1 p.2⟩
  have h0 := hb.1 (hzero.trans (map_zero _).symm)
  obtain ⟨c, hc, hd⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact ⟨c, hc, fun g h => congrFun hd (g, h)⟩

theorem coboundary_of_characters_GK : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] (z : ↥(GK K) × ↥(GK K) → M), IsLocallyConstant z → (∀ g h k, (χ g : ZMod (l ^ n)) • z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → (∀ ψ : M →+ ZMod (l ^ n), ∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) → ∃ f : ↥(GK K) → M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  intro hT D l _ K n χ hn hχ M _ _ _ z hz hcoc hchar
  obtain ⟨hΦ1, hΦ2⟩ := GlobalTheory.Cyc.TwistLift.continuous_fixingSubgroupEquiv K.1
  let Ψ : Formalism.GaloisCohomology.GK l K.1 ≃* ↥(GK K) := K.1.fixingSubgroupEquiv.symm
  have hΨ : Continuous Ψ := hΦ1
  have hΨ' : Continuous Ψ.symm := hΦ2
  have hcyc : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = ((D.loc l).χQ (Ψ g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΨ)
  have hval : ∀ g : Formalism.GaloisCohomology.GK l K.1,
      (χ (Ψ g) : ZMod (l ^ n)) = (Formalism.GaloisCohomology.cycK l K.1 n g : ZMod (l ^ n)) := fun g => by
    obtain ⟨u, hu, hu'⟩ := hχ (Ψ g)
    rw [(D.loc l).PD_χ K (Ψ g), ← hχZ] at hu
    rw [← hu', show u = (χZ g : ℤ_[l]) from Subtype.ext hu]
    rfl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨c, hc, hd⟩ := coboundary_of_characters hT l K.1 K.2 n hn
    ((continuous_toZModPow n).comp hχc) M (fun p => z (Ψ p.1, Ψ p.2))
    (hz.continuous.comp (hΨ.prodMap hΨ))
    (fun g h k => by
      have := hcoc (Ψ g) (Ψ h) (Ψ k)
      rw [hval, ← map_mul Ψ, ← map_mul Ψ] at this
      exact this)
    (fun ψ => by
      obtain ⟨f, hf, hd⟩ := hchar ψ
      refine ⟨fun g => f (Ψ g), hf.continuous.comp hΨ, fun g h => ?_⟩
      have := hd (Ψ g) (Ψ h)
      rw [hval, ← map_mul Ψ] at this
      exact this)
  refine ⟨fun g => c (Ψ.symm g), (IsLocallyConstant.iff_continuous _).2 (hc.comp hΨ'), fun g h => ?_⟩
  have := hd (Ψ.symm g) (Ψ.symm h)
  rw [← map_mul Ψ.symm, ← hval] at this
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.TopCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.GenChar

theorem exists_addHom_zmod_ne_zero {N : ℕ} [NeZero N] {A : Type} [AddCommGroup A]
    (hA : ∀ a : A, N • a = 0) {q : A} (hq : q ≠ 0) : ∃ f : A →+ ZMod N, f q ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq
  let c' : A →+ AddCircle (1 : ℚ) := c
  have hc' : c' q ≠ 0 := hc
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  let g : ℤ →+ AddCircle (1 : ℚ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      ((AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Int.castAddHom ℚ))
  have hg : ∀ z : ℤ, g z = QuotientAddGroup.mk ((z : ℚ) * (N : ℚ)⁻¹) := fun z => rfl
  have hgN : g N = 0 := by
    rw [hg, Int.cast_natCast, mul_inv_cancel₀ hN]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨g, hgN⟩
  have hι : ∀ z : ℤ, ι z = g z := fun z => ZMod.lift_coe N ⟨g, hgN⟩ z
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).2 fun m hm => ?_
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
    rw [hι, hg] at hm
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 hm)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have h2 : (z : ℚ) = (N : ℚ) * k := by
      field_simp at hk
      linarith
    exact_mod_cast h2
  have hmem : ∀ a : A, c' a ∈ ι.range := by
    intro a
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (c' a)
    have h1 : N • c' a = 0 := by rw [← map_nsmul, hA, map_zero]
    have h0 : (N • r : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hr]
      exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h0
    refine AddMonoidHom.mem_range.2 ⟨(k : ZMod N), ?_⟩
    rw [hι, hg, ← hr]
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    rw [hk]
    field_simp
  refine ⟨(AddMonoidHom.ofInjective hinj).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict c' ι.range hmem), ?_⟩
  intro h0
  apply hc'
  have h1 : AddMonoidHom.codRestrict c' ι.range hmem q = 0 := by
    have h3 := congrArg (AddMonoidHom.ofInjective hinj) h0
    simpa using h3
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem exists_mul_eq_socle {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) {x : O ⧸ Ideal.span {ϖ ^ (s + 1)}} (hx : x ≠ 0) :
    ∃ o, o * x = Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  have hn : n ≤ s := by
    by_contra hlt
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.succ_le_of_lt (not_le.1 hlt))) _
  refine ⟨Ideal.Quotient.mk _ (↑u⁻¹ * ϖ ^ (s - n)), ?_⟩
  rw [← map_mul, hu]
  congr 1
  calc ↑u⁻¹ * ϖ ^ (s - n) * (↑u * ϖ ^ n) = (↑u⁻¹ * ↑u) * (ϖ ^ (s - n) * ϖ ^ n) := by ring
    _ = ϖ ^ s := by rw [Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hn]

theorem socle_ne_zero {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) :
    Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  omega

theorem exists_generating_character : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  intro O _ _ _ ϖ hϖ r N hN hfin hNmem
  haveI : NeZero N := ⟨by omega⟩
  have htors : ∀ a : O ⧸ Ideal.span {ϖ ^ r}, N • a = 0 := by
    intro a
    have hN0 : ((N : O ⧸ Ideal.span {ϖ ^ r})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}))]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hNmem
    rw [nsmul_eq_mul, hN0, zero_mul]
  have key : ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N,
      ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0 := by
    cases r with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    | succ s =>
      obtain ⟨ψ₀, hψ₀⟩ := exists_addHom_zmod_ne_zero htors (socle_ne_zero hϖ s)
      refine ⟨ψ₀, fun x hx => ?_⟩
      by_contra hne
      obtain ⟨o, ho⟩ := exists_mul_eq_socle hϖ s hne
      have h5 := hx o
      rw [ho] at h5
      exact hψ₀ h5
  obtain ⟨ψ₀, hψ₀⟩ := key
  refine ⟨ψ₀, hψ₀, ?_⟩
  let Φ : (O ⧸ Ideal.span {ϖ ^ r}) → ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    fun o => ψ₀.comp (AddMonoidHom.mulLeft o)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∀ x, ψ₀ ((a - b) * x) = 0 := by
      intro x
      have h6 : ψ₀ (a * x) = ψ₀ (b * x) := DFunLike.congr_fun hab x
      rw [sub_mul, map_sub, h6, sub_self]
    have h7 : a - b = 0 := hψ₀ (a - b) (fun o => by rw [mul_comm]; exact h0 o)
    exact sub_eq_zero.1 h7
  haveI : Finite ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    Finite.of_injective (fun f : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N =>
      (f : (O ⧸ Ideal.span {ϖ ^ r}) → ZMod N)) DFunLike.coe_injective
  have hbij := hinj.bijective_of_nat_card_le (GlobalTheory.natCard_addMonoidHom_zmod_le N _)
  intro ψ
  obtain ⟨o, ho⟩ := hbij.2 ψ
  exact ⟨o, fun x => by rw [← ho]; rfl⟩

end GlobalTheory.CompanionTheory.LocDual.GenChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FundamentalSequenceContinuityAllStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm6_of_D7 : ∀ D : D7, LocalSituation.adm6 D := by
  first | exact @GlobalTheory.CompanionTheory.AdmSix.adm6_all | exact GlobalTheory.CompanionTheory.AdmSix.adm6_all | (intros; apply GlobalTheory.CompanionTheory.AdmSix.adm6_all <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LinearRelationExactSequenceDim
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.InertiaEigenvalues

theorem finrank_along_relation : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  intro k _ H M N Q _ _ _ _ _ _ _ _ _ _ a b R hinj hex hN hQ h0 hb
  let p1 : R →ₗ[k] N := (LinearMap.fst k N Q).comp R.subtype
  let p2 : R →ₗ[k] Q := (LinearMap.snd k N Q).comp R.subtype
  have p1bij : Function.Bijective p1 := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨⟨n, q⟩, hr⟩ h
      have hn : n = 0 := h
      subst hn
      have hq : q = 0 := h0 q hr
      subst hq
      rfl
    · intro n
      obtain ⟨q, hq⟩ := hN n
      exact ⟨⟨(n, q), hq⟩, rfl⟩
  let e : R ≃ₗ[k] N := LinearEquiv.ofBijective p1 p1bij
  let δ : N →ₗ[k] Q := p2.comp e.symm.toLinearMap
  have hδ : ∀ x : R, δ (p1 x) = p2 x := by
    intro x
    have h : e.symm (p1 x) = x := e.symm_apply_apply x
    show p2 (e.symm (p1 x)) = p2 x
    rw [h]
  have hsurj : Function.Surjective δ := by
    intro q
    obtain ⟨n, hn⟩ := hQ q
    exact ⟨n, hδ ⟨(n, q), hn⟩⟩
  have hker : LinearMap.ker δ = LinearMap.range b := by
    ext n
    rw [LinearMap.mem_ker, ← hb n]
    obtain ⟨q, hq⟩ := hN n
    have h1 : δ n = q := hδ ⟨(n, q), hq⟩
    rw [h1]
    constructor
    · rintro rfl
      exact hq
    · intro h
      have h2 : ((n, q) - (n, 0) : N × Q) ∈ R := R.sub_mem hq h
      have h3 : ((n, q) - (n, 0) : N × Q) = (0, q) := by simp
      rw [h3] at h2
      exact h0 q h2
  refine ⟨Module.Finite.of_surjective δ hsurj, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker δ
  have e2 := LinearMap.finrank_range_add_finrank_ker b
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hker] at e1
  rw [← hex] at e2
  have e3 : finrank k (LinearMap.range a) = finrank k H := LinearMap.finrank_range_of_inj hinj
  rw [e3] at e2
  omega

end GlobalTheory.CompanionTheory.InertiaEigenvalues
end

