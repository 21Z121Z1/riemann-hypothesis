import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitQuotientPrimePowEqExponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.LenUnitPow

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem _root_.GlobalTheory.LenUnitPow.natCast_ne_zero : (l : O) ≠ 0 := by
  intro h
  have hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
    intro hbot
    have hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O) := by
      rw [RingHom.mem_ker, map_natCast]; exact h
    rw [hbot, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  have hbot : (⊥ : Ideal O).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ ?_
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit : ¬ IsUnit (l : O) := by
  intro h
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
    rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
  exact hl h

theorem lenUnit_quot_unit_mul_pow (w : Oˣ) (m : ℕ) :
    lenUnit (O := O) l (O ⧸ Ideal.span {(w : O) * (l : O) ^ m}) = (m : ℚ) := by
  have h0 := natCast_ne_zero l (O := O)
  have h1 := natCast_not_isUnit l (O := O)
  unfold lenUnit
  change ((Ring.ord O ((w : O) * (l : O) ^ m)).toNat : ℚ) / ((Ring.ord O (l : O)).toNat : ℚ) = m
  rw [Ring.ord_mul_of_isUnit_left w.isUnit, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero h0),
    Ring.ord_eq_addVal]
  have htop : IsDiscreteValuationRing.addVal O (l : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hz : IsDiscreteValuationRing.addVal O (l : O) ≠ 0 := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← he] at hz ⊢
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_coe, ENat.toNat_coe, Nat.cast_mul]
  exact mul_div_cancel_right₀ _ he0

theorem main : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (w : Oˣ) (m : ℕ),
    lenUnit (O := O) l (O ⧸ Ideal.span {(w : O) * (l : O) ^ m}) = (m : ℚ) :=
  fun l _ _ _ _ _ _ _ w m => lenUnit_quot_unit_mul_pow l w m

end GlobalTheory.LenUnitPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CycBridge

theorem locChi_epsU : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Br.G D.nbr i w hw), Br.locChi D.nbr i w hw (epsU D.nd i) g = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :=
  fun D i w hw g => Units.ext (GlobalTheory.Survey.CrystallineCharacterRatio.locChi_eps D i w hw g)

end GlobalTheory.CycBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOrderAboveLFiniteModules
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocCountFinite

theorem card_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (h : Function.Exact f g) (hg : Function.Surjective g) : Nat.card B = Nat.card A * Nat.card C := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr (g.quotKerEquivOfSurjective hg).toEquiv,
    h.linearMap_ker_eq, ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]

section Abstract

variable {R Γ M' M M'' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup M''] [Module R M''] [TopologicalSpace M''] [DiscreteTopology M'']
  (ρ' : Representation R Γ M') (ρ : Representation R Γ M) (ρ'' : Representation R Γ M'')

abbrev coc (L : Submodule R (H1 ρ)) : Submodule R (Z1 ρ) := L.comap (Submodule.mkQ _)

theorem card_coc (hc : ContAction ρ) (L : Submodule R (H1 ρ)) :
    Nat.card (coc ρ L) * Nat.card (H0 ρ) = Nat.card L * Nat.card M := by
  let B := (B1 ρ).comap (Z1 ρ).subtype
  have hB : B ≤ coc ρ L := fun z hz => by
    have : (Submodule.Quotient.mk z : H1 ρ) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    change (Submodule.Quotient.mk z : H1 ρ) ∈ L
    rw [this]; exact L.zero_mem
  have h1 : Nat.card (coc ρ L) = Nat.card B * Nat.card L := by
    refine card_of_exact (Submodule.inclusion hB) ((Submodule.mkQ B).restrict (p := coc ρ L) (q := L) fun _ h => h)
      (Submodule.inclusion_injective _) (fun z => ?_) (fun x => ?_)
    · constructor
      · intro hz
        exact ⟨⟨z.1, (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hz)⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 b.2)
    · obtain ⟨x, hx⟩ := x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨⟨z, hx⟩, rfl⟩
  have h2 : Nat.card M = Nat.card (H0 ρ) * Nat.card B := by
    refine card_of_exact (H0 ρ).subtype
      (((d0 ρ).codRestrict (Z1 ρ) fun m => coboundaries_le_cocycles ρ hc ⟨m, rfl⟩).codRestrict B fun m => ⟨m, rfl⟩)
      (Submodule.subtype_injective _) (fun m => ?_) (fun x => ?_)
    · constructor
      · intro hm
        refine ⟨⟨m, (mem_riemannRochSpace_iff_regularAt_everywhere ρ m).2 fun g => ?_⟩, rfl⟩
        have : ρ g m - m = 0 := congrFun (congrArg (fun z => z.1.1) hm) g
        exact sub_eq_zero.1 this
      · rintro ⟨b, rfl⟩
        refine Subtype.ext (Subtype.ext (funext fun g => ?_))
        exact sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere ρ _).1 b.2 g)
    · obtain ⟨⟨z, hz⟩, m, hm⟩ := x
      exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
  rw [h1, h2]; ring

theorem card_coc_mul (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc : ContAction ρ) (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card (coc ρ L) = Nat.card (coc ρ' L') * Nat.card (coc ρ'' L'') := by
  refine card_of_exact
    ((cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu).restrict (p := coc ρ' L') (q := coc ρ L) fun z h => (h1 _).2 h)
    ((cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw).restrict (p := coc ρ L) (q := coc ρ'' L'') fun z h => h2 _ h)
    (fun a b h => Subtype.ext (Subtype.ext (funext fun g => hinj (congrFun (congrArg (fun z => z.1.1) h) g))))
    (fun z => ?_) (fun x => ?_)
  · constructor
    · intro hz
      have e1 : ∀ g, u (Function.invFun u (z.1.1 g)) = z.1.1 g := fun g =>
        Function.invFun_eq ((hex _).1 (congrFun (congrArg (fun z => z.1.1) hz) g))
      let z' : Z1 ρ' := ⟨fun g => Function.invFun u (z.1.1 g),
        (continuous_of_discreteTopology (f := Function.invFun u)).comp z.1.2.1, fun g h => hinj (by
          rw [map_add, hu, e1, e1, e1]
          exact z.1.2.2 g h)⟩
      have e : cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z' = z.1 := Subtype.ext (funext e1)
      refine ⟨⟨z', (h1 _).1 ?_⟩, Subtype.ext e⟩
      change Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ' ρ u continuous_of_discreteTopology hu z') ∈ L
      rw [e]; exact z.2
    · rintro ⟨b, rfl⟩
      exact Subtype.ext (Subtype.ext (funext fun g => hex.apply_apply_eq_zero _))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, e⟩ := h3 hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have e' : (Submodule.Quotient.mk (x - cocycles1MapOfEquivariant ρ ρ'' w continuous_of_discreteTopology hw z) : H1 ρ'') = 0 := by
      rw [Submodule.Quotient.mk_sub, sub_eq_zero]
      exact e.symm
    obtain ⟨m, hm⟩ := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ'' _).1 e'
    obtain ⟨m, rfl⟩ := hsurj m
    let b : Z1 ρ := ⟨d0 ρ m, coboundaries_le_cocycles ρ hc ⟨m, rfl⟩⟩
    have hb : (Submodule.Quotient.mk b : H1 ρ) = 0 := (GlobalTheory.SelLeftExact.mk_eq_zero_iff ρ b).2 ⟨m, fun _ => rfl⟩
    refine ⟨⟨z + b, ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    · change (Submodule.Quotient.mk (z + b) : H1 ρ) ∈ L
      rw [Submodule.Quotient.mk_add, hb, add_zero]
      exact hy
    · change w (z.1 g + (ρ g m - m)) = x.1 g
      have : x.1 g - w (z.1 g) = ρ'' g (w m) - w m := hm g
      rw [map_add, map_sub, hw, ← this]
      abel

theorem card_six [Finite M] (u : M' →ₗ[R] M) (hu : ∀ g m, u (ρ' g m) = ρ g (u m)) (hinj : Function.Injective u)
    (w : M →ₗ[R] M'') (hw : ∀ g m, w (ρ g m) = ρ'' g (w m)) (hex : Function.Exact u w) (hsurj : Function.Surjective w)
    (hc' : ContAction ρ') (hc : ContAction ρ) (hc'' : ContAction ρ'')
    (L' : Submodule R (H1 ρ')) (L : Submodule R (H1 ρ)) (L'' : Submodule R (H1 ρ''))
    (h1 : ∀ x, mapH1 ρ' ρ u continuous_of_discreteTopology hu x ∈ L ↔ x ∈ L')
    (h2 : ∀ x ∈ L, mapH1 ρ ρ'' w continuous_of_discreteTopology hw x ∈ L'')
    (h3 : L'' ≤ L.map (mapH1 ρ ρ'' w continuous_of_discreteTopology hw)) :
    Nat.card L * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) = Nat.card (H0 ρ) * (Nat.card L' * Nat.card L'') := by
  have a := card_coc ρ hc L
  have a' := card_coc ρ' hc' L'
  have a'' := card_coc ρ'' hc'' L''
  have b := card_coc_mul ρ' ρ ρ'' u hu hinj w hw hex hsurj hc L' L L'' h1 h2 h3
  have c := card_of_exact u w hinj hex hsurj
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := M)) ?_
  calc _ = (Nat.card L * Nat.card M) * (Nat.card (H0 ρ') * Nat.card (H0 ρ'')) := by ring
    _ = Nat.card (H0 ρ) * ((Nat.card (coc ρ' L') * Nat.card (H0 ρ')) * (Nat.card (coc ρ'' L'') * Nat.card (H0 ρ''))) := by
      rw [← a, b]; ring
    _ = _ := by rw [a', a'', c]; ring

theorem contAction_sub (hc : ContAction ρ) (U : Subgroup Γ) : ContAction (ρ.comp U.subtype) :=
  hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end Abstract

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem finite_places (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) : (placesOver F l).Finite := by
  have h : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    simpa using hl
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem locCountFin : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → LocSat bkP i s κ → LocCount bkP i s κ → LocCountFin bkP i s κ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS hK hL hC Y _ _ _ _ _
  haveI := hS.2.1
  have hfin := finite_places D.host.E (X.l i) (Fact.out : (X.l i).Prime).ne_zero
  have hcont : ∀ (B : Type) [AddCommGroup B] [Module A B] [TopologicalSpace B] [DiscreteTopology B] (v : PlE D.host),
      ContAction ((repOn (Tgl i s) κ B).comp (DecV N v).subtype) := fun B _ _ _ _ v =>
    contAction_sub _ (GlobalTheory.SelLeftExact.contAction_of_tors (X.twistBaseCoefficientRing_isAdic i) _ (GlobalTheory.SelLeftExact.continuous_Tgl i s) κ
      hS.2.2.2.1 (tors_of_finite A B)) _
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  subst hn
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have e1 : ∀ v, Nat.card (bkOn bkP i (Tgl i s) κ Y v) = 1 := fun v => by
      haveI : Subsingleton (H1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : ∀ v, Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) = 1 := fun v => Nat.card_unique
    have e3 : Nat.card Y = 1 := Nat.card_unique
    simp only [e1, e2, e3, one_pow, mul_one]
  · obtain ⟨K, hKa, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule A Y)).resolve_left top_ne_bot
    have hKs : IsSimpleModule A K := isSimpleModule_iff_isAtom.2 hKa
    letI : TopologicalSpace (Y ⧸ K) := ⊥
    haveI : DiscreteTopology (Y ⧸ K) := ⟨rfl⟩
    haveI : Finite (Y ⧸ K) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective K)
    have hex : Function.Exact K.subtype K.mkQ := LinearMap.exact_subtype_mkQ K
    have hcard := card_of_exact K.subtype K.mkQ K.subtype_injective hex K.mkQ_surjective
    have hlt : Nat.card (Y ⧸ K) < Nat.card Y := by
      haveI := IsSimpleModule.nontrivial A K
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2 : 0 < Nat.card (Y ⧸ K) := Nat.card_pos
      rw [hcard]
      nlinarith
    have a := hC K hKs
    have b := ih _ hlt (Y ⧸ K) rfl
    have c : ∀ v ∈ hfin.toFinset, Nat.card (bkOn bkP i (Tgl i s) κ Y v) *
        (Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype)) *
          Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype))) =
        Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype)) *
          (Nat.card (bkOn bkP i (Tgl i s) κ K v) * Nat.card (bkOn bkP i (Tgl i s) κ (Y ⧸ K) v)) := fun v hv => by
      have hv' := hfin.mem_toFinset.1 hv
      refine card_six _ _ _ (K.subtype.compLeft (Fin D.R.r)) (fun g m => repOn_map (Tgl i s) κ K.subtype g.1 m)
        (fun x y h => funext fun a => Subtype.ext (congrFun h a)) (K.mkQ.compLeft (Fin D.R.r))
        (fun g m => repOn_map (Tgl i s) κ K.mkQ g.1 m) (fun m => ⟨fun hm => ?_, ?_⟩) (fun m => ?_)
        (hcont _ v) (hcont _ v) (hcont _ v) _ _ _
        (fun x => ⟨hL v hv' K Y (tors_of_finite A Y) K.subtype K.subtype_injective x,
          localConditionAboveL_coeffMap_functorial bkP i _ κ K.subtype v x⟩)
        (localConditionAboveL_coeffMap_functorial bkP i _ κ K.mkQ v)
        (GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective D N X bkP i s A κ Q hS hK Y (Y ⧸ K) K.mkQ K.mkQ_surjective v)
      · choose m' hm' using fun a => (hex (m a)).1 (congrFun hm a)
        exact ⟨m', funext hm'⟩
      · rintro ⟨m', rfl⟩
        exact funext fun a => hex.apply_apply_eq_zero _
      · choose m' hm' using fun a => K.mkQ_surjective (m a)
        exact ⟨m', funext hm'⟩
    have c' := Finset.prod_congr rfl c
    simp only [Finset.prod_mul_distrib] at c'
    simp only [finprod_mem_eq_finite_toFinset_prod _ hfin] at a b ⊢
    rw [a, b] at c'
    have hpos : 0 < (∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        ∏ v ∈ hfin.toFinset, Nat.card (H0 ((repOn (Tgl i s) κ (Y ⧸ K)).comp (DecV N v).subtype)) :=
      Nat.mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (Finset.prod_pos fun v _ => Nat.card_pos)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [c', hcard, mul_pow]
    ring

end GlobalTheory.LocCountFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.HubLoc

theorem localField_unramified : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  intro D i hs hq hd w hw
  have h2 : D.nd.l i ≠ 2 := fun e => hs (e ▸ D.host.toHostRaw.two_mem_small)
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small (Fact.out : (D.nd.l i).Prime)).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hK := kw_le_Kur_of_ne i hN w hw
  have h1 := le_Ks_one_of_Kur _ hK
  exact ⟨inf_eq_left.2 hK, h1, (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 h1⟩

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_map_ringHom : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (M.map φ).rank = M.rank := by
  first | exact @GlobalTheory.matrix_rank_map_field | exact GlobalTheory.matrix_rank_map_field | (intros; apply GlobalTheory.matrix_rank_map_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemHeckeEigOfImageMovedByCentreStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_heckeEig_of_image_moved_by_centre : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i) (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x → S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  first | exact @GlobalTheory.PendOf.CenEig.main | exact GlobalTheory.PendOf.CenEig.main | (intros; apply GlobalTheory.PendOf.CenEig.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingletonStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' : ∀ (A : Type) [CommRing A] (d : A), Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | exact GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | (intros; apply GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowOfMulMemPowBoundedTorsionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pow_of_mul_mem_pow_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → ∀ (n : ℕ) (z : A), d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1)) → z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
  first | exact @GlobalTheory.div_d_continuous_of_bdd_ltorsion | exact GlobalTheory.div_d_continuous_of_bdd_ltorsion | (intros; apply GlobalTheory.div_d_continuous_of_bdd_ltorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReadingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_separable_of_complex_normal_reading : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  first | exact @GlobalTheory.NormalSeparable.minpoly_separable_of_normal | exact GlobalTheory.NormalSeparable.minpoly_separable_of_normal | (intros; apply GlobalTheory.NormalSeparable.minpoly_separable_of_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulLtFinrankCyclotomicAtQAndDStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  first | exact @GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | exact GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | (intros; apply GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_eq_of_power_sums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 → (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ, (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  first | exact @GlobalTheory.multiset_eq_of_powerSums_zpow_eq | exact GlobalTheory.multiset_eq_of_powerSums_zpow_eq | (intros; apply GlobalTheory.multiset_eq_of_powerSums_zpow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ), ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧ ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  first | exact @GlobalTheory.BSP.polyDelta_supported_linear_mod | exact GlobalTheory.BSP.polyDelta_supported_linear_mod | (intros; apply GlobalTheory.BSP.polyDelta_supported_linear_mod <;> assumption)
end

