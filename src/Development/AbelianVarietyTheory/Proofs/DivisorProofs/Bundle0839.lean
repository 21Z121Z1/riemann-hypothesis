import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquiv
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.LocalDualityAll

def cycP (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    GK p K →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
    ((cyclotomicCharacter (PadicAlgCl p) l).comp
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p)))

theorem localCyclotomicCharacter_spec (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) (σ : GK p K) (ζ : PadicAlgCl p) (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycP p K l r σ : ZMod (l ^ r)).val) := by
  have : NeZero ((l : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl p) σ) ζ hζ

theorem exists_mulEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (e : Dec (F := F) A ≃* GK p K),
      Continuous e ∧ Continuous e.symm ∧
        ∀ (r : ℕ) (g : Dec (F := F) A), cycP p K l r (e g) = cycMod F Ω l r (g : G F Ω) := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK p K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycP p K.1 l r σ : ZMod (l ^ r))).val :=
    localCyclotomicCharacter_spec p K.1 l r σ _ hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

theorem exists_mu (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) : ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).V,
      ∀ (g : GK p K) (m : ZMod (l ^ r)), e ((cycP p K l r g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g (e m) := by
  have : IsSepClosure ↥K (PadicAlgCl p) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[p] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g x =
        (cycP p K l r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine localCyclotomicCharacter_spec p K l r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem tate_p (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (GK p K) M) (hrho : ContAction rho) :
    Nonempty (H2 (charRep (cycP p K l r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycP p K l r) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycP p K l r) rho (MonoidHom.id _)) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨eD, hD⟩ := exists_mu p K l r
  exact CompanionTheory.LocalTateOrthogonality.Gcoh.tate_core CompanionTheory.LocalTateOrthogonality.Gcoh.gcRep CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 CompanionTheory.LocalTateOrthogonality.Gcoh.gc1 CompanionTheory.LocalTateOrthogonality.Gcoh.gc2
    (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)) (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    (cycP p K l r) eD hD M rho hrho

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', hcyc⟩ := exists_mulEquiv F Ω p l v A hpv hA
  have hc' : ContAction (rho.comp e.symm.toMonoidHom) := hc.comp' he'
  have hχ : ((cycMod F Ω l r).comp (Dec (F := F) A).subtype).comp e.symm.toMonoidHom = cycP p K l r := by
    ext1 σ
    have := hcyc r (e.symm σ)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine GlobalTheory.CohTransport.dualityClauses_of_mulEquiv (ZMod (l ^ r)) _ _ M e.symm he' he _ rho hc hc' ?_
  rw [hχ]
  exact tate_p p K hK l r M _ hc'

end GlobalTheory.LocalDualityAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRed
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hs : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  first
  | exact @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | (apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step ..)

theorem exists_limit_of_steps {R σ : Type} [CommRing R] (F : ℕ → MvPowerSeries σ R)
    (hF : ∀ n (α : σ →₀ ℕ), α.degree ≠ n + 2 → coeff α (F (n + 1)) = coeff α (F n)) :
    ∃ f : MvPowerSeries σ R, ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → coeff α f = coeff α (F n) := by
  have stab : ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → ∀ m, n ≤ m →
      coeff α (F m) = coeff α (F n) := by
    intro n α hα m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hF m α (by omega), ih]
  refine ⟨fun α => coeff α (F α.degree), fun n α hα => ?_⟩
  change coeff α (F α.degree) = _
  rw [← stab α.degree α (by omega) (max n α.degree) (le_max_right _ _),
    stab n α hα _ (le_max_left _ _)]

theorem exists_quasiLog_red (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) :
    ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h,
      Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  intro c hc w
  obtain ⟨f₀, hf₀, hw, hb⟩ := GlobalTheory.T.exists_cob1_witt_lift_mod_p p k d μ h c hc w
  have hq₀ : f₀ ∈ quasiInt p k (Fin d) := by
    intro α i
    obtain ⟨v, hv⟩ := hf₀ α
    exact ⟨(α i : WittVector p k) * (1 * v), by rw [hv, map_mul _ (α i : WittVector p k), map_natCast]⟩
  obtain ⟨F, hF0, hF⟩ := exists_seq_of_step
    (fun n (f : MvPowerSeries (Fin d) (Fr p k)) => f ∈ quasiInt p k (Fin d) ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < n + 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w))
    (fun n a b => ∀ α : Fin d →₀ ℕ, α.degree ≠ n + 2 → coeff α b = coeff α a) f₀ ⟨hq₀, hb⟩
    (by
      intro n a ha
      obtain ⟨g, hg0, hg1, hg2⟩ := GlobalTheory.T.quasiLogarithm_successive_approximation_step p k d μ h c hc (n + 2) a (by omega) ha.1 ha.2
      exact ⟨a - g, ⟨hg1, hg2⟩, fun α hα => by rw [map_sub, hg0 α hα, sub_zero]⟩)
  obtain ⟨f, hf⟩ := exists_limit_of_steps F fun n => (hF n).2
  have hq : f ∈ quasiInt p k (Fin d) := by
    intro α i
    rw [hf α.degree α (by omega)]
    exact (hF α.degree).1.1 α i
  have hp : cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c ∈ intBy p k (Fin d ⊕ Fin d) p := by
    intro γ
    obtain ⟨v, hv⟩ := (hF γ.degree).1.2 γ (by omega)
    refine ⟨v, ?_⟩
    have h1 := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) (γ.degree + 2)
      (fun i α hα => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ h i α hα).2)).1 (f - F γ.degree)
      (fun α hα => by rw [map_sub, hf _ α hα, sub_self]) γ).1 (by omega)
    have h2 := formalCoboundary_add (fun i => constantCoeff_lift p (h.const i)) (f - F γ.degree) (F γ.degree)
    rw [sub_add_cancel] at h2
    rw [h2, add_sub_assoc, map_add, h1, zero_add, hv]
  obtain ⟨r1, -, r3, r4, -, r6, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hred : Red p (cob1 (fun i => Katz.lift p (μ i)) f) c := by
    have := (r4 _ _ _ _ ((r6 _).1 hp) (r3 c)).1
    rwa [sub_add_cancel, zero_add] at this
  refine ⟨f, ⟨hq, (r1 _).2 ⟨c, hred⟩⟩, hred, ?_⟩
  have hl : lin f = lin f₀ := by
    funext i
    unfold lin
    rw [hf 0 _ (by simp), hF0]
  rw [hl]
  exact hw

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLie
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  first | exact @GlobalTheory.QSA.exists_unit_intertwiner | exact GlobalTheory.QSA.exists_unit_intertwiner | (intros; apply GlobalTheory.QSA.exists_unit_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZeroSectionValueInPowerFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeroSection_value_in_powerFrame : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (s : LB.Sec (LPow A L (k : ℤ) (topS Rg))), L.IsLB → eA.IsGen → ∃ α : Γ(Sp Rg, ⊤), GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) s α := by
  first | (exact @GlobalTheory.HomFixUnivVals.vals) | (exact GlobalTheory.HomFixUnivVals.vals) | (intros; apply GlobalTheory.HomFixUnivVals.vals  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitarySheafContinuousBaseChangeLevelwiseQcqs
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_bc_sch_qcqs (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (S X : Scheme.{0})
    (r : X ⟶ S) (hqc : QuasiCompact r) (hqs : QuasiSeparated r) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G : I ⥤ Over S) (c : Cone G) (hc : IsLimit c) (hG : ∀ i, IsAffine (G.obj i).left) :
    ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨e, -⟩ := GlobalTheory.EtC.bc_sch_iso S X r
  let H : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget X
  have hl : IsLimit (H.mapCone c) := isLimitOfPreserves H hc
  have hcomp : ∀ i, CompactSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiCompact (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqc
    have hc' := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (G.obj i).hom r)
    exact hc'
  have hqsp : ∀ i, QuasiSeparatedSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiSeparated (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqs
    have hs' := quasiSeparatedSpace_of_quasiSeparated (pullback.fst (G.obj i).hom r)
    exact hs'
  have haff : ∀ (i j : I) (f : i ⟶ j), IsAffineHom ((G ⋙ H).map f) := by
    intro i j f
    haveI := hG i
    haveI := hG j
    have hsq : IsPullback ((G ⋙ H).map f) (pullback.fst (G.obj i).hom r) (pullback.fst (G.obj j).hom r)
        (G.map f).left := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (G.obj j).hom r) (h₂₂ := (G.obj j).hom) (v₁₃ := r) ?_ ?_ ?_
      · have e1 : (G ⋙ H).map f ≫ pullback.snd (G.obj j).hom r = pullback.snd (G.obj i).hom r := by
          exact pullback.lift_snd _ _ _
        have e2 : (G.map f).left ≫ (G.obj j).hom = (G.obj i).hom := Over.w (G.map f)
        have key : ∀ {P₁ P₂ P₃ P₄ : Scheme.{0}} {l : P₁ ⟶ P₃} {rr : P₂ ⟶ P₄} {a a' : P₁ ⟶ P₂} {b b' : P₃ ⟶ P₄},
            a = a' → b = b' → IsPullback a' l rr b' → IsPullback a l rr b := by
          rintro _ _ _ _ _ _ _ _ _ _ rfl rfl h; exact h
        exact key e1 e2 (IsPullback.of_hasPullback (G.obj i).hom r).flip
      · exact pullback.lift_fst _ _ _
      · exact (IsPullback.of_hasPullback (G.obj j).hom r).flip
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip (isAffineHom_of_isAffine _)
  have h1 : ContCone R F (sch.mapCone (H.mapCone c)) :=
    GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions R F hF I (G ⋙ H) (H.mapCone c) hl hcomp hqsp haff
  have hb := GlobalTheory.EtC.eqv_basic R F
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ H ⋙ sch) (G ⋙ bc (sch.map r)) (sch.mapCone (H.mapCone c))
    ((bc (sch.map r)).mapCone c) (Functor.whiskerLeft G e.hom) (e.hom.app c.pt) ?_ ?_ ?_).1 h1
  · intro i
    exact e.hom.naturality (c.π.app i)
  · intro i
    exact hb.1 _ _ _ inferInstance
  · exact hb.1 _ _ _ inferInstance

theorem contCone_bc_qcqsOver : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S), QcqsOver p → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((bc p).mapCone c)) := by
  intro R _ F hF S E p hp I _ _ G c hc hG
  refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S E p I G c ?_
  intro k
  obtain ⟨X, r, e, hqc, hqs, he⟩ := hp k
  exact ⟨X, r, e, he, contCone_bc_sch_qcqs R F hF S X r hqc hqs I G c hc hG⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRatStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdele_module_exists_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  first | exact @GlobalTheory.CMVal.ModFRat.modF_rat | exact GlobalTheory.CMVal.ModFRat.modF_rat | (intros; apply GlobalTheory.CMVal.ModFRat.modF_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_add_le_of_image_mem {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (Z R : Submodule K V) (Z' R' : Submodule K W) (hR' : R' ≤ Z')
    (hZ : ∀ x ∈ Z, A x ∈ Z') (hk : ∀ x ∈ Z, A x ∈ R' → x ∈ R) :
    Module.finrank K Z + Module.finrank K R' ≤ Module.finrank K Z' + Module.finrank K R := by
  let g : (Z × R') →ₗ[K] W := LinearMap.coprod (A ∘ₗ Z.subtype) R'.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_prod] at h1
  have h2 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K Z' := by
    apply Submodule.finrank_mono
    rintro _ ⟨⟨x, r⟩, rfl⟩
    simp only [g, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Z'.add_mem (hZ x x.2) (hR' r.2)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K R := by
    let φ : LinearMap.ker g →ₗ[K] R :=
      LinearMap.codRestrict R (Z.subtype ∘ₗ LinearMap.fst K Z R' ∘ₗ (LinearMap.ker g).subtype) (by
        rintro ⟨⟨x, r⟩, hx⟩
        simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
        apply hk x x.2
        have : A x = -(r : W) := eq_neg_of_add_eq_zero_left hx
        rw [this]; exact R'.neg_mem r.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, r⟩, hx⟩ h0
    simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h0
      simpa [φ] using this
    subst hx0
    have hr : r = 0 := by
      apply Subtype.ext
      simpa using hx
    subst hr
    rfl
  omega

theorem finrank_homology_base_change_resolutions : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  intro O _ K _ _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _
    G₂ _ _ _ _ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    GlobalTheory.T.partialFreeResolutions_homotopyEquivalent O N F₀ F₁ F₂ F₃ G₀ G₁ G₂ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  have bc : ∀ {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      {f g : P →ₗ[O] Q}, f = g → ∀ x, f.baseChange K x = g.baseChange K x := by
    intro P Q _ _ _ _ f g h x; rw [h]
  have z12 : ∀ x, d₁.baseChange K (d₂.baseChange K x) = 0 := by
    intro x; have := bc hd₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have ze12 : ∀ x, e₁.baseChange K (e₂.baseChange K x) = 0 := by
    intro x; have := bc he₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have q1 : ∀ x, e₁.baseChange K (a₁.baseChange K x) = a₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c1 x; simpa [LinearMap.baseChange_comp] using this
  have q2 : ∀ x, e₂.baseChange K (a₂.baseChange K x) = a₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c2 x; simpa [LinearMap.baseChange_comp] using this
  have q3 : ∀ x, d₁.baseChange K (b₁.baseChange K x) = b₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c3 x; simpa [LinearMap.baseChange_comp] using this
  have q4 : ∀ x, d₂.baseChange K (b₂.baseChange K x) = b₁.baseChange K (e₂.baseChange K x) := by
    intro x; have := bc c4 x; simpa [LinearMap.baseChange_comp] using this
  have q5 : ∀ x, x - b₁.baseChange K (a₁.baseChange K x) =
      d₂.baseChange K (h₁.baseChange K x) + h₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c5 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q6 : ∀ x, x - b₂.baseChange K (a₂.baseChange K x) =
      d₃.baseChange K (h₂.baseChange K x) + h₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c6 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q7 : ∀ x, x - a₁.baseChange K (b₁.baseChange K x) =
      e₂.baseChange K (k₁.baseChange K x) + k₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c7 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine finrank_add_le_of_image_mem (a₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact ze12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q1, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨b₂.baseChange K y + h₁.baseChange K x, ?_⟩
      have := q5 x
      rw [hx, map_zero, add_zero, ← hy, ← q4] at this
      rw [map_add, ← this]; abel
  · refine finrank_add_le_of_image_mem (b₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact z12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q3, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨a₂.baseChange K y + k₁.baseChange K x, ?_⟩
      have := q7 x
      rw [hx, map_zero, add_zero, ← hy, ← q2] at this
      rw [map_add, ← this]; abel
  · have := finrank_add_le_of_image_mem (a₂.baseChange K) (LinearMap.ker (d₂.baseChange K))
      (LinearMap.range (d₃.baseChange K)) ⊤ ⊥ bot_le (fun _ _ => Submodule.mem_top) (by
        intro x hx h0
        rw [LinearMap.mem_ker] at hx
        rw [Submodule.mem_bot] at h0
        refine ⟨h₂.baseChange K x, ?_⟩
        have := q6 x
        rw [hx, h0, map_zero, map_zero, add_zero, sub_zero] at this
        exact this.symm)
    simp only [finrank_top, finrank_bot, add_zero] at this
    omega

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleClassIdentityComponentIffArtinKernelStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleClass_identityComponent_iff_artin_kernel : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}, GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ s : Ideles K, (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 := by
  first | exact @GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff | exact GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff | (intros; apply GlobalTheory.ArtinKernel.idele_class_mem_identity_component_iff <;> assumption)
end

