import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomi
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtAlgCD

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem subsingleton_of_ringEquiv (q : ℕ) (d i : ℤ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Subsingleton (Ht q (sp A) d i)] : Subsingleton (Ht q (sp B) d i) := by
  constructor
  intro x y
  have h : ∀ z : Ht q (sp B) d i,
      pull _ (spMap (e : A →+* B)) _ _ (pull _ (spMap (e.symm : B →+* A)) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  rw [← h x, ← h y, Subsingleton.elim (pull _ (spMap (e.symm : B →+* A)) _ _ x) (pull _ _ _ _ y)]

theorem subsingleton_prod (q : ℕ) (d i : ℤ) (A B : Type) [CommRing A] [CommRing B]
    [Subsingleton (Ht q (sp A) d i)] [Subsingleton (Ht q (sp B) d i)] :
    Subsingleton (Ht q (sp (A × B)) d i) := by
  constructor
  intro x y
  exact (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B d i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem subsingleton_of_subsingleton_ring (q : ℕ) (d i : ℤ) (A : Type) [CommRing A] [Subsingleton A] :
    Subsingleton (Ht q (sp A) d i) := by
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A A d i).2 (a, b)
  have hfs : RingHom.fst A A = RingHom.snd A A := RingHom.ext fun _ => Subsingleton.elim _ _
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2, hfs]

def piFinSuccRingEquiv (n : ℕ) (B : Fin (n + 1) → Type) [∀ j, CommRing (B j)] :
    (∀ j, B j) ≃+* B 0 × ∀ j : Fin n, B j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem subsingleton_pi (q : ℕ) (d i : ℤ) : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)],
    (∀ j, Subsingleton (Ht q (sp (B j)) d i)) → Subsingleton (Ht q (sp (∀ j, B j)) d i) := by
  intro n
  induction n with
  | zero =>
    intro B _ _
    exact subsingleton_of_subsingleton_ring q d i _
  | succ n ih =>
    intro B _ hB
    have := ih (fun j => B j.succ) (fun j => hB j.succ)
    have := hB 0
    have := subsingleton_prod q d i (B 0) (∀ j : Fin n, B j.succ)
    exact subsingleton_of_ringEquiv q d i (piFinSuccRingEquiv n B).symm

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD

open Polynomial in

theorem dimensionLEOne_of_etale (K E : Type) [Field K] [CommRing E] [IsDomain E] [Algebra K[X] E]
    [Algebra.Etale K[X] E] : Ring.DimensionLEOne E := by
  have h1 : ringKrullDim E ≤ 1 := by
    refine (GlobalTheory.AffineCover.ringKrullDim_le_of_quasiFinite K[X] E).trans ?_
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  refine ⟨fun {p} hp0 hp => ?_⟩
  have h2 := Order.krullDim_le_one_iff.1 h1 ⟨p, hp⟩
  rcases h2 with h | h
  · exfalso
    have := h (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum E) ≤ ⟨p, hp⟩ from bot_le)
    exact hp0 (le_bot_iff.1 this)
  · obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
    have := h (show (⟨p, hp⟩ : PrimeSpectrum E) ≤ ⟨m, hm.isPrime⟩ from hpm)
    have hmp : m ≤ p := this
    exact (le_antisymm hpm hmp) ▸ hm

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD

open Polynomial in

theorem subsingleton_of_domain (hcurve : GlobalTheory.EtC.C2) (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K]
    [CommRing E] [IsDomain E] [Algebra K[X] E] [Algebra.Etale K[X] E] (hq : IsUnit (q : K))
    (n i : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sp E) n i) := by
  letI : Algebra K E := ((algebraMap K[X] E).comp (algebraMap K K[X])).toAlgebra
  haveI : IsScalarTower K K[X] E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType K E := Algebra.FiniteType.trans (S := K[X]) inferInstance inferInstance
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing K[X] E
  haveI : IsIntegrallyClosed E := GlobalTheory.isIntegrallyClosed_of_smooth K[X] E
  haveI : Ring.DimensionLEOne E := dimensionLEOne_of_etale K E
  haveI : IsDedekindDomain E := {}
  exact hcurve q K E hq n i hn

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD

theorem isCoprime_of_minimalPrimes {E : Type} [CommRing E]
    (hloc : ∀ (p : Ideal E) [p.IsPrime], IsDomain (Localization.AtPrime p))
    {p q : Ideal E} (hp : p ∈ minimalPrimes E) (hq : q ∈ minimalPrimes E) (hpq : p ≠ q) :
    IsCoprime p q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hloc m
  let P0 : Ideal E := (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap E (Localization.AtPrime m))
  haveI : P0.IsPrime := Ideal.comap_isPrime _ _
  have key : ∀ r : Ideal E, r ∈ minimalPrimes E → r ≤ m → r = P0 := by
    intro r hr hrm
    have hsub : P0 ≤ r := by
      intro x hx
      have hx0 : algebraMap E (Localization.AtPrime m) x = 0 := hx
      obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0
      have hsr : s ∉ r := fun h => hs (hrm h)
      have : s * x ∈ r := by rw [hsx]; exact r.zero_mem
      exact (hr.1.1.mem_or_mem this).resolve_left hsr
    exact le_antisymm (hr.2 ⟨inferInstance, bot_le⟩ hsub) hsub
  exact hpq ((key p hp (le_sup_left.trans hle)).trans (key q hq (le_sup_right.trans hle)).symm)

theorem isLocalizationAway_of_pi {E ι : Type} [CommRing E] [DecidableEq ι] (f : ι → Ideal E)
    (Φ : E ≃+* ∀ j, E ⧸ f j) (hΦ : ∀ x j, Φ x j = Ideal.Quotient.mk (f j) x) (j : ι) :
    IsLocalization.Away (Φ.symm (Pi.single j 1)) (E ⧸ f j) := by
  set e := Φ.symm (Pi.single j 1) with he
  have hΦe : Φ e = Pi.single j 1 := by simp [e]
  have hid : IsIdempotentElem e := by
    apply Φ.injective
    rw [map_mul, hΦe]
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  refine IsLocalization.away_of_isIdempotentElem hid ?_ Ideal.Quotient.mk_surjective
  change RingHom.ker (Ideal.Quotient.mk (f j)) = _
  rw [Ideal.mk_ker]
  apply le_antisymm
  · intro x hx
    have : x = x * (1 - e) := by
      apply Φ.injective
      ext k
      rw [map_mul, map_sub, map_one, hΦe]
      by_cases hk : k = j
      · subst hk
        have h0 : Φ x k = 0 := by rw [hΦ]; exact Ideal.Quotient.eq_zero_iff_mem.2 hx
        simp [h0]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change 1 - e ∈ f j
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hΦ, map_sub, map_one, hΦe]
    simp

end GlobalTheory.EtAlgCD

namespace GlobalTheory.EtAlgCD

open Polynomial in

theorem etale_polynomial_cd_le_one : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K]
    [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) →
    ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  classical
  intro q _ K E _ _ _ _ _ hq n i hn
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing K[X] E
  haveI : IsReduced E := GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K[X] E
  have hloc : ∀ (p : Ideal E) [p.IsPrime], IsDomain (Localization.AtPrime p) := fun p _ =>
    (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale K[X] p _).1
  let ι := {p : Ideal E // p ∈ minimalPrimes E}
  haveI : Finite ι := (minimalPrimes.finite_of_isNoetherianRing E).to_subtype
  letI : Fintype ι := Fintype.ofFinite ι
  let f : ι → Ideal E := Subtype.val
  have hcop : Pairwise (Function.onFun IsCoprime f) := fun a b hab =>
    isCoprime_of_minimalPrimes hloc a.2 b.2 (fun h => hab (Subtype.ext h))
  have hinf : ⨅ j, f j = ⊥ := by
    have h1 : ⨅ j, f j = sInf (minimalPrimes E) := (sInf_eq_iInf' (minimalPrimes E)).symm
    rw [h1]
    change sInf (Ideal.minimalPrimes ⊥) = ⊥
    rw [Ideal.sInf_minimalPrimes]
    exact nilradical_eq_zero E
  let ψ : E →+* ∀ j, E ⧸ f j := RingHom.pi fun j => Ideal.Quotient.mk (f j)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ ⨅ j, f j := Ideal.mem_iInf.2 fun j => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx j)
    rwa [hinf, Ideal.mem_bot] at this
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨z, rfl⟩ := (Ideal.quotientInfRingEquivPiQuotient f hcop).surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, by ext j; first | rfl | simp [ψ, Ideal.quotientInfRingEquivPiQuotient, Ideal.quotientInfToPiQuotient]⟩
  let Φ : E ≃+* ∀ j, E ⧸ f j := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  have hfac : ∀ j, Subsingleton (Ht q (sp (E ⧸ f j)) n i) := by
    intro j
    haveI : (f j).IsPrime := j.2.1.1
    haveI : IsLocalization.Away (Φ.symm (Pi.single j 1)) (E ⧸ f j) :=
      isLocalizationAway_of_pi f Φ (fun x j => rfl) j
    haveI : Algebra.Etale E (E ⧸ f j) := Algebra.Etale.of_isLocalizationAway (Φ.symm (Pi.single j 1))
    haveI : Algebra.Etale K[X] (E ⧸ f j) := Algebra.Etale.comp K[X] E _
    exact subsingleton_of_domain GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (E ⧸ f j) hq n i hn
  let σ := (Fintype.equivFin ι).symm
  haveI := subsingleton_pi q n i (Fintype.card ι) (fun k => E ⧸ f (σ k)) (fun k => hfac (σ k))
  haveI := subsingleton_of_ringEquiv q n i (RingEquiv.piCongrLeft (fun j => E ⧸ f j) σ)
  exact subsingleton_of_ringEquiv q n i Φ.symm

end GlobalTheory.EtAlgCD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Vec

section Mat

open Matrix
open scoped ComplexOrder

theorem exists_isONBasis {n P Q : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s)
    (hs : Formalism.UG.HasSignature G P Q) : ∃ B : Matrix (Fin n) (Fin n) ℂ, IsONBasis G s B P := by
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n G s h.1 h.2.1 h.2.2
  have hn : p + q = n := by
    have e := Matrix.trace_mul_comm B B'
    rw [h1, h2, Matrix.trace_one, Matrix.trace_one] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e
    exact_mod_cast e.symm
  subst hn
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  have hsig : Formalism.UG.HasSignature G p q := by
    refine ⟨e.symm, ⟨B.submatrix e id, B'.submatrix id e, ?_, ?_⟩, ?_⟩
    · have : B.submatrix e id * B'.submatrix id e = (B * B').submatrix e e := by
        ext a b; simp [Matrix.mul_apply]
      rw [this, h1, Matrix.submatrix_one_equiv]
    · rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_id_id]
    · rw [Formalism.UG.P.cT_conj_eq, Matrix.reindex_apply, Equiv.symm_symm]
      show (B.submatrix e id)ᴴ * G.submatrix e e * B.submatrix e id = _
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h3,
        Matrix.submatrix_id_id]
      rfl
  obtain ⟨rfl, -⟩ := Formalism.UG.P.signature_unique _ G _ _ _ _ hsig hs
  let ε : Fin (p + q) → ℝ := fun a => Sum.elim (fun _ => 1) (fun _ => -1) (e.symm a)
  have hd : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e.symm e.symm =
      Matrix.diagonal fun a => (ε a : ℂ) := by
    ext a b
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [ε, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  refine ⟨B.submatrix id e.symm, ε, fun a => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective a
    rcases a with a | a
    · exact Or.inl ⟨by simp [ε], by simp [e]⟩
    · exact Or.inr ⟨by simp [ε], by simp [e]⟩
  · rw [← hd, ← h3]
    rfl
  · rw [← hd, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M id e.symm) h4

theorem isCartanInv_one {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

end Mat

variable {D : D7}

theorem theta_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) (h₀ : IsThetaFunO ψ S T f₀) :
    IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  let H : WO S T → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun w =>
    { toFun := heisO ψ S T w
      map_add' := fun a b => funext fun x => mul_add _ _ _
      map_smul' := fun a b => funext fun x => mul_left_comm _ _ _ }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.pi fun w => l ∘ₗ H w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((H x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((H y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

theorem theta_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (P : PolF D T.rank S.rank) : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) :=
  (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

theorem exists_vecData : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ _
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i A.μ0).std
  have hQ : R.Q A.μ0 = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hC.lev.xi_base]; exact fun _ _ => rfl)
  have h0 := (hC.thP.vP i A.μ0).2
  obtain ⟨e, he, -⟩ := h0
  rw [hQ] at he
  have sdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hc := GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)
  have h1 := GlobalTheory.Member.vacuum_oriented_exists D R.ψ R.θ hψ hθ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ))
    (D.sp.V_sig _) (D.sp.W_sig _) (fun τ => isCartanInv_one (hC.models.BV i τ)) hc _ _ sdV sdW
  obtain ⟨f₀, hf₀⟩ := h1
  have h2 := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) _ _ (R.βV i) (R.βW i)
    R.Pg ∅ (fun _ => 1) sdV sdW (hC.lev.βV i).choose_spec.1 (hC.lev.βW i).choose_spec.1 (Finset.disjoint_empty_right _)
    ⟨e, he⟩ f₀ hf₀
  obtain ⟨f, hf⟩ := h2
  have h3 := fun ρ => exists_isONBasis (hc ρ) (D.sp.W_sig _ (tauE D ρ))
  choose B hB using h3
  have h4 := hf.2
  obtain ⟨e', -, h5⟩ := h4
  exact ⟨f₀, f, B, hf, hB, theta_pureTensorO hψ hθ _ _ _ _ (theta_of_thetaAt hψ hθ h5 hf₀.2.theta)⟩

end GlobalTheory.GalLift.Vec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZeroStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_vector_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ i, VStd D i → R.vP i A.μ0 ≠ 0 := by
  first | exact @GlobalTheory.AdTh.VecNe.thetaVector_ne_zero | exact GlobalTheory.AdTh.VecNe.thetaVector_ne_zero | (intros; apply GlobalTheory.AdTh.VecNe.thetaVector_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubsetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset : ∀ (T : Type) [TopologicalSpace T] (A B : Set T), IsClosed A → IsIrreducible A → IsIrreducible B → A ⊂ B → topologicalKrullDim A + 1 ≤ topologicalKrullDim B := by
  first | exact @GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | exact GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset | (intros; apply GlobalTheory.topologicalKrullDim_add_one_le_of_ssubset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

variable (ι : Type) [Fintype ι] (P Q R S : ℕ)

def degLE (k : ℕ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {T | ∃ f : ι → Formalism.BasicNotions.TH.Pol P Q R S, ∑ w, (f w).totalDegree ≤ k ∧ T = PiTensorProduct.tprod ℂ f}

def chiPart [DecidableEq ι] (x : ι → ℚ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ w : ι, ⨅ X : {X : Mat P Q // IsKC X},
    LinearMap.ker (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X.1) - ((x w : ℂ) * X.1.trace) • 1)

variable {ι P Q R S}

theorem mem_chiPart [DecidableEq ι] (x : ι → ℚ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :
    T ∈ chiPart ι P Q R S x ↔ ∀ w (X : Mat P Q), IsKC X →
      atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X) T = ((x w : ℂ) * X.trace) • T := by
  simp only [chiPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

theorem degLE_mono : Monotone (degLE ι P Q R S) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨f, hf, e⟩ => ⟨f, hf.trans h, e⟩

theorem tprod_mem_degLE (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) {k : ℕ} (h : ∑ w, (f w).totalDegree ≤ k) :
    PiTensorProduct.tprod ℂ f ∈ degLE ι P Q R S k :=
  Submodule.subset_span ⟨f, h, rfl⟩

end GlobalTheory.KFixIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormEqGLOneUnramifiedStatement
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  first | (exact @GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (exact GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (intros; apply GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessGl1UnramifiedStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_gl1_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r), GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  first | (exact @GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (exact GlobalTheory.TwFinGL1.twisted_finiteness_gl1) | (intros; apply GlobalTheory.TwFinGL1.twisted_finiteness_gl1  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ γ ∈ GQ V, ν γ = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | exact GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | (intros; apply GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split <;> assumption)
end

