import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_closedPointTo {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (V : X.Opens) (hy : p.1 ∈ V) (hx : genPt ξ ∈ V) (b : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hy b) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hx b) := by
  have h : X.presheaf.germ V (genPt ξ) hx = X.presheaf.germ V p.1 hy ≫ X.presheaf.stalkSpecializes p.2 :=
    (X.presheaf.germ_stalkSpecializes hy p.2).symm
  rw [h]
  rfl

theorem exists_frac_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) := (X.presheaf.germ U (genPt ξ) hgU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, hgU⟩
  obtain ⟨s, rfl⟩ : ∃ s : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s = a := hξ.bij.2 a
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal.primeCompl s
  refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU d, ?_, ?_⟩
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have hu := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) d
    exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU, genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have h := congrArg (Scheme.stalkClosedPointTo ξ).hom (IsLocalization.mk'_spec (X.presheaf.stalk (genPt ξ)) r d)
    exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans h

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExtendToFractionField
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem extend_to_fraction_field_relay : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ :=
  PositivityTheory.UnitarySelfGeneration.extends_to_fraction_field

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElementStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_stable_subspace_element : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  first | exact @GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | exact GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | (intros; apply GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) := by
  have h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) =
      (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)
  rw [h p hp, h q hq]

theorem exists_open_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  exact ⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩

theorem regAt_unitAt_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), (a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) ∧ (unitAt ξ p a → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a) := by
  intro X Ω _ ξ p a
  refine ⟨exists_open_mem_regAt ξ p a, ?_⟩
  rintro ⟨h0, h1, h2⟩
  obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ p a h1
  obtain ⟨V, hV, HV⟩ := exists_open_mem_regAt ξ p _ h2
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtMono

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (x : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom x) = genMap ξ p x := by
  have e := X.presheaf.stalkSpecializes_comp q.2 h
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)

theorem genMap_germ_eq (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (U : X.Opens) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom t) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom t) := by
  rw [← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem unitAt_of_isUnit (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) {x : X.presheaf.stalk q.1}
    (hx : IsUnit x) : unitAt ξ q (genMap ξ q x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩
  exact map_units_inv (genMap ξ q) u

theorem regAt_mono :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ), q.1 ⤳ p.1 →
      regAt ξ p ≤ regAt ξ q ∧
        (IsCptGen ξ → ∀ a ∈ regAt ξ q, ∃ s ∈ regAt ξ p, unitAt ξ q s ∧ s * a ∈ regAt ξ p) := by
  intro X Ω _ ξ p q h
  refine ⟨?_, fun _ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, genMap_stalkSpecializes ξ p q h x⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ
    have hU : IsAffineOpen U := hU
    have hq : q.1 ∈ U := h.mem_open U.2 hp
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨q.1, hq⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) x
    have hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1) :=
      IsLocalization.map_units (X.presheaf.stalk q.1) t
    have e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r := e
    refine ⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩
    · exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩
    · rw [mul_comm, ← map_mul, e']
      exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩

end GlobalTheory.CompanionTheory.Ar.RegAtMono
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem spec_inj (X : Scheme.{0}) [IsIntegral X] {x y : X} (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨U, hyU, s, rfl⟩ := X.presheaf.germ_exist t
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  have e : ConcreteCategory.hom (X.presheaf.stalkSpecializes h) (ConcreteCategory.hom (X.presheaf.germ U y hyU) s) =
      ConcreteCategory.hom (X.presheaf.germ U x hxU) s := by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hs : s = 0 := by
    apply germ_injective_of_isIntegral X x hxU
    rw [map_zero, ← e]
    exact ht
  rw [hs, map_zero]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unit_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  simp only [unitAt, regAt, RingHom.mem_range]
  constructor
  · rintro ⟨ha, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, ?_, rfl⟩
    have e : genMap ξ p (u * v) = genMap ξ p 1 := by
      rw [map_mul, hv, map_one, mul_inv_cancel₀ ha]
    exact IsUnit.of_mul_eq_one v (h.inj p e)
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    have key : genMap ξ p ↑w * genMap ξ p ↑w⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one key, ⟨↑w, rfl⟩, ⟨↑w⁻¹, eq_inv_of_mul_eq_one_right key⟩⟩

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUniqueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lu_decomposition_mul_generic_unipotent : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) → ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧ (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GenericLU.generic_lu | exact GlobalTheory.CompanionTheory.GenericLU.generic_lu | (intros; apply GlobalTheory.CompanionTheory.GenericLU.generic_lu <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishing
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegSec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

noncomputable def val (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) {q : X} (hq : genPt ξ ⤳ q) (hqU : q ∈ U)
    (s : Γ(X, U)) :
    genMap ξ ⟨q, hq⟩ ((X.presheaf.germ U q hqU).hom s) = val ξ U h s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold genMap val
  rw [← X.presheaf.germ_stalkSpecializes hqU hq]
  exact (key (X.presheaf.stalkSpecializes hq) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.germ U q hqU) (X.presheaf.stalkSpecializes hq) s).symm).trans
      (key (X.presheaf.germ U q hqU ≫ X.presheaf.stalkSpecializes hq)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_res {V U : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V) (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    val ξ V hV ((X.presheaf.map i.op).hom s) = val ξ U hU s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold val
  rw [← X.presheaf.germ_res i (genPt ξ) hV]
  exact (key (X.presheaf.germ V (genPt ξ) hV) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.map i.op) (X.presheaf.germ V (genPt ξ) hV) s).symm).trans
      (key (X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (val ξ U h) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t (fun q hq => ?_)
  have hq' := hU q hq
  apply hξ.inj ⟨q, hq'⟩
  exact (genMap_germ ξ U h hq' hq s).trans (hst.trans (genMap_germ ξ U h hq' hq t).symm)

theorem mem_range_val_iff (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) :
    a ∈ (val ξ U h).range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  constructor
  · intro ha q hqU
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom s, genMap_germ ξ U h q.2 hqU s⟩
  · intro H
    have loc : ∀ q : U, ∃ (W : X.Opens) (t : Γ(X, W)) (_ : (q : X) ∈ W) (hg : genPt ξ ∈ W),
        val ξ W hg t = a := by
      rintro ⟨q, hq⟩
      have hq' : genPt ξ ⤳ q := hU q hq
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H ⟨q, hq'⟩ hq)
      obtain ⟨W, hqW, t, ht⟩ := TopCat.Presheaf.germ_exist X.presheaf x
      have hg : genPt ξ ∈ W := hq'.mem_open W.isOpen hqW
      refine ⟨W, t, hqW, hg, ?_⟩
      rw [← genMap_germ ξ W hg hq' hqW t]
      exact (congrArg (genMap ξ ⟨q, hq'⟩) ht).trans hx
    choose W t hqW hg hval using loc
    let V : U → X.Opens := fun q => W q ⊓ U
    have hgV : ∀ q, genPt ξ ∈ V q := fun q => ⟨hg q, h⟩
    let sf : ∀ q : U, Γ(X, V q) := fun q =>
      (X.presheaf.map (homOfLE inf_le_left : V q ⟶ W q).op).hom (t q)
    have hsf : ∀ q, val ξ (V q) (hgV q) (sf q) = a := fun q =>
      (val_res ξ (homOfLE inf_le_left : V q ⟶ W q) (hgV q) (hg q) (t q)).trans (hval q)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
      intro i j
      apply val_injective ξ hξ (V i ⊓ V j) ⟨hgV i, hgV j⟩ (fun q hq => hU q hq.1.2)
      exact ((val_res ξ (TopologicalSpace.Opens.infLELeft (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV i) (sf i)).trans (hsf i)).trans
        ((val_res ξ (TopologicalSpace.Opens.infLERight (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV j) (sf j)).trans (hsf j)).symm
    have hcover : U ≤ iSup V := by
      intro q hq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hqW ⟨q, hq⟩, hq⟩
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.sheaf) (U := V) U
      (fun q => homOfLE inf_le_right) hcover sf hcompat
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    have i0 : U := ⟨genPt ξ, h⟩
    exact (val_res ξ (homOfLE inf_le_right : V i0 ⟶ U) (hgV i0) h s).symm.trans
      ((congrArg (val ξ (V i0) (hgV i0)) (hs i0)).trans (hsf i0))

end GlobalTheory.CompanionTheory.Ar.RegSec

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X),
    IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) →
      Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧
      ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔
        ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  intro X Ω _ ξ hξ U h hU
  exact ⟨RegSec.val_injective ξ hξ U h hU, RegSec.mem_range_val_iff ξ hξ U h hU⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphic
section
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.HoloChart

theorem holomorphic_inverse_with_parameters :
    ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ)))
      (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ)
      (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω →
      HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧
      X (b, Φ (b, x)) = x := by
  intro n I J _ _ Ω Φ b₀ x₀ L hΩ ha hΦ hL
  have cS := ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hΩ hΦ
  have cΦ : ContDiffAt ℂ 1 Φ (b₀, x₀) :=
    (cS.contDiffAt (hΩ.mem_nhds ha)).of_le (by exact_mod_cast le_top)
  have hinr : ∀ p : (Fin n → ℂ) × (I → ℂ), DifferentiableAt ℂ Φ p →
      HasFDerivAt (fun x => Φ (p.1, x))
        ((fderiv ℂ Φ p).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ))) p.2 := fun p hp =>
    HasFDerivAt.comp p.2 (f := fun x => (p.1, x)) hp.hasFDerivAt (hasFDerivAt_prodMk_right p.1 p.2)
  let D := fderiv ℂ Φ (b₀, x₀)
  have hD : HasFDerivAt Φ D (b₀, x₀) := (cΦ.differentiableAt one_ne_zero).hasFDerivAt
  have hDL : D.comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ)) = (L : (I → ℂ) →L[ℂ] (J → ℂ)) :=
    (hinr (b₀, x₀) hD.differentiableAt).unique hL
  have hDuv : ∀ u v, D (u, v) = D (u, 0) + L v := fun u v => by
    have h1 : D (0, v) = L v := by
      have := congrArg (fun A : (I → ℂ) →L[ℂ] (J → ℂ) => A v) hDL
      simpa using this
    rw [← h1, ← map_add]; simp
  let F₀ : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod D
  let G₀ : ((Fin n → ℂ) × (J → ℂ)) →L[ℂ] ((Fin n → ℂ) × (I → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ)).prod
      ((L.symm : (J → ℂ) →L[ℂ] (I → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (J → ℂ) -
          (D.comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) (I → ℂ))).comp
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ))))
  have hGF : Function.LeftInverse G₀ F₀ := by
    rintro ⟨u, v⟩
    simp [F₀, G₀, hDuv u v]
  have hFG : Function.RightInverse G₀ F₀ := by
    rintro ⟨u, w⟩
    have h : G₀ (u, w) = (u, L.symm (w - D (u, 0))) := by simp [G₀]
    rw [h]
    refine Prod.ext rfl ?_
    show D (u, L.symm (w - D (u, 0))) = w
    rw [hDuv]
    simp
  let F' : ((Fin n → ℂ) × (I → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse F₀ G₀ hGF hFG
  let F : (Fin n → ℂ) × (I → ℂ) → (Fin n → ℂ) × (J → ℂ) := fun p => (p.1, Φ p)
  have hF : HasFDerivAt F (F' : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ))) (b₀, x₀) :=
    hasFDerivAt_fst.prodMk hD
  have cF : ContDiffAt ℂ 1 F (b₀, x₀) := contDiffAt_fst.prodMk cΦ
  let T := cF.toOpenPartialHomeomorph F (f' := F') hF one_ne_zero
  have hTF : ∀ p, T p = F p := fun _ => rfl
  have src : (b₀, x₀) ∈ T.source := cF.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero
  have tgt : F (b₀, x₀) ∈ T.target :=
    cF.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero
  have hinv : T.symm (F (b₀, x₀)) = (b₀, x₀) := T.left_inv src
  let O := (T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}) ∩ (T.target ∩ T.symm ⁻¹' Ω)
  have oO : IsOpen O := (T.open_target.inter isOpen_interior).inter (T.isOpen_inter_preimage_symm hΩ)
  have mO : F (b₀, x₀) ∈ O := by
    refine ⟨⟨tgt, mem_interior_iff_mem_nhds.2 ?_⟩, tgt, ?_⟩
    · exact (cF.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp)
    · simpa [hinv] using ha
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 oO _ mO
  have hball : ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε ⊆ O := by
    rw [ball_prod_same]; exact hε
  obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem
    (T.open_source.mem_nhds src) (hΩ.mem_nhds ha))
    (hF.continuousAt.preimage_mem_nhds (ball_mem_nhds (F (b₀, x₀)) ε0)))
  have hsec : ∀ p ∈ O, T.symm p = (p.1, (T.symm p).2) ∧ Φ (T.symm p) = p.2 := fun p hp => by
    have h : F (T.symm p) = p := T.right_inv hp.1.1
    have h1 : (T.symm p).1 = p.1 := congrArg Prod.fst h
    have h2 : Φ (T.symm p) = p.2 := congrArg Prod.snd h
    exact ⟨Prod.ext h1 rfl, h2⟩
  refine ⟨ε, min δ δ, fun p => (T.symm p).2, ε0, lt_min δ0 δ0, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hinv
  · intro p hp
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset (hball hp).1.2
    exact ((differentiableAt_snd).comp p (c.differentiableAt one_ne_zero)).differentiableWithinAt
  · intro p hp
    have hpO := hball hp
    obtain ⟨e1, e2⟩ := hsec p hpO
    have hq : T.symm p ∈ Ω := hpO.2.2
    have hq' : (p.1, (T.symm p).2) ∈ Ω := e1 ▸ hq
    refine ⟨hq', by rw [← e1]; exact e2, fun v hv => ?_⟩
    have dΦ : DifferentiableAt ℂ Φ (T.symm p) := (hΦ _ hq).differentiableAt (hΩ.mem_nhds hq)
    have h1 := (hinr (T.symm p) dΦ).fderiv
    have h2 : (T.symm p).1 = p.1 := congrArg Prod.fst e1
    rw [h2] at h1
    rw [h1] at hv
    have dF : HasFDerivAt F ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (T.symm p) := hasFDerivAt_fst.prodMk dΦ.hasFDerivAt
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset hpO.1.2
    have dS : HasFDerivAt T.symm (fderiv ℂ T.symm p) (F (T.symm p)) := by
      rw [show F (T.symm p) = p from T.right_inv hpO.1.1]
      exact (c.differentiableAt one_ne_zero).hasFDerivAt
    have hcomp := dS.comp (T.symm p) dF
    have hid : HasFDerivAt (T.symm ∘ F) (ContinuousLinearMap.id ℂ _) (T.symm p) := by
      refine (hasFDerivAt_id (𝕜 := ℂ) (T.symm p)).congr_of_eventuallyEq ?_
      filter_upwards [T.open_source.mem_nhds (T.map_target hpO.1.1)] with q hq
      exact T.left_inv hq
    have hu := hcomp.unique hid
    have hv' : fderiv ℂ Φ (T.symm p) (0, v) = 0 := by simpa using hv
    have e0 : ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (0, v) = 0 := Prod.ext (by simp) (by simpa using hv')
    have h3 := DFunLike.congr_fun hu (0, v)
    rw [ContinuousLinearMap.comp_apply, e0, map_zero] at h3
    exact (congrArg Prod.snd h3).symm
  · intro b hb x hx
    have hbx : (b, x) ∈ ball (b₀, x₀) δ := by
      rw [← ball_prod_same]; exact ⟨by simpa using hb, by simpa using hx⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hδ hbx
    have h3' : F (b, x) ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε := by
      rw [ball_prod_same]; exact h3
    exact ⟨h2, h3'.2, congrArg Prod.snd (T.left_inv h1)⟩

end GlobalTheory.CompanionTheory.HoloChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalyticStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  first | exact @GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | exact GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | (intros; apply GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaledStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_over_localization_scaled : ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K), (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) → ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | exact GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | (intros; apply GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral <;> assumption)
end

