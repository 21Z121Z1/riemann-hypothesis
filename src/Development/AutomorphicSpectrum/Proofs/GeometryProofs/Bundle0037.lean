import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem NormAt.isoAt_of_integrallyClosed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ),
    NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) →
      IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory

def locSub {F : Type} [Field F] (R : Subring F) (a : F) : Subring F :=
  Subring.closure ((R : Set F) ∪ {a⁻¹})

theorem le_locSub {F : Type} [Field F] (R : Subring F) (a : F) : R ≤ locSub R a :=
  fun _ h => Subring.subset_closure (Or.inl h)

theorem inv_mem_locSub {F : Type} [Field F] (R : Subring F) (a : F) : a⁻¹ ∈ locSub R a :=
  Subring.subset_closure (Or.inr rfl)

theorem mem_locSub_iff {F : Type} [Field F] {R : Subring F} {a : F} (ha : a ∈ R) (h0 : a ≠ 0) (b : F) :
    b ∈ locSub R a ↔ ∃ k : ℕ, a ^ k * b ∈ R := by
  constructor
  · intro hb
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨1, by simpa [h0] using R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y) := by ring
      rw [e]
      exact R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)
    | neg x _ hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using R.neg_mem hk⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y) := by ring
      rw [e]
      exact R.mul_mem hk hl
  · rintro ⟨k, hk⟩
    have e : b = (a⁻¹) ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]
    rw [e]
    exact (locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)

structure IsPiece {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens)
    (R : Subring Ω) : Prop where
  affine : IsAffineOpen U
  spec : ∀ q : X, q ∈ U → genPt ξ ⤳ q
  ring : ∀ a : Ω, a ∈ R ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q

def stepMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : F :=
  (A.submatrix J (Fin.castLE i.2)).det

variable {Ω : Type} [Field Ω] {S : Type} {r n : S → ℕ}

def flagB (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  (M s * T s).map (algebraMap Ω (GenField Ω r)) * genU Ω r s

def ratioRing (R : Subring Ω) (B : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) : Subring (GenField Ω r) :=
  Subring.closure (((R.map (algebraMap Ω (GenField Ω r)) : Subring _) : Set (GenField Ω r)) ∪
    {a | ∃ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      a = stepMinor (B q.1) q.2 J' / stepMinor (B q.1) q.2 (J q)})

def chartSub {F : Type} [Field F] {κ : Type} (x : κ → F) (c : κ) : Subring F :=
  (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring

theorem stepMinor_smul {F : Type} [CommRing F] {n r : ℕ} (b : F) (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor (b • A) i J = b ^ ((i : ℕ) + 1) * stepMinor A i J := by
  unfold stepMinor
  rw [Matrix.submatrix_smul]
  simp [Matrix.det_smul]

theorem flagMat_eq {E : Type} [AddCommGroup E] [Module Ω E] {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (s : S) :
    flagMat φ cc s = (algebraMap Ω (GenField Ω r) a ^ m s) • flagB M T s := by
  unfold flagMat flagB
  rw [← Matrix.smul_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]

theorem flagCoord_eq [Fintype S] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type} (x : κ → Ω) {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (k : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc (k, J) = algebraMap Ω (GenField Ω r) (x k) *
      ∏ q : (Σ s, Fin (r s)), ((algebraMap Ω (GenField Ω r) a ^ m q.1) ^ ((q.2 : ℕ) + 1) *
        stepMinor (flagB M T q.1) q.2 (J q)) := by
  unfold flagCoord
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  have := stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)
  rw [← this, ← flagMat_eq h q.1]
  rfl

theorem prod_update_div {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {F : Type} [Field F]
    (f : ∀ q, β q → F) (J : ∀ q, β q) (h : ∀ q, f q (J q) ≠ 0) (q : ι) (b : β q) :
    (∏ q', f q' (Function.update J q b q')) / (∏ q', f q' (J q')) = f q b / f q (J q) := by
  have h1 : ∏ q', f q' (Function.update J q b q') =
      f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q') := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q' hq' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
  have h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q') :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h q'
  rw [h1, h2]
  field_simp [h q, h3]

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem nonempty_pModel_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) →
    Nonempty (PModel o x) := by
  intro o _ Ω _ _ κ _ x ⟨c, hc, h⟩
  have h' : ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c),
      ∃ k ∈ Algebra.adjoin o (Set.range fun j => x j / x c), k ≠ 0 ∧ a = g / k := by
    intro a
    obtain ⟨u, hu, v, hv, rfl⟩ := h a
    by_cases hv0 : v = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [hv0]⟩
    · exact ⟨u, hu, v, hv, hv0, rfl⟩
  obtain ⟨X, ξ, s, tie, all, -, -, hover⟩ := GlobalTheory.T.exists_proper_integral_model Ω o κ x c hc h'
  exact ⟨{ X := X, ξ := ξ, s := s, hover := hover, all := all, tie := tie }⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDominatingSurjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

section Surj

variable {X : Scheme.{0}}

theorem germ_closedPoint_eq_appLE {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem f hU).ge ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Scheme.Hom.appLE]
  rfl

theorem val_comp_spec {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) (z : Spec R ⟶ X)
    (w : Spec S ⟶ X) (hw : Spec.map φ ≫ z = w) (U : X.Opens)
    (h1 : z (IsLocalRing.closedPoint R) ∈ U) (h2 : w (IsLocalRing.closedPoint S) ∈ U) (t : Γ(X, U)) :
    φ.hom ((Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ U _ h1).hom t)) =
      (Scheme.stalkClosedPointTo w).hom ((X.presheaf.germ U _ h2).hom t) := by
  subst hw
  have key : (Spec.map φ ≫ z).appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem _ h2).ge ≫
      (Scheme.ΓSpecIso S).hom =
      z.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge ≫ (Scheme.ΓSpecIso R).hom ≫ φ := by
    have e₂ : (⊤ : (Spec S).Opens) ≤ (Spec.map φ) ⁻¹ᵁ ⊤ := by simp
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) z U ⊤ ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem z h1).ge e₂,
      Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e1 := congrArg (fun g => (g ≫ φ).hom t) (germ_closedPoint_eq_appLE z U h1)
  have e2 := congrArg (fun g => g.hom t) (germ_closedPoint_eq_appLE (Spec.map φ ≫ z) U h2)
  have e3 := congrArg (fun g => g.hom t) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e2 e3
  rw [e1, e2, e3]

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Ω' : Type} [Field Ω']

def DomAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (A : ValuationSubring Ω') (p : Cpt ξ) : Prop :=
  ∃ ν : X.presheaf.stalk p.1 →+* A, IsLocalHom ν ∧ ∀ s, (ν s : Ω') = i (genMap ξ p s)

theorem DomAt.inv_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p) {a : Ω}
    (h0 : a ≠ 0) (ha : a ∈ regAt ξ p) (hi : i a⁻¹ ∈ A) : a⁻¹ ∈ regAt ξ p := by
  obtain ⟨ν, hloc, hν⟩ := h
  obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
  have hu : IsUnit (ν s) := by
    refine IsUnit.of_mul_eq_one (a := ν s) ⟨i (genMap ξ p s)⁻¹, hi⟩ ?_
    apply Subtype.ext
    show (ν s : Ω') * i (genMap ξ p s)⁻¹ = 1
    rw [hν s, ← map_mul, mul_inv_cancel₀ h0, map_one]
  have hs : IsUnit s := (isUnit_map_iff ν s).mp hu
  refine RingHom.mem_range.mpr ⟨↑hs.unit⁻¹, ?_⟩
  rw [map_units_inv, IsUnit.unit_spec]

theorem genMap_germ (r : Cpt ξ) {U : X.Opens} (hr : r.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ r ((X.presheaf.germ U r.1 hr).hom t) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr)).hom t) := by
  have e := congrArg (fun g => g.hom t) (X.presheaf.germ_stalkSpecializes hr r.2)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes r.2).hom ((X.presheaf.germ U r.1 hr).hom t)) = _
  rw [e]

theorem DomAt.eq_of_mem_affine {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p p' : Cpt ξ} (h : DomAt ξ i A p)
    (h' : DomAt ξ i A p') {U : X.Opens} (hU : IsAffineOpen U) (hp : p.1 ∈ U) (hp' : p'.1 ∈ U) : p.1 = p'.1 := by
  obtain ⟨ν, hν1, hν⟩ := h
  obtain ⟨ν', hν1', hν'⟩ := h'
  have key : ∀ b : Γ(X, U), p.1 ∈ X.basicOpen b ↔ p'.1 ∈ X.basicOpen b := by
    intro b
    have e : ν ((X.presheaf.germ U p.1 hp).hom b) = ν' ((X.presheaf.germ U p'.1 hp').hom b) := by
      apply Subtype.ext
      simp only [hν, hν', genMap_germ]
    rw [X.mem_basicOpen b p.1 hp, X.mem_basicOpen b p'.1 hp', ← isUnit_map_iff ν, ← isUnit_map_iff ν', e]
  have sp : ∀ {a c : X}, a ∈ U → c ∈ U → (∀ b : Γ(X, U), a ∈ X.basicOpen b → c ∈ X.basicOpen b) → c ⤳ a := by
    intro a c ha hc hab
    rw [specializes_iff_forall_open]
    intro s hs has
    obtain ⟨b, hb, hab'⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨a, has⟩ ha
    exact hb (hab b hab')
  exact ((sp hp' hp (fun b => (key b).2)).antisymm (sp hp hp' (fun b => (key b).1))).eq

theorem domAt_of_spec {i : Ω →+* Ω'} {A : ValuationSubring Ω'} (z : Spec (CommRingCat.of A) ⟶ X)
    (hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ ξ)
    (h : genPt ξ ⤳ z (IsLocalRing.closedPoint A)) :
    DomAt ξ i A ⟨z (IsLocalRing.closedPoint A), h⟩ := by
  refine ⟨(Scheme.stalkClosedPointTo z).hom, inferInstance, fun s => ?_⟩
  obtain ⟨U, hU, t, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : genPt ξ ∈ U := h.mem_open U.isOpen hU
  have hw : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') ∈ U := by
    rw [← hz]
    exact ((IsLocalRing.specializes_closedPoint _).map z.continuous).mem_open U.isOpen hU
  have e1 := val_comp_spec (CommRingCat.ofHom (algebraMap A Ω')) z _ hz U hU hw t
  have e2 := val_comp_spec (CommRingCat.ofHom i) ξ _ rfl U hg hw t
  have e3 := congrArg i (genMap_germ (ξ := ξ) ⟨z (IsLocalRing.closedPoint A), h⟩ hU t)
  exact e1.trans (e2.symm.trans e3.symm)

private theorem exists_domAt_of_injective_genMap (i : Ω →+* Ω') (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p)) :
    ∃ A : ValuationSubring Ω', DomAt ξ i A p := by
  let g : X.presheaf.stalk p.1 →+* Ω' := i.comp (genMap ξ p)
  have hg : Function.Injective g := i.injective.comp hinj
  obtain ⟨A, hA⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range g)
  obtain ⟨hle, hloc⟩ := hA
  have hmem : ∀ s, g s ∈ A.toSubring := fun s => hle ⟨s, rfl⟩
  refine ⟨A, g.codRestrict A.toSubring hmem, ⟨fun s hs => ?_⟩, fun s => rfl⟩
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have hv' : g s * (v : Ω') = 1 := congrArg Subtype.val hv
  let y : (LocalSubring.range g).toSubring := ⟨g s, ⟨s, rfl⟩⟩
  have hy : IsUnit y := by
    apply hloc.map_nonunit
    refine IsUnit.of_mul_eq_one ⟨v, v.2⟩ ?_
    exact Subtype.ext hv'
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨s', hs'⟩ := w.2
  refine IsUnit.of_mul_eq_one s' ?_
  apply hg
  rw [map_mul, map_one, hs']
  exact congrArg Subtype.val hw

private theorem inChart_of_domAt_of_div_mem {i : Ω →+* Ω'} {A : ValuationSubring Ω'} {p : Cpt ξ} (h : DomAt ξ i A p)
    {κ : Type} {x : κ → Ω} {c : κ} (hxc : x c ≠ 0) (hA : ∀ c', i (x c' / x c) ∈ A) {c'' : κ}
    (h'' : InChart ξ x c'' p) : InChart ξ x c p := by
  refine ⟨hxc, fun c' => ?_⟩
  have hc'' : x c'' ≠ 0 := h''.1
  have h1 : x c / x c'' ∈ regAt ξ p := h''.2 c
  have h0 : x c / x c'' ≠ 0 := div_ne_zero hxc hc''
  have h2 : (x c / x c'')⁻¹ ∈ regAt ξ p := h.inv_mem h0 h1 (by rw [inv_div]; exact hA c'')
  have e : x c' / x c = (x c' / x c'') * (x c / x c'')⁻¹ := by
    rw [inv_div, div_mul_div_cancel₀ hc'']
  rw [e]
  exact mul_mem (h''.2 c') h2

private theorem div_mem_of_valuation_le {K : Type} [Field K] (A : ValuationSubring K) {a b : K} (hb : b ≠ 0)
    (h : A.valuation a ≤ A.valuation b) : a / b ∈ A := by
  rw [← A.valuation_le_one_iff, map_div₀]
  have hb' : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  exact div_le_one_of_le₀ h zero_le'

theorem surjective_of_dominates (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type)
    [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω') (hc : CoordTie ℤ ξ x)
    (hg : ∀ q : X, genPt ξ ⤳ q) (hp : IsProper s') (hd : Dominates ξ' ξ f i) : Function.Surjective f := by
  intro q
  obtain ⟨A, hdom⟩ := exists_domAt_of_injective_genMap i ⟨q, hg q⟩ (hc.gen.inj ⟨q, hg q⟩)
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s' := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    infer_instance
  let S : ValuativeCommSq s' :=
    { R := A, K := Ω', i₁ := ξ', i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  obtain ⟨⟨l, hl1, -⟩⟩ := (hex.1 S).exists_lift
  have hl : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ l = ξ' := hl1
  have hz : Spec.map (CommRingCat.ofHom (algebraMap A Ω')) ≫ (l ≫ f) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [← Category.assoc, hl]
    exact hd
  have hdom' := domAt_of_spec (i := i) (A := A) (l ≫ f) hz (hg _)
  obtain ⟨c₁, hc₁⟩ := hc.cover ⟨q, hg q⟩
  have : Nonempty κ := ⟨c₁⟩
  obtain ⟨c, hcmax⟩ := Finite.exists_max (fun c => A.valuation (i (x c)))
  have hxc : x c ≠ 0 := by
    intro h0
    have h1 := hcmax c₁
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hc₁.1 ((map_eq_zero i).1 h1)
  have hA : ∀ c', i (x c' / x c) ∈ A := fun c' => by
    rw [map_div₀]
    exact div_mem_of_valuation_le A ((map_ne_zero i).2 hxc) (hcmax c')
  obtain ⟨U, hUaff, hUmem⟩ := hc.affine c hxc
  have hq : q ∈ U := (hUmem q).2 ⟨hg q, inChart_of_domAt_of_div_mem hdom hxc hA hc₁⟩
  obtain ⟨c₂, hc₂⟩ := hc.cover ⟨(l ≫ f) (IsLocalRing.closedPoint A), hg _⟩
  have hq' : (l ≫ f) (IsLocalRing.closedPoint A) ∈ U :=
    (hUmem _).2 ⟨hg _, inChart_of_domAt_of_div_mem hdom' hxc hA hc₂⟩
  have e := DomAt.eq_of_mem_affine hdom hdom' hUaff hq hq'
  exact ⟨l (IsLocalRing.closedPoint A), e.symm⟩

end Surj
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChange
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  first | exact @PositivityTheory.HtPt.Htat.reg_pull | exact PositivityTheory.HtPt.Htat.reg_pull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem exists_germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {y : X}
    (hs : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (a : Ω) :
    ∃ f g : X.presheaf.stalk y,
      (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g ≠ 0 ∧
      a * (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g =
        (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hzU : ξ (IsLocalRing.closedPoint Ω) ∈ U := hs.mem_open U.isOpen hyU
  let z : U := ⟨_, hzU⟩
  letI := X.presheaf.algebra_section_stalk z
  have hl := hU.isLocalization_stalk z
  obtain ⟨s, rfl⟩ := hb.2 a
  obtain ⟨⟨f, g⟩, e⟩ := IsLocalization.surj (S := X.presheaf.stalk z.1)
    (hU.primeIdealOf z).asIdeal.primeCompl s
  have hgerm : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes hs).hom (X.presheaf.germ U y hyU r) =
      X.presheaf.germ U _ hzU r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU hs) r
  refine ⟨X.presheaf.germ U y hyU f, X.presheaf.germ U y hyU g.1, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U _ hzU g.1) :=
      IsLocalization.map_units (X.presheaf.stalk z.1) g
    have := hu.map (Scheme.stalkClosedPointTo ξ).hom
    simpa [hgerm] using this.ne_zero
  · have e' : s * X.presheaf.germ U _ hzU g.1 = X.presheaf.germ U _ hzU f := e
    have := congrArg (Scheme.stalkClosedPointTo ξ).hom e'
    simpa [hgerm] using this

theorem isFractionRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ →
    ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  intro X Ω _ ξ h p
  refine IsFractionRing.of_field (regAt ξ p) Ω fun a => ?_
  obtain ⟨f, g, hg, e⟩ := exists_germ_frac ξ h.bij (y := p.1) p.2 a
  refine ⟨⟨genMap ξ p f, f, rfl⟩, ⟨genMap ξ p g, g, rfl⟩, ?_⟩
  exact eq_div_of_mul_eq hg e

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReversedDualTriangularStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_dual_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | exact GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri | (intros; apply GlobalTheory.CompanionTheory.Ar.DualPair.dualRevTri <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SepCountNonneg
section
noncomputable section

open Classical

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst

open GlobalTheory.CompanionTheory.Ar.Cmp

def relab (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

def Sep {Ψ : Type} (N j : ℕ) (x : Ψ × Fin N) (c : LowEnt Ψ N) : Prop :=
  c.1 = x.1 ∧ min (relab N j c.2.1.1) (relab N j c.2.1.2) ≤ (x.2 : ℕ) ∧
    (x.2 : ℕ) < max (relab N j c.2.1.1) (relab N j c.2.1.2)

def sepCount {Ψ : Type} [Fintype Ψ] {e : ℕ} (N j : ℕ) (w : Fin e → Ψ × Fin N) : ℝ :=
  ∑ f : LowEnt Ψ N ≃ Fin e, ∏ c : LowEnt Ψ N, if Sep N j (w (f c)) c then (1 : ℝ) else 0

theorem relab_self (N : ℕ) (a : Fin N) : relab N N a = a := by
  simp [relab]

theorem sepCount_nonneg {Ψ : Type} [Fintype Ψ] {e : ℕ} (N j : ℕ) (w : Fin e → Ψ × Fin N) :
    0 ≤ sepCount N j w :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num

end GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupTangentLiftStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_group_tangent_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime],
  ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V),
    RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
    ∃ u : Γ(G.left, U) →+* Localization.Away f,
      (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | exact GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslateIntoSmallerOpenStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_into_smaller_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover | exact GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover <;> assumption)
end

