import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0032
import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
import ReciprocityTheory.DualLattices.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpairGeo

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GfMono
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_mono : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ϖ ϖ' : o) (N : ℕ) (b : Fin N → K → ℤ), ϖ' ∣ ϖ → Num.TrivFlagMod o ϖ y N b → Num.TrivFlagMod o ϖ' y N b := by
  intro o _ Ω _ _ K _ J _ y ϖ ϖ' N b ⟨c, hc⟩ ⟨g, h1, h2⟩
  refine ⟨g, fun s hs => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨hg, h, hh, r, hr, e⟩ := h1 s hs
    refine ⟨hg, h, hh, algebraMap o Ω c * r, mul_mem (Subalgebra.algebraMap_mem _ c) hr, ?_⟩
    rw [e, hc, map_mul, mul_assoc]
  · obtain ⟨m, U, Z, hU, hZ, hU0, hUd, hm, e⟩ := h2 s t hs ht
    refine ⟨m, U, algebraMap o Ω c • Z, hU, fun i j => ?_, hU0, hUd, hm, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact mul_mem (Subalgebra.algebraMap_mem _ c) (hZ i j)
    · rw [e, hc, map_mul, mul_smul]

end PositivityTheory.HtPt.Gf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart
section
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartFin ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : genMap ξ q (u : X.presheaf.stalk q.1) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h, ⟨_, rfl⟩, ⟨_, eq_inv_of_mul_eq_one_right h⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine IsUnit.of_mul_eq_one t (hi ?_)
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem overZp_iff {p : ℕ} (hp : p.Prime) (q : Cpt ξ) :
    (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) ↔ ∀ b : ℕ, ¬ p ∣ b → unitAt ξ q (b : Ω) := by
  constructor
  · intro hq b hb
    induction b using Nat.recOnMul with
    | zero => exact absurd (dvd_zero p) hb
    | one =>
      rw [Nat.cast_one]
      exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
    | prime r hr =>
      by_contra h
      exact hb (by rw [hq r hr h])
    | mul a b iha ihb =>
      have ha := iha fun h => hb (h.mul_right b)
      have hb' := ihb fun h => hb (h.mul_left a)
      rw [Nat.cast_mul]
      exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
        rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩
  · intro h r hr hf
    by_contra hne
    exact hf (h r fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd).symm)

theorem mem_adjoin_loc [CharZero Ω] {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (T : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin o T) :
    ∃ b : ℕ, ¬ p ∣ b ∧ a * b ∈ Algebra.adjoin ℤ T := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, hp.not_dvd_one, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨m, b, hb, e⟩ := (ho _).1 ⟨r, rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    exact ⟨b, hb, by rw [e, div_mul_cancel₀ _ hb0]; exact intCast_mem _ m⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x + y) * ((b * b' : ℕ) : Ω) = x * b * b' + y * b' * b := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem hx (natCast_mem _ _)) (mul_mem hy (natCast_mem _ _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hx⟩ := hx
    obtain ⟨b', hb', hy⟩ := hy
    refine ⟨b * b', hp.not_dvd_mul hb hb', ?_⟩
    have : (x * y) * ((b * b' : ℕ) : Ω) = x * b * (y * b') := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

theorem chart_int {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {c : κ} (hc : x c ≠ 0) :
    IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω ∧
      IsIntegrallyClosed (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
  have hf : IsFractionRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, e⟩
  refine ⟨hf, (isIntegrallyClosed_iff Ω).2 fun {a} ha => ?_⟩
  refine ⟨⟨a, (T.ring c hc a).2 fun q hq => ?_⟩, rfl⟩
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
  have h4 := h3 (hn q.1).2
  let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ q :=
    (algebraMap (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) Ω).codRestrict _
      fun r => (T.ring c hc r).1 r.2 q hq
  have h5 : IsIntegral (regAt ξ q) a := ha.map_of_comp_eq φ (RingHom.id Ω) rfl
  obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
  exact r.2

theorem chart_loc [CharZero Ω] {κ : Type} [Finite κ] {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (hn : IsNormalScheme X) {p : ℕ} (hp : p.Prime) {o : Type} [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {c : κ} (hc : x c ≠ 0) (B : Subalgebra o Ω) (hB : B = Algebra.adjoin o (Set.range fun j => x j / x c)) :
    IsNoetherianRing B ∧ IsIntegrallyClosed B ∧ IsFractionRing B Ω ∧
      ∃ z : Sp B ⟶ X, spMap (algebraMap B Ω) ≫ z = ξ ∧
        ∀ q : Cpt ξ, q.1 ∈ Set.range z ↔ (InChart ξ x c q ∧ ∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) := by
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  obtain ⟨E, hE⟩ := ChartSmooth.exists_secEquiv hall T hc hUm hg
  obtain ⟨hAf, hAi⟩ := chart_int T hn hc
  have hAB : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), a ∈ B := by
    intro a ha
    have : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ subalgebraOfSubring B.toSubring :=
      Algebra.adjoin_le (by rw [hB]; exact Algebra.subset_adjoin)
    exact this ha
  have hinj := secVal_injective hall T.gen.inj U hg
  let ψ : Γ(X, U) →+* B := (secVal ξ U hg).codRestrict _ fun s => hAB _ (hE s ▸ (E s).2)
  have hψ : ∀ s, (ψ s : Ω) = secVal ξ U hg s := fun _ => rfl
  letI : Algebra Γ(X, U) B := ψ.toAlgebra
  let M : Submonoid Γ(X, U) :=
    { carrier := {r | ∃ b : ℕ, ¬ p ∣ b ∧ r = b}
      one_mem' := ⟨1, hp.not_dvd_one, Nat.cast_one.symm⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b * b', hp.not_dvd_mul hb hb', (Nat.cast_mul _ _).symm⟩ }
  have hb0 : ∀ b : ℕ, ¬ p ∣ b → (b : Ω) ≠ 0 := fun b hb => Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
  haveI hloc : IsLocalization M B := by
    refine ⟨?_, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, b, hb, rfl⟩
      obtain ⟨r, hr⟩ := (ho ((1 : ℤ) / (b : Ω))).2 ⟨1, b, hb, rfl⟩
      refine IsUnit.of_mul_eq_one (algebraMap o B r) (Subtype.ext ?_)
      have h1 : ((algebraMap o B r : B) : Ω) = algebraMap o Ω r := rfl
      simp only [map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast, h1, hr, OneMemClass.coe_one]
      rw [Int.cast_one, mul_one_div_cancel (hb0 b hb)]
    · obtain ⟨b, hb, hab⟩ := mem_adjoin_loc hp ho _ (hB.le a.2)
      refine ⟨⟨E.symm ⟨_, hab⟩, ⟨b, b, hb, rfl⟩⟩, Subtype.ext ?_⟩
      show (a : Ω) * secVal ξ U hg (b : Γ(X, U)) = secVal ξ U hg _
      rw [← hE (E.symm _), E.apply_symm_apply, map_natCast]
    · have h' : secVal ξ U hg r = secVal ξ U hg s := (hψ r).symm.trans ((congrArg Subtype.val h).trans (hψ s))
      rw [hinj h']
  haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  haveI : IsNoetherianRing (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  have hRN : IsNoetherianRing Γ(X, U) := isNoetherianRing_of_ringEquiv _ E.symm
  haveI : IsDomain Γ(X, U) := hinj.isDomain _
  haveI : IsIntegrallyClosed Γ(X, U) := IsIntegrallyClosed.of_equiv E.symm
  have hM : M ≤ nonZeroDivisors Γ(X, U) := by
    rintro _ ⟨b, hb, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => hb0 b hb ?_
    rw [← map_natCast (secVal ξ U hg), h, map_zero]
  refine ⟨IsLocalization.isNoetherianRing M B hRN, isIntegrallyClosed_of_isLocalization B M hM, ?_,
    Spec.map (CommRingCat.ofHom ψ) ≫ hUa.fromSpec, ?_, fun q => ?_⟩
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ κ x c T hc a
    exact ⟨⟨g, hAB g hg⟩, ⟨h, hAB h hh⟩, e⟩
  · have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e1 : X.fromSpecStalk (genPt ξ) = Spec.map (X.presheaf.germ U _ hg) ≫ hUa.fromSpec :=
      (hUa.fromSpecStalk_eq_fromSpecStalk hg).symm
    have e2 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap B Ω) =
        X.presheaf.germ U _ hg ≫ Scheme.stalkClosedPointTo ξ := rfl
    refine Eq.trans ?_ e0
    rw [e1, ← Spec.map_comp_assoc]
    exact (congrArg (fun m => Spec.map m ≫ hUa.fromSpec) e2).trans (Spec.map_comp_assoc _ _ _)
  · have hunit : ∀ (P : PrimeSpectrum Γ(X, U)) (hP : hUa.fromSpec P = q.1) (b : ℕ),
        (b : Γ(X, U)) ∉ P.asIdeal ↔ unitAt ξ q (b : Ω) := by
      intro P hP b
      have hq : q.1 ∈ U := by
        rw [← hP, ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨P, rfl⟩
      have h1 : P ∈ hUa.fromSpec ⁻¹ᵁ X.basicOpen (b : Γ(X, U)) ↔ q.1 ∈ X.basicOpen (b : Γ(X, U)) := by
        rw [← hP]; rfl
      rw [hUa.fromSpec_preimage_basicOpen, X.mem_basicOpen _ _ hq, isUnit_iff_unitAt (T.gen.inj q), map_natCast,
        map_natCast] at h1
      exact h1
    have hrange := PrimeSpectrum.localization_comap_range B M
    rw [overZp_iff hp]
    constructor
    · rintro ⟨P, hP⟩
      have hP' : hUa.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) B) P) = q.1 := hP
      have hq : q.1 ∈ U := by
        rw [← hP', ← SetLike.mem_coe, ← hUa.range_fromSpec]
        exact ⟨_, rfl⟩
      refine ⟨((hUm _).1 hq).2, fun b hb => (hunit _ hP' b).1 fun hm => ?_⟩
      have hd := hrange.subset ⟨P, rfl⟩
      exact Set.disjoint_left.1 hd ⟨b, hb, rfl⟩ hm
    · rintro ⟨hq, hu⟩
      have hqU : q.1 ∈ (U : Set X) := (hUm _).2 ⟨q.2, hq⟩
      rw [← hUa.range_fromSpec] at hqU
      obtain ⟨P, hP⟩ := hqU
      have hd : (P : PrimeSpectrum Γ(X, U)) ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U) B)) := by
        rw [hrange]
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨b, hb, rfl⟩
        exact (hunit P hP b).2 (hu b hb)
      obtain ⟨Q, rfl⟩ := hd
      exact ⟨Q, hP⟩

end PositivityTheory.HtPt.Hcptgen
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

lemma gens_of_len {M : Type} [AddCommGroup M] [Module R M] {m : ℕ} {c : Fin m → R}
    (e : M ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span {c i})) :
    ∃ y : Fin m → M, (∀ i, c i • y i = 0) ∧ ∀ x, ∃ r : Fin m → R, x = ∑ i, r i • y i := by
  refine ⟨fun i => e.symm (Pi.single i 1), fun i => ?_, fun x => ⟨fun i => Quotient.out (e x i), ?_⟩⟩
  · rw [← map_smul, single_smul_self, map_zero]
  · apply e.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact eq_sum_single c (e x)

lemma len_mul_le (hv : v.Integers R) {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup D] [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D)
    (hπ : Function.Surjective π) (hex : ∀ x, π x = 0 → x ∈ LinearMap.range ι) {a b d : NNReal}
    (ha : HasLen v R A a) (hb : HasLen v R B b) (hd : HasLen v R D d) : a * d ≤ b := by
  obtain ⟨m, α, ⟨e⟩, rfl⟩ := ha
  obtain ⟨n, γ, ⟨e'⟩, rfl⟩ := hd
  obtain ⟨u, hu0, hu⟩ := gens_of_len e
  obtain ⟨w, hw0, hw⟩ := gens_of_len e'
  choose z hz using fun j => hπ (w j)
  have hk : ∀ x, π x = 0 → ∃ r : Fin m → R, x = ∑ i, r i • ι (u i) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hex x hx
    obtain ⟨r, rfl⟩ := hu y
    exact ⟨r, by simp⟩
  have h := prod_le_of_gen hv hb (Fin.append (fun i => ι (u i)) z) ?_ (Fin.append α γ) ?_
  · rw [Fin.prod_univ_add] at h
    simpa using h
  · rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs⟩ := hw (π x)
    obtain ⟨r, hr⟩ := hk (x - ∑ j, s j • z j) (by simp [hz, ← hs])
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Fin.append r s, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hr, sub_add_cancel]
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · refine ⟨0, ?_⟩
      simp [← map_smul, hu0]
    · obtain ⟨r, hr⟩ := hk (γ j • z j) (by rw [map_smul, hz, hw0])
      refine ⟨Fin.append r 0, ?_⟩
      rw [Fin.sum_univ_add]
      have hlt : ∀ i : Fin m, Fin.castAdd n i < Fin.natAdd m j := fun i => by
        rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        have := i.2
        omega
      simp [hlt, hr]

variable {F : Type} [Field F] {N X : Type} [AddCommGroup N] [Module F N] [AddCommGroup X]
  [Module F X]

lemma eig_fg (hv : v.Integers R) (M : Submodule R (N → C)) (hM : M.FG) (χ : MulChar F R) :
    (eig M χ).FG := by
  let φ : (N → C) →ₗ[R] (F × N → C) := LinearMap.pi fun q =>
    LinearMap.proj (q.1 • q.2) - χ q.1 • LinearMap.proj q.2
  have hφ : ∀ g q, φ g q = g (q.1 • q.2) - algebraMap R C (χ q.1) * g q.2 := fun g q => by
    simp [φ, Algebra.smul_def]
  refine fg_of_iff (fg_inf_comap hv M hM φ ⊥ Submodule.fg_bot) fun g => ⟨fun hg => ⟨hg.1, ?_⟩,
    fun hg => ⟨hg.1, fun a x => ?_⟩⟩
  · show φ g = 0
    funext q
    rw [hφ, hg.2, sub_self, Pi.zero_apply]
  · have : φ g (a, x) = 0 := congrFun (hg.2 : φ g = 0) _
    rw [hφ] at this
    exact sub_eq_zero.1 this

def omMap (χ : MulChar F R) (φ : X →ₗ[F] N) (M : Submodule R (N → C))
    (M' : Submodule R (X → C)) (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') :
    OmType M χ →ₗ[R] OmType M' χ :=
  Submodule.mapQ _ _ ((LinearMap.funLeft R C φ).restrict fun _ hg => eig_pull χ φ M M' h hg)
    (fun _ hg => sq_pull φ.toAddMonoidHom M M' h hg)

lemma prod_Icc_fin (r : ℕ → NNReal) (n : ℕ) :
    ∏ m ∈ Finset.Icc 1 n, r m = ∏ i : Fin n, r ((i : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]; rfl

end Gen

theorem om_step : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f _ N _ _ _ _ AA hAA K χ a b c ha hb hc
  have hu := exists_inv_card (F := F) hv p hvp
  have hQ : FStable F (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) := fstable_comap _ hAA _
  rw [mul_comm]
  refine len_mul_le hv (omMap χ K.mkQ (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) AA.carrier
      (fun _ hg => hg))
    (omMap χ K.subtype AA.carrier (AA.carrier.map (LinearMap.funLeft R C K.subtype))
      (fun _ hg => Submodule.mem_map_of_mem hg)) ?_ ?_ hb hc ha
  · intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hgh⟩ := hh.1
    have hga : g ∈ augIdeal AA.carrier := by
      rw [mem_aug]
      refine ⟨hg, ?_⟩
      have := ((mem_aug _ _).1 (eig_le_aug _ χ hh)).2
      rw [← hgh] at this
      exact this
    refine ⟨Submodule.Quotient.mk ⟨projL χ g, projL_eig hu χ hAA hga⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    show LinearMap.funLeft R C K.subtype (projL χ g) = h
    rw [← projL_funLeft, ← projL_self χ hh, ← hgh]
  · intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨q, hq, hgq⟩ := om_exact hv AA K.subtype.toAddMonoidHom K.mkQ.toAddMonoidHom
      K.mkQ_surjective Subtype.val_injective (range_subtype_eq K) g (eig_le_aug _ χ hg) hx'
    refine ⟨Submodule.Quotient.mk ⟨projL χ q, projL_eig hu χ hQ hq⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show g - LinearMap.funLeft R C K.mkQ (projL χ q) ∈ sqIdeal (augIdeal AA.carrier)
    have := projL_mem hu χ _ (fstable_sq hAA) hgq
    rw [map_sub, projL_self χ hg] at this
    rw [← projL_funLeft]
    exact this

theorem om_split : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf N _ _ _ _ AA hAA σ hσ
  have := hv.hom_inj.isDomain
  have hu := exists_inv_card (F := F) hv p hvp
  have hfg := fg_of_isLat AA.lat
  constructor
  · intro χ
    obtain ⟨-, -, cO, -, -, hcO0, -, -, hcO⟩ := lens p C v R hv hvp N (fun x => by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]) AA
    obtain ⟨r, hr⟩ := exists_hasLen hv _ _ (eig_fg hv _ hfg χ) (sq_aug_fg hv _ hfg)
    refine ⟨r, ?_, hr⟩
    obtain ⟨s, hs0, hs⟩ := (len_ne_zero_iff hv hcO).1 hcO0
    refine (len_ne_zero_iff hv hr).2 ⟨s, hs0, fun m => ?_⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have h := hs (Submodule.Quotient.mk ⟨g, eig_le_aug _ χ g.2⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h ⊢
    exact h
  · intro r hr
    obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
    have hn : p ^ f - 1 = Fintype.card Fˣ := by rw [Fintype.card_units, hf]
    rw [hn] at hr hord ⊢
    have hsum := sum_projL (C := C) (N := N) σ (fun a ha => by
      by_contra hne
      have := hsep a 1 (fun h => hne (Units.ext h))
      rw [ha, map_one, sub_self, map_zero, map_zero] at this
      exact zero_ne_one this)
    let Ψ : augIdeal AA.carrier →ₗ[R]
        ((i : Fin (Fintype.card Fˣ)) → OmType AA.carrier (σ ^ ((i : ℕ) + 1))) :=
      LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
        (projL (σ ^ ((i : ℕ) + 1))).restrict fun _ hg => projL_eig hu _ hAA hg
    have hsurj : Function.Surjective Ψ := by
      intro y
      choose g hg using fun i => Submodule.Quotient.mk_surjective _ (y i)
      refine ⟨⟨∑ i, (g i : N → C), Submodule.sum_mem _ fun i _ => eig_le_aug _ _ (g i).2⟩, ?_⟩
      funext i
      rw [← hg i]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      show projL (σ ^ ((i : ℕ) + 1)) (∑ i, (g i : N → C)) = g i
      rw [map_sum, Finset.sum_eq_single i, projL_self _ (g i).2]
      · intro j _ hj
        refine projL_ne (fun h => hj ?_) (g j).2
        rw [pow_succ, pow_succ] at h
        exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact j.2) (by rw [hord]; exact i.2)
          (mul_right_cancel h).symm)
      · simp
    have hker : (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype =
        LinearMap.ker Ψ := by
      ext g
      rw [LinearMap.mem_ker, funext_iff]
      constructor
      · intro hg i
        exact (Submodule.Quotient.mk_eq_zero _).2 (projL_mem hu _ _ (fstable_sq hAA) hg)
      · intro hg
        show (g : N → C) ∈ sqIdeal (augIdeal AA.carrier)
        rw [← hsum g]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h1 : (Submodule.Quotient.mk
            (⟨projL (σ ^ ((i : ℕ) + 1)) (g : N → C), projL_eig hu _ hAA g.2⟩ :
              eig AA.carrier (σ ^ ((i : ℕ) + 1))) :
            OmType AA.carrier (σ ^ ((i : ℕ) + 1))) = 0 := hg i
        rw [Submodule.Quotient.mk_eq_zero] at h1
        exact h1
    rw [prod_Icc_fin]
    exact hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans
      (Ψ.quotKerEquivOfSurjective hsurj)) (Tot.hasLen_pi _ _ fun i =>
        hr _ (Finset.mem_Icc.2 ⟨by omega, i.2⟩))

end PositivityTheory.HtPt.Rc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ReTens
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Re

theorem tens_hopf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  intro p _ C _ _ _ v R _ _ _ _ N₁ _ _ _ N₂ _ _ _ A₁ A₂
  refine ⟨PositivityTheory.HtPt.Re.hopfProd A₁ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; rfl
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inl A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_inr A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₁ A₁ A₂
  · rw [PositivityTheory.HtPt.Re.hopfProd_carrier]; exact PositivityTheory.HtPt.Re.tn_stab₂ A₁ A₂
  · intro c₁ c₂ h₁ h₂
    rw [PositivityTheory.HtPt.Re.hopfProd_carrier]
    exact PositivityTheory.HtPt.Re.hasColen_tn h₁ h₂

end PositivityTheory.HtPt.Re
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Twpair
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Twpair

theorem tw_pair : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, ζ n ^ p ^ n = 1) → X.PairingRegular B ζ → ∀ n, ∃ s ∈ prodSpan ((X.Γ n).btOrder ⊤), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p hpp C _ _ _ v O _ _ _ hv _ _ S _ G _ _ _ y La _ _ _ X B ζ hζ hreg n
  have : ValuationRing O := ValuationRing.of_integers v hv
  have := finite_levGrp (La := La) hpp.out.ne_zero n
  obtain ⟨β, hβ⟩ := exists_bichar p n B (ζ n) (hζ n)
  obtain ⟨s, hs⟩ := hreg n
  refine ⟨_, bichar_mem_prodSpan (henselian hv) (fun P => ?_) (X.Γ n) β s fun a b => ?_, fun a b => ?_⟩
  · exact (prime_eq_bot_or_maximal hv P.asIdeal).imp id fun h => PrimeSpectrum.ext h
  · obtain ⟨a, rfl⟩ := lev_surjective p n a
    obtain ⟨b, rfl⟩ := lev_surjective p n b
    rw [hβ]
    exact hs a b
  · exact congrArg Units.val (hβ a b)

end PositivityTheory.HtPt.Twpair
end

