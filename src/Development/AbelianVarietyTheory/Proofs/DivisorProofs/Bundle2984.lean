import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationDescendedClosedTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2891
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveGoodReductionModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPlaceCurve

theorem sz_of_pow {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {y : ℂ} {n : ℕ} (hn : 0 < n)
    (h : Sz l lam 0 (y ^ n)) : Sz l lam 0 y := by
  obtain ⟨hy, hn'⟩ := h
  have ha : IsAlgebraic ℚ y := IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 hy)
  have hy' : y ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.2 ha
  refine ⟨hy', ?_⟩
  rw [Real.rpow_zero] at hn' ⊢
  have e : (⟨y ^ n, hy⟩ : algebraicClosure ℚ ℂ) = (⟨y, hy'⟩ : algebraicClosure ℚ ℂ) ^ n := rfl
  rw [e, map_pow, norm_pow] at hn'
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 hn'

theorem exists_curve : GlobalTheory.Published.SerreTateGoodReductionSt →
  ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ), FiniteDimensional ℚ k₁ ∧ IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧
        u.IsDiff (fun _ ↦ t) v' ∧ t ≠ 0 ∧ Sz l lam 0 ((t * Ω)⁻¹) := by
  intro _ d Λ hd hΛ l _ lam Ω hΩ
  have hJ := GlobalTheory.T.j_invariant_integral d Λ hd hΛ
  obtain ⟨k₁, R₁, W, hk, hpl, hsub, hΔ, hj⟩ := GlobalTheory.T.weierstrass_model_good_reduction l lam _ hJ
  have hD : latDisc Λ ≠ 0 := g₂_cube_sub_g₃_sq_ne_zero Λ
  have hΔ0 : ((W.Δ : R₁) : ℂ) ≠ 0 := by
    intro h0
    exact hΔ.ne_zero (Subtype.ext h0)
  have hrel : 1728 * ((W.Δ : R₁) : ℂ) = ((W.c₄ : R₁) : ℂ) ^ 3 - ((W.c₆ : R₁) : ℂ) ^ 2 := by
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) W.c_relation
    push_cast at this
    exact this
  have hΔ' : (((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2 = ((W.Δ : R₁) : ℂ) := by
    linear_combination -hrel / 1728
  have e : Λ.g₂ ^ 3 * ((((W.c₄ : R₁) : ℂ) / 12) ^ 3 - 27 * (((W.c₆ : R₁) : ℂ) / 216) ^ 2) =
      (((W.c₄ : R₁) : ℂ) / 12) ^ 3 * (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2) := by
    rw [hΔ', div_pow, hj]
    unfold latDisc at hD ⊢
    field_simp
    ring
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq hD (by rw [hΔ']; exact hΔ0) e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hu (by simpa using hc.symm)
  have h4 : ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ := by
    rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; linear_combination 12 * h2
  have h6 : ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ := by
    rw [show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; linear_combination 216 * h3
  obtain ⟨P, A', _, φ', L', uu, v, v', h1, h2', h3', h4', h5, h6', h7, h8⟩ := GlobalTheory.T.elliptic_curve_abelian_scheme_model R₁ W hΔ Λ c hc0 h4 h6
  have hΩ0 : Ω ≠ 0 := by rintro rfl; apply hD; rw [← hΩ]; norm_num
  have key : (c * Ω) ^ 12 = ((W.Δ : R₁) : ℂ) := by
    rw [← hΔ', h4, h6, mul_pow, hΩ]
    unfold latDisc
    ring
  refine ⟨k₁, R₁, hk, hpl, hsub, P, A', inferInstance, φ', L', uu, v, v', c, h1, h2', h3', h4', h5, h6', h7, h8, hc0, ?_⟩
  obtain ⟨w, hw⟩ := hΔ
  refine sz_of_pow (n := 12) (by norm_num) ?_
  have e2 : ((c * Ω)⁻¹) ^ 12 = ((w⁻¹ : R₁ˣ) : R₁) := by
    rw [inv_pow, key, ← hw]
    have := congrArg (fun x : R₁ ↦ (x : ℂ)) w.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at this ⊢
    exact (eq_inv_of_mul_eq_one_right this).symm
  rw [e2]
  exact hpl.2.1 _ (w⁻¹ : R₁ˣ).1.2

end GlobalTheory.CMPlaceCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferentialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_map_uniformization_line : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) → ∀ e : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ z w, e (z + w) = e z * e w) → (∀ z, (e z).left = pt Λ Ω z ≫ f) → ∃ β₁ : Fin n → ℂ, ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left := by
  first | exact @GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | exact GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | (intros; apply GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticSectionFromUniformizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_section_from_uniformization : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ x : Sp ℂ ⟶ scheme (curve Λ Ω), x ≫ toSpec (curve Λ Ω) = 𝟙 _ → ∃ z : ℂ, pt Λ Ω z = x := by
  first | exact @GlobalTheory.CMTorsion.exists_pt_eq | exact GlobalTheory.CMTorsion.exists_pt_eq | (intros; apply GlobalTheory.CMTorsion.exists_pt_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PadicRootNorm

open Polynomial Filter Topology

variable {l : ℕ} [Fact l.Prime]

theorem norm_prod_map {β : Type*} (s : Multiset β) (f : β → PadicAlgCl l) :
    ‖(s.map f).prod‖ = (s.map fun a => ‖f a‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

open Classical in
theorem eventually_norm_prod (s : Multiset (PadicAlgCl l)) (M : ℚ_[l][X]) :
    ∀ᶠ n : ℕ in atTop, ‖(s.map fun a => aeval a (M + C ((l : ℚ_[l]) ^ n))).prod‖ =
      ‖(l : ℚ_[l])‖ ^ (n * (s.filter fun a => aeval a M = 0).card) *
        ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod := by
  have hl : Tendsto (fun n : ℕ => ‖(l : ℚ_[l])‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one
  have hev : ∀ᶠ n : ℕ in atTop, ∀ a ∈ (s.filter fun a => ¬ aeval a M = 0).toFinset,
      ‖(l : ℚ_[l])‖ ^ n < ‖aeval a M‖ := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have : aeval a M ≠ 0 := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 ha)).2
    exact (tendsto_order.1 hl).2 _ (norm_pos_iff.2 this)
  filter_upwards [hev] with n hn
  conv_lhs => rw [← Multiset.filter_add_not (fun a => aeval a M = 0) s]
  rw [Multiset.map_add, Multiset.prod_add, norm_mul, norm_prod_map, norm_prod_map]
  congr 1
  · rw [Multiset.map_congr rfl (g := fun _ => ‖(l : ℚ_[l])‖ ^ n), Multiset.map_const',
      Multiset.prod_replicate, ← pow_mul]
    intro a ha
    have h0 : aeval a M = 0 := (Multiset.mem_filter.1 ha).2
    rw [map_add, aeval_C, h0, zero_add, norm_algebraMap', norm_pow]
  · apply congrArg
    apply Multiset.map_congr rfl
    intro a ha
    have hlt := hn a (Multiset.mem_toFinset.2 ha)
    have hc : ‖algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
      rw [norm_algebraMap', norm_pow]
    rw [map_add, aeval_C, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hc]; exact hlt.ne'),
      hc, max_eq_left hlt.le]

open Classical in
theorem card_filter_eq (s t : Multiset (PadicAlgCl l))
    (h : ∀ F : ℚ_[l][X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (M : ℚ_[l][X]) :
    (s.filter fun a => aeval a M = 0).card = (t.filter fun a => aeval a M = 0).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_norm_prod s M).and (eventually_norm_prod t M))
  set x := ‖(l : ℚ_[l])‖ with hxdef
  have hx0 : 0 < x := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hx1 : x < 1 := Padic.norm_p_lt_one
  set k := (s.filter fun a => aeval a M = 0).card
  set k' := (t.filter fun a => aeval a M = 0).card
  set c := ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  set c' := ((t.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  have hc' : 0 < c' := Multiset.prod_pos fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
    exact norm_pos_iff.2 (Multiset.mem_filter.1 ha).2
  have e1 : x ^ (N * k) * c = x ^ (N * k') * c' := by
    rw [← (hN N le_rfl).1, ← (hN N le_rfl).2, h]
  have e2 : x ^ ((N + 1) * k) * c = x ^ ((N + 1) * k') * c' := by
    rw [← (hN (N + 1) (Nat.le_succ N)).1, ← (hN (N + 1) (Nat.le_succ N)).2, h]
  have e3 : x ^ k * (x ^ (N * k') * c') = x ^ k' * (x ^ (N * k') * c') := by
    calc x ^ k * (x ^ (N * k') * c') = x ^ k * (x ^ (N * k) * c) := by rw [e1]
      _ = x ^ ((N + 1) * k) * c := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
      _ = x ^ ((N + 1) * k') * c' := e2
      _ = x ^ k' * (x ^ (N * k') * c') := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
  have hne : x ^ (N * k') * c' ≠ 0 := by positivity
  exact pow_right_injective₀ hx0 hx1.ne (mul_right_cancel₀ hne e3)

theorem monic_eq_one_of_no_root {P : ℚ_[l][X]} (hP : P.Monic)
    (h : ∀ a : PadicAlgCl l, a ∉ P.aroots (PadicAlgCl l)) : P = 1 := by
  by_contra hne
  have hd : P.degree ≠ 0 := by
    intro hd
    exact hne (eq_one_of_monic_natDegree_zero hP (natDegree_eq_of_degree_eq_some hd))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero (PadicAlgCl l) P hd
  exact h a (mem_aroots.2 ⟨hP.ne_zero, ha⟩)

open Classical in
theorem exists_root_minpoly_eq_of_card_eq (P Q : ℚ_[l][X]) (hQ : Q ≠ 0)
    (hc : ∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card)
    (a : PadicAlgCl l) (ha : a ∈ P.aroots (PadicAlgCl l)) :
    ∃ b ∈ Q.aroots (PadicAlgCl l), minpoly ℚ_[l] a = minpoly ℚ_[l] b := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have h1 : 0 < ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨a, Multiset.mem_filter.2 ⟨ha, minpoly.aeval _ _⟩⟩
  rw [hc a] at h1
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 h1
  obtain ⟨hbQ, hbM⟩ := Multiset.mem_filter.1 hb
  exact ⟨b, hbQ, minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hbM (minpoly.monic hint)⟩

open Classical in
theorem eq_of_card_filter (n : ℕ) : ∀ P Q : ℚ_[l][X], P.natDegree = n → P.Monic → Q.Monic →
    (∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card) → P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hn hP hQ hc
  by_cases hr : ∃ a : PadicAlgCl l, a ∈ P.aroots (PadicAlgCl l)
  · obtain ⟨a, ha⟩ := hr
    have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
    obtain ⟨b, hbQ, hab⟩ := exists_root_minpoly_eq_of_card_eq P Q hQ.ne_zero hc a ha
    have hMQ : minpoly ℚ_[l] a ∣ Q := by rw [hab]; exact minpoly.dvd _ _ (mem_aroots.1 hbQ).2
    have hMP : minpoly ℚ_[l] a ∣ P := minpoly.dvd _ _ (mem_aroots.1 ha).2
    have hM : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
    have hMpos := minpoly.natDegree_pos hint
    obtain ⟨P', rfl⟩ := hMP
    obtain ⟨Q', rfl⟩ := hMQ
    have hP' := hM.of_mul_monic_left hP
    have hQ' := hM.of_mul_monic_left hQ
    have hdeg : (minpoly ℚ_[l] a * P').natDegree = (minpoly ℚ_[l] a).natDegree + P'.natDegree :=
      hM.natDegree_mul hP'
    rw [ih P'.natDegree (by omega) P' Q' rfl hP' hQ' ?_]
    intro b
    have h := hc b
    rw [aroots_mul hP.ne_zero, aroots_mul hQ.ne_zero, Multiset.filter_add, Multiset.filter_add,
      Multiset.card_add, Multiset.card_add] at h
    omega
  · push_neg at hr
    have hr' : ∀ b : PadicAlgCl l, b ∉ Q.aroots (PadicAlgCl l) := by
      intro b hb
      obtain ⟨a, haP, hab⟩ := exists_root_minpoly_eq_of_card_eq Q P hP.ne_zero (fun c => (hc c).symm) b hb
      have hint : IsIntegral ℚ_[l] b := Algebra.IsIntegral.isIntegral b
      exact hr a haP
    rw [monic_eq_one_of_no_root hP hr, monic_eq_one_of_no_root hQ hr']

theorem norm_eq_rat (s t : Multiset (PadicAlgCl l)) (hst : Multiset.card s = Multiset.card t)
    (h : ∀ F : ℤ[X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (R : ℚ[X]) :
    ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) R
  set G := IsLocalization.integerNormalization (nonZeroDivisors ℤ) R
  have key : ∀ a : PadicAlgCl l, aeval a G = ((b : ℤ) : PadicAlgCl l) * aeval a (R.map (algebraMap ℚ ℚ_[l])) := by
    intro a
    rw [aeval_map_algebraMap, ← aeval_map_algebraMap ℚ a G, hb, map_zsmul, zsmul_eq_mul]
  have hb0 : ((b : ℤ) : PadicAlgCl l) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero b)
  have hG := h G
  simp only [key] at hG
  rw [Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const', Multiset.map_const',
    Multiset.prod_replicate, Multiset.prod_replicate, norm_mul, norm_mul, hst] at hG
  exact mul_left_cancel₀ (by simpa using hb0) hG

theorem norm_eq_all (s t : Multiset (PadicAlgCl l))
    (h : ∀ R : ℚ[X], ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖)
    (F : ℚ_[l][X]) :
    ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖ := by
  have hr : ∀ (n i : ℕ), ∃ q : ℚ, ‖F.coeff i - q‖ < 1 / ((n : ℝ) + 1) :=
    fun n i => Padic.rat_dense l _ (by positivity)
  choose r hr using hr
  set D := F.natDegree
  let R : ℕ → ℚ[X] := fun n => ∑ i ∈ Finset.range (D + 1), C (r n i) * Polynomial.X ^ i
  have hcoef : ∀ i, Tendsto (fun n => ((r n i : ℚ) : ℚ_[l])) atTop (𝓝 (F.coeff i)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact (hr n i).le
  have hval : ∀ a : PadicAlgCl l, Tendsto (fun n => aeval a ((R n).map (algebraMap ℚ ℚ_[l])))
      atTop (𝓝 (aeval a F)) := by
    intro a
    have e : ∀ n, aeval a ((R n).map (algebraMap ℚ ℚ_[l])) =
        ∑ i ∈ Finset.range (D + 1), algebraMap ℚ_[l] (PadicAlgCl l) ((r n i : ℚ) : ℚ_[l]) * a ^ i := by
      intro n
      rw [aeval_map_algebraMap]
      simp [R, map_sum]
    simp only [e]
    rw [aeval_eq_sum_range]
    simp only [Algebra.smul_def]
    exact tendsto_finset_sum _ fun i _ =>
      (((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).tendsto _).comp (hcoef i)).mul_const _
  have hs := (tendsto_multiset_prod s fun a _ => hval a).norm
  have ht := (tendsto_multiset_prod t fun a _ => hval a).norm
  exact tendsto_nhds_unique hs (ht.congr fun n => (h (R n)).symm)

theorem card_aroots (P : ℚ_[l][X]) : Multiset.card (P.aroots (PadicAlgCl l)) = P.natDegree := by
  rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem eq_of_norm_prod_aeval_eq : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic →
    P.natDegree = Q.natDegree →
    (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ =
      ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  intro l _ P Q hP hQ hdeg h
  classical
  have hcard : Multiset.card (P.aroots (PadicAlgCl l)) = Multiset.card (Q.aroots (PadicAlgCl l)) := by
    rw [card_aroots, card_aroots, hdeg]
  have hall := norm_eq_all _ _ (norm_eq_rat _ _ hcard h)
  exact eq_of_card_filter _ P Q rfl hP hQ fun a => card_filter_eq _ _ hall _

end GlobalTheory.PadicRootNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_same_generic_projective_coords : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  first | exact @GlobalTheory.SiegCrd.eq_of_generic_pCrd | exact GlobalTheory.SiegCrd.eq_of_generic_pCrd | (intros; apply GlobalTheory.SiegCrd.eq_of_generic_pCrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_linearExtension_to_algClosedField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  first | exact @GlobalTheory.Mum.UpAct.act_extension | exact GlobalTheory.Mum.UpAct.act_extension | (intros; apply GlobalTheory.Mum.UpAct.act_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_coord_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  have hq := GlobalTheory.T.isolated_in_fibre_coordinateMap_affineSpace R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  obtain ⟨T, h, W, p, hfl, hpW, hpx, hW⟩ := GlobalTheory.T.exists_flat_chart_etale_of_quasiFiniteAt_alt R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj hq
  obtain ⟨V, hxV, hV⟩ := GlobalTheory.T.etale_nhds_affineSpace_map_of_flat_baseChange R hR U g τ hlft hτ T h hfl W p hpW hW
  rw [hpx] at hxV
  exact GlobalTheory.T.family_pulled_back_near_point_of_etale_coordinates R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj V hxV hV

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationDescendedClosedTorusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenCubicalTrivialisation_descended_closedTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) → EvenOn P := by
  first | exact @GlobalTheory.Mum.EvenDesc.evenOn_of_galAct | exact GlobalTheory.Mum.EvenDesc.evenOn_of_galAct | (intros; apply GlobalTheory.Mum.EvenDesc.evenOn_of_galAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationOfTraitUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenCubicalTrivialisation_of_trait_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  first | exact @GlobalTheory.Mum.evenOn_of_unifTrait | exact GlobalTheory.Mum.evenOn_of_unifTrait | (intros; apply GlobalTheory.Mum.evenOn_of_unifTrait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianVariety_of_halved_periodMap : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D' : PLat O bar) (Q : D'.La →+ (Fin g → ℂ)) (E₁ : LinearMap.BilinForm ℤ D'.La), IsPeriod D' ρ Q → D'.EF = (2 : ℤ) • E₁ → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (_ : IsCommMonObj A) (act : OActN O A) (P : LB (G2 A).left) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ IsExp (𝟙 (Sp ℂ)) e ∧ (∀ z, e z = 1 ↔ z ∈ Q.range) ∧ (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ act.act a) ∧ (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) := by
  first | exact @GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | exact GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod | (intros; apply GlobalTheory.HalvedPeriod.exists_abelian_of_isPeriod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicSum_null_family_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) → ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) → s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  first | exact @GlobalTheory.Mum.AdicSum.exists_adic_sum | exact GlobalTheory.Mum.AdicSum.exists_adic_sum | (intros; apply GlobalTheory.Mum.AdicSum.exists_adic_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ F : ∀ β, SecT D.toPre a n j β, IsSum (maximalIdeal R) s F ∧ Small (maximalIdeal R) (w := id) F := by
  first | exact @GlobalTheory.TwFam.AdicSum.exists_isSum | exact GlobalTheory.TwFam.AdicSum.exists_isSum | (intros; apply GlobalTheory.TwFam.AdicSum.exists_isSum <;> assumption)
end

