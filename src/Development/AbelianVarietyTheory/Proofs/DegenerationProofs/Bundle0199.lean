import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttained
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_exists_norm_FF_eq :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  intro o Ω _ _ _ hA S p _ y₀ hy T c B hle ⟨t, i, hge⟩
  have hN := S.N_ge
  have hr := S.r_pos
  have hrN : 2 ≤ S.r * S.N := le_trans hN (Nat.le_mul_of_pos_left _ hr)
  have hn : 1 < (S.r * S.N) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have : Fact (1 < (S.r * S.N) ^ 2) := ⟨hn⟩
  have : IsDomain o := hA.inj.isDomain _
  have : NeZero (S.r * S.N) := ⟨by omega⟩
  have := Fintype.ofFinite T
  have hmem := (thetaSys_FF_mem_finite_perp_proj o Ω S).1 T c
  set E : T → PadicAlgCl p := fun s =>
    ∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev s j, S.ev_mem s j⟩ with hE
  have hval : ∀ k : T → ZMod ((S.r * S.N) ^ 2), y₀ ⟨S.FF T c (i, k), hmem _⟩
      = ∑ s, y₀ (algebraMap o S.R S.ζ) ^ (k s).val * E s := fun k => by
    have : (⟨S.FF T c (i, k), hmem _⟩ : S.R) = ∑ s : T, algebraMap o S.R S.ζ ^ (k s).val *
        ∑ j, algebraMap o S.R (S.proj T c j i) * ⟨S.ev s j, S.ev_mem s j⟩ := by
      apply Subtype.ext
      simp [ThetaSys.FF, finsum_eq_sum_of_fintype]
    rw [this]
    simp [hE, map_sum]
  have hB : ‖E t‖ = B := le_antisymm (hle t i) hge
  have hB0 : 0 ≤ B := hB ▸ norm_nonneg _
  have h0 : ‖∑ s, E s‖ ≤ B :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun s _ => hle s i
  rcases h0.eq_or_lt with h0 | h0
  · refine ⟨(i, 0), hmem _, ?_⟩
    rw [hval]
    simpa using h0
  · have hu : IsUnit (1 - S.ζ) := by
      obtain ⟨m, hm⟩ : ∃ m, (S.r * S.N) ^ 2 = m + 1 + 1 := ⟨(S.r * S.N) ^ 2 - 2, by omega⟩
      have hp := S.prim
      rw [hm] at hp
      have h1 := hp.prod_one_sub_pow_eq_order
      have h2 : IsUnit ((((S.r * S.N) ^ 2 : ℕ)) : o) := by
        rw [Nat.cast_pow]; exact S.unit.pow _
      rw [hm, Nat.cast_succ, ← h1, Finset.prod_range_succ'] at h2
      simpa using isUnit_of_mul_isUnit_right h2
    have hone : ‖1 - y₀ (algebraMap o S.R S.ζ)‖ = 1 := by
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 := hy (1 - S.ζ)
      have h2 := hy v
      have h3 : ‖y₀ (algebraMap o S.R (1 - S.ζ))‖ * ‖y₀ (algebraMap o S.R v)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, hv, map_one, map_one, norm_one]
      rw [map_sub, map_sub, map_one, map_one] at h1 h3
      refine le_antisymm h1 ?_
      calc (1 : ℝ) = _ := h3.symm
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2
    refine ⟨(i, Pi.single t 1), hmem _, ?_⟩
    have hs : ∑ s, y₀ (algebraMap o S.R S.ζ) ^ ((Pi.single t 1 : T → ZMod ((S.r * S.N) ^ 2)) s).val * E s
        = ∑ s, E s + -((1 - y₀ (algebraMap o S.R S.ζ)) * E t) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
        ← Finset.add_sum_erase _ E (Finset.mem_univ t),
        Finset.sum_congr rfl (g := E) fun s hs => by
          rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs), ZMod.val_zero, pow_zero,
            _root_.one_mul]]
      rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      ring
    have hn' : ‖-((1 - y₀ (algebraMap o S.R S.ζ)) * E t)‖ = B := by
      rw [norm_neg, norm_mul, hone, _root_.one_mul, hB]
    rw [hval, hs, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn']; exact h0.ne),
      hn', max_eq_right h0.le]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem perp_torus_point : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  intro h h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x hx t
  obtain ⟨x', h₁, hadd, -, hs⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₁ a).symm) (by rw [Over.w, Over.w]))
  obtain ⟨q, τ, a, b, c, d⟩ := PerpCharacter.exists_torus_point_eStd (laws_all h h₂).1 hT o Ω S ρ p y₀ u l x h₁ hadd hs
    t t.2
  exact ⟨τ, q, a, b, c, fun a β e => (d a β e).trans (by rw [map_pow, map_pow])⟩

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_sum_perp_char_eq_zero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  intro o Ω _ _ _ _ S F _ ζ hζ H _ a ha
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hω : IsPrimitiveRoot (ζ ^ (S.r * S.N)) (S.r * S.N) :=
    hζ.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod (S.r * S.N)) F := AddChar.zmodChar _ hω.pow_eq_one
  have hχ : ∀ b, χ b = 1 → b = 0 := fun b hb =>
    ((AddChar.zmodChar_primitive_of_primitive_root _ hω).zmod_char_eq_one_iff _ b).mp hb
  let f : S.perp H →+ ZMod (S.r * S.N) :=
    { toFun := fun t => eStd S.g _ (t : S.Gam) a
      map_zero' := by simp [eStd]
      map_add' := fun x y => by
        simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hne : χ.compAddMonoidHom f ≠ 1 := by
    intro h
    apply ha
    rw [← (thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 H]
    intro t ht
    have h1 : f ⟨t, ht⟩ = 0 := hχ _ (DFunLike.congr_fun h ⟨t, ht⟩)
    have h2 : eStd S.g _ t a = 0 := h1
    rw [ThetaProj.eStd_swap, h2, neg_zero]
  have h0 : ∑ t : S.perp H, χ (f t) = 0 := AddChar.sum_eq_zero_of_ne_one hne
  rw [← h0]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pow_mul]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem proj_fixes_eigen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  intro o Ω _ _ _ S F _ y T c hT b E h
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, y (GlobalGen.chi S (c t)) * y S.ζN ^ (c t).val = 1 := fun t => by
    have h2 := GlobalGen.chi_add S (c t) (-(c t))
    rw [add_neg_cancel, GlobalGen.chi_zero] at h2
    rw [← map_pow, ← map_one y, h2, map_mul, GlobalGen.chi.eq_1 S (-(c t)), neg_neg]
  have h3 : y (Ring.inverse (Nat.card T : o)) * (Fintype.card T : F) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← map_natCast y, ← map_mul,
      Ring.inverse_mul_cancel _ (GlobalGen.isUnit_card hT), map_one]
  have h4 : ∑ i, b i * ∑ j, y (S.proj T c j i) * E j =
      y (Ring.inverse (Nat.card T : o)) * ∑ t : T, y (GlobalGen.chi S (c t)) *
        ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j := by
    simp only [GlobalGen.proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h4]
  simp only [h, ← _root_.mul_assoc, h1, _root_.one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← _root_.mul_assoc, h3, _root_.one_mul]

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.TorsionGalois

theorem pow_fix {M : Type} [CommGroup M] (l : ℕ) (f : Monoid.End M) (h : ∀ x : M, x ^ l = 1 → f x = x) (n : ℕ) :
    ∀ x : M, x ^ l ^ n = 1 → (f ^ l ^ n) x = x := by
  have hp : ∀ (g : Monoid.End M) (x : M), g x = x → ∀ k : ℕ, (g ^ k) x = x := by
    intro g x hx k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ]; show (g ^ k) (g x) = x; rw [hx, ih]
  induction n with
  | zero => intro x hx; rw [pow_zero, pow_one] at hx; rw [hx, map_one]
  | succ n ih =>
    intro x hx
    set g := f ^ l ^ n with hg
    have h1 : g (x ^ l) = x ^ l := ih _ (by rw [← pow_mul, ← pow_succ']; exact hx)
    have hd : (g x * x⁻¹) ^ l = 1 := by rw [mul_pow, ← map_pow, h1, inv_pow, mul_inv_cancel]
    have hgd : g (g x * x⁻¹) = g x * x⁻¹ := hp f _ (h _ hd) _
    have hk : ∀ k : ℕ, (g ^ k) x = x * (g x * x⁻¹) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ']
        show g ((g ^ k) x) = _
        rw [ihk, map_mul, map_pow, hgd, pow_succ', ← _root_.mul_assoc, mul_comm (g x) x⁻¹, mul_inv_cancel_left]
    rw [pow_succ, pow_mul, ← hg, hk, hd, _root_.mul_one]

theorem spMap_comp' {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def tw (τ : Ω ≃ₐ[K] Ω) : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K Ω)) :=
  Over.homMk (spMap τ.toRingEquiv.toRingHom) (by
    show spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K Ω) = spMap (algebraMap K Ω)
    rw [← spMap_comp']
    congr 1
    ext c
    exact τ.commutes c)

theorem tw_one : tw (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap (RingHom.id Ω) = 𝟙 _
  exact Spec.map_id _

theorem tw_mul (τ σ : Ω ≃ₐ[K] Ω) : tw (τ * σ) = tw τ ≫ tw σ := by
  apply Over.OverMorphism.ext
  exact spMap_comp' σ.toRingEquiv.toRingHom τ.toRingEquiv.toRingHom

theorem tw_pow_fix (P : Out.PolAV (Sp K)) (l : ℕ) (τ : Ω ≃ₐ[K] Ω)
    (h : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 → tw τ ≫ x = x) (n : ℕ)
    (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) (hx : x ^ l ^ n = 1) : tw (τ ^ l ^ n) ≫ x = x := by
  have := P.isAb.comm
  let f : Monoid.End (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) :=
    MonoidHom.mk' (fun x => tw τ ≫ x) (fun a b => MonObj.comp_mul _ _ _)
  have hf : ∀ (k : ℕ) x, (f ^ k) x = tw (τ ^ k) ≫ x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero, tw_one, Category.id_comp]; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, tw_mul, Category.assoc, ← ih]; rfl
  rw [← hf]
  exact pow_fix l f h n x hx

theorem exists_field [CharZero K] [IsAlgClosure K Ω] (P : Out.PolAV (Sp K)) (l n : ℕ)
    (hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1})
    (h : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 → tw τ ≫ x = x) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧
      ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 →
        ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left := by
  have hpr := P.isAb.proper
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1},
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        (∀ τ : Ω ≃ₐ[K] Ω, τ ∈ L.fixingSubgroup ↔ tw τ ≫ x.1 = x.1) ∧
        ∀ L' : IntermediateField K Ω, L ≤ L' → ∃ y : Sp L' ⟶ P.A.left, spMap (algebraMap L' Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, h1, h2, h3⟩ := GlobalTheory.T.exists_field_of_definition_of_point P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    refine ⟨L, hL, fun τ => ?_, fun L' hL' => (h2 L' (algebraMap L' Ω)).1 fun c hc => ⟨⟨c, hL' hc⟩, rfl⟩⟩
    have e : spMap (RingHom.id Ω) ≫ x.1.left = x.1.left := by
      have e₀ : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
      rw [e₀]; exact Category.id_comp _
    have := h1 τ.toRingEquiv.toRingHom (RingHom.id Ω)
    rw [e] at this
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun hh => Over.OverMorphism.ext (this.2 hh), fun hh => this.1 (congrArg CommaMorphism.left hh)⟩
  choose F hF1 hF2 hF3 using key
  have hmem : ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ (⨆ x, F x).fixingSubgroup ↔
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l ^ n = 1 → tw τ ≫ x = x := by
    intro τ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    simp only [IntermediateField.le_iff_le, Subgroup.zpowers_le, hF2]
    exact ⟨fun hh x hx => hh ⟨x, hx⟩, fun hh x => hh x.1 x.2⟩
  have hn : (⨆ x, F x).fixingSubgroup.Normal := ⟨fun τ hτ σ => by
    rw [hmem] at hτ ⊢
    intro x hx
    have hx' : (tw σ⁻¹ ≫ x) ^ l ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    rw [tw_mul, tw_mul, Category.assoc, Category.assoc, hτ _ hx', ← Category.assoc, ← tw_mul, mul_inv_cancel,
      tw_one, Category.id_comp]⟩
  have hg : IsGalois K (⨆ x, F x : IntermediateField K Ω) := (InfiniteGalois.normal_iff_isGalois _).1 hn
  refine ⟨⨆ x, F x, IntermediateField.finiteDimensional_iSup_of_finite, hg.to_normal, fun g => ?_,
    fun x hx => hF3 ⟨x, hx⟩ _ (le_iSup F _)⟩
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := (⨆ x, F x : IntermediateField K Ω)) Ω g
  refine ⟨n, ?_⟩
  rw [← map_pow, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hmem]
  exact tw_pow_fix P l τ (h τ) n

theorem exists_pairing (hL : Out.Laws) (P : Out.PolAV (Sp K)) :
    ∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ,
      ∀ (k : ℕ) x y, x ^ k = 1 → y ^ k = 1 → ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ e k x y = u := by
  classical
  have key : ∀ (k : ℕ) (x y : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), ∃ v : Ωˣ, x ^ k = 1 → y ^ k = 1 →
      ∀ u : Ωˣ, Out.WeilIs P.A P.L k x y
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom u) ↔ v = u := by
    intro k x y
    by_cases hh : x ^ k = 1 ∧ y ^ k = 1
    · obtain ⟨c, hc, hu⟩ := (hL.weil _ P k _).1 x y hh.1 hh.2
      let E := Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.toMulEquiv
      refine ⟨E c, fun _ _ u => ⟨fun H => ?_, fun H => ?_⟩⟩
      · rw [← hu _ H]
        exact E.apply_symm_apply u
      · subst H
        have : Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (E c) = c :=
          E.symm_apply_apply c
        rw [this]; exact hc
    · exact ⟨1, fun a b => (hh ⟨a, b⟩).elim⟩
  choose e he using key
  exact ⟨e, he⟩

end GlobalTheory.TorsionGalois

open GlobalTheory.TorsionGalois in

theorem GlobalTheory.torsion_points_galois_module : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  intro K _ _ P Ω _ _ _ l hl
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hne : ∀ n, ((l ^ n : ℕ) : Ω) ≠ 0 := fun n => Nat.cast_ne_zero.2 (pow_ne_zero n hl.ne_zero)
  have hcard : ∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} =
      l ^ (n * (2 * P.g)) := fun n => by
    rw [pow_mul]
    exact (hL.mulN _ P (l ^ n) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero n hl.ne_zero))).2.2.2.2 Ω _ (hne n)
  refine ⟨hcard, ?_, fun h n => exists_field P l n
    (Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hl.ne_zero))
    fun τ x hx => Over.OverMorphism.ext (h τ x hx)⟩
  have := P.isAb.comm
  obtain ⟨e, he⟩ := exists_pairing (Ω := Ω) hL P
  have hmul : ∀ (k : ℕ) x x' y, x ^ k = 1 → x' ^ k = 1 → y ^ k = 1 → e k (x * x') y = e k x y * e k x' y := by
    intro k x x' y hx hx' hy
    rw [← he k _ _ (by rw [mul_pow, hx, hx', _root_.mul_one]) hy, map_mul]
    exact (hL.weil _ P k _).2.1 x x' y _ _ ((he k _ _ hx hy _).2 rfl) ((he k _ _ hx' hy _).2 rfl)
  refine ⟨fun n => e (l ^ n), ⟨fun n x x' y hx hx' hy => ⟨hmul _ _ _ _ hx hx' hy, ?_⟩, fun n x y hx hy => ?_,
    fun n x hx h => ?_⟩, fun τ n x y x' y' hx hy hx' hy' => ⟨?_, ?_⟩⟩
  · rw [← he _ _ _ hy hx, map_inv]
    exact GlobalTheory.CommPairing.weilIs_symm P.isLB ((he _ _ _ hx hy _).2 rfl)
  · have hxl : (x ^ l) ^ l ^ n = 1 := by rw [← pow_mul, ← pow_succ']; exact hx
    have hu : IsUnit ((l ^ n * l : ℕ) : Γ((Over.mk (spMap (algebraMap K Ω))).left, ⊤)) := by
      have := (IsUnit.mk0 _ (hne (n + 1))).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
      rw [map_natCast, pow_succ] at this
      exact this
    have H := ((hL.weil _ P (l ^ n) _).2.2.2 l x y _ hu (by rw [← pow_succ]; exact hx) hy).2
      ((he _ _ _ hxl hy _).2 rfl)
    rw [← Nat.cast_mul, ← pow_succ] at H
    exact (he _ _ _ hx (by rw [pow_succ, pow_mul, hy, one_pow]) _).1 H
  · refine GlobalTheory.ThetaRep.eq_one_of_weilIs hL P _ (hne n) x hx fun y hy => ?_
    have H := (he _ _ _ hx hy _).2 (h y hy)
    rwa [map_one] at H
  · have h1 : e (l ^ n) 1 y = 1 := by
      have := hmul (l ^ n) 1 1 y (one_pow _) (one_pow _) hy
      rw [_root_.mul_one] at this
      exact left_eq_mul.1 this
    have hp : ∀ m : ℕ, e (l ^ n) (x ^ m) y = e (l ^ n) x y ^ m := by
      intro m
      induction m with
      | zero => rw [pow_zero x, pow_zero, h1]
      | succ m ih =>
        rw [pow_succ x, hmul _ _ _ _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) hx hy, ih, pow_succ]
    show (e (l ^ n) x y : Ω) ^ l ^ n = 1
    rw [← Units.val_pow_eq_pow_val, ← hp, hx, h1, Units.val_one]
  · obtain rfl : x' = tw τ ≫ x := Over.OverMorphism.ext hx'
    obtain rfl : y' = tw τ ≫ y := Over.OverMorphism.ext hy'
    have H := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (tw τ) ((he _ _ _ hx hy _).2 rfl)
    have E : Units.map (tw τ).left.appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom (e (l ^ n) x y)) =
        Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
          (Units.map τ.toRingEquiv.toRingHom.toMonoidHom (e (l ^ n) x y)) :=
      Units.ext (congrArg (fun q => q.hom (e (l ^ n) x y).val)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ.toRingEquiv.toRingHom))).symm
    rw [E] at H
    exact congrArg Units.val ((he _ _ _ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) _).1 H)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
noncomputable section
namespace GlobalTheory.TestFibre

theorem ptsOver_group_pairing : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∃ x, PtsOver u x) ∧ ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → (∀ a b, x (a + b) = x a * x b) ∧ (∀ a, x a ^ (S.r * S.N) = 1) ∧ (∀ z, z ^ (S.r * S.N) = 1 → ∃! a, x a = z) ∧ ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ a b).val) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x₀, h₀, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  refine ⟨⟨x₀, h₀⟩, fun x hx => ?_⟩
  obtain rfl : x = x₀ := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₀ a).symm) ((Over.w _).trans (Over.w _).symm))
  refine ⟨hadd, fun a => GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) u.cart (hx a) (ρ.fr_tors a).1,
    fun z hz => ?_, fun a b c hc => weilIs_uTest hL o Ω S ρ p y₀ u x hx a b c ?_⟩
  · obtain ⟨a, ha⟩ := hsurj z hz
    exact ⟨a, ha.symm, fun b hb => hinj (hb.trans ha)⟩
  · rw [hc, map_pow, map_pow]

end GlobalTheory.TestFibre
end
end

