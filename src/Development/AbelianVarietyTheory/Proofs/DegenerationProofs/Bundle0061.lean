import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.SplitChartsField

open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS

include hinj in

theorem exists_mem_basicOpen (P : Γ(G.left, q ⁻¹ᵁ V) → Prop)
    (hP : ∀ x ∈ q ⁻¹ᵁ V, ∃ b, IsWt i _ b 0 ∧ x ∈ G.left.basicOpen b ∧ P b) {y : B} (hy : y ∈ V) :
    ∃ c : Γ(B, V), y ∈ B.basicOpen c ∧ P ((q.app V).hom c) := by
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  let s : Set Γ(B, V) := {c | P ((q.app V).hom c)}
  let α : Γ(B, V) →+* wtZero i (q ⁻¹ᵁ V) := (q.app V).hom.codRestrict _ fun c => (h₀ _).2 ⟨c, rfl⟩
  have hα : Function.Bijective α := ⟨fun a b h => hinj (congrArg Subtype.val h), fun a => by
    obtain ⟨c, hc⟩ := (h₀ a.1).1 a.2
    exact ⟨c, Subtype.ext hc⟩⟩
  have h1 : Ideal.span ((q.app V).hom '' s) = ⊤ := by
    rw [← (hV.preimage q).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hb, hxb, hPb⟩ := hP x hx
    obtain ⟨c, rfl⟩ := (h₀ b).1 hb
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, c, hPb, rfl⟩, hxb⟩
  have h2 : (1 : wtZero i (q ⁻¹ᵁ V)) ∈ (Ideal.span s).map α := hG.mem_map _ α 1 (by
    rw [Ideal.map_span]
    exact h1.ge trivial)
  have h3 : Ideal.span s = ⊤ := by
    obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).1 h2
    rw [Ideal.eq_top_iff_one, ← hα.1 (e.trans (map_one α).symm)]
    exact hc
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV.self_le_iSup_basicOpen_iff.2 h3 hy)
  exact ⟨c.1, hc, c.2⟩

theorem isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by
  have e : q ⁻¹ᵁ B.basicOpen c = G.left.basicOpen ((q.app V).hom c) := Scheme.preimage_basicOpen _ _
  have hle := B.basicOpen_le c
  have hG : Graded i (q ⁻¹ᵁ V) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ (hV.preimage q) (preimage_le_of_stable hS)
  have hS' : Stable i (q ⁻¹ᵁ B.basicOpen c) := e ▸ stable_basicOpen hS (hasWt_iff.2 ((h₀ _).2 ⟨c, rfl⟩))
  have hG' : Graded i (q ⁻¹ᵁ B.basicOpen c) :=
    GlobalTheory.functions_graded_by_weights _ G _ i hi _ ((hV.basicOpen c).preimage q) (preimage_le_of_stable hS')
  have hw : ∀ x, IsWt i _ ((q.app (B.basicOpen c)).hom (rs hle x)) 0 := fun x => by
    rw [app_rs]
    exact ((h₀ _).2 ⟨x, rfl⟩).res _
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  constructor
  · intro ha
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul (hV.preimage q) (q.preimage_mono hle) _ a e
    rw [← app_rs q hle] at hy
    obtain ⟨x, hx, hx'⟩ := hG.exists_lift hG' (rs (q.preimage_mono hle)) (fun _ _ hx => hx.res _) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (S := wtZero i _) (hw c) n) ha)
    obtain ⟨x, rfl⟩ := (h₀ x).1 hx
    refine ⟨(v⁻¹).val ^ n * rs hle x, ?_⟩
    rw [map_mul, app_rs, hx', hy, ← hv, ← map_pow _ v.val, ← _root_.mul_assoc, ← map_mul, ← mul_pow,
      Units.inv_mul, one_pow, map_one, _root_.one_mul]
  · rintro ⟨c', rfl⟩
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c c' rfl
    have e' : c' = (v⁻¹).val ^ n * rs hle y := by
      rw [hy, ← hv, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
    have h1 : IsWt i _ (Units.map (q.app (B.basicOpen c)).hom.toMonoidHom v).val 0 := by
      have := hw c
      rwa [← hv] at this
    have h2 := h1.inv
    rw [neg_zero] at h2
    rw [e', map_mul, map_pow]
    exact mul_mem (pow_mem (S := wtZero i _) h2 n) (hw y)

omit hi h₀ hS in
include hinj in

theorem injective_basicOpen (c : Γ(B, V)) : Function.Injective (q.app (B.basicOpen c)).hom := by
  have hle := B.basicOpen_le c
  obtain ⟨v, hv⟩ : IsUnit (rs hle c) := B.toRingedSpace.isUnit_res_basicOpen c
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle c a rfl
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (hV.preimage q) (q.preimage_mono hle) ((q.app V).hom c)
    ((q.app V).hom y) (Scheme.preimage_basicOpen _ _) (by rw [← app_rs q hle, hy, map_mul, ha, mul_zero])
  rw [← map_pow, ← map_mul, map_eq_zero_iff _ hinj] at hm
  have := congrArg (rs hle) hm
  rwa [map_mul, map_pow, map_zero, hy, ← hv, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero, Units.mul_right_eq_zero] at this

omit hi hV h₀ hS in

theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), GeometricallyConnected H.hom → C.Torus c i → ∃ (B : Over (Sp K)) (_ : GrpObj B) (q : H ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsPullback i (toUnit _) q (η[B]) ∧ ∀ a, ∃ (V : B.left.Opens) (h : C.W a = q.left ⁻¹ᵁ V), IsAffineOpen V ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE V (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hc hT
  obtain ⟨B, q, hp, ha, V, hcov, hV⟩ := Charts.Torus.exists_proper_quotient K H C d c i hT
  obtain ⟨hm, hf, hs, hsm, hfib⟩ := GlobalTheory.LocTriv.main (Sp K) (Fin d → ℤ) H B i q hT.hom ha fun y => by
    obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ y))
    obtain ⟨haff, h, hinj, h₀⟩ := hV a
    have hS := hT.stable a
    have hl := GlobalTheory.LocalWeightUnits.main K H C d c i hT a
    generalize C.W a = W at h hinj h₀ hS hl
    subst h
    rw [Scheme.Hom.appLE_eq_app] at hinj h₀
    have h₀' := fun u => hasWt_iff.symm.trans (h₀ u)
    obtain ⟨b, hb, hb₁, u, hu⟩ := exists_mem_basicOpen hT.hom haff h₀' hinj hS
      (fun b => Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ,
        ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ)
      (fun x hx => (hl x hx).imp fun b hb => ⟨hasWt_iff.1 hb.1, hb.2⟩) hy
    refine ⟨B.left.basicOpen b, hb, haff.basicOpen b, isWt_basicOpen_iff hT.hom haff h₀' hS b,
      injective_basicOpen haff hinj b, ?_⟩
    rw [Scheme.preimage_basicOpen]
    exact ⟨preimage_le_of_stable hb₁, u, fun χ => hasWt_iff.1 (hu χ)⟩
  obtain ⟨g, hcomm, hq, hker⟩ :=
    GlobalTheory.grpObj_of_flat_coset_quotient (Sp K) H _ B i q hT.hom hm hf hs inferInstance hfib
  have : GeometricallyConnected (q.left ≫ B.hom) := by rwa [Over.w]
  refine ⟨B, g, q, ⟨hcomm, hsm inferInstance, hp, geometricallyConnected_of_surjective q.left B.hom⟩, hq, hf, hs, ha,
    hker, fun a => ?_⟩
  obtain ⟨haff, h, -, h₀⟩ := hV a
  exact ⟨V a, h, haff, h₀⟩

end GlobalTheory.SplitChartsField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaBound

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem proj_mul_proj (T T' : AddSubgroup S.Gam) (h : T' ≤ T) (hT : T ≤ S.perp T)
    (hT' : S.IsoFree T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t : T', c' t = c (AddSubgroup.inclusion h t)) :
    S.proj T' c' * S.proj T c = S.proj T c := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite T'
  obtain ⟨d, ⟨e⟩⟩ := hT'.2
  have hζ : IsPrimitiveRoot S.ζN S.N := S.prim.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
  have hu : IsUnit (Nat.card T' : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have h1 : S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, χ (-c t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h2 : S.proj T' c' = Ring.inverse (Nat.card T' : o) • ∑ t : T', χ (-c' t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h3 : ∀ u : T', (χ (-c' u) • S.ρ u) * ∑ t : T, χ (-c t) • S.ρ t
      = ∑ t : T, χ (-c t) • S.ρ t := fun u => by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft (AddSubgroup.inclusion h u))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ← AddChar.map_add_eq_mul, S.ρ_add _ _ (by
      rw [hT (h u.2) t t.2, smul_zero]), hc]
    simp only [Equiv.coe_addLeft, map_add, neg_add]
    rfl
  have h4 : ∀ u : T', (χ (-c' u) • S.ρ u) * S.proj T c = S.proj T c := fun u => by
    rw [h1, mul_smul_comm, h3]
  rw [h2, smul_mul_assoc, Finset.sum_mul]
  simp_rw [h4]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul o,
    smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

theorem norm_FF_le {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p)
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : _) (hk : S.FF T c k ∈ S.R) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : T, ‖∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem _ j⟩‖ ≤ B) :
    ‖y ⟨S.FF T c k, hk⟩‖ ≤ B := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  have h1 : (⟨S.FF T c k, hk⟩ : S.R) = ∑ t : T, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj T c j k.1) * ⟨S.ev t j, S.ev_mem _ j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finset_sum,
      MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]
  rw [h1, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun t _ => ?_
  rw [map_mul, norm_mul, map_sum]
  simp_rw [map_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hy _)).trans (h t)

end GlobalTheory.ThetaBound

namespace GlobalTheory

open ThetaBound

theorem thetaSys_norm_FF_le_exp :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  intro o Ω _ _ _ hA S H p _ y τ hy T c k hk hT
  obtain ⟨-, -, hperp, href⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  have hpos : ∀ α : τ.X, 0 ≤ τ.δ * Real.exp (-(τ.q α / S.N)) := fun α =>
    mul_nonneg τ.δ_pos.le (Real.exp_pos _).le
  refine ⟨fun h1 h2 α hα hc => ?_, fun h1 => ?_⟩
  · refine norm_FF_le S y hy T c k hk (hpos α) fun t => ?_
    rw [← proj_mul_proj S T _ h1 hT.1 τ.isoFree c (τ.wt α) fun u => (hc u (h1 u.2) u.2).symm]
    simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos α) fun l _ => ?_
    simp_rw [mul_right_comm _ (y (algebraMap o S.R (S.proj T c l k.1)))]
    rw [← Finset.sum_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hy _)).trans (τ.le α hα t (h2 t.2) l)
  · have hN := S.N_ge
    have hr := S.r_pos
    have : NeZero S.N := ⟨by omega⟩
    have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    choose a ha hwa using (H p y τ).1
    obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨π, hπ⟩ := ThetaProj.exists_retraction T e
    have hfin : Finite (S.perp τ.yy.ker →+ ZMod S.N) := DFunLike.finite _
    set s := {c' : S.perp τ.yy.ker →+ ZMod S.N | c'.comp (AddSubgroup.inclusion h1) = c} with hs
    have hne : s.Nonempty := ⟨(c.comp π).comp (AddSubgroup.subtype _), by
      ext t
      exact congrArg c (hπ t)⟩
    obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image s
      (fun c' => τ.δ * Real.exp (-(τ.q (a c') / S.N))) (Set.toFinite _) hne
    refine ⟨a c₀, ha c₀, fun t h₁ h₂ => ?_, ?_⟩
    · rw [hwa, ← show _ = c from hc₀]
      rfl
    · refine norm_FF_le S y hy T c k hk (hpos _) fun t => ?_
      rw [href _ T h1 τ.isoFree hT c, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      simp_rw [Matrix.sum_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun c' hc' => ?_
      have ht : (t : S.Gam) ∈ τ.yy.ker := by
        rw [← hperp τ.yy.ker]
        exact τ.isoFree.1 (h1 t.2)
      have := τ.le (a c') (ha c') t ht k.1
      rw [hwa] at this
      exact this.trans (hmax c' ((Set.Finite.mem_toFinset _).mp hc'))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreForm

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_eq_of_id {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (h : Y' ⟶ Y)
    (H : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s h y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s' r z J = sval s (r ≫ h) z J := by
  have e := sval_comp_stalk s' (𝟙 Y') r z hJ
  rw [Category.comp_id] at e
  rw [e, sval_comp_stalk s h r z hJ, H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ))]

theorem under_iff_match {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) : Under U U₀ ↔ Match U U₀ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩⟩

theorem under_exists_and_expands : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  intro hL _ R _ _ I D A G _ _ hG
  refine ⟨fun U₀ => ?_, fun U => ?_, fun U U₀ hU k σ f σ₀ f₀ hσ hf => ?_⟩
  · obtain ⟨w, hw⟩ := U₀.ext
    obtain ⟨U, hU, -⟩ := GlobalTheory.ValueForm.exists_preU_match hL.globalFns R I D A G U₀ hG w hw
    exact ⟨U, (under_iff_match U U₀).2 hU⟩
  · obtain ⟨U₀, hU⟩ := GlobalTheory.UU.ToChart.exists_match R I D A G U
    exact ⟨U₀, (under_iff_match U U₀).2 hU⟩
  · have hM := (under_iff_match U U₀).1 hU
    have ht : H0 U₀.LG.L k = H0 U.P.L.L k := by rw [hM.LG]
    have hc : HEq (cast ht σ₀) σ₀ := cast_heq ht σ₀
    have sG : SameG (cast ht σ₀) σ := fun Z r z J hJ => sval_eq_of_id _ _ _ (hσ _ hc) Z r z J hJ
    have sB : SameB f₀ f := fun α Z r z J hJ => sval_eq_of_id _ _ _ (hf α) Z r z J hJ
    exact ⟨expandsAt_of_expT R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB,
      expT_of_expandsAt R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB⟩

end GlobalTheory.LN.PreForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem labelled_torsion_pull {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over B') {E : Over B}
    (U : Over.mk (T.hom ≫ f) ⟶ E) {Γ : Type} [Add Γ] (pt : Γ → (E ⟶ G)) (m : ℕ)
    (hadd : ∀ a b, pt (a + b) = pt a * pt b) (htors : ∀ a, pt a ^ m = 1)
    (hbij : ∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ m = 1 → ∃! a, U ≫ pt a = z) :
    ∃ x : Γ → (T ⟶ G'), (∀ a, (x a).left ≫ φ = U.left ≫ (pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧
      Function.Injective x ∧ ∀ z : T ⟶ G', z ^ m = 1 → ∃ a, z = x a := by
  have hinj : Function.Injective (pushHom h T) := fun x y e => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) e
    · rw [Over.w, Over.w]
  have hsurj : Function.Surjective (pushHom h T) := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  choose x hx using fun a => hsurj (U ≫ pt a)
  refine ⟨x, fun a => congrArg (fun z => z.left) (hx a), fun a b => hinj ?_, fun a b e => ?_, fun z hz => ?_⟩
  · rw [map_mul, hx, hx, hx, hadd, MonObj.comp_mul]
  · have ht : (U ≫ pt a) ^ m = 1 := by
      have := map_pow (preHom U) (pt a) m
      rw [htors, map_one] at this
      exact this.symm
    exact (hbij _ ht).unique rfl (by rw [← hx, ← hx, e])
  · obtain ⟨a, ha, -⟩ := hbij (pushHom h T z) (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj (by rw [hx, ha])⟩

theorem utest_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  intro o Ω _ _ _ S ρ p _ y₀ u
  have e : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull u.cart (TFK (R := u.V) (PadicAlgCl p))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK :) (by simp)) ρ.pt (S.r * S.N) ρ.pt_add
    (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (PadicAlgCl p) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.DualSection

theorem proj_mul_proj_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω]
    (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N) (hc : c.comp (AddSubgroup.inclusion h) ≠ c') :
    S.proj T c * S.proj T' c' = 0 := by
  haveI : IsDomain o := hA.inj.isDomain
  haveI := FreeNear.finite_char S T
  haveI := Fintype.ofFinite (T →+ ZMod S.N)
  rw [(thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 T T' h hT hT' c',
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
  refine Finset.sum_eq_zero fun c'' hc'' => ?_
  rw [(FreeNear.proj_orthogonal S T hT).1, if_neg]
  rintro rfl
  rw [Set.Finite.mem_toFinset] at hc''
  exact hc hc''

theorem mul_dotProduct_mem_of_mem_span {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    (O : Subalgebra o Ω) (a : Ω) (u : J → Ω) (V : Set (J → Ω)) (hV : ∀ v ∈ V, a * (u ⬝ᵥ v) ∈ O) :
    ∀ v ∈ Submodule.span O V, a * (u ⬝ᵥ v) ∈ O := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h' => exact hV _ h'
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, mul_add]; exact add_mem hx hy
  | smul s x _ hx =>
    rw [dotProduct_smul, Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 hx

theorem ff_div_th_mul_dotProduct_mem : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → ∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ EE hAdm hLL hT hS hG hW hB hE _ hEE ξ c k i
  have hO := hAdm.1
  have key : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z,
      S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
    intro z hz hI x₀ hx₀
    have hH : S.HH M ξ ≤ S.HH M z := AddSubgroup.closure_mono hI
    have hTT : S.TT M z ≤ S.TT M ξ := FirstIneq.perp_anti_of_le S hH
    rw [hEE z hz]
    refine mul_dotProduct_mem_of_mem_span _ _ _ _ ?_
    rintro _ ⟨c₁, k₁, x₁, i₁, hd, -, rfl⟩
    have e : S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ
        fun j => S.th x₁ / S.FF _ c₁ k₁ * algebraMap o Ω (S.proj _ c₁ j i₁)) =
        S.FF _ c k / S.FF _ c₁ k₁ * (S.th x₁ / S.th x₀) *
          algebraMap o Ω ((S.proj _ c * S.proj _ c₁) i i₁) := by
      simp only [dotProduct, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    by_cases hc : c.comp (AddSubgroup.inclusion hTT) = c₁
    swap
    · rw [proj_mul_proj_eq_zero S hTT (hG.1 ξ).1 (hG.1 z).1 c c₁ hc]
      simp
    refine mul_mem (mul_mem ?_ (hx₀.2 x₁)) (Subalgebra.algebraMap_mem _ _)
    have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c k)
    have hf' : S.FF _ c₁ k₁ ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c₁ k₁)
    have hi : (S.FF _ c₁ k₁)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c₁ k₁ (hG.1 z).1 hd.1
    refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
    · rw [div_eq_mul_inv]
      exact mul_mem hf hi
    intro p _ y hy
    obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
    have hker : S.HH M z = τ.yy.ker := (hS z p y y₀ τ hy hAt).2
    have hperp : S.perp τ.yy.ker = S.TT M z := by rw [← hker]; rfl
    obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c₁.comp (AddSubgroup.inclusion hperp.le))
    have h1 := (hB p y₀ τ hint (S.TT M ξ) c k (FirstIneq.ff_mem_ring S _ c k) (hG.1 ξ).1).1
      (hperp.le.trans hTT) (((hG.1 ξ).1.1.trans (hG.1 ξ).2.le).trans (hH.trans hker.le)) α hα
      (fun t h₁ h₂ => by rw [hwt, ← hc]; rfl)
    have h2 := hE z p y y₀ τ hy hAt c₁ k₁ α hd hα (fun t h₁ h₂ => by rw [hwt]; rfl)
    rw [hAt, ← h2] at h1
    set yg := gPt p ≫ y with hyg
    have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
    have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
    have e1 : M.val yg (S.FF _ c₁ k₁) * M.val yg (S.FF _ c₁ k₁)⁻¹ = 1 := by
      rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
        mul_inv_cancel₀ hd.1, RatModel.val_one]
    rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
      norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  intro z hI x₀ hx₀
  obtain ⟨U, b, hzU, -, hb⟩ := EE.loc z
  obtain ⟨x, hxU, hxc, hzx, hIx⟩ := hG.2.2.2 z U hzU
  rw [hb z hzU]
  refine mul_dotProduct_mem_of_mem_span _ _ _ _ fun v hv => RatModel.O_le_of_specializes hzx ?_
  refine key x hxc (hIx ▸ hI) x₀ (hIx ▸ hx₀) v ?_
  rw [hb x hxU]
  exact Submodule.subset_span hv

end GlobalTheory.ZH.DualSection
end

