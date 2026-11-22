import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBound
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace MinorTest

theorem exists_norm_between {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : ∃ x : C, a < ‖x‖ ∧ ‖x‖ < b := by
  have hb : 0 < b := ha.trans_lt hab
  have hr : a / b < 1 := (div_lt_one hb).2 hab
  have hr0 : 0 ≤ a / b := div_nonneg ha hb.le
  obtain ⟨z, hz1, hz2⟩ : ∃ z : C, a / b < ‖z‖ ∧ ‖z‖ < 1 := by
    obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one C
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).eventually_lt_const hy0
    obtain ⟨n, hn, hn1⟩ := (h.and (Filter.eventually_gt_atTop 0)).exists
    obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y hn1
    rw [norm_pow] at hn hy1
    exact ⟨x, lt_of_pow_lt_pow_left₀ n (norm_nonneg x) hn,
      (pow_lt_one_iff_of_nonneg (norm_nonneg x) hn1.ne').1 hy1⟩
  have hz0 : 0 < ‖z‖ := hr0.trans_lt hz1
  have hy : 1 < ‖z‖⁻¹ := (one_lt_inv₀ hz0).2 hz2
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow hb hy
  refine ⟨z⁻¹ ^ n, ?_, ?_⟩
  · rw [norm_zpow, norm_inv]
    rw [zpow_add_one₀ (inv_pos.2 hz0).ne', ← div_eq_mul_inv, le_div_iff₀ hz0] at h2
    rw [div_lt_iff₀ hb, mul_comm] at hz1
    exact hz1.trans_le h2
  · rwa [norm_zpow, norm_inv]

theorem norm_det_le_pow {C J : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J] [DecidableEq J]
    (A : Matrix J J C) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ i j, ‖A i j‖ ≤ ρ) :
    ‖A.det‖ ≤ ρ ^ Fintype.card J := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, _root_.one_mul, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => h _ _

theorem norm_det_le_of_comb {C J I : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J]
    [DecidableEq J] [Fintype I] (g : I → J → C) (c : J → I → C) (hc : ∀ i m, ‖c i m‖ ≤ 1) {ν : ℝ}
    (hν : 0 ≤ ν) (h : ∀ k : J → I, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν) :
    ‖Matrix.det (Matrix.of fun i => ∑ m, c i m • g m)‖ ≤ ν := by
  have e : Matrix.det (Matrix.of fun i => ∑ m, c i m • g m) =
      ∑ k : J → I, (∏ i, c i (k i)) • Matrix.det (Matrix.of fun i j => g (k i) j) := by
    have := (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_sum
      (fun i m => c i m • g m)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_smul_univ
      (fun i => c i (k i)) (fun i => g (k i))
  rw [e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hν fun k _ => ?_
  rw [smul_eq_mul, norm_mul, norm_prod]
  calc _ ≤ 1 * ν := mul_le_mul (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hc _ _) (h k)
        (norm_nonneg _) zero_le_one
    _ = ν := _root_.one_mul _

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) {x : X} (hx0 : x ≠ 0) : 0 < q x := by
  by_contra hx
  push_neg at hx
  have hfin : {v | ¬ (0 : ℝ) < q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_gt_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_nonpos_of_nonneg_of_nonpos ?_ hx
  positivity

theorem exists_eStd_eq (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  let ψ : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n := φ.toZModLinearMap n
  refine ⟨Sum.elim (fun i => φ (Pi.single (.inr i) 1)) (fun i => -φ (Pi.single (.inl i) 1)), fun b => ?_⟩
  have hb : φ b = ∑ s, b s * φ (Pi.single s 1) := by
    change ψ b = ∑ s, b s * ψ (Pi.single s 1)
    conv_lhs => rw [pi_eq_sum_univ' b]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hb, Fintype.sum_sum_type, ← Finset.sum_add_distrib, eStd]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem subsingleton_of_perp_eq_bot (τ : S.Test p y₀) (h : S.perp τ.yy.ker = ⊥) (x : τ.X) : x = 0 := by
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  haveI : Fact (1 < S.r * S.N) := ⟨h2⟩
  let b := Module.Free.chooseBasis ℤ τ.X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ τ.X) := by
    refine ⟨fun i => ?_⟩
    let f : τ.X →+ ZMod (S.r * S.N) := (Int.castAddHom _).comp (b.coord i).toAddMonoidHom
    let f' : τ.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : τ.X →+ τ.X).range →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ f (by
        rintro _ ⟨v, rfl⟩
        rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, map_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq _ _ (f'.comp τ.yy)
    have hm : a ∈ S.perp τ.yy.ker := fun u hu => by
      rw [ha, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hu, map_zero]
    rw [h, AddSubgroup.mem_bot] at hm
    obtain ⟨u, hu⟩ := τ.yy_onto (QuotientAddGroup.mk (b i))
    have := ha u
    rw [hm, AddMonoidHom.comp_apply, hu] at this
    simp [eStd, f', f] at this
  exact b.repr.injective (Subsingleton.elim _ _)

theorem eq_bot_of_char {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (h : ∀ c : T →+ ZMod S.N, c = 0) :
    T = ⊥ := by
  obtain ⟨-, d, ⟨e⟩⟩ := hT
  haveI : Fact (1 < S.N) := ⟨S.N_ge⟩
  haveI : IsEmpty (Fin d) := by
    refine ⟨fun i => ?_⟩
    have := DFunLike.congr_fun (h ((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
      ((Pi.evalAddMonoidHom (fun _ : Fin d => ZMod (S.r * S.N)) i).comp e.toAddMonoidHom)))
      (e.symm (fun _ => 1))
    simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      AddEquiv.apply_symm_apply, Pi.evalAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, map_one,
      AddMonoidHom.zero_apply] at this
    exact one_ne_zero this
  rw [eq_bot_iff]
  intro t ht
  have : (⟨t, ht⟩ : T) = 0 := e.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val this

end MinorTest
open MinorTest in

theorem minors_dual_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  intro o Ω _ _ _ _ S p _ y₀ τ hint _ n ρ₀ g hρ hg
  obtain ⟨B, l, α, -, hdet, -, hl, hall, -, hE⟩ := exists_adapted_basis_testLattice o Ω S p y₀ τ hint
  have hN : (0 : ℝ) < S.N := by exact_mod_cast lt_of_lt_of_le two_pos S.N_ge
  have hq : ∀ x, 0 ≤ τ.q x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (pos_of_tendsto τ.q τ.pos hx).le
  have hl1 : ∀ i, 1 ≤ ‖l i‖ := fun i => by
    rw [hl]; exact Real.one_le_exp (div_nonneg (hq _) hN.le)
  set M : Matrix S.J S.J (PadicAlgCl p) := Matrix.of fun i j => l i * B i j with hM
  have hMdet : ‖M.det‖ = ∏ i, ‖l i‖ := by
    rw [hM, Matrix.det_mul_column, norm_mul, hdet, _root_.mul_one, norm_prod]
  have hM1 : 1 ≤ ‖M.det‖ := by
    rw [hMdet]; exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
  have key : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ * ‖M.det‖ ≤ ρ₀ ^ Fintype.card S.J := fun k => by
    rw [← Matrix.det_transpose M, ← norm_mul, ← Matrix.det_mul]
    refine norm_det_le_pow _ hρ.le fun i j => ?_
    exact (hg (g (k i))).1 (Submodule.subset_span ⟨_, rfl⟩) (fun t => l j * B j t)
      (hE ▸ Submodule.subset_span ⟨j, rfl⟩)
  have h1 : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J := fun k =>
    (le_mul_of_one_le_right (norm_nonneg _) hM1).trans (key k)
  have hρd : 0 < ρ₀ ^ Fintype.card S.J := pow_pos hρ _
  refine ⟨h1, ⟨?_, fun hbot => ?_⟩⟩
  · rintro ⟨k, hk⟩
    have h2 := key k
    rw [hk, mul_le_iff_le_one_right hρd, hMdet] at h2
    refine eq_bot_of_char τ.isoFree fun c => ?_
    obtain ⟨i, rfl⟩ := hall c
    have h3 : ‖l i‖ ≤ 1 := by
      refine le_trans ?_ h2
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      refine le_mul_of_one_le_right (norm_nonneg _) ?_
      exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
    have h4 : α i = 0 := by
      by_contra hne
      have := Real.one_lt_exp_iff.2 (div_pos (pos_of_tendsto τ.q τ.pos hne) hN)
      rw [hl] at h3
      linarith
    rw [h4, map_zero]
  · have hMe : ‖M.det‖ = 1 := by
      rw [hMdet]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hl, subsingleton_of_perp_eq_bot τ hbot (α i)]
      simp
    have hMu : IsUnit M.det := by
      rw [isUnit_iff_ne_zero, ← norm_ne_zero_iff, hMe]; exact one_ne_zero
    by_contra hne
    push_neg at hne
    obtain ⟨ν, hν0, hν1, hν2⟩ : ∃ ν : ℝ, 0 ≤ ν ∧ ν < ρ₀ ^ Fintype.card S.J ∧
        ∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν := by
      rcases isEmpty_or_nonempty (S.J → Fin n) with he | he
      · exact ⟨0, le_rfl, hρd, fun k => he.elim k⟩
      · obtain ⟨k₀, hk₀⟩ := Finite.exists_max
          fun k : S.J → Fin n => ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖
        exact ⟨_, norm_nonneg _, lt_of_le_of_ne (h1 k₀) (hne k₀), hk₀⟩
    obtain ⟨x, hx1, hx2⟩ := exists_norm_between (C := PadicAlgCl p) hν0 hν1
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x (Fintype.card_pos (α := S.J))
    have hz : ‖z‖ ≤ ρ₀ := by
      rw [norm_pow] at hx2
      exact (lt_of_pow_lt_pow_left₀ _ hρ.le hx2).le
    set W : Matrix S.J S.J (PadicAlgCl p) := z • (M.transpose)⁻¹ with hW
    have hWM : W * M.transpose = z • (1 : Matrix S.J S.J (PadicAlgCl p)) := by
      rw [hW, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose])]
    have hWdet : ‖W.det‖ = ‖z ^ Fintype.card S.J‖ := by
      have := congrArg (fun A => ‖Matrix.det A‖) hWM
      simpa only [Matrix.det_mul, Matrix.det_transpose, norm_mul, hMe, _root_.mul_one, Matrix.det_smul,
        Matrix.det_one] using this
    have hmem : ∀ i, W i ∈ Submodule.span (OO p) (Set.range g) := fun i => by
      rw [hg, hE]
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have : W i ⬝ᵥ (fun t => l j * B j t) = (W * M.transpose) i j := rfl
        rw [this, hWM, Matrix.smul_apply, Matrix.one_apply]
        split_ifs
        · simpa using hz
        · simpa using hρ.le
      | zero => simpa using hρ.le
      | add u v _ _ hu hv =>
        rw [dotProduct_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
      | smul a v _ hv =>
        have : a • v = (a : PadicAlgCl p) • v := rfl
        rw [this, dotProduct_smul, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 a.2)).trans hv
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem i)
    have h5 := norm_det_le_of_comb g (fun i m => (c i m : PadicAlgCl p))
      (fun i m => (mem_OO_iff _).1 (c i m).2) hν0 hν2
    have h6 : (Matrix.of fun i => ∑ m, (c i m : PadicAlgCl p) • g m) = W := by
      ext i j
      exact congrFun (hc i) j
    rw [h6, hWdet] at h5
    linarith
end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PointDescendsToValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_range_of_dominating {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {W C : Type} [CommRing W]
    [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C) (hα : IsLocalHom α)
    (hβ : Function.Injective β) (hc : β.comp α = ga.comp (algebraMap V (FractionRing V)))
    (a : FractionRing V) (w : W) (h : β w = ga a) : a ∈ (algebraMap V (FractionRing V)).range := by
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, hv⟩
  · by_cases ha : a = 0
    · exact ha ▸ Subring.zero_mem _
    have h1 : β (α v) = ga a⁻¹ := by rw [← hv]; exact congrArg (· v) (congrArg DFunLike.coe hc)
    have h2 : α v * w = 1 := hβ (by rw [map_mul, h1, h, ← map_mul, inv_mul_cancel₀ ha, map_one, map_one])
    obtain ⟨u, rfl⟩ := hα.map_nonunit v (IsUnit.of_mul_eq_one _ h2)
    refine ⟨(u⁻¹ : Vˣ), ?_⟩
    rw [← inv_inv a, ← hv]
    exact map_units_inv _ u

theorem point_descends_to_valuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  intro V _ _ _ W C _ _ _ α β ga hα hβ hc X y x hxy
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (IsLocalRing.closedPoint W)) trivial
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of W) y hp).ge
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    intro p _
    have h1 : (spMap β ≫ y) (IsLocalRing.closedPoint C) ∈ U := hy (x := spMap β _) trivial
    rw [hxy] at h1
    obtain rfl : p = spMap ga (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) _ _
    exact h1
  have key : ∀ f, β (valR y U f) = ga (valR x U f) := fun f => by
    rw [← HolHom.valR_spMap β y U hy, ← HolHom.valR_spMap ga x U hx, hxy]
  have hinj := IsFractionRing.injective V (FractionRing V)
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((HolHom.evalHom x U hx).codRestrict _ fun f =>
    mem_range_of_dominating α β ga hα hβ hc _ _ ((key f).trans (by rw [HolHom.valR_eq _ _ hx])))
  have hφ : ∀ f, algebraMap V (FractionRing V) (φ f) = valR x U f := fun f => by
    rw [HolHom.valR_eq _ _ hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let h : Sp V ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hh : ⊤ ≤ h ⁻¹ᵁ U := fun p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR h U f = φ f := fun f => by
    rw [HolHom.valR_eq _ _ hh]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom φ) hh)
  refine ⟨h, HolHom.point_ext hU (fun p _ => hh (x := spMap α p) trivial) hy fun f => ?_,
    HolHom.point_ext hU (fun p _ => hh (x := jK V p) trivial) hx fun f => ?_⟩
  · rw [HolHom.valR_spMap _ _ _ hh, hval]
    refine hβ ?_
    rw [key, ← hφ]
    exact congrArg (· (φ f)) (congrArg DFunLike.coe hc)
  · exact (HolHom.valR_spMap (algebraMap V (FractionRing V)) _ _ hh f).trans (by rw [hval, hφ])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenDescendBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}

theorem inv_comp_of_isGrpPullback (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) :
    (ι[D'.P.A]).left ≫ β = β ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom gp D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ β) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem val_sym_comp (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hv₀ : v.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ β) z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := by
  have he : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hv₀) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw v (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw v (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ β)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => β ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ β) ^ (1 : ℤ) * k (𝟙 _ ≫ β) ^ (-1 : ℤ) =
        k (β ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (β ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_comp_of_isGrpPullback gp, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen β) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (spMap φ)
      rw [val_pull hI, val_one, ← he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

theorem psiEven_descend : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  intro hG R V _ _ _ _ φ D D' β v xe gp hv hc gam hgam hψ h χ
  obtain ⟨x, rfl⟩ := xe.surjective χ
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  have cx : ∀ a, D'.xK a ≫ β = gam ≫ D.xK (xe a) := fun a => by
    show (jK V ≫ (D'.c a).left) ≫ β = gam ≫ jK R ≫ (D.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  refine TauPull.corr_of_dense D.P.isLB gam z (fun U ⟨y, hy⟩ => Subsingleton.elim y (gam z) ▸ hy) fun J hJ => ?_
  choose J' hJ₀ using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have hJ' : Good D'.P.L z J' := hJ₀
  have vψ : ∀ a, val (D.psi (xe a)) gam z J =
      (gw v (D'.xK a) z (J (D'.xK a ≫ β)) (J' (D'.xK a)))⁻¹ * val (D'.psi a) (𝟙 _) z J' := fun a => by
    have := CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ hJ'
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have e := val_corr hJ' (h x) (𝟙 _)
  rw [val_mul hJ', val_pull hJ', Category.id_comp] at e
  rw [val_mul hJ, val_pull hJ, ← map_neg, vψ, vψ, ← cx, val_sym_comp hG gp hv _ z hJ hJ', ← cn]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PsiRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarEqExpansionCoefRatio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRatio

theorem exists_cstHom {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    ∃ φ : F →+* Z.presheaf.stalk z, (∀ c, cst p z c = φ c) ∧ ∀ c, gs (𝟙 _) z ⊤ (scal p c) = φ c := by
  refine ⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩
  exact gs_eq (𝟙 _) z ⊤ trivial _

theorem cst_eq_scal {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    cst p z c = gs (𝟙 _) z ⊤ (scal p c) := by
  obtain ⟨φ, h₁, h₂⟩ := exists_cstHom p z
  rw [h₁, h₂]

end GlobalTheory.PsiRatio

namespace GlobalTheory

theorem psiScal_eq_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  intro R _ _ D ga a f th hS hR hN χ q p hq hp
  let B : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let T : Over (Spec (CommRingCat.of R)) := TK R ⊗ B
  let pt : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨z₀, hz₀, hth⟩ := hN (jK R pt)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm
  let z' : T.left := z
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z'
  let x : T ⟶ D.P.A := snd (TK R) B ≫ snd _ _
  have ex : lift (toUnit T) x = snd (TK R) B := by
    ext1
    · exact toUnit_unique _ _
    · exact lift_snd _ _
  have ey : x * (cT D T χ)⁻¹ * cT D T χ = x := inv_mul_cancel_right _ _
  have hu : IsUnit (sval th (snd (TK R) B).left z' J) := by
    refine (MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_
    have : (snd (TK R) B).left z' = z₀ := hz
    rw [this]
    exact hth
  have e₁ := hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ
  have e₂ := (hS χ).2 T (fst (TK R) B) z' J hJ
  have e₃ := hq _ (snd (TK R) B).left z' J hJ
  have e₄ := hp T (x * (cT D T χ)⁻¹) z' J hJ
  rw [ey, ex] at e₁ e₄
  have e' : T.hom = (fst (TK R) B).left ≫ jK R := (Over.w (fst (TK R) B)).symm
  have e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R := (Over.w (snd (TK R) B)).trans e'
  obtain ⟨φ, -, hφ⟩ := PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'
  have hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c) := fun c =>
    (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))
  have c₃ := (congrArg (fun s => cst s z' q) e'').trans (hc q)
  have c₄ := (congrArg (fun s => cst s z' p) e').trans (hc p)
  have alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t →
      s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) →
      cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp' := by
    intro A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₅ h₆ h₇
    refine (((g * r).isUnit.mul ht).mul_left_inj).1 ?_
    rw [← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]
    ring
  apply φ.injective
  rw [map_mul]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTestStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.thetaSystem_norm_weightSum_le_exp_of_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  first | exact @GlobalTheory.thetaSys_norm_FF_le_exp | exact GlobalTheory.thetaSys_norm_FF_le_exp | (intros; apply GlobalTheory.thetaSys_norm_FF_le_exp <;> assumption)
end

