import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
section
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodSBBil (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X →ₗ[ℂ] SB Y →ₗ[ℂ] SB (X × Y) :=
  LinearMap.mk₂ ℂ prodSB
    (fun f f' g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g g' => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp; ring)

def tensorToProd (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X ⊗[ℂ] SB Y →ₗ[ℂ] SB (X × Y) := TensorProduct.lift (prodSBBil X Y)

theorem tensorToProd_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) :
    tensorToProd X Y (f ⊗ₜ g) = prodSB f g := by
  simp [tensorToProd, prodSBBil]

theorem tensorToProd_injective (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB X)
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i n => b i ⊗ₜ n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ x y, ∑ i ∈ c.support, (b i).1 x * (c i).1 y = 0 := by
    intro x y
    have := congrArg (fun F : SB (X × Y) => F.1 (x, y)) ht
    simp only [ht', Finsupp.sum, map_sum, tensorToProd_tmul] at this
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hzero : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support (fun i => (c i).1 y)
        (by
          ext x
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
          rw [← hm x y]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
      simpa using hli
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat.CFac

theorem exists_linear_of_bilinear_prodSB : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  intro X Y _ _ M _ _ B
  let m := tensorToProd X Y
  let e := LinearEquiv.ofInjective m (tensorToProd_injective X Y)
  let l₀ : LinearMap.range m →ₗ[ℂ] M := (TensorProduct.lift B).comp e.symm.toLinearMap
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  refine ⟨l, fun f g => ?_⟩
  have hmem : prodSB f g = ((e (f ⊗ₜ g) : LinearMap.range m) : SB (X × Y)) := by
    simp [e, LinearEquiv.ofInjective_apply, m, tensorToProd_tmul]
  have := LinearMap.congr_fun hl (e (f ⊗ₜ g))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, l₀,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul] at this
  rw [hmem, this]

end GlobalTheory.LocFlat.CFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasFDerivAtOfContinuousCoordinatePartialsStatement
section
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials : ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) → (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) → ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  first | exact @GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | exact GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs | (intros; apply GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDualStatement
section
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_integral_of_addChar_trace_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ x : Matrix Y Y' k, (∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1) → ∀ r q, x r q ∈ 𝒪[k] := by
  first | exact @GlobalTheory.CharDualMat.integral_of_dual | exact GlobalTheory.CharDualMat.integral_of_dual | (intros; apply GlobalTheory.CharDualMat.integral_of_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PadicResidueFieldCardAndPrimeIrreducible
section
open ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.TAdicInt

def intEquiv (T : ℕ) [Fact T.Prime] : 𝒪[ℚ_[T]] ≃+* ℤ_[T] where
  toFun x := ⟨x.1, by
    have h := (Valuation.mem_integer_iff _ _).1 x.2
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.1 (by rw [map_one]; exact not_lt.2 h)
    rwa [norm_one, not_lt] at this⟩
  invFun x := ⟨x.1, (Valuation.mem_integer_iff _ _).2 (by
    have := (GlobalTheory.SplitWeil.padic_valuation_lt_iff T 1 x.1).not.2 (by rw [norm_one]; exact not_lt.2 x.2)
    rwa [map_one, not_lt] at this)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem card_residueField (T : ℕ) [Fact T.Prime] : Nat.card (ResidueField 𝒪[ℚ_[T]]) = T := by
  rw [Nat.card_congr ((ResidueField.mapEquiv (intEquiv T)).trans PadicInt.residueField).toEquiv, Nat.card_zmod]

theorem irreducible_natCast (T : ℕ) [Fact T.Prime] : Irreducible (T : 𝒪[ℚ_[T]]) := by
  have := (PadicInt.irreducible_p (p := T)).map (intEquiv T).symm.toMulEquiv
  rwa [show (intEquiv T).symm.toMulEquiv (T : ℤ_[T]) = (T : 𝒪[ℚ_[T]]) from
    map_natCast (intEquiv T).symm T] at this

theorem card_residueField_and_irreducible :
    ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧
      Irreducible ((T : 𝒪[ℚ_[T]])) :=
  fun T _ => ⟨card_residueField T, irreducible_natCast T⟩

end GlobalTheory.TAdicInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivs
section
open scoped ContDiff Topology

namespace GlobalTheory

theorem contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by
  intro E _ _ A _ v c hc P hP
  have key : ∀ φ, P φ → Differentiable ℝ φ ∧ ∃ (α χ : A → E → ℂ), (∀ a, ContDiff ℝ ∞ (α a)) ∧
      (∀ a, P (χ a)) ∧ fderiv ℝ φ =
        fun y => ∑ a, (α a y * φ y + χ a y) • ((c a).smulRight (1 : ℂ)) := by
    intro φ hφ
    obtain ⟨g, hg, hlim, hd⟩ := hP φ hφ
    choose α hα χ hχ hlim' using hd
    have h := GlobalTheory.T.differentiableAt_limit_of_directional_derivs_converge v c hc φ g (fun a y => α a y * φ y + χ a y) hg hlim hlim'
    refine ⟨fun y => (h y).1, α, χ, hα, hχ, ?_⟩
    funext y
    ext x
    conv_lhs => rw [← hc x]
    simp only [map_sum, map_smul, (h y).2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  have main : ∀ n : ℕ, ∀ φ, P φ → ContDiff ℝ n φ := by
    intro n
    induction n with
    | zero =>
      intro φ hφ
      simpa using (key φ hφ).1.continuous
    | succ n ih =>
      intro φ hφ
      obtain ⟨hd, α, χ, hα, hχ, hf⟩ := key φ hφ
      have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) φ := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨hd, by simp, ?_⟩
        rw [hf]
        refine ContDiff.sum fun a _ => ?_
        have h1 : ContDiff ℝ n (α a) := (hα a).of_le (by exact_mod_cast le_top)
        exact ((h1.mul (ih φ hφ)).add (ih _ (hχ a))).smul contDiff_const
      exact_mod_cast this
  intro φ hφ
  exact contDiff_infty.2 fun n => main n φ hφ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
section
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

open Filter Topology

noncomputable section
namespace GlobalTheory.LocFlat.CFac.Span

theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem indicator_one_mem_SB {Z : Type} [TopologicalSpace Z] {W : Set Z} (hc : IsCompact W)
    (hW : IsClopen W) : W.indicator (1 : Z → ℂ) ∈ SB Z :=
  ⟨isLocallyConstant_indicator_one hW, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩

def S (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Submodule ℂ (X × Y → ℂ) :=
  Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodFn q.1.1 q.2.1)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def IsBox (r : Set X × Set Y) : Prop := IsCompact r.1 ∧ IsClopen r.1 ∧ IsCompact r.2 ∧ IsClopen r.2

theorem IsBox.inter {r s : Set X × Set Y} (hr : IsBox r) (hs : IsBox s) :
    IsBox (r.1 ∩ s.1, r.2 ∩ s.2) :=
  ⟨hr.1.inter_right hs.2.1.isClosed, hr.2.1.inter hs.2.1, hr.2.2.1.inter_right hs.2.2.2.isClosed,
    hr.2.2.2.inter hs.2.2.2⟩

theorem box_mem {r : Set X × Set Y} (hr : IsBox r) :
    (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  have : (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) = prodFn (r.1.indicator 1) (r.2.indicator 1) := by
    ext ⟨x, y⟩
    by_cases hx : x ∈ r.1 <;> by_cases hy : y ∈ r.2 <;> simp [prodFn, Set.indicator, hx, hy]
  rw [this]
  exact Submodule.subset_span ⟨(⟨_, indicator_one_mem_SB hr.1 hr.2.1⟩,
    ⟨_, indicator_one_mem_SB hr.2.2.1 hr.2.2.2⟩), rfl⟩

def U (L : List (Set X × Set Y)) : Set (X × Y) := ⋃ r ∈ L, r.1 ×ˢ r.2

theorem U_cons (r : Set X × Set Y) (L : List (Set X × Set Y)) : U (r :: L) = r.1 ×ˢ r.2 ∪ U L := by
  simp [U]

theorem inter_U (r : Set X × Set Y) (L : List (Set X × Set Y)) :
    r.1 ×ˢ r.2 ∩ U L = U (L.map fun s => (r.1 ∩ s.1, r.2 ∩ s.2)) := by
  ext p
  simp only [U, Set.mem_inter_iff, Set.mem_iUnion, List.mem_map, Set.mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, s, hs, h3, h4⟩
    exact ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨h1, h2⟩, s, hs, h3, h4⟩

theorem U_mem : ∀ (n : ℕ) (L : List (Set X × Set Y)), L.length ≤ n → (∀ r ∈ L, IsBox r) →
    (U L).indicator (1 : X × Y → ℂ) ∈ S X Y := by
  intro n
  induction n with
  | zero =>
    intro L hL _
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]
    simp [U]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro L hL hB
    cases L with
    | nil => simp [U]; exact Submodule.zero_mem _
    | cons r L =>
      have key := Set.indicator_union_add_inter (f := (1 : X × Y → ℂ)) (r.1 ×ˢ r.2) (U L)
      have hL' : L.length ≤ n := by simp at hL; omega
      rw [U_cons, eq_sub_of_add_eq key, inter_U]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (box_mem (hB r (by simp)))
        (ih L hL' fun s hs => hB s (by simp [hs]))) (ih _ (by simpa using hL') ?_)
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      exact (hB r (by simp)).inter (hB t (by simp [ht]))

theorem F_mem (F : X × Y → ℂ) : ∀ L : List (Set X × Set Y),
    (∀ r ∈ L, IsBox r ∧ ∃ c : ℂ, ∀ p ∈ r.1 ×ˢ r.2, F p = c) → (U L).indicator F ∈ S X Y := by
  intro L
  induction L with
  | nil => intro _; simp [U]; exact Submodule.zero_mem _
  | cons r L ih =>
    intro hL
    obtain ⟨hB, c, hc⟩ := hL r (by simp)
    have key := Set.indicator_union_add_inter (f := F) (r.1 ×ˢ r.2) (U L)
    have hA : (r.1 ×ˢ r.2).indicator F = c • (r.1 ×ˢ r.2).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    have hI : (r.1 ×ˢ r.2 ∩ U L).indicator F = c • (r.1 ×ˢ r.2 ∩ U L).indicator (1 : X × Y → ℂ) := by
      ext p
      simp only [Pi.smul_apply]
      by_cases hp : p ∈ r.1 ×ˢ r.2 ∩ U L
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp [hc p hp.1]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
    rw [U_cons, eq_sub_of_add_eq key, hA, hI, inter_U]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ c (box_mem hB))
      (ih fun s hs => hL s (by simp [hs]))) (Submodule.smul_mem _ c (U_mem _ _ le_rfl ?_))
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hB.inter (hL t (by simp [ht])).1

theorem exists_compact_clopen [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hO hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).isOpen_iff.1
    isOpen_interior x hxK
  exact ⟨V, hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), hV, hxV,
    (hVK.trans interior_subset).trans hKO⟩

theorem mem_S [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    (F : X × Y → ℂ) (hF : F ∈ SB (X × Y)) : F ∈ S X Y := by
  have hbox : ∀ p : X × Y, ∃ r : Set X × Set Y, IsBox r ∧ p ∈ r.1 ×ˢ r.2 ∧
      ∀ q ∈ r.1 ×ˢ r.2, F q = F p := by
    intro p
    have hO : IsOpen {q | F q = F p} := hF.1.isOpen_fiber _
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ := isOpen_prod_iff.1 hO p.1 p.2 rfl
    obtain ⟨U₁, hU1, hU2, hU3, hU4⟩ := exists_compact_clopen hu hpu
    obtain ⟨V₁, hV1, hV2, hV3, hV4⟩ := exists_compact_clopen hv hpv
    exact ⟨(U₁, V₁), ⟨hU1, hU2, hV1, hV2⟩, ⟨hU3, hV3⟩, fun q hq => huv (Set.prod_mono hU4 hV4 hq)⟩
  choose R hRb hRp hRc using hbox
  obtain ⟨t, -, ht⟩ := hF.2.isCompact.elim_nhds_subcover (fun p => (R p).1 ×ˢ (R p).2)
    fun p _ => ((hRb p).2.1.isOpen.prod (hRb p).2.2.2.isOpen).mem_nhds (hRp p)
  have hsub : tsupport F ⊆ U (t.toList.map R) := by
    intro q hq
    have := ht hq
    simp only [Set.mem_iUnion] at this
    obtain ⟨p, hp, hq'⟩ := this
    simp only [U, Set.mem_iUnion]
    exact ⟨R p, List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, hq'⟩
  have heq : (U (t.toList.map R)).indicator F = F :=
    Set.indicator_eq_self.2 ((subset_tsupport F).trans hsub)
  rw [← heq]
  refine F_mem F _ ?_
  intro r hr
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
  exact ⟨hRb p, F p, hRc p⟩

theorem span_prodSB_eq_top : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y],
    Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2) = ⊤ := by
  intro X Y _ _ _ _ _ _ _ _
  have hmap : (Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodSB q.1 q.2)).map
      (SB (X × Y)).subtype = S X Y := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  rintro F -
  have h := mem_S F.1 F.2
  rw [← hmap] at h
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 h
  have : G = F := Subtype.ext hGF
  rwa [← this]

end GlobalTheory.LocFlat.CFac.Span
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBoundedStatement
section
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
end

