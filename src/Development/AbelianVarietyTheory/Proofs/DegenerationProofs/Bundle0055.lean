import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsOfForallValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_vecMul_inv {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {c : Matrix J J Ω} (hc : c.det ≠ 0) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range c) ↔ ∀ j, Matrix.vecMul v c⁻¹ j ∈ S := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have key : ∀ a : J → S, ∑ i, a i • c i = Matrix.vecMul (fun i => (a i : Ω)) c := fun a => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun S (v := fun i => c i)).trans ?_
  constructor
  · rintro ⟨a, rfl⟩ j
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (a j).2
  · intro h
    refine ⟨fun j => ⟨_, h j⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v c⁻¹) c = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
  {J : Type} [Fintype J] [DecidableEq J]

theorem mem_span_rows_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {c : Matrix J J Ω} (hc : c.det ≠ 0) (x : M.Z) (v : J → Ω)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) → v ∈ Submodule.span (M.O ξ) (Set.range c)) :
    v ∈ Submodule.span (M.O x) (Set.range c) :=
  (mem_span_rows_iff_vecMul_inv _ hc v).2 fun j => M.mem_O_of_forall_valuationRing hn x _ fun ξ hξ hv =>
    (mem_span_rows_iff_vecMul_inv _ hc v).1 (h ξ hξ hv) j

theorem span_rows_eq_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {b c : Matrix J J Ω} (hb : b.det ≠ 0) (hc : c.det ≠ 0) (x : M.Z)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range b) = Submodule.span (M.O ξ) (Set.range c)) :
    Submodule.span (M.O x) (Set.range b) = Submodule.span (M.O x) (Set.range c) :=
  le_antisymm
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hc x v fun ξ hξ hr =>
      (h ξ hξ hr).le (Submodule.subset_span hv))
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hb x v fun ξ hξ hr =>
      (h ξ hξ hr).ge (Submodule.subset_span hv))

end RatModel

theorem exists_lat_of_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
      [JacobsonSpace M.Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (J : Type) [Fintype J] [DecidableEq J]
      (b : M.Z → Matrix J J Ω) (D : ∀ ξ : M.Z, Submodule (M.O ξ) (J → Ω)), (∀ z, (b z).det ≠ 0) →
      (∀ z, IsClosed ({z} : Set M.Z) → ∃ W : M.Z.Opens, z ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
        Submodule.span (M.O ξ) (Set.range (b z)) = D ξ) →
      ∃ EE : M.Lat J, (∀ z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) (Set.range (b z))) ∧
        ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
          (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
          ∀ x ∈ W, EE.E x = Submodule.span (M.O x) (Set.range c) := by
  intro o Ω _ _ _ M _ _ hn J _ _ b D hb h
  have hx : ∀ x : M.Z, ∃ (z : M.Z) (W : M.Z.Opens), x ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range (b z)) = D ξ := fun x => by
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.Z))
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨W, hzW, hW⟩ := h z hzc
    exact ⟨z, W, (specializes_iff_mem_closure.2 hz).mem_open W.isOpen hzW, hW⟩
  choose g U hU hg using hx
  have main : ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
      (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
      ∀ x ∈ W, Submodule.span (M.O x) (Set.range (b (g x))) = Submodule.span (M.O x) (Set.range c) :=
    fun W c hc hW x hx => M.span_rows_eq_of_forall_valuationRing hn (hb _) hc x fun ξ hξ hr =>
      (hg x ξ (hξ.mem_open (U x).isOpen (hU x)) hr).trans (hW ξ (hξ.mem_open W.isOpen hx) hr)
  refine ⟨⟨fun x => Submodule.span (M.O x) (Set.range (b (g x))), fun x => ⟨U x, b (g x), hU x, hb _,
    main _ _ (hb _) fun ξ hξ hr => (hg x ξ hξ hr).symm⟩⟩, fun z hz => ?_, main⟩
  obtain ⟨W, hzW, hW⟩ := h z hz
  exact main W _ (hb z) (fun ξ hξ hr => (hW ξ hξ hr).symm) z hzW

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.mem_supI_iff_and_HH_eq_ker :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) := by
  intro o Ω _ _ _ _ S M U₀ hO z p _ y y₀ τ hC hA
  have hw : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
    RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))
  have hξ : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hC.2 ⟨_, rfl⟩
  have hsp := RatModel.specializes_of_range_eq hw
  have hthO : ∀ j, S.th j ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j => RatModel.ringOn_le_O hξ (hO.le (S.th_mem j))
  have hinvO : ∀ j, S.th j ≠ 0 →
      (S.th j)⁻¹ ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j hj => RatModel.ringOn_le_O hξ (hO.th_unit j hj)
  have hmul : ∀ i j, S.th i ≠ 0 → M.val (gPt p ≫ y) (S.th j) =
      M.val (gPt p ≫ y) (S.th j / S.th i) * M.val (gPt p ≫ y) (S.th i) := by
    intro i j hi
    have hq : S.th j / S.th i ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
      rw [div_eq_mul_inv]; exact mul_mem (hthO j) (hinvO i hi)
    rw [← RatModel.val_mul hsp hq (hthO i), div_mul_cancel₀ _ hi]
  have hval : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = ‖M.val (gPt p ≫ y) (S.th x)‖ := fun x => by rw [hA]
  have hmax : IsGreatest (Set.range fun x => ‖M.val (gPt p ≫ y) (S.th x)‖) τ.δ := by
    simpa only [hval] using τ.δ_max
  have fwd : ∀ x, M.Div S.th x z → ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x hx
    apply le_antisymm (hmax.2 ⟨x, rfl⟩)
    obtain ⟨j, hj⟩ := hmax.1
    rw [← hj]
    dsimp only
    rw [hmul x j hx.1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.Cen.norm_val_le_one hC (hx.2 j))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    refine ⟨fun h => fwd x h, fun hx => ?_⟩
    obtain ⟨i, hi⟩ := hO.div z
    have h1 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ = 1 := by
      rw [hmul i x hi.1, norm_mul, fwd i hi] at hx
      have h2 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ * τ.δ = 1 * τ.δ := by rw [_root_.one_mul]; exact hx
      exact (mul_left_inj' τ.δ_pos.ne').mp h2
    show M.Div S.th x z
    exact (RatModel.Div.div_iff_isUnit hi x).mpr ((RatModel.norm_val_eq_one_iff hC.1 (hi.2 x)).mp h1)
  refine ⟨key, ?_⟩
  rw [← τ.supp]
  show AddSubgroup.closure (S.supI M z) = _
  congr 1
  ext x
  rw [key x, Set.mem_ofPred_eq, hval]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

theorem quadraticMap_nonneg_of_tendsto_cofinite {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (q : QuadraticMap ℤ X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hneg
  push_neg at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hneg
  have hinj : Function.Injective (fun n : ℤ => n • x) := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨n, hn⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  nlinarith [mul_self_nonneg (n : ℝ)]

namespace RatModel
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem dotProduct_div_mem_O {J : Type} [Fintype J] {a₀ : M.Z} {v e : J → Ω} {t : Ω}
    (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) : (v ⬝ᵥ e) / t ∈ M.O a₀ := by
  rw [div_eq_mul_inv]
  exact mul_mem (sum_mem fun j _ => mul_mem (hv j) (he j)) ht

theorem val_dotProduct_div {K : Type} [Field K] {y : Sp K ⟶ M.Z} {a₀ : M.Z} (h : ∀ w, y w ⤳ a₀)
    {J : Type} [Fintype J] {v e : J → Ω} {t : Ω} (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀)
    (ht0 : t ≠ 0) (ht' : t ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) :
    M.val y ((v ⬝ᵥ e) / t) = (∑ j, M.val y (v j) * M.val y (e j)) / M.val y t := by
  have h1 : M.val y t * M.val y t⁻¹ = 1 := by
    rw [← val_mul h ht' ht, mul_inv_cancel₀ ht0, val_one]
  have h2 : ∀ s : Finset J, M.val y (∑ j ∈ s, v j * e j) = ∑ j ∈ s, M.val y (v j) * M.val y (e j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [val_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        val_add h (mul_mem (hv a) (he a)) (sum_mem fun j _ => mul_mem (hv j) (he j)),
        val_mul h (hv a) (he a), ih]
  rw [div_eq_mul_inv, div_eq_mul_inv, dotProduct,
    val_mul h (sum_mem fun j _ => mul_mem (hv j) (he j)) ht, h2, eq_inv_of_mul_eq_one_right h1]

end RatModel

namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem Test.norm_pair_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {h : S.Gam} (hh : h ∈ τ.yy.ker) {u : S.J → PadicAlgCl p} (hu : u ∈ τ.E) :
    ‖∑ j, u j * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := hu
    have h1 := τ.le α hα h hh i
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ Real.exp (τ.q α / S.N) * (τ.δ * Real.exp (-(τ.q α / S.N))) :=
          mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = τ.δ := by rw [Real.exp_neg]; field_simp
  | zero => simpa using τ.δ_pos.le
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul c a _ ha =>
    have hc : ‖(c : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 c.2
    have : ∀ j, (c • a) j = (c : PadicAlgCl p) * a j := fun j => rfl
    simp only [this, _root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ 1 * τ.δ := mul_le_mul hc ha (norm_nonneg _) zero_le_one
      _ = τ.δ := _root_.one_mul _

theorem Test.norm_proj_zero_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) (i : S.J) :
    ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  subst hT
  have := τ.le 0 (fun v0 => by
    rw [map_zero]; exact quadraticMap_nonneg_of_tendsto_cofinite τ.q τ.pos _) h hh i
  simpa only [map_zero, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] using this

theorem Test.exists_norm_proj_zero_eq {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) :
    ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = τ.δ := by
  subst hT
  have := τ.unit0 h hh
  simpa only [map_zero] using this

theorem val_pair_div {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {U : Set M.Z}
    (hU : U ⊆ U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U z y)
    {y₀ : S.R →+* PadicAlgCl p} (hat : S.At M y y₀) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U)
    (h : S.Gam) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) :
    M.val (gPt p ≫ y) ((v ⬝ᵥ S.ev h) / S.th x₀) =
      (∑ j, M.val (gPt p ≫ y) (v j) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) / M.val (gPt p ≫ y) (S.th x₀) := by
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hζ : (gPt p ≫ y) w ∈ U := hc.2 ⟨w, rfl⟩
  have hs := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (gPt p ≫ y) w)
  rw [RatModel.val_dotProduct_div hs (fun j => RatModel.ringOn_le_O hζ (hv j))
    (fun j => RatModel.ringOn_le_O (hU hζ) (hO.le (S.ev_mem h j))) hx
    (RatModel.ringOn_le_O (hU hζ) (hO.le (S.th_mem x₀)))
    (RatModel.ringOn_le_O (hU hζ) (hO.th_unit x₀ hx))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hat]

end ThetaSys

theorem coord_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧ ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧ S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ := by
  intro o Ω _ _ _ _ S M U₀ EE hO hLL hT hsup hstr hEE
  have closed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z, ∀ h ∈ S.HH M z,
      (∀ v ∈ EE.E z, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z) ∧
      ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
        S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O z := by
    intro z hz x₀ hx₀ h hh
    have hx : S.th x₀ ≠ 0 := hx₀.1
    refine ⟨fun v hv => ?_, ?_⟩
    · let V : M.Z.Opens := ⟨⋂ j, {a | v j ∈ M.O a}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
      have hV : (V : Set M.Z).Nonempty := ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => by
        simp only [Set.mem_setOf_eq, M.O_genericPoint]; trivial⟩
      have hvV : ∀ j, v j ∈ M.ringOn ((U₀ ⊓ V : M.Z.Opens) : Set M.Z) := fun j =>
        RatModel.mem_ringOn.2 fun a ha => Set.mem_iInter.1 ha.2 j
      refine (hLL.1 (U₀ ⊓ V) inf_le_left (M.nonempty_inf hO.ne hV) z hz).2 _ ?_ ?_
      · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
          (fun j => RatModel.ringOn_le_O ha (hvV j))
          (fun j => RatModel.ringOn_le_O ha.1 (hO.le (S.ev_mem h j)))
          (RatModel.ringOn_le_O ha.1 (hO.th_unit x₀ hx))
      · intro p _ y hc
        have hc0 : M.Cen U₀ z y := ⟨hc.1, fun a ha => (hc.2 ha).1⟩
        obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc0
        obtain ⟨h1, h2⟩ := hsup z p y y₀ τ hc0 hat
        rw [ThetaSys.val_pair_div hO (fun a ha => ha.1) hc hat hvV h hx, norm_div, (h1 x₀).1 hx₀,
          div_le_one τ.δ_pos]
        refine τ.norm_pair_le (h2 ▸ hh) (u := fun j => M.val (gPt p ≫ y) (v j)) ?_
        rw [← hEE.2 z p y y₀ τ hc0 hat]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have hw : ∀ i j, algebraMap o Ω (S.proj (S.TT M z) 0 j i) ∈ M.ringOn (U₀ : Set M.Z) :=
        fun i j => Subalgebra.algebraMap_mem _ _
      have hval : ∀ i (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p)
          (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ →
          ‖M.val (gPt p ≫ y) (((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀)‖ =
            ‖∑ j, y₀ (algebraMap o S.R (S.proj (S.TT M z) 0 j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ / τ.δ := by
        intro i p _ y y₀ τ hc hat
        rw [ThetaSys.val_pair_div hO subset_rfl hc hat (hw i) h hx, norm_div,
          ((hsup z p y y₀ τ hc hat).1 x₀).1 hx₀]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hat (algebraMap o S.R _)]; rfl
      have hmem : ∀ i, ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
        intro i
        refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
        · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
            (fun j => RatModel.ringOn_le_O ha (hw i j))
            (fun j => RatModel.ringOn_le_O ha (hO.le (S.ev_mem h j)))
            (RatModel.ringOn_le_O ha (hO.th_unit x₀ hx))
        · intro p _ y hc
          obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
          have h2 := (hsup z p y y₀ τ hc hat).2
          rw [hval i p y y₀ τ hc hat, div_le_one τ.δ_pos]
          exact τ.norm_proj_zero_le (by rw [← h2]; rfl) (h2 ▸ hh) i
      obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hz).1
      obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
      have h2 := (hsup z p y y₀ τ hc hat).2
      obtain ⟨i, hi⟩ := τ.exists_norm_proj_zero_eq (T := S.TT M z) (by rw [← h2]; rfl) (h2 ▸ hh)
      have h3 := hval i p y y₀ τ hc hat
      rw [hi, div_self τ.δ_pos.ne', RatModel.norm_val_eq_one_iff hc.1 (hmem i), RatModel.isUnit_O_iff] at h3
      refine ⟨i, fun h0 => h3.1 (by simp only [h0, zero_div]), ?_⟩
      simpa only [inv_div] using h3.2
  intro ξ x₀ hx₀ h hh
  obtain ⟨U, b, hξU, -, hb⟩ := EE.loc ξ
  obtain ⟨x, hxU, hxc, hsp, hI⟩ := hstr.2.2.2 ξ U hξU
  have hH : S.HH M x = S.HH M ξ := by simp only [ThetaSys.HH, hI]
  have hTT : S.TT M x = S.TT M ξ := by simp only [ThetaSys.TT, hH]
  obtain ⟨c1, c2⟩ := closed x hxc x₀ (hI ▸ hx₀) h (hH ▸ hh)
  have hle := RatModel.O_le_of_specializes hsp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hb ξ hξU] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hle (c1 v (by rw [hb x hxU]; exact Submodule.subset_span hv))
    | zero => simp
    | add a c _ _ ha hc => rw [add_dotProduct, add_div]; exact add_mem ha hc
    | smul c a _ ha =>
      have : c • a = (c : Ω) • a := rfl
      rw [this, smul_dotProduct, smul_eq_mul, mul_div_assoc]
      exact mul_mem c.2 ha
  · rw [hTT] at c2
    obtain ⟨i, h1, h2⟩ := c2
    exact ⟨i, h1, hle h2⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem txT_tendsto {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hq : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : Tendsto (N.txT m p) cofinite (𝓝 0) := by
  have h0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine squeeze_zero_norm (a := fun χ => Real.exp (-q χ)) (fun χ => ?_)
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq.pos))
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 m hm p χ, hp, toAdd_one, zero_add, ← natCast_zsmul, QuadraticMap.map_smul]
  have : (((m : ℤ) * (m : ℤ)) • q χ) / (m : ℝ) ^ 2 = q χ := by
    rw [zsmul_eq_mul]; push_cast; field_simp
  rw [this]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hq.th _)

theorem exists_txT_ne {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by
  obtain ⟨t, ht, hx⟩ := hT.good (N.c x)
  obtain ⟨b, rfl⟩ := hT.div t
  obtain ⟨γ, rfl⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT 0).1 b
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ ^ (n ^ 1) ^ 2)).2 (by rw [NumD.Gt.pow_b, pow_one, sq, pow_mul, ht])
  obtain ⟨s, rfl⟩ := exists_char_pow (k := (n ^ 1) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')) s
  refine ⟨⟨(1, γ * (N.tor s)⁻¹), ?_⟩, rfl, ?_⟩
  · rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
    exact N.io_zero.symm
  · rw [← norm_ne_zero_iff, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 _ hn.pow]
    refine mul_ne_zero (Real.exp_pos _).ne' ?_
    simp [hx]

theorem tx_twist {C : Type} [NormedField C] {N : NumD C} {M m : ℕ} (hM : Odd M) (hm : Odd m)
    (p : N.QT (m ^ 2)) (P : N.QT ((M * m) ^ 2)) (hp : p.1.1 = 1) (hP : P.1.1 = 1) (h : p.1.2 = P.1.2 ^ M)
    (s : Multiplicative N.X →* Cˣ) (hs : s ^ (M * m) ^ 2 = 1) :
    N.tx (M * m) (P * N.qTor s hs) = ∑' β, N.txT m p β * ((s ^ (M * m)) (Multiplicative.ofAdd β) : C) := by
  refine tsum_congr fun β => ?_
  rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (M * m) (hM.mul hm) P (P * N.qTor s hs) β).2 s (mul_one _) rfl,
    GlobalTheory.T.degenerationSeriesTerms_nest C N M m hM hm P p (by rw [hP, hp, one_pow]) h, hP, map_one, one_pow, one_mul, toAdd_one, zero_add,
    ofAdd_nsmul, map_pow, mul_comm]
  rfl

section
variable {C : Type} [NormedField C] [IsAlgClosed C] {N N' : NumD C} {n g : ℕ} (μ : Match N N' n)

theorem tx_eq {m : ℕ} (hm : ∃ j, m = n ^ j) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r _ p p') :
    N'.tx m p' = μ.c₀ * N.tx m p := by
  obtain ⟨j, rfl⟩ := hm
  exact μ.tx j p p' h

theorem twisted_eq (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (hA : μ.A) (i j : ℕ)
    {p : N.QT ((n ^ j) ^ 2)} {p' : N'.QT ((n ^ j) ^ 2)} (h : μ.r _ p p') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1)
    {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ i = 1} {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ i = 1}
    (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    ∑' β, N'.txT (n ^ j) p' β * (t' (Multiplicative.ofAdd β) : C) =
      μ.c₀ * ∑' β, N.txT (n ^ j) p β * (t (Multiplicative.ofAdd β) : C) := by
  have h0 : ∀ a, n ^ a ≠ 0 := fun a => pow_ne_zero _ hn.pos.ne'
  have hL0 : n ^ i * n ^ j ≠ 0 := mul_ne_zero (h0 _) (h0 _)
  have hL : ∃ a, (n ^ i * n ^ j) ^ 2 = n ^ a := ⟨(i + j) * 2, by ring⟩
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT i).2.1 p.1.2
  have hp1 : p.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N.mem_QT.1 p.2, hp]; exact N.io_zero
  have hp1' : p'.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N'.mem_QT.1 p'.2, hp']; exact N'.io_zero
  let P : N.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, γ), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = n ^ i * ((n ^ j) ^ 2 * n ^ i) by ring, pow_mul, hγ, pow_mul, hp1, one_pow]
    exact N.io_zero.symm⟩
  obtain ⟨P', hPP, hP'⟩ := tot_G μ hA hL P rfl
  let Q' : N'.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, p'.1.2), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = (n ^ j) ^ 2 * (n ^ i) ^ 2 by ring, pow_mul, hp1', one_pow]
    exact N'.io_zero.symm⟩
  have h1 : μ.r _ (P ^ n ^ i) Q' :=
    (r_incl μ (p := p) (p' := p') (q := P ^ n ^ i) (q' := Q') ((n ^ i) ^ 2) (by ring) (pow_ne_zero _ (h0 i)) (by rw [hp, one_pow]; exact one_pow _) hγ
      (by rw [hp', one_pow]) rfl).1 h
  have h2 : Q' = P' ^ n ^ i := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h1 (r_pow μ hL hPP _))
    (by change 1 = P'.1.1 ^ n ^ i; rw [hP', one_pow])
  have h3 : p'.1.2 = P'.1.2 ^ n ^ i := congrArg (fun q : N'.QT _ => q.1.2) h2
  obtain ⟨s, rfl⟩ := exists_char_pow hL0 t
  have hs : s ^ (n ^ i * n ^ j) ^ 2 = 1 := by rw [sq, pow_mul, pow_mul _ (n ^ i), ht, one_pow]
  obtain ⟨s', hs', hss⟩ := thetaMatching_exists_right_torus_torsion μ hA hL s hs
  have ht'' : t' ^ (n ^ i * n ^ j) ^ 2 = 1 := by
    rw [show (n ^ i * n ^ j) ^ 2 = n ^ i * (n ^ i * (n ^ j) ^ 2) by ring, pow_mul, ht', one_pow]
  have h4 : μ.r _ (N.qTor s hs ^ (n ^ i * n ^ j)) (N'.qTor t' ht'') :=
    (r_incl μ (p := N.qTor _ ht) (p' := N'.qTor t' ht') (q := N.qTor s hs ^ (n ^ i * n ^ j))
      (q' := N'.qTor t' ht'') (n ^ i * (n ^ j) ^ 2) (by ring) (mul_ne_zero (h0 i) (pow_ne_zero _ (h0 j)))
      ((one_pow _).trans (one_pow _).symm) (N.tor_pow _ _).symm (one_pow _).symm rfl).1 e
  have h5 := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h4 (r_pow μ hL hss _)) (one_pow _).symm
  have h6 : t' = s' ^ (n ^ i * n ^ j) :=
    N'.tor_injective ((congrArg (fun q : N'.QT _ => q.1.2) h5).trans (N'.tor_pow _ _).symm)
  rw [h6, ← tx_twist hn.pow hn.pow p P hp rfl hγ.symm s hs, ← tx_twist hn.pow hn.pow p' P' hp' hP' h3 s' hs']
  exact tx_eq μ ⟨i + j, (pow_add _ _ _).symm⟩ (μ.mul _ _ _ _ _ hPP hss)
end

theorem main : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  intro C _ _ _ _ N N' q q' n g g' hpr hn hn1 hq hq' hT hT' μ hA
  have hC : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  have hn0 := hpr.ne_zero
  have key : ∀ i j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)), μ.r _ p p' → p.1.1 = 1 → p'.1.1 = 1 →
      ∀ α α', Cl μ i α α' →
      ∑' z, N'.txT (n ^ j) p' (α' + n ^ i • z) = μ.c₀ * ∑' z, N.txT (n ^ j) p (α + n ^ i • z) := by
    intro i j p p' h hp hp' α α' hα
    obtain ⟨E, hE, hr⟩ := exists_torus_bij μ hn0 hA ⟨i, rfl⟩
    exact class_sum_eq (by rw [Nat.cast_pow, norm_pow, hn1, one_pow]) _ _ (txT_tendsto hq hn.pow p hp)
      (txT_tendsto hq' hn.pow p' hp') _ α α' E hE (fun t => hα.tor μ (hr t))
      fun t => twisted_eq μ hn hC hT hA i j h hp hp' (hr t)
  have tot : ∀ j x, ∃ x', Cl μ j x x' := fun j x => by
    obtain ⟨p, hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT j).2.2.1 x
    obtain ⟨p', h⟩ := μ.tot j p
    exact ⟨_, p, p', h, hp, rfl⟩
  have cotot : ∀ j x', ∃ x, Cl μ j x x' := fun j x' => by
    obtain ⟨p', hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' hC hT' j).2.2.1 x'
    obtain ⟨p, h⟩ := μ.cotot j p'
    exact ⟨_, p, p', h, rfl, hp⟩
  have hL : ∃ a, (n ^ 1) ^ 2 = n ^ a := ⟨2, by ring⟩
  have hf : ∀ x, ∃ x', ∀ j, Cl μ j x x' := fun x => by
    choose α hα using fun j => tot j x
    obtain ⟨p, hp, hx⟩ := exists_txT_ne hq hn hC hT x
    obtain ⟨p', h, hp'⟩ := tot_G μ hA hL p hp
    obtain ⟨x', hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
      μ.c₀ x α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).1 ⟨0, by simp⟩)
      fun i => key i 1 p p' h hp hp' _ _ (hα i)).2 (mul_ne_zero μ.c₀_ne hx)
    refine ⟨x', fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ 0 z
  have hg : ∀ x', ∃ x, ∀ j, Cl μ j x x' := fun x' => by
    choose α hα using fun j => cotot j x'
    obtain ⟨p', hp', hx⟩ := exists_txT_ne hq' hn hC hT' x'
    obtain ⟨p, h, hp⟩ := cotot_G μ hA hL p' hp'
    obtain ⟨x, hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq' hn.pow p' hp') (txT_tendsto hq hn.pow p hp)
      μ.c₀⁻¹ x' α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).2 ⟨0, by simp⟩)
      fun i => by rw [key i 1 p p' h hp hp' _ _ (hα i), inv_mul_cancel_left₀ μ.c₀_ne]).2
      (mul_ne_zero (inv_ne_zero μ.c₀_ne) hx)
    refine ⟨x, fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ z 0
  obtain ⟨e, he, -⟩ := existsUnique_addEquiv_of_compatible_congr N.X N'.X n hpr.two_le (Cl μ) tot cotot
    (fun _ _ _ _ _ h h' => h.add μ h') (fun _ _ _ _ _ h h' => h.cong μ hA h') (fun _ _ _ _ _ h => h.shift μ _ _) hf hg
  refine ⟨e, fun j p p' h => ((he j _).cong μ hA ⟨p, p', h, rfl, rfl⟩).1 ⟨0, by simp⟩, fun j p p' h hp hp' χ => ?_⟩
  exact (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
    μ.c₀ χ (fun _ => e χ) (fun j => ⟨0, by simp⟩) fun i => key i j p p' h hp hp' _ _ (he i χ)).1 _
    fun j => ⟨0, by simp⟩

end GlobalTheory.MatchTerm
end

