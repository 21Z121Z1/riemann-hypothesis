import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.LineNorm.Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def IsChart (N : TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (D : ℕ) (W : N.X.Opens)
    (r : Y.Fnˣ) : Prop :=
  (∀ y, N.j y ∈ W → (D • Δ).IsEqn y r) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ W →
      (D : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn)))

variable {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y}

theorem below_mem (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    N.j (below y.1) ∈ W := by
  change (y.1 ≫ N.j) _ ∈ W
  rw [← h]
  exact hW (x := spMap e.O.subtype _) trivial

theorem unitAt_of_isEqn (ht : ∀ y, Δ.IsEqn y (t y)) {D : ℕ} {y : Y.X} {r : Y.Fnˣ} :
    (D • Δ).IsEqn y r ↔ UnitAt y (((t y)⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn) := by
  rw [((ht y).nsmul D).iff_unitAt, inv_pow, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_inv_mul]

theorem IsChart.pull {N N' : TrueGeo.Model Y} {D : ℕ} {W : N.X.Opens} {r : Y.Fnˣ} (h : IsChart N Δ t φ D W r)
    (π : N'.X ⟶ N.X) (hπ : N'.j ≫ π = N.j) : IsChart N' Δ t φ D (π ⁻¹ᵁ W) r := by
  refine ⟨fun y hy => h.1 y ?_, fun v e y yt hc hW => h.2 v e y (yt ≫ π) ?_ hW⟩
  · rw [← hπ]; exact hy
  · rw [← Category.assoc, hc, Category.assoc, hπ]

theorem IsChart.pow (ht : ∀ y, Δ.IsEqn y (t y)) {N : TrueGeo.Model Y} {D : ℕ} {W : N.X.Opens} {r : Y.Fnˣ}
    (h : IsChart N Δ t φ D W r) (k : ℕ) : IsChart N Δ t φ (D * k) W (r ^ k) := by
  refine ⟨fun y hy => ?_, fun v e y yt hc hW => ?_⟩
  · rw [mul_nsmul]; exact (h.1 y hy).nsmul k
  · have hu := (unitAt_of_isEqn ht).1 (h.1 _ (below_mem N hc hW))
    rw [pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, valAt_pow hu.regAt, map_pow, Real.log_pow,
      ← h.2 v e y yt hc hW]
    push_cast
    ring

theorem hom_unique {N M : TrueGeo.Model Y} {f g : N.X ⟶ M.X} (hf : N.j ≫ f = M.j) (hg : N.j ≫ g = M.j) : f = g := by
  have := N.ar.isIntegral
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsDominant N.j := ⟨(dense_iff_closure_eq.2 (genericPoint_spec N.X)).mono
    (Set.singleton_subset_iff.2 ⟨_, ((j_gen_specializes N).antisymm (genericPoint_specializes _)).eq⟩)⟩
  refine ext_of_isDominant_of_isSeparated M.p (ext_of_isDominant N.j ?_) N.j (hf.trans hg.symm)
  rw [← Category.assoc, ← Category.assoc, hf, hg]

theorem exists_normal_dominating_finset {ι : Type} (M : TrueGeo.Model Y) (N : ι → TrueGeo.Model Y) (S : Finset ι) :
    ∃ (P : TrueGeo.Model Y) (π : P.X ⟶ M.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P.X ∧ P.j ≫ π = M.j ∧
      ∀ a ∈ S, ∃ ρ : P.X ⟶ (N a).X, P.j ≫ ρ = (N a).j := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨P, π, -, hP, -, -, h, -⟩ := ModelDom.exists_normal_dominating F Y M M
    exact ⟨P, π, hP, h, by simp⟩
  | insert a S _ ih =>
    obtain ⟨P, π, -, h, hS⟩ := ih
    obtain ⟨Q, σ, τ, hQ, -, -, h₁, h₂, -⟩ := ModelDom.exists_normal_dominating F Y P (N a)
    refine ⟨Q, σ ≫ π, hQ, by rw [← Category.assoc, h₁, h], fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact ⟨τ, h₂⟩
    · obtain ⟨ρ, hρ⟩ := hS b hb
      exact ⟨σ ≫ ρ, by rw [← Category.assoc, h₁, hρ]⟩

theorem w_le_one (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    (g : Γ(N.X, W)) (hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W) :
    e.w (valAt y.1 (fnOf (N.j ⁻¹ᵁ W) hg (N.j.app W g))) ≤ 1 := by
  have hb : below y.1 ∈ N.j ⁻¹ᵁ W := below_mem N h hW
  have ht : ⊤ ≤ y.1 ⁻¹ᵁ (N.j ⁻¹ᵁ W) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W
    rw [← h]
    exact hW (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype N.j y.1 yt h (U := W) (W := N.j ⁻¹ᵁ W) le_rfl ht hW g
  rw [OfModel.valAt_fnOf _ hb ht, Scheme.Hom.app_eq_appLE, hev, ← e.mem_O]
  exact Subtype.prop _

theorem isChart_of_dvd (ht : ∀ y, Δ.IsEqn y (t y)) {M N : TrueGeo.Model Y} (π : N.X ⟶ M.X) (hπ : N.j ≫ π = M.j)
    {V : M.X.Opens} {d n : ℕ} {s : Fin n → Y.Fn} (hs : Generates M t V d s)
    (hφ : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ V →
      (d : ℝ) * φ v e y = Real.log (⨆ i, e.w (valAt y.1 (s i * (((t (below y.1))⁻¹ ^ d : Y.Fnˣ) : Y.Fn)))))
    {i : Fin n} {W : N.X.Opens} (hi : s i ≠ 0)
    (hg : ∀ k, ∃ g : Γ(N.X, W), ∀ h : genericPoint Y.X ∈ N.j ⁻¹ᵁ W,
      fnOf (N.j ⁻¹ᵁ W) h (N.j.app W g) * s i = s k) :
    IsChart N Δ t φ d (W ⊓ π ⁻¹ᵁ V) (Units.mk0 (s i) hi) := by
  have hV (y : Y.X) (hy : N.j y ∈ W ⊓ π ⁻¹ᵁ V) : M.j y ∈ V := by rw [← hπ]; exact hy.2
  have e₀ (y : Y.X) : (((t y)⁻¹ ^ d * Units.mk0 (s i) hi : Y.Fnˣ) : Y.Fn) =
      s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn) := by rw [Units.val_mul, mul_comm]; rfl
  refine ⟨fun y hy => (unitAt_of_isEqn ht).2 ?_, fun v e y yt hc hW => ?_⟩
  · obtain ⟨h₁, k, hk⟩ := hs y (hV y hy)
    obtain ⟨g, hg⟩ := hg k
    have hy' : y ∈ N.j ⁻¹ᵁ W := hy.1
    obtain ⟨a, ha⟩ := regAt_fnOf hy' (gen_mem hy') (N.j.app W g)
    obtain ⟨b, hb⟩ := h₁ i
    obtain ⟨c, hu, hc⟩ := hk
    rw [← hg (gen_mem hy'), mul_assoc, ← ha, ← hb, ← map_mul] at hc
    obtain rfl := IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField hc
    rw [e₀]
    exact ⟨b, isUnit_of_mul_isUnit_right hu, hb⟩
  · have hb := below_mem N hc hW
    have hb' : below y.1 ∈ N.j ⁻¹ᵁ W := hb.1
    rw [hφ v e y (yt ≫ π) (by rw [← Category.assoc, hc, Category.assoc, hπ]) (fun p hp => (hW hp).2), e₀]
    congr 1
    have : Nonempty (Fin n) := ⟨i⟩
    refine le_antisymm (ciSup_le fun k => ?_) (le_ciSup (f := fun k =>
      e.w (valAt y.1 (s k * (((t (below y.1))⁻¹ ^ d : Y.Fnˣ) : Y.Fn)))) (Finite.bddAbove_range _) i)
    obtain ⟨g, hg⟩ := hg k
    rw [← hg (gen_mem hb'), mul_assoc, valAt_mul (regAt_fnOf hb' _ _) ((hs _ (hV _ hb)).1 i), map_mul]
    exact mul_le_of_le_one_left (e.w.nonneg _) (w_le_one N hc (fun p hp => (hW hp).1) g _)

theorem IsChart.w_div_le (ht : ∀ y, Δ.IsEqn y (t y)) {N : TrueGeo.Model Y} {D : ℕ} {W W' : N.X.Opens}
    {r r' : Y.Fnˣ} (h : IsChart N Δ t φ D W r) (h' : IsChart N Δ t φ D W' r')
    {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y} {yt : Sp e.O ⟶ N.X}
    (hc : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) (hW : ⊤ ≤ yt ⁻¹ᵁ (W ⊓ W')) :
    e.w (valAt y.1 ((r : Y.Fn) / (r' : Y.Fn))) ≤ 1 := by
  have hb := below_mem N hc hW
  have e₁ := h.1 _ hb.1
  have e₂ := h'.1 _ hb.2
  have u₁ := (unitAt_of_isEqn ht).1 e₁
  have u₂ := (unitAt_of_isEqn ht).1 e₂
  have u₃ := e₂.iff_unitAt.1 e₁
  have p₁ := e.w.pos (valAt_ne_zero u₁)
  have p₂ := e.w.pos (valAt_ne_zero u₂)
  have q := Real.log_injOn_pos p₁ p₂ ((h.2 v e y yt hc fun p hp => (hW hp).1).symm.trans
    (h'.2 v e y yt hc fun p hp => (hW hp).2))
  have e₃ : (((t (below y.1))⁻¹ ^ D * r : Y.Fnˣ) : Y.Fn) =
      (r : Y.Fn) / (r' : Y.Fn) * (((t (below y.1))⁻¹ ^ D * r' : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, mul_left_comm, div_mul_cancel₀ _ r'.ne_zero]
  rw [e₃, valAt_mul u₃.regAt u₂.regAt, map_mul] at q
  exact ((mul_eq_right₀ p₂.ne').1 q).le

theorem fromModel_of_charts (ht : ∀ y, Δ.IsEqn y (t y)) (N : TrueGeo.Model Y)
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X) (D : ℕ+)
    (h : ∀ x : N.X, ∃ (W : N.X.Opens) (r : Y.Fnˣ), x ∈ W ∧ IsChart N Δ t φ D W r) : FromModel Y Δ t φ := by
  have := N.ar.isIntegral
  choose W r hx hch using h
  obtain ⟨ρ, hρ₁, hρ₂, -, hρ₄, -⟩ := ModelFn.main F Y N
  have hreg (a b : N.X) : ∀ x ∈ W a ⊓ W b, RegAt x (ρ.symm ((r a : Y.Fn) / (r b : Y.Fn))) :=
    GlobalTheory.T.regular_of_valuation_bounded_at_points F Y N hN _ _ fun v e y yt hc hW => by
      rw [hρ₄, RingEquiv.apply_symm_apply]
      exact (hch a).w_div_le ht (hch b) hc hW
  have hne (a b : N.X) : ρ.symm ((r a : Y.Fn) / (r b : Y.Fn)) ≠ 0 :=
    (map_ne_zero _).2 (div_ne_zero (r a).ne_zero (r b).ne_zero)
  have hunit (a b : N.X) : ∀ x ∈ W a ⊓ W b, UnitAt x (ρ.symm ((r a : Y.Fn) / (r b : Y.Fn))) := fun x hx =>
    (unitAt_iff (hne a b)).2 ⟨hreg a b x hx, by
      rw [← map_inv₀, inv_div]
      exact hreg b a x ⟨hx.2, hx.1⟩⟩
  choose g hg using fun a b => exists_unit_fnOf_eq (hunit a b)
  let L : LB N.X := { ι := N.X, U := W, g := g }
  have hL : L.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩, fun i => Units.ext (Cartier.fn_ext fun h => ?_),
      fun i j k => Units.ext (Cartier.fn_ext fun h => ?_)⟩
    · rw [LB.val_res, fnOf_resG, Units.val_one, map_one]
      refine (hg i i _).trans ?_
      rw [div_self (Units.ne_zero _), map_one]
    · simp only [Units.val_mul, map_mul, LB.val_res, fnOf_resG]
      refine (congrArg₂ (· * ·) (hg i j _) (hg j k _)).trans (Eq.trans ?_ (hg i k _).symm)
      rw [← map_mul, div_mul_div_cancel₀ (Units.ne_zero _)]
  refine ⟨N, L, D, fun i => r (i PUnit.unit), hL, ⟨LB.isLB_pull hL N.j, fun i i' hii => ?_,
    fun i y hy => (hch _).1 y (Set.mem_iInter.1 hy PUnit.unit)⟩, fun v e y yt i hc hW => (hch _).2 v e y yt hc hW⟩
  have l : (L.pull N.j).U i ⊓ (L.pull N.j).U i' ≤ N.j ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hp : ((L.pull N.j).g i i').val =
      resG Y.X l (N.j.app _ (L.g (i PUnit.unit) (i' PUnit.unit)).val) := by
    have : (L.pull N.j).g i i' = res l (pullU N.j _ (L.g (i PUnit.unit) (i' PUnit.unit))) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have hU : genericPoint N.X ∈ L.U (i PUnit.unit) ⊓ L.U (i' PUnit.unit) := hρ₂ ▸ l hii
  rw [hp, fnOf_resG, ← hρ₁ _ hU]
  have := congrArg ρ (hg (i PUnit.unit) (i' PUnit.unit) hU)
  rw [RingEquiv.apply_symm_apply] at this
  exact ((congrArg (· * _) this).trans (div_mul_cancel₀ _ (Units.ne_zero _))).symm

theorem fromModel_of_locMax : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv)
    (t : Y.X → Y.Fnˣ) (φ : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → (∀ z, LocMax M t φ z) → FromModel Y Δ t φ := by
  intro F _ _ Y M Δ t φ ht h
  classical
  choose V d n s hz hs hφ using h
  choose N π V' hπ _ hz' hle hN using fun z => GlobalTheory.T.exists_model_refinement_generating F Y M Δ t (V z) (d z) (n z) (s z) z ht (hz z) (hs z)
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : CompactSpace M.X := QuasiCompact.compactSpace_of_compactSpace M.p
  obtain ⟨S, hS⟩ := CompactSpace.elim_nhds_subcover (fun z => (V' z : Set M.X))
    fun z => (V' z).isOpen.mem_nhds (hz' z)
  obtain ⟨P, σ, hP, hσ, hdom⟩ := exists_normal_dominating_finset M N S
  refine fromModel_of_charts ht P hP (∏ a ∈ S, d a) fun x => ?_
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS.ge (Set.mem_univ (σ x)))
  obtain ⟨τ, hτ⟩ := hdom a ha
  obtain rfl : σ = τ ≫ π a := hom_unique hσ (by rw [← Category.assoc, hτ, hπ])
  obtain ⟨i, W, hxW, hi, hg⟩ := hN a (τ x) hxa
  have hc := ((isChart_of_dvd ht (π a) (hπ a) (hs a) (hφ a) hi hg).pow ht
    ((∏ b ∈ S.erase a, d b : ℕ+) : ℕ)).pull τ hτ
  rw [← PNat.mul_coe, Finset.mul_prod_erase S d ha] at hc
  exact ⟨_, _, show τ x ∈ W ⊓ π a ⁻¹ᵁ V a from ⟨hxW, hle a hxa⟩, hc⟩

end GlobalTheory.LineNorm.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericStalkPointInInterior
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem fromSpecStalk_bot_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)),
    p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  intro E _ _ _ H D l Xo c Z z p hp
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI hdom : IsDomain (Z.X.presheaf.stalk z) := (Z.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Z.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (Iso.commRingCatIsoToRingEquiv _).bijective
  obtain ⟨y, hy⟩ := @DomFine.exists_generic_point (𝓞 c.F) c.F _ _ _ _ _ Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense (Z.X.presheaf.stalk z) _ hdom _ (Z.X.fromSpecStalk z) hfl
  let w : PrimeSpectrum (FractionRing (Z.X.presheaf.stalk z)) := ⊥
  have hw : (jK (Z.X.presheaf.stalk z)) w = p := by
    apply PrimeSpectrum.ext
    rw [hp]
    show Ideal.comap (algebraMap (Z.X.presheaf.stalk z) (FractionRing (Z.X.presheaf.stalk z))) (⊥ : Ideal _) = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)
  refine ⟨y w, ?_⟩
  have e := congrArg (fun f => f w) hy
  simp only [Scheme.Hom.comp_apply] at e
  rw [← hw]
  exact e

end GlobalTheory.TorRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreservedStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmann_cell_span_preserved : ∀ (S : Type) [CommRing S] (m a k b : ℕ) (Q : Type) [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S), a ≤ k → k ≤ b → (LinearIndependent S c → LinearIndependent S (gvec c w x)) ∧ Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) ∧ ∀ e : ℕ, e ≤ a ∨ b ≤ e → initSpan S (gvec c w x) e = initSpan S c e := by
  first | exact @GlobalTheory.GrCl.gvec_frame | exact GlobalTheory.GrCl.gvec_frame | (intros; apply GlobalTheory.GrCl.gvec_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def ConeAt (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) (z : Z.X) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R))
    (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R ∧ ξ (closedPoint R) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
    Cn P.D.toPre.X m γ ∧ InCone P.D.toPre γ

theorem hasCones_iff (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : Model Xo c β) : HasCones Cn Z ↔ ∀ z, ConeAt Cn Z z :=
  Iff.rfl

theorem exists_of_id (Y : Model Xo c (RingHom.id c.F)) (z : Y.X) :
    (∃ x ∈ genBd Y, genι Y x = z) ∨ z ∈ Set.range Y.j := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  have : IsIso (genι Y) := inferInstance
  set x := inv (genι Y) z with hx
  have hz : genι Y x = z := by rw [hx, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  by_cases h : x ∈ genBd Y
  · exact Or.inl ⟨x, h, hz⟩
  · obtain ⟨w, hw⟩ := not_not.1 h
    exact Or.inr ⟨w, by rw [← hz, ← hw]; rfl⟩

end GlobalTheory.GenFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

section Vals

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem InvFun.evalZ_comb [Module.Finite O X] (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O)
    (β : LinearMap.BilinForm ℤ X) : (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := rfl

end Vals

theorem InvFun.eval_resInt {O : Type} [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Finite ℤ X] (B : X → X → ℝ) : (resInt O φ).eval X B = φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(resInt O φ).eval_eq hr]
  exact φ.eval_comp (r := r.restrictScalars ℤ) hr B

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

section Ord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def TraitOrd (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (U : Z.X.Opens) (f : Γ(Z.X, U)) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t),
      Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
      ∀ hU : χ (closedPoint W) ∈ U, ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧
        Associated ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ U _ hU).hom f)) (ϖ ^ n)

end Ord

def HasLinForms {E : Type} [Field E] [NumberField E]
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
    Cn X m γ → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) →
      ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φ.evalZ be

def ConeZr (E : Type) [Field E] [NumberField E] (g : ℕ) (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ConeZ E φ X m γ ∧ Module.Free ℤ X ∧ Module.finrank ℤ X ≤ g

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementInvLatticeClausesOfFrameConjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElementInv_latticeClauses_of_frameConj : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → (∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → C ∈ Formalism.L2.DIV.St 1 → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z ∈ Formalism.L2.NTheta.LamHat V, (fun a => finPart D e * (finPart D (incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) * y a)) =
      fun a => finPart D e * (finMat D.sp.cm.sig V.gram α⁻¹).mulVec z a) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | exact GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat | (intros; apply GlobalTheory.Mem.R3.LiftBrg.EtaInvLat.eta_inv_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConj
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.HodgeConj

theorem spMap_conj_conj' : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by simp))

theorem spMap_dual_conj_conj' :
    spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (starRingEnd ℂ)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap]))

theorem smul_gram_map_conj {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((c : ℂ) • (Mᴴ * M)) a b = starRingEnd ℂ (((c : ℂ) • ((M.map (starRingEnd ℂ))ᴴ * M.map (starRingEnd ℂ))) a b) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]

theorem smoothOn_hodge_of_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  intro D A N j S κ s x σ σ' hσ h'
  have hφ : σ' = (starRingEnd ℂ).comp σ := RingHom.ext fun a => by
    rw [hσ]; simp
  have hpt : ∀ y : CxPts (genStr s.T.Z) σ, (spMap (starRingEnd ℂ) ≫ y.1) ≫ genStr s.T.Z = spMap σ' := fun y => by
    have h0 : y.1 ≫ genStr s.T.Z = spMap σ := y.2
    rw [Category.assoc, h0, hσ, spMap, spMap, spMap, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  let jm : CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ' := fun y => ⟨spMap (starRingEnd ℂ) ≫ y.1, hpt y⟩
  have hj : IsConjMap jm := fun _ => rfl
  intro V φ F τ a b hV
  obtain ⟨g', h1, h2, h3⟩ := h' V φ F τ a b hV
  set W' : Set (CxPts (genStr s.T.Z) σ') := {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ' V.1 with hW'
  have hWo : IsOpen W' := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hsub : {y | ¬ LiesIn y (genBd s.T.Z)} ∩ ptsIn _ σ V.1 ⊆ jm ⁻¹' W' := fun y hy =>
    ⟨fun h => hy.1 ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h),
      (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hy.2⟩
  have k1 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h1).2.1.mono hsub
  have k2 := (smoothOn_comp_ddcForm_of_isConjMap _ _ (genStr s.T.Z) _ σ' σ jm hj W' _ hWo h2).2.1.mono hsub
  refine ⟨fun y => starRingEnd ℂ (g' (jm y)), k1.congr fun y _ => by simp, (show (manifold s.T.Z σ).SmoothOn _ (fun y => -(g' (jm y)).im) from fun i => (k2 i).neg).congr
    fun y _ => by simp, fun y hy hyV f hf => ?_⟩
  have hnb : ¬ LiesIn y (genBd s.T.Z) := hy
  have hjy : jm y ∈ ptsIn _ σ' V.1 := (mem_ptsIn_iff_of_conj (y := y) (y' := jm y) rfl).2 hyV
  have hjnb : ¬ LiesIn (jm y) (genBd s.T.Z) := fun h => hnb ((liesIn_iff_of_comp (y := y) (y' := jm y) rfl _).1 h)
  have hx : (jm y).1 ≫ genι s.T.Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι s.T.Z := Category.assoc _ _ _
  obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) hφ hx
  have e : evHom hjy = (starRingEnd ℂ).comp (evHom hyV) := RingHom.ext fun c => by
    rw [← ev_eq, ev_conj' (y := y) (y' := jm y) rfl, ev_eq hyV]
    rfl
  have hF' : F.IsMap (evHom hjy) f' := fun τ i => by
    refine (hf' τ i).trans ((congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (hf τ i)).trans ?_)
    refine (GlobalTheory.GradedPieces.dual_comp (evHom hyV) (starRingEnd ℂ) (F.v τ i)).trans ?_
    rw [e]
  have k3 := h3 (jm y) hjnb hjy f' hF'
  obtain ⟨hh, hhH⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y)).2 hnb
  obtain ⟨hh', hhm⟩ := hh.exists_isMap (starRingEnd ℂ) hφ hx
  have hhH' : IsHodgeFrame s.U (jm y) hh' := hhH.conj hσ
    (by show y.1 = spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ y.1
        rw [← Category.assoc, spMap_conj_conj', Category.id_comp])
    fun τ i => by rw [hhm τ i, ← Category.assoc, spMap_dual_conj_conj', Category.id_comp]
  have hco : hh'.co f' τ = (hh.co f τ).map (starRingEnd ℂ) := hhm.co τ hf' hx
  show _ = starRingEnd ℂ (g' (jm y))
  rw [← k3, x.hodge_gram hhH' f' τ, x.hodge_gram hhH f τ, hco]
  exact smul_gram_map_conj _ _ a b

end GlobalTheory.ShFam.HodgeConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorRef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

def IsChartOf (Z : GMod Xo c) {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (a : 𝓞 c.F)
    (b : 𝓞 c.F →+* R) (u : C.X ⟶ Z.X) : Prop :=
  IsOpenImmersion u ∧ u ≫ Z.s = C.s ≫ spMap b ∧
    Set.range u = Z.s ⁻¹' {x : Sp (𝓞 c.F) | a ∉ x.asIdeal} ∧ C.j ≫ u = Z.j ∧ Nonempty (SABMap C.t Z.t u)

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExponential_modelFiber_of_uniformisationExp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | exact GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_hol <;> assumption)
end

