import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundCharZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0199
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorLatticeCoordDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit

section Sizes

variable {L : Type} [Field L] [NumberField L] (v : FinitePlace L)

theorem size_int_le (a : 𝓞 L) : v (algebraMap (𝓞 L) L a) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one L v.maximalIdeal a

theorem size_int_eq_one_iff (a : 𝓞 L) : v (algebraMap (𝓞 L) L a) = 1 ↔ a ∉ (primeOf v).asIdeal := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_eq_one_iff_notMem L v.maximalIdeal a

theorem local_sizes (A : Type) [CommRing A] [Algebra (𝓞 L) A] [IsLocalization.AtPrime A (primeOf v).asIdeal]
    [Algebra A L] [IsScalarTower (𝓞 L) A L] :
    (∀ r : A, v (algebraMap A L r) ≤ 1) ∧ ∀ r : A, v (algebraMap A L r) = 1 → IsUnit r := by
  have key : ∀ r : A, ∃ (a d : 𝓞 L), d ∉ (primeOf v).asIdeal ∧ r * algebraMap (𝓞 L) A d = algebraMap (𝓞 L) A a ∧
      v (algebraMap A L r) = v (algebraMap (𝓞 L) L a) := by
    intro r
    obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq (primeOf v).asIdeal.primeCompl r
    have e := IsLocalization.mk'_spec A a d
    refine ⟨a, d, d.2, e, ?_⟩
    have e' := congrArg (fun t => v (algebraMap A L t)) e
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e'
    rwa [(size_int_eq_one_iff v d).2 d.2, _root_.mul_one] at e'
  refine ⟨fun r => ?_, fun r hr => ?_⟩
  · obtain ⟨a, d, -, -, e⟩ := key r
    rw [e]
    exact size_int_le v a
  · obtain ⟨a, d, -, e₁, e₂⟩ := key r
    have ha : a ∉ (primeOf v).asIdeal := (size_int_eq_one_iff v a).1 (e₂ ▸ hr)
    have hu : IsUnit (algebraMap (𝓞 L) A a) :=
      IsLocalization.map_units A (⟨a, ha⟩ : (primeOf v).asIdeal.primeCompl)
    rw [← e₁] at hu
    exact isUnit_of_mul_isUnit_left hu

end Sizes

section Centre

variable {X : Scheme.{0}} {L : Type} [Field L] [NumberField L] (v : FinitePlace L) (z : Sp (𝓞 L) ⟶ X)

theorem centre_local (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A (primeOf v).asIdeal] :
    centre (spMap (algebraMap (𝓞 L) A) ≫ z) = z (primeOf v) := by
  have e : (spMap (algebraMap (𝓞 L) A)) (IsLocalRing.closedPoint A) = primeOf v := by
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.comap_maximalIdeal A (primeOf v).asIdeal
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg z e)

end Centre

section Det

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem div_mem_of_span_eq (R : Subring Ω) {t g : Ω} (ht : t ≠ 0) (hg : g ≠ 0)
    (h : Submodule.span R {t} = Submodule.span R {g}) : g / t ∈ R ∧ t / g ∈ R := by
  have h1 : t ∈ Submodule.span R {g} := h ▸ Submodule.mem_span_singleton_self _
  have h2 : g ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r₁, hr₁⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨r₂, hr₂⟩ := Submodule.mem_span_singleton.1 h2
  have e₁ : (r₁ : Ω) * g = t := hr₁
  have e₂ : (r₂ : Ω) * t = g := hr₂
  constructor
  · rw [← e₂, mul_div_cancel_right₀ _ ht]; exact r₂.2
  · rw [← e₁, mul_div_cancel_right₀ _ hg]; exact r₁.2

theorem detLat_isGenAt {E : Type} [AddCommGroup E] [Module Ω E] (V : Lat ξ E) {r : ℕ} {s b : Fin r → E}
    {T : Matrix (Fin r) (Fin r) Ω} {p : Cpt ξ} (hs : LinearIndependent Ω s) (hb : V.IsFrameAt b p)
    (hT : ∀ k, b k = ∑ k', T k' k • s k') (hdet : T.det ≠ 0) : (detLat V s).IsGenAt p T.det := by
  refine ⟨hdet, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨b₂, T₂, hb₂, hT₂, rfl⟩
    have hch : ∀ q, ∃ c : Fin r → regAt ξ p, b₂ q = ∑ i, (c i : Ω) • b i := fun q => by
      have hm : b₂ q ∈ V p := by rw [hb₂.2]; exact Submodule.subset_span ⟨q, rfl⟩
      rw [hb.2] at hm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
      exact ⟨c, hc.symm⟩
    choose c hc using hch
    let M : Matrix (Fin r) (Fin r) (regAt ξ p) := Matrix.of fun i q => c q i
    have hM : T₂ = T * M.map (regAt ξ p).subtype := by
      ext k' q
      have e : ∑ k', T₂ k' q • s k' = ∑ k', (T * M.map (regAt ξ p).subtype) k' q • s k' := by
        rw [← hT₂ q, hc q]
        simp only [hT, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [M, _root_.mul_comm]
      have e' : ∑ k', (T₂ k' q - (T * M.map (regAt ξ p).subtype) k' q) • s k' = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self]
      exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hs _ e' k')
    refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
    show (M.det : Ω) * T.det = T₂.det
    have e : (M.det : Ω) = (M.map (regAt ξ p).subtype).det := RingHom.map_det (regAt ξ p).subtype M
    rw [hM, Matrix.det_mul, e, _root_.mul_comm]
  · rintro _ rfl
    exact ⟨b, T, hb, hT, rfl⟩

end Det

section Core

theorem valAt_det {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [CommRing F] [IsLocalRing F]
    {z : Sp F ⟶ X} (h : genPt ξ ⤳ centre z) {r : ℕ} {T' : Matrix (Fin r) (Fin r) Ω} {T : Matrix (Fin r) (Fin r) F}
    (hv : ∀ i j, ValAt ξ z (T' i j) (T i j)) : ValAt ξ z T'.det T.det := by
  have hex : ∀ i j, ∃ s, genMap ξ ⟨centre z, h⟩ s = T' i j ∧ (Scheme.stalkClosedPointTo z).hom s = T i j :=
    fun i j => by
      obtain ⟨_, s, h1, h2⟩ := hv i j
      exact ⟨s, h1, h2⟩
  choose S h1 h2 using hex
  let M : Matrix (Fin r) (Fin r) (X.presheaf.stalk (centre z)) := Matrix.of S
  have e1 : T' = M.map (genMap ξ ⟨centre z, h⟩) := by ext i j; exact (h1 i j).symm
  have e2 : T = M.map (Scheme.stalkClosedPointTo z).hom := by ext i j; exact (h2 i j).symm
  exact ⟨h, M.det, by rw [e1]; exact RingHom.map_det _ _, by rw [e2]; exact RingHom.map_det _ _⟩

theorem core (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei]
    (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hs : ∀ τ, LinearIndependent Ω (s τ))
    (hdeg : (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀)
    (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L)
    (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω)
    (T : Ψ → Matrix (Fin m) (Fin m) L)
    (hC : CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w) (hw0 : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (hg : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g)
    (hfr : ∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩)
    (hb : ∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k')
    (hval : ∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j))
    (hdet : ∀ τ, (T τ).det ≠ 0)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A] [IsLocalization.AtPrime A (primeOf v).asIdeal]
    [Algebra A L] [IsScalarTower (𝓞 L) A L] :
    (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  classical
  have hξ := hT.gen
  have he₀ : e₀ ≠ 0 := hdeg.1
  obtain ⟨hA₁, hA₂⟩ := local_sizes v A
  set zL : Sp L ⟶ X := spMap (algebraMap (𝓞 L) L) ≫ z with hzLdef
  set zA : Sp A ⟶ X := spMap (algebraMap (𝓞 L) A) ≫ z with hzA
  have hzL : zL = spMap (algebraMap A L) ≫ zA := by
    rw [hzLdef, hzA, ← Category.assoc, IsScalarTower.algebraMap_eq (𝓞 L) A L]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨ch, h, hcne, hmax, hin⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.bestChart_finite X Ω ξ K J y L w v A zA hall hT hA₁ hA₂
    (hzL ▸ hC)
  have hL : genPt ξ ⤳ centre zL := hall _
  have hP : (⟨z (primeOf v), hall _⟩ : Cpt ξ) = ⟨centre zA, h⟩ := Subtype.ext (centre_local v z A).symm
  have hfr' : ∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨centre zA, h⟩ := fun τ => hP ▸ hfr τ

  have hdv : ∀ τ, ValAt ξ zL (T' τ).det (T τ).det := fun τ => valAt_det hL (hval τ)
  have hdet' : ∀ τ, (T' τ).det ≠ 0 := fun τ h0 => hdet τ <| by
    have h1 := hdv τ
    rw [h0] at h1
    exact LieTangent.valAt_unique hξ h1 ⟨hL, 0, map_zero _, map_zero _⟩
  have hgen : ∀ τ, (detLat (Vl τ) (s τ)).IsGenAt ⟨centre zA, h⟩ (T' τ).det := fun τ =>
    detLat_isGenAt (Vl τ) (hs τ) (hfr' τ) (hb τ) (hdet' τ)
  have htg := Flag.tens_gen (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1) ⟨centre zA, h⟩ _ hgen

  have hdg := hdeg.2 ⟨centre zA, h⟩ trivial ch hin
  rw [htg.2] at hdg
  set D : Ω := ∏ τ, (T' τ).det with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hdet' τ
  have ht : (∏ τ, (T' τ).det ^ (-1 : ℤ)) = D⁻¹ := by
    simp only [_root_.zpow_neg, zpow_one, hD, Finset.prod_inv_distrib]
  have hy : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k => (hC.2 k (ch k) (isUnit_iff_ne_zero.2 (hcne k))).1
  have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hC.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hw0 k))).1
  set G : Ω := GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ ch with hG
  have hG0 : G ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) he₀
  have hsp : Submodule.span (regAt ξ ⟨centre zA, h⟩) {D⁻¹} = Submodule.span (regAt ξ ⟨centre zA, h⟩) {G} := by
    rw [← ht]
    exact hdg
  obtain ⟨hε, hε'⟩ := div_mem_of_span_eq _ (inv_ne_zero hD0) hG0 hsp

  obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_of_mem h hε
  obtain ⟨r', hr'⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_of_mem h hε'
  have hrr : r * r' = 1 := by
    have h1 := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul hr hr'
    have e : G / D⁻¹ * (D⁻¹ / G) = 1 := by field_simp
    rw [e] at h1
    exact LieTangent.valAt_unique hξ h1 (GlobalTheory.CompanionTheory.Ar.RootHt.valAt_one h)
  have hvr : v (algebraMap A L r) = 1 := by
    have h1 : v (algebraMap A L r) * v (algebraMap A L r') = 1 := by
      rw [← map_mul, ← map_mul, hrr, map_one, map_one]
    have h2 := hA₁ r
    have h3 := hA₁ r'
    nlinarith [apply_nonneg v (algebraMap A L r), apply_nonneg v (algebraMap A L r')]
  have hrL : ValAt ξ zL (G / D⁻¹) (algebraMap A L r) := by
    rw [hzL]; exact LieTangent.valAt_base hξ (algebraMap A L) hr

  have hτ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_gen_ratio hC hL a he₀ ch c₀ hcne hw0
  have hm₀ : chartMono y c₀ a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy₀ k)
  have hgen₀ : GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ c₀ = e₀ * chartMono y c₀ a := _root_.mul_comm _ _
  have hid : G / D⁻¹ * (e₀ * chartMono y c₀ a)⁻¹ = D * (G / GlobalTheory.CompanionTheory.Ar.RootHt.gen y a e₀ c₀) := by
    rw [hgen₀]
    field_simp
  have hl := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul hrL hg
  have hr₂ := GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal.val_mul
    (GlobalTheory.CompanionTheory.Ar.RootHt.valAt_prod hL Finset.univ _ _ hdv) hτ
  rw [hid] at hl
  have hv := LieTangent.valAt_unique hξ hl hr₂
  have hn := congrArg v hv
  rw [map_mul, hvr, _root_.one_mul, map_mul, map_prod] at hn
  rw [hn]
  congr 1
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hsup : (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, ch k⟩) :=
    le_antisymm (by haveI : Nonempty (J k) := ⟨ch k⟩; exact ciSup_le (hmax k))
      (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (ch k))
  rw [map_zpow₀, map_div₀, hsup]

end Core

theorem det_frames_size : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (Ψ : Type) [Fintype Ψ] (Ei : Type) [AddCommGroup Ei] [Module Ω Ei] (Vl : Ψ → Lat ξ Ei) (m : ℕ) (s : Ψ → Fin m → Ei) (a : K → ℤ) (e₀ : Ω) (hall : ∀ q : X, genPt ξ ⤳ q), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ τ, LinearIndependent Ω (s τ)) → (Lat.tens (fun τ => detLat (Vl τ) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (c₀ : (k : K) → J k) (g : L) (v : FinitePlace L) (b' : Ψ → Fin m → Ei) (T' : Ψ → Matrix (Fin m) (Fin m) Ω) (T : Ψ → Matrix (Fin m) (Fin m) L), CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (e₀ * chartMono y c₀ a)⁻¹ g → g ≠ 0 → (∀ τ, (Vl τ).IsFrameAt (b' τ) ⟨z (primeOf v), hall _⟩) → (∀ τ k, b' τ k = ∑ k', T' τ k' k • s τ k') → (∀ τ i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' τ i j) (T τ i j)) → (∀ τ, (T τ).det ≠ 0) → (∏ τ, v (T τ).det) * GlobalTheory.CompanionTheory.Ar.RootHt.locRatio a w c₀ v = v g := by
  intro X Ω _ ξ K _ J _ y Ψ _ Ei _ _ Vl m s a e₀ hall hT hs hdeg L _ _ w z c₀ g v b' T' T hC hw0 hg _ hfr hb hval hdet
  have hu : ∀ d : (primeOf v).asIdeal.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d => by
    refine isUnit_iff_ne_zero.2 fun h0 => d.2 ?_
    have : (d : 𝓞 L) = 0 := (FaithfulSMul.algebraMap_injective (𝓞 L) L) (by rw [h0, map_zero])
    rw [this]
    exact zero_mem _
  letI : Algebra (Localization.AtPrime (primeOf v).asIdeal) L := (IsLocalization.lift hu).toAlgebra
  haveI : IsScalarTower (𝓞 L) (Localization.AtPrime (primeOf v).asIdeal) L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hu x).symm
  exact core X Ω ξ K J y Ψ Ei Vl m s a e₀ hall hT hs hdeg L w z c₀ g v b' T' T hC hw0 hg hfr hb hval hdet
    (Localization.AtPrime (primeOf v).asIdeal)

end GlobalTheory.CompanionTheory.Ar.RootHt.FinUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

theorem alg {R : Type*} [CommRing R] (t s : R) (g g' a r v : Rˣ) (N n : ℕ)
    (h : t * ((g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2)) ^ n =
      ((g' ^ (n : ℤ)).val * s) ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) :
    t * (a.val * r.val ^ (N ^ 2)) ^ n = s ^ (N ^ 2) * v.val ^ n := by
  have hz : ∀ u : Rˣ, u ^ (-((N : ℤ) ^ 2)) = (u ^ (N ^ 2))⁻¹ := fun u => by
    rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
  have e₁ : g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a * (g * r) ^ (N ^ 2) = g * (a * r ^ (N ^ 2)) := by
    rw [hz, zpow_one, mul_pow]
    calc g * (g ^ (N ^ 2))⁻¹ * a * (g ^ (N ^ 2) * r ^ (N ^ 2))
        = g * (a * r ^ (N ^ 2)) * ((g ^ (N ^ 2))⁻¹ * g ^ (N ^ 2)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, _root_.mul_one]
  have e₂ : ((g' ^ (n : ℤ)) ^ (N ^ 2)) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v) ^ n = g ^ n * v ^ n := by
    rw [hz, zpow_one, zpow_natCast, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n]
    calc g' ^ (N ^ 2 * n) * (g ^ n * (g' ^ (N ^ 2 * n))⁻¹ * v ^ n)
        = g ^ n * v ^ n * (g' ^ (N ^ 2 * n) * (g' ^ (N ^ 2 * n))⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, _root_.mul_one]
  have l : (g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2) = g.val * (a.val * r.val ^ (N ^ 2)) := by
    have := congrArg Units.val e₁
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have m : (g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n = g.val ^ n * v.val ^ n := by
    have := congrArg Units.val e₂
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  rw [l] at h
  apply (g ^ n).isUnit.mul_right_inj.1
  simp only [Units.val_pow_eq_pow_val]
  calc g.val ^ n * (t * (a.val * r.val ^ (N ^ 2)) ^ n)
      = t * (g.val * (a.val * r.val ^ (N ^ 2))) ^ n := by rw [mul_pow g.val]; ring
    _ = _ := h
    _ = ((g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) * s ^ (N ^ 2) := by
        rw [mul_pow (g' ^ (n : ℤ)).val]; ring
    _ = g.val ^ n * v.val ^ n * s ^ (N ^ 2) := by rw [m]
    _ = _ := by ring

variable {F : Type} [Field F] {X S : Scheme.{0}}

theorem charts {L : LB X} {q : X ⟶ X} {e : S ⟶ X} {b : Sp F ⟶ S} {o y : Sp F ⟶ X}
    (hbe : b ≫ e = o) (hoq : o ≫ q = o) (hyq : y ≫ q = o) {n N : ℕ}
    (w : LB.Gen (LB.LinComb L (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => 1))) (hr : rig.IsGen)
    (s : Out.H0 L n) (T : F) (i₀ i : L.ι) (h₀ : ⊤ ≤ o ⁻¹ᵁ L.U i₀) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i)
    (hE : T * (valF o _ (w.s ![i₀, i₀]).val * valF b _ (rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y _ (s.f fun _ => i) ^ (N ^ 2) * valF y _ (w.s ![i₀, i]).val ^ n)
    (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z T * ((val w o z J).val * (val rig b z J).val ^ (N ^ 2)) ^ n =
      sval s y z J ^ (N ^ 2) * (val w y z J).val ^ n := by
  have m₀ : o z ∈ L.U i₀ := (top_le_iff_mem _ _ z).1 h₀
  have mi : y z ∈ L.U i := (top_le_iff_mem _ _ z).1 hi
  have mo : o z ∈ L.U (J o) := hJ o
  have my : y z ∈ L.U (J y) := hJ y
  have wm : ∀ (r : Sp F ⟶ X), r ≫ q = o → ∀ a c : L.ι, o z ∈ L.U a → r z ∈ L.U c →
      r z ∈ LB.wchart L (K := Fin 2) ![q, 𝟙 X] ![a, c] := by
    intro r hr' a c ha hc
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show q (r z) ∈ L.U a
      have : q (r z) = o z := by rw [← hr']; rfl
      rw [this]; exact ha
    · exact hc
  have rm : ∀ a : L.ι, o z ∈ L.U a → b z ∈ LB.wchart L (K := PUnit) (fun _ => e) (fun _ => a) := by
    intro a ha
    refine Set.mem_iInter.2 fun _ => ?_
    show e (b z) ∈ L.U a
    have : e (b z) = o z := by rw [← hbe]; rfl
    rw [this]; exact ha
  have sm : ∀ a : L.ι, y z ∈ L.U a → y z ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a) :=
    fun a ha => Set.mem_iInter.2 fun _ => ha
  have a₁ : toStk z (valF o _ (w.s ![i₀, i₀]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] *
        gm o z (LB.wchart L ![q, 𝟙 X] ![J o, J o]) (w.s ![J o, J o])).val :=
    (toStk_valF o _ z (wm o hoq _ _ m₀ m₀) _).trans
      (congrArg Units.val (gen_trans hw o z (wm o hoq _ _ m₀ m₀) (wm o hoq (J o) (J o) mo mo)))
  have a₂ : toStk z (valF b _ (rig.s fun _ => i₀).val) =
      (trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) *
        gm b z (LB.wchart L (fun _ => e) (fun _ => J o)) (rig.s fun _ => J o)).val :=
    (toStk_valF b _ z (rm _ m₀) _).trans (congrArg Units.val (gen_trans hr b z (rm _ m₀) (rm (J o) mo)))
  have a₃ : toStk z (valF y _ (s.f fun _ => i)) =
      (trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y)).val *
        gs y z (LB.wchart L (fun _ => 𝟙 X) (fun _ => J y)) (s.f fun _ => J y) :=
    (GlobalTheory.ThetaInValues.toStk_valF' y _ z (sm _ mi) _).trans (sec_trans s y z (sm _ mi) (sm (J y) my))
  have a₄ : toStk z (valF y _ (w.s ![i₀, i]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] *
        gm y z (LB.wchart L ![q, 𝟙 X] ![J o, J y]) (w.s ![J o, J y])).val :=
    (toStk_valF y _ z (wm y hyq _ _ m₀ mi) _).trans
      (congrArg Units.val (gen_trans hw y z (wm y hyq _ _ m₀ mi) (wm y hyq (J o) (J y) mo my)))
  have hE' := congrArg (toStk z) hE
  simp only [map_mul, map_pow] at hE'
  rw [a₁, a₂, a₃, a₄] at hE'
  have f₁ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm o z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (o ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (o ≫ 𝟙 X) z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hoq, Category.comp_id]
  have f₂ : trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) =
      gm o z _ (L.g i₀ (J o)) := by
    rw [trF, Fintype.prod_unique]
    show gm (b ≫ e) z _ (L.g i₀ (J o)) ^ (1 : ℤ) = _
    rw [hbe, zpow_one]
  have f₃ : trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y) =
      gm y z _ (L.g i (J y)) ^ (n : ℤ) := by
    rw [trF, Fintype.prod_unique]
    show gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (n : ℤ) = _
    rw [Category.comp_id]
  have f₄ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm y z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (y ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hyq, Category.comp_id]
  rw [f₁, f₂, f₃, f₄] at hE'
  rw [val_of w o z J ![J o, J o] (Fin.forall_fin_two.2 ⟨congrArg J hoq, congrArg J (Category.comp_id _)⟩),
    val_of rig b z J (fun _ => J o) (fun _ => congrArg J hbe),
    sval_of s y z J (fun _ => J y) (fun _ => congrArg J (Category.comp_id _)),
    val_of w y z J ![J o, J y] (Fin.forall_fin_two.2 ⟨congrArg J hyq, congrArg J (Category.comp_id _)⟩)]
  exact alg _ _ _ _ _ _ _ N n hE'

end GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem torsVal_charts : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  intro S G _ _ P n s F _ b y N T hT z J hJ
  obtain ⟨-, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  have key : ∀ t : Over.mk b ⟶ G, t ^ N = 1 →
      t.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    intro t ht
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ht]
  have hbe : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl
  refine ⟨w, hw, TorsChart.charts (e := eSec G) hbe (key 1 (one_pow N)) (key y hy) w hw P.rig P.rigGen
    s T i₀ i h₀ hi hE z J hJ⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_value_frame_domain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | exact GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | (intros; apply GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_lie_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieTransport.main | exact GlobalTheory.CompanionTheory.Ar.LieTransport.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieTransport.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesIdentityPowerRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem values_units_identity {G : Type*} [CommGroup G] (m N : ℕ)
    (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : G)
    (h3 : A = bo * (bz ^ (N ^ 2))⁻¹ * Wy)
    (h4 : B = bo * (bo ^ (N ^ 2))⁻¹ * Wo)
    (h5 : R = bo * R')
    (h7 : Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ =
      Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹)
    (h8 : Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2))
    (h9 : u0 = e0 * (R ^ (m ^ 2))⁻¹)
    (h10 : e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1) :
    (Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2) * bz ^ (m ^ 2 * (N * m) ^ 2) =
      Wk1 * R ^ ((N * m) ^ 2) * Wkz⁻¹ * (up ^ ((N * m) ^ 2))⁻¹ * Wy ^ ((m ^ 2) ^ 2) := by
  apply Additive.ofMul.injective
  have e3 := congrArg Additive.ofMul h3
  have e4 := congrArg Additive.ofMul h4
  have e5 := congrArg Additive.ofMul h5
  have e7 := congrArg Additive.ofMul h7
  have e8 := congrArg Additive.ofMul h8
  have e9 := congrArg Additive.ofMul h9
  have e10 := congrArg Additive.ofMul h10
  first
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, ← natCast_zsmul, Nat.cast_pow,
          Nat.cast_mul] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)

theorem values_cancel_of_unit_identity {C : Type*} [CommRing C] (T2 T' s t D : C) (X Z Y V c K : Cˣ)
    (a : T2 * (X : C) = s * (Y : C)) (b : (Z : C) * s = D * (t * (V : C)))
    (c1 : T' * (c : C) = t * (K : C)) (hU : X * Z = c * K⁻¹ * V * Y) :
    T2 = D * T' := by
  have hU' : (X : C) * (Z : C) = (c : C) * ((K⁻¹ : Cˣ) : C) * (V : C) * (Y : C) := by
    simpa only [Units.val_mul] using congrArg Units.val hU
  have hK : ((K⁻¹ : Cˣ) : C) * (K : C) = 1 := Units.inv_mul K
  refine (Units.mul_left_inj (X * Z)).mp ?_
  rw [Units.val_mul]
  linear_combination (Z : C) * a + (Y : C) * b - D * T' * hU'
    - D * (V : C) * (Y : C) * ((K⁻¹ : Cˣ) : C) * c1 - D * t * (V : C) * (Y : C) * hK

theorem values_identity_units : ∀ {C : Type} [CommRing C] (m N : ℕ) (T T' th sv d : C) (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : Cˣ), T' * ((Wk1 : C) * (R : C) ^ ((N * m) ^ 2)) = th ^ ((N * m) ^ 2) * (Wkz : C) → T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2) = sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2) → A = bo * (bz ^ (N ^ 2))⁻¹ * Wy → B = bo * (bo ^ (N ^ 2))⁻¹ * Wo → R = bo * R' → ((bz ^ (m ^ 2) : Cˣ) : C) * sv = d * (th * ((up⁻¹ : Cˣ) : C)) → Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ = Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹ → Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2) → u0 = e0 * (R ^ (m ^ 2))⁻¹ → e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1 → T ^ (m ^ 2) = d ^ ((N * m) ^ 2) * T' := by
  intro C _ m N T T' th sv d Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz e1 e2 h3 h4 h5 e6 h7
    h8 h9 h10
  have hU := GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_units_identity m N Wk1 Wkz Wkx Wm1 Wmx A B up u0
    e0 R R' Wo Wy bo bz h3 h4 h5 h7 h8 h9 h10
  rw [← inv_pow] at hU
  have e2' : (T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2)) ^ (m ^ 2) =
      (sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2)) ^ (m ^ 2) := by rw [e2]
  have e6' : (((bz ^ (m ^ 2) : Cˣ) : C) * sv) ^ ((N * m) ^ 2) =
      (d * (th * ((up⁻¹ : Cˣ) : C))) ^ ((N * m) ^ 2) := by rw [e6]
  refine GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_cancel_of_unit_identity (T ^ (m ^ 2)) T' (sv ^ ((N * m) ^ 2))
    (th ^ ((N * m) ^ 2)) (d ^ ((N * m) ^ 2)) ((Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2))
    (bz ^ (m ^ 2 * (N * m) ^ 2)) (Wy ^ ((m ^ 2) ^ 2)) (up⁻¹ ^ ((N * m) ^ 2))
    (Wk1 * R ^ ((N * m) ^ 2)) Wkz ?_ ?_ ?_ hU
  · push_cast at e2' ⊢
    linear_combination e2'
  · push_cast at e6' ⊢
    linear_combination e6'
  · push_cast
    exact e1

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end

