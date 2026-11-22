import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicNormLeOneIffValuation
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
open scoped NNReal

namespace GlobalTheory.PlaceNorm

theorem norm_le_one_iff_valuation_le_one :
    ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR)
      (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]),
      (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) →
      ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  intro K _ _ la p _ T io e ho k kO hk a
  obtain ⟨r, hr⟩ := GlobalTheory.CompHt.exists_log_eq (PadicComplexInt.integers p) k kO hk
  have hnorm : ∀ x : ℂ_[p], ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := GlobalTheory.FlatModel.coe_valued p
  have hpne : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp0 : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hpne

  have hpv : 0 ≤ vV T.V (p : T.Fr) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (p : T.V)
    have h1' : valV T.V (p : T.Fr) ≤ 1 := by
      rw [← map_natCast (algebraMap T.V T.Fr)]; exact h1
    have h2 : valV T.V (p : T.Fr) ≠ 0 := valV_ne_zero hp0
    have h3 := (WithZero.log_le_log h2 one_ne_zero).2 h1'
    rw [WithZero.log_one] at h3
    simp only [vV]; omega

  have h1 := hr (p : T.Fr) hp0
  rw [map_natCast, hnorm] at h1
  have hpn : ‖(p : ℂ_[p])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hpos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hpne)
  have hl : Real.log ‖(p : ℂ_[p])‖ < 0 := Real.log_neg hpos hpn
  have hr0 : r < 0 := by
    rw [h1] at hl
    by_contra hc
    push_neg at hc
    have : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) * r := mul_nonneg (by exact_mod_cast hpv) hc
    linarith
  by_cases ha : a = 0
  · subst ha; simp
  have hx : io a ≠ 0 := (map_ne_zero io).2 ha
  have hk0 : k (io a) ≠ 0 := (map_ne_zero k).2 hx
  have h2 := hr (io a) hx
  rw [hnorm, ho.2 a] at h2
  have hva : la.valuation K a ≠ 0 := (la.valuation K).ne_zero_iff.2 ha
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  rw [← Real.log_nonpos_iff (norm_nonneg _), h2, ← WithZero.log_le_log hva one_ne_zero, WithZero.log_one]
  have hv : vLa la a = -WithZero.log (la.valuation K a) := rfl
  push_cast
  constructor
  · intro h
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := by nlinarith
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by
      by_contra hc; push_neg at hc; nlinarith
    have h5 : (0 : ℤ) ≤ vLa la a := by exact_mod_cast h4
    omega
  · intro h
    have h5 : (0 : ℤ) ≤ vLa la a := by omega
    have h4 : (0 : ℝ) ≤ (vLa la a : ℝ) := by exact_mod_cast h5
    have h3 : 0 ≤ (e : ℝ) * (vLa la a : ℝ) := mul_nonneg he.le h4
    nlinarith

end GlobalTheory.PlaceNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPairingApproximation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.HTCong

theorem norm_natp (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  rw [e, norm_algebraMap', Padic.norm_p]

theorem norm_le_of_mem_span (p : ℕ) [Fact p.Prime] (n : ℕ) (z : 𝓞_ℂ_[p])
    (hz : z ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) : ‖(z : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hw : ‖(w : ℂ_[p])‖ ≤ 1 := (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 w.2
  push_cast
  rw [norm_mul, norm_pow, norm_natp]
  exact mul_le_of_le_one_left (by positivity) hw

end GlobalTheory.FlatModel.HTCong

namespace GlobalTheory.FlatModel.HTCong

theorem pair_comb_congr : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  intro E _ _ p _ _ P n N g J ta x h Tc U hh i
  have key : P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) =
      ((∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    have e1 : ∀ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m = (Tc i m : ℂ_[p]) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) := by
      intro m; rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [e1, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, P.pairV_bLie, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    have ha : ∀ z : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] z = (z : ℂ_[p]) := fun _ => rfl
    simp only [ha]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [key, ← AddSubgroupClass.coe_sub]
  refine norm_le_of_mem_span p n _ ?_
  have e2 : (∑ b, (∑ a, Tc i a * h a b) * U b) - (∑ b, (∑ a, Tc i a * (P.al₀ (ta a)).1 (x b)) * U b) =
      ∑ b, ∑ a, (Tc i a * U b) * (h a b - (P.al₀ (ta a)).1 (x b)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e2]
  exact Ideal.sum_mem _ fun b _ => Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hh a b)

end GlobalTheory.FlatModel.HTCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLevelPower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatModel

theorem tateIso_transport_ptOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hl yb yy P π ψ hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : KA l' →+* ℂ_[p], yy ≫ (pullback.fst _ _ ≫ Xo'.s) = spMap β₀ :=
    ⟨(Spec.preimage (yy ≫ (pullback.fst _ _ ≫ Xo'.s))).hom, by simp [spMap]⟩
  obtain ⟨-, I, -, hI, -⟩ := Y.oF.geom ℂ_[p] yy β₀ hβ₀
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h4 (Over.mk (𝟙 _)) yy (Category.id_comp _).symm
  have hact : ∀ o : 𝓞 E, (P.oA.act o).left ≫ ψ = ψ ≫ (Y.oF.t.act.act o).left := by
    intro o
    apply Y.m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, h5, Y.m.act o, ← Category.assoc ψ, h5, ← Category.assoc, P.gen_act o,
        Category.assoc, Category.assoc, h3 o]
    · rw [Category.assoc, Category.assoc, Over.w (Y.oF.t.act.act o), h4.1.w, ← Category.assoc, Over.w]
  have hlin : ∀ (x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (o : 𝓞 E), e (x ≫ P.oA.act o) = e x ≫ Y.oF.t.act.act o := by
    intro x o
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hact]
  have hsymm : ∀ y : Over.mk yy ⟶ Y.oF.t.G, (e.symm y).left ≫ ψ = y.left := fun y => by
    rw [← he, MulEquiv.apply_symm_apply]
  have hweil : ∀ (g : Sp ℂ_[p] ⟶ Xo'.XF c'), 𝟙 _ ≫ yy = g → ∀ (k : ℤ) (x y : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)
      (x₀ y₀ : Over.mk g ⟶ Y.oF.t.G) (c : (Γ(Sp ℂ_[p], ⊤))ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      (Out.WeilIs P.A.A P.A.L k x y c ↔ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L k x₀ y₀ c) := by
    rintro g rfl k x y x₀ y₀ c hx hy
    exact GlobalTheory.weilIs_grpPullback_of_comm _ _ Y.oF.t.G P.A.A yy ψ Y.oF.t.PP.L P.A.L Y.oF.t.PP.isLB P.A.isLB h4 h6
      (Over.mk (𝟙 _)) k x y x₀ y₀ c hx hy
  have onto : ∀ k, 0 < k → ∀ x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A, x ^ k = 1 ↔ ∃ a, e.symm (I.ev k a) = x := by
    intro k hk x
    rw [← e.injective.eq_iff, map_pow, map_one, I.onto k hk]
    simp only [MulEquiv.symm_apply_eq]
  refine ⟨fun k a => e.symm (I.ev k a), I.ζ, I.ζ_prim, I.ζ_pow, ?_, ?_, onto, ?_, ?_, ?_⟩
  · intro k a b
    simp only [I.add, map_mul]
  · intro k o a
    apply e.injective
    rw [hlin, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact I.lin k o a
  · intro k m hk hm a
    simp only [← map_pow, I.tower k m hk hm a]
  · intro k hk a b
    have hza : (e.symm (I.ev k a)) ^ k = 1 := (onto k hk _).2 ⟨a, rfl⟩
    have hzb : (e.symm (I.ev k b)) ^ k = 1 := (onto k hk _).2 ⟨b, rfl⟩
    refine ((GlobalTheory.HTLat.weilIs_iff (A := P.A) (Nat.one_le_iff_ne_zero.2 hk.ne') hza hzb _).1 ?_).symm
    rw [hweil yy (Category.id_comp yy) _ _ _ (I.ev k a) (I.ev k b) _ (hsymm _).symm (hsymm _).symm]
    exact I.isom k hk a b
  · intro a
    rw [hsymm, ← hl, ← hI a, Over.comp_left]
    congr 1

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPairingCompatible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {G : Over X} [GrpObj G] {yb : Sp O ⟶ X} {π : P.G.left ⟶ G.left}

theorem hom_ext_pb (hπ : IsGrpPullback P.G G yb π) {R : Type} [CommRing R] [Algebra O R]
    {f g : specO O R ⟶ P.G} (h : f.left ≫ π = g.left ≫ π) : f = g :=
  Over.OverMorphism.ext (hπ.1.hom_ext h ((Over.w f).trans (Over.w g).symm))

theorem exists_lift (hπ : IsGrpPullback P.G G yb π) {R : Type} [CommRing R] [Algebra O R]
    (u : Sp R ⟶ G.left) (hu : u ≫ G.hom = spMap (algebraMap O R) ≫ yb) :
    ∃ f : specO O R ⟶ P.G, f.left ≫ π = u :=
  ⟨Over.homMk (hπ.1.lift u (spMap (algebraMap O R)) hu) (hπ.1.lift_snd _ _ hu), hπ.1.lift_fst _ _ hu⟩

theorem one_left_comp (hπ : IsGrpPullback P.G G yb π) (T : Over (Sp O)) :
    (1 : T ⟶ P.G).left ≫ π = (1 : Over.mk (T.hom ≫ yb) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ yb) ⟶ G := Over.homMk ((1 : T ⟶ P.G).left ≫ π) (by
    rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hπ.2 T 1 1 x₀ x₀ rfl rfl
  have h2 : x₀ * x₀ = x₀ := by
    ext1
    rw [h, _root_.mul_one]
    rfl
  have h3 : (x₀ : Over.mk (T.hom ≫ yb) ⟶ G) = 1 := mul_eq_left.1 h2
  exact congrArg (fun f : Over.mk (T.hom ≫ yb) ⟶ G => f.left) h3

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {yb : Sp O ⟶ X}

theorem one_left_mk {G : Over X} [GrpObj G] {π : P.G.left ⟶ G.left} (hπ : IsGrpPullback P.G G yb π) :
    (1 : specO O O ⟶ P.G).left ≫ π = (1 : Over.mk yb ⟶ G).left := by
  rw [one_left_comp hπ (specO O O)]
  change ((specO O O).hom ≫ yb) ≫ _ = yb ≫ _
  rw [show (specO O O).hom = 𝟙 _ from ?_, Category.id_comp]
  change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {t : SAB H X}
  {π : P.G.left ⟶ t.G.left}

theorem tan_lift (hπ : IsGrpPullback P.G t.G yb π) {u : Sp (DualNumber O) ⟶ t.G.left} (hu : IsTanAtG t yb u) :
    ∃ xG : LieG P.G, xG.1.left ≫ π = u := by
  obtain ⟨f, hf⟩ := exists_lift hπ u hu.1
  refine ⟨⟨f, hom_ext_pb hπ ?_⟩, hf⟩
  rw [Over.comp_left, Category.assoc, hf]
  exact hu.2.trans (one_left_mk hπ).symm

theorem tan_of_lie (hπ : IsGrpPullback P.G t.G yb π) (xG : LieG P.G) : IsTanAtG t yb (xG.1.left ≫ π) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w]
    rfl
  · rw [← Category.assoc, ← one_left_mk hπ]
    change (ptMap (TrivSqZeroExt.fstHom O O O) ≫ xG.1).left ≫ π = _
    rw [xG.2]
    rfl

end Tan

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem corr_left_unique {x x' : specO O (DualNumber O) ⟶ P.Gt} {y : specO O (DualNumber O) ⟶ P.G}
    (h : Corr P x y) (h' : Corr P x' y) : x = x' := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h =>
    (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  exact (existsUnique_left hp (isAdicComplete_dualNumber p) y).unique h h'

theorem corr_right_unique {x : specO O (DualNumber O) ⟶ P.Gt} {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : Corr P x y) (h' : Corr P x y') : y = y' := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h =>
    (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  exact (existsUnique_right hp (isAdicComplete_dualNumber p) x).unique h h'

theorem exists_corr_left (xG : LieG P.G) : ∃ x : LieG P.Gt, Corr P x.1 xG.1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  obtain ⟨x, hx, -⟩ := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p) xG.1
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hx⟩
  have h := hx.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h
  exact h

theorem exists_corr_right (x : LieG P.Gt) : ∃ xG : LieG P.G, Corr P x.1 xG.1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  obtain ⟨y, hy, -⟩ := existsUnique_right (P := P) hp (isAdicComplete_dualNumber p) x.1
  refine ⟨⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hy⟩
  have h := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [x.2] at h
  exact h

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {yb : Sp O ⟶ X}

theorem prod_left_comp {G : Over X} [GrpObj G] {π : P.G.left ⟶ G.left} (hπ : IsGrpPullback P.G G yb π)
    {T : Over (Sp O)} : ∀ {m : ℕ} (ws : Fin m → (T ⟶ P.G)) (w : Fin m → (Over.mk (T.hom ≫ yb) ⟶ G)),
      (∀ i, (w i).left = (ws i).left ≫ π) → ((List.ofFn w).prod).left = ((List.ofFn ws).prod).left ≫ π
  | 0, _, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact (one_left_comp hπ T).symm
  | m + 1, ws, w, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact hπ.2 T _ _ _ _ (h 0) (prod_left_comp hπ (fun i => ws i.succ) (fun i => w i.succ) fun i => h i.succ)

theorem corr_prod {R : Type} [CommRing R] [Algebra O R] : ∀ {m : ℕ} (xs : Fin m → (specO O R ⟶ P.Gt))
    (ys : Fin m → (specO O R ⟶ P.G)), (∀ i, Corr P (xs i) (ys i)) → Corr P (List.ofFn xs).prod (List.ofFn ys).prod
  | 0, _, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact Corr.one
  | m + 1, xs, ys, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (h 0).mul (corr_prod (fun i => xs i.succ) (fun i => ys i.succ) fun i => h i.succ)

noncomputable def combLie (G : Over (Sp O)) [GrpObj G] : ∀ m : ℕ, (Fin m → O) → (Fin m → LieG G) → LieG G
  | 0, _, _ => lieZero G
  | m + 1, cf, xs => lieAdd (AvDefs.lieScale G (cf 0) (xs 0)) (combLie G m (fun i => cf i.succ) fun i => xs i.succ)

theorem combLie_val (G : Over (Sp O)) [GrpObj G] : ∀ (m : ℕ) (cf : Fin m → O) (xs : Fin m → LieG G),
    (combLie G m cf xs).1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xs i).1).prod
  | 0, _, _ => rfl
  | m + 1, cf, xs => by
    rw [List.ofFn_succ, List.prod_cons, ← combLie_val G m]
    rfl

theorem bLie_combLie {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PtP E p) :
    ∀ (m : ℕ) (cf : Fin m → 𝓞_ℂ_[p]) (xs : Fin m → LieG P.Gt),
      P.bLie (combLie P.Gt m cf xs) = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)
  | 0, _, _ => by simp [combLie, P.bLie_zero]
  | m + 1, cf, xs => by
    rw [combLie, P.bLie_add, P.bLie_scale, bLie_combLie P m, Fin.sum_univ_succ]
    congr 1

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel

open RetractionModules in

theorem tanTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    (∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃! x : LieG P.Gt, ITie P π x u) ∧
    (∀ x : LieG P.Gt, ∃ u, IsTanAtG Y.t yb u ∧ ITie P π x u) ∧
    (∀ (m : ℕ) (v : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (xs : Fin m → LieG P.Gt) (cf : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left) (x : LieG P.Gt), (∀ i, IsTanAtG Y.t yb (v i)) →
      (∀ i, ITie P π (xs i) (v i)) → IsCombAtG Y.t yb v cf u → ITie P π x u →
      P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)) ∧
    ∀ (σ : 𝓞 E →+* 𝓞_ℂ_[p]) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), IsTanAtG Y.t yb u →
      ITie P π x u → (IsEigG Y.t σ u ↔ AvDefs.IsEig P.Gt P.oGt σ x) := by
  intro E _ _ _ H Dw p _ _ l' Xo' c' W Y yb yy P π ψ hP
  have hπ := hP.2.1
  refine ⟨fun u hu => ?_, fun x => ?_, fun m vv xs cf u x _ hxs hu hx => ?_, fun σ x u _ hx => ?_⟩
  · obtain ⟨xG, hxG⟩ := tan_lift hπ hu
    obtain ⟨x, hx⟩ := exists_corr_left xG
    refine ⟨x, ⟨xG, hx, hxG⟩, fun x' hx' => ?_⟩
    obtain ⟨xG', hc', hxG'⟩ := hx'
    have e : xG'.1 = xG.1 := hom_ext_pb hπ (hxG'.trans hxG.symm)
    rw [e] at hc'
    exact Subtype.ext (corr_left_unique hc' hx)
  · obtain ⟨xG, hx⟩ := exists_corr_right x
    exact ⟨xG.1.left ≫ π, tan_of_lie hπ xG, xG, hx, rfl⟩
  · choose xG hxc hxG using hxs
    obtain ⟨w, hw, hwu⟩ := hu
    obtain ⟨yG, hyc, hyG⟩ := hx
    have h1 : ((List.ofFn w).prod).left =
        ((List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod).left ≫ π :=
      prod_left_comp hπ (T := specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]))
        (fun i => ptMap (dualScale (cf i)) ≫ (xG i).1) w fun i => by
        rw [hw i, Over.comp_left, Category.assoc, hxG i]
        rfl
    have h2 : yG.1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod :=
      hom_ext_pb hπ (hyG.trans (hwu.symm.trans h1))
    have h3 : Corr P (combLie P.Gt m cf xs).1 yG.1 := by
      rw [combLie_val, h2]
      exact corr_prod _ _ fun i => (hxc i).comp (dualScale (cf i))
    have h4 : x = combLie P.Gt m cf xs := Subtype.ext (corr_left_unique hyc h3)
    rw [h4, bLie_combLie]
  · obtain ⟨xG, hxc, hxG⟩ := hx
    have hact : ∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left := hP.2.2.1
    have tA : ∀ a, (xG.1 ≫ P.oG.act a).left ≫ π = u ≫ (Y.t.act.act a).left := fun a => by
      rw [Over.comp_left, Category.assoc, hact, ← Category.assoc, hxG]
    have tS : ∀ a, (ptMap (dualScale (σ a)) ≫ xG.1).left ≫ π = spMap (epsMul (σ a)) ≫ u := fun a => by
      rw [Over.comp_left, Category.assoc, hxG]
      rfl
    have cA : ∀ a, Corr P (AvDefs.lieAct P.Gt P.oGt a x).1 (xG.1 ≫ P.oG.act a) := fun a => corr_act hxc a
    have cS : ∀ a, Corr P (AvDefs.lieScale P.Gt (σ a) x).1 (ptMap (dualScale (σ a)) ≫ xG.1) := fun a =>
      hxc.comp _
    constructor
    · intro h a
      have e := hom_ext_pb hπ ((tA a).trans ((h a).trans (tS a).symm))
      have c2 := cA a
      rw [e] at c2
      exact Subtype.ext (corr_left_unique c2 (cS a))
    · intro h a
      have c2 := cS a
      rw [← h a] at c2
      have e := corr_right_unique (cA a) c2
      rw [← tA a, ← tS a, e]

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhdsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open MeasureTheory Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  first | exact @GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | exact GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds | (intros; apply GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_decay_vacuum : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @GlobalTheory.SoPureThetaCont.continuous_I_pure | exact GlobalTheory.SoPureThetaCont.continuous_I_pure | (intros; apply GlobalTheory.SoPureThetaCont.continuous_I_pure <;> assumption)
end

