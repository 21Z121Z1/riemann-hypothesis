import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoisoCount

open Matrix

theorem vecMul_eq_zero_of_rows_li {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : LinearIndependent K (fun i => X i)) (y : m → K)
    (hy : y ᵥ* X = 0) : y = 0 := by
  rw [Fintype.linearIndependent_iff] at h
  funext i; exact h y (by rw [← vecMul_eq_sum]; exact hy) i

theorem rows_li_of_vecMul {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) :
    LinearIndependent K (fun i => X i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [h g (by rw [vecMul_eq_sum]; exact hg)]; rfl

theorem det_gram_ne_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] (X : Matrix m n K)
    (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) : (X * Xᵀ).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hd
  apply hy0; apply h
  apply dotProduct_self_eq_zero.1
  have : (y ᵥ* X) ⬝ᵥ (y ᵥ* X) = y ⬝ᵥ (X *ᵥ (y ᵥ* X)) := by rw [dotProduct_mulVec]
  rw [this, ← vecMul_transpose, vecMul_vecMul, hy, dotProduct_zero]

theorem gram_map {K : Type*} [CommRing K] {m n : Type*} [Fintype n] (Z : Matrix m n ℤ) :
    Z.map (Int.cast : ℤ → K) * (Z.map (Int.cast : ℤ → K))ᵀ = (Z * Zᵀ).map (Int.cast : ℤ → K) := by
  ext i j; simp [Matrix.mul_apply]

theorem det_map_intCast {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) : (Z.map (Int.cast : ℤ → K)).det = (Z.det : K) := by
  have := RingHom.map_det (Int.castRingHom K) Z
  simpa using this.symm

theorem rank_bound {r r₀ : ℕ} (P : Matrix (Fin r₀) (Fin r₀) ℤ)
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ x ∈ S, P.map (Int.cast : ℤ → ZMod N) *ᵥ x = 0) :
    r + (P.map (Int.cast : ℤ → ℝ)).rank ≤ 2 * r₀ := by
  classical
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' ℝ (fun k => Pr k)
  haveI : Finite κ := Finite.of_injective c hc
  letI : Fintype κ := Fintype.ofFinite κ
  have hρ : Pr.rank = Nat.card κ := by
    rw [Matrix.rank_eq_finrank_span_row, Nat.card_eq_fintype_card, ← finrank_span_eq_card hli, hsp]; rfl
  set R : Matrix κ (Fin r₀) ℤ := P.submatrix c id with hR
  have hRr : ∀ y : κ → ℝ, y ᵥ* R.map (Int.cast : ℤ → ℝ) = 0 → y = 0 :=
    vecMul_eq_zero_of_rows_li _ hli
  have hd0 : (R * Rᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero _ hRr
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  set d := (R * Rᵀ).det
  set N := d.natAbs + 1 with hN
  have hN2 : 2 ≤ N := by have := Int.natAbs_pos.2 hd0; omega
  haveI : NeZero N := ⟨by omega⟩
  have hu : IsUnit (d : ZMod N) := by
    have h1 : ((d.natAbs : ℕ) : ZMod N) = -1 := by
      have : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
      rw [hN] at this; push_cast at this; exact eq_neg_of_add_eq_zero_left this
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast, h1]; exact isUnit_one.neg
    · rw [h, Int.cast_neg, Int.cast_natCast, h1, neg_neg]; exact isUnit_one
  obtain ⟨S, hcard, hSk⟩ := hS N (by omega)
  set RN := R.map (Int.cast : ℤ → ZMod N) with hRN
  let f : (Fin r₀ → ZMod N) →+ (κ → ZMod N) := RN.mulVecLin.toAddMonoidHom
  have hsurj : Function.Surjective f := by
    intro z
    have hG : IsUnit (RN * RNᵀ).det := by rw [hRN, gram_map, det_map_intCast]; exact hu
    refine ⟨RNᵀ *ᵥ ((RN * RNᵀ)⁻¹ *ᵥ z), ?_⟩
    show RN *ᵥ (RNᵀ *ᵥ _) = z
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, one_mulVec]
  have hkc : Nat.card f.ker * N ^ Nat.card κ = N ^ r₀ := by
    have h1 := f.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
      Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r₀),
      Fintype.card_fin] at h1
    exact h1
  have hsub : S ⊆ (f.ker : Set (Fin r₀ → ZMod N)) := by
    intro x hx
    show RN *ᵥ x = 0
    funext k
    have := congrFun (hSk x hx) (c k)
    exact this
  have hle : Nat.card S ≤ Nat.card f.ker := Nat.card_mono (Set.toFinite _) hsub
  have key : N ^ r * N ^ Nat.card κ ≤ N ^ r₀ * N ^ r₀ := by
    rw [← hcard, ← hkc, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hle)
  rw [← pow_add, ← pow_add] at key
  have := (Nat.pow_le_pow_iff_right hN2).1 key
  rw [hρ]; omega

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem ker_le_span {r r₀ : ℕ} (Mr : Matrix (Fin r) (Fin r) ℝ) (Ar : Matrix (Fin r₀) (Fin r) ℝ)
    (hM : IsUnit Mr.det) (hA : LinearIndependent ℝ (fun i => Ar i))
    (hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀) :
    LinearMap.ker (Ar * Mrᵀ).mulVecLin ≤ Submodule.span ℝ (Set.range fun i => Ar i) := by
  set T := (Ar * Mrᵀ).mulVecLin
  set E := Arᵀ.mulVecLin
  have hE : Function.Injective E := by
    intro x y hxy
    have : (x - y) ᵥ* Ar = 0 := by
      rw [sub_vecMul, ← mulVec_transpose, ← mulVec_transpose]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (vecMul_eq_zero_of_rows_li _ hA _ this)
  have hrE : LinearMap.range E = Submodule.span ℝ (Set.range fun i => Ar i) := by
    rw [Matrix.range_mulVecLin]; rfl
  have hAr : Ar.rank = r₀ := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => Ar i)) = r₀
    rw [finrank_span_eq_card hA, Fintype.card_fin]
  have hT : Module.finrank ℝ (LinearMap.range T) = r₀ := by
    change (Ar * Mrᵀ).rank = r₀
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]), hAr]
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ E)
  have hQ : Module.finrank ℝ (LinearMap.range (T ∘ₗ E)) = (Ar * Mrᵀ * Arᵀ).rank := by
    rw [Matrix.rank, Matrix.mulVecLin_mul]
  have hmap : Submodule.map E (LinearMap.ker (T ∘ₗ E)) = LinearMap.range E ⊓ LinearMap.ker T := by
    rw [LinearMap.ker_comp, Submodule.map_comap_eq]
  have h3 : Module.finrank ℝ (LinearMap.range E ⊓ LinearMap.ker T : Submodule ℝ (Fin r → ℝ)) =
      Module.finrank ℝ (LinearMap.ker (T ∘ₗ E)) := by
    rw [← hmap]; exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE _)).symm
  rw [Module.finrank_fin_fun] at h1 h2
  have heq := Submodule.eq_of_le_of_finrank_le
    (inf_le_right : LinearMap.range E ⊓ LinearMap.ker T ≤ LinearMap.ker T) (by omega)
  rw [← hrE, ← heq]; exact inf_le_left

theorem gramQ {r r₀ : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ) :
    (Matrix.of fun i j => (A i j : ℝ)) * (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun i j => (A i j : ℝ))ᵀ
      = (Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k).map (Int.cast : ℤ → ℝ) := by
  ext i k
  simp [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem coisotropic_of_torsion_count (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ)
    (A : Fin r₀ → Fin r → ℤ) (hM : M.det ≠ 0)
    (hA : LinearIndependent ℚ (fun i j => (A i j : ℚ)))
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i))
    (v : Fin r → ℝ)
    (hv : ∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) :
    v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  classical
  set Ar : Matrix (Fin r₀) (Fin r) ℝ := Matrix.of fun i j => (A i j : ℝ) with hAr
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set P : Matrix (Fin r₀) (Fin r₀) ℤ := Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k with hP
  have hAz : ((Matrix.of A) * (Matrix.of A)ᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero ((Matrix.of A).map (Int.cast : ℤ → ℚ))
      (vecMul_eq_zero_of_rows_li ((Matrix.of A).map (Int.cast : ℤ → ℚ)) hA)
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  have hArli : LinearIndependent ℝ (fun i => Ar i) := by
    apply rows_li_of_vecMul
    intro y hy
    have hdet : (Ar * Arᵀ).det ≠ 0 := by
      have : Ar = (Matrix.of A).map (Int.cast : ℤ → ℝ) := rfl
      rw [this, gram_map, det_map_intCast]; exact_mod_cast hAz
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← vecMul_vecMul, hy, zero_vecMul]
  have hMu : IsUnit Mr.det := by
    rw [hMr, det_map_intCast]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hM)
  have hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀ := by
    rw [hAr, hMr, gramQ]
    apply rank_bound P
    intro N hN
    haveI : NeZero N := ⟨hN.ne'⟩
    obtain ⟨S, hc, hS'⟩ := hS N hN
    refine ⟨S, hc, fun x hx => ?_⟩
    funext k
    set a : Fin r₀ → ℤ := fun i => ((x i).val : ℤ) with ha_def
    have ha : (fun j => (a j : ZMod N)) = x := by funext j; simp only [a]; rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdv := hS' a (Pi.single k 1) (by rw [ha]; exact hx)
    have hsum : (∑ i, (Pi.single k (1 : ℤ) : Fin r₀ → ℤ) i • A i) = A k := by
      simp [Pi.single_apply]
    rw [hsum] at hdv
    have hvs : ∑ i, a i • A i = a ᵥ* Matrix.of A := (vecMul_eq_sum _ _).symm
    have hz : (∑ i, a i • A i) ⬝ᵥ M *ᵥ A k = (P *ᵥ a) k := by
      rw [hvs, ← dotProduct_mulVec, dotProduct_comm]; rfl
    rw [hz] at hdv
    have hcast := RingHom.map_mulVec (Int.castRingHom (ZMod N)) P a k
    have e1 : (((P *ᵥ a) k : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdv
    simp only [Int.coe_castRingHom, e1] at hcast
    have h2 : (Int.cast ∘ a : Fin r₀ → ZMod N) = x := ha
    rw [h2] at hcast
    exact hcast.symm
  have hker : v ∈ LinearMap.ker (Ar * Mrᵀ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    rw [← mulVec_mulVec, mulVec_transpose]
    have := hv i
    rw [dotProduct_mulVec, dotProduct_comm] at this
    exact this
  exact ker_le_span Mr Ar hMu hArli hρ hker

end GlobalTheory.CoisoCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef

open IsLocalRing in

theorem isEtaleCompletion_comp_bij {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : Toroidal.IsEtaleCompletion φ) : Toroidal.IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem hasCones_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F}
    {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F}
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X)
    (hcov : IsCover (algebraMap (𝓞 c.F) c.F) R a b ω) (hch : ∀ i, IsChartOf Z (C i) (a i) (b i) (u i))
    (hC : ∀ i, HasCones Cn (C i)) : HasCones Cn Z := by
  intro z
  obtain ⟨i, hi⟩ : ∃ i, a i ∉ (Z.s z).asIdeal := by
    by_contra hne
    push_neg at hne
    have hle : Ideal.span (Set.range a) ≤ (Z.s z).asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hne j
    rw [hcov.2.2] at hle
    exact (Z.s z).isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨hoi, -, hrange, -, ⟨mu⟩⟩ := hch i
  have hz : z ∈ Set.range (u i) := by
    rw [hrange]
    exact hi
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨Rl, _, _, _, ξ, t, m, P, k, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩ := hC i z'
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp mu m
  have hb : Function.Bijective ((u i).stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of Rl)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨Rl, inferInstance, inferInstance, inferInstance, ξ ≫ u i, t, n, P, k, γ, hcn, ?_, ?_, ?_, htor, hcone, hin⟩
  · show (u i) (ξ _) = _
    rw [hpt]
  · rw [Scheme.stalkClosedPointTo_comp]
    exact isEtaleCompletion_comp_bij _ hb _ het
  · rw [Scheme.stalkClosedPointTo_comp]
    have h2 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hb.2) hfu
    exact h2

end GlobalTheory.TorRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairFam

open HolTorsion in

theorem cubWeil_const_of_isHolTo : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ b₁ hN _ hB hx hx' htor hb₀ hb₁ h₀
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.TorsionPairFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesianStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  first | exact @GlobalTheory.ArcLieCoord.sep | exact GlobalTheory.ArcLieCoord.sep | (intros; apply GlobalTheory.ArcLieCoord.sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped Matrix CategoryTheory.Obj Topology in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.det_ne_zero_of_im_hermForm_eq_int : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u u).re) → LinearIndependent ℝ lam → Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 := by
  intro g r Hm lam M hpos hli hspan hM hdet
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have h := RingHom.map_det (Int.castRingHom ℝ) M
    rw [hdet, map_zero] at h
    exact h.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  set w : Fin g → ℂ := ∑ j, v j • lam j with hwdef
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    funext j
    exact Fintype.linearIndependent_iff.mp hli v hw j
  have hlin : ∀ x : Fin g → ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w = ∑ j, v j • _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x (lam j) := by
    intro x
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, hwdef, star_sum, star_smul, star_trivial, Matrix.mulVec_sum,
      Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]
  have hlamw : ∀ i, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) w).im = 0 := by
    intro i
    have hrow := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hrow
    rw [hlin, Complex.im_sum]
    simp only [Complex.smul_im, hM, smul_eq_mul]
    rw [← hrow]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall : ∀ x, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hlamw i
    | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
    | add y z _ _ hy hz =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct, Complex.add_im] at hy hz ⊢
      rw [hy, hz, add_zero]
    | smul c y _ hy =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im] at hy ⊢
      rw [hy, smul_zero]
  have hI := hall (Complex.I • w)
  have hre := hpos w hw0
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at hI hre
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominatesLinearFormsOnBalancedFormsCmStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominatesLinearFormsOnBalancedForms_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X := by
  first | exact @GlobalTheory.DomBal.dominates | exact GlobalTheory.DomBal.dominates | (intros; apply GlobalTheory.DomBal.dominates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSetStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_on_set : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ)), (∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S, y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)), F.IsMap (evHom hy) f → G.gram y f τ a b = g y) → G.SmoothOn (manifold Z σ) S := by
  first | exact @GlobalTheory.ShFam.EigMet.smoothOn_of_locally | exact GlobalTheory.ShFam.EigMet.smoothOn_of_locally | (intros; apply GlobalTheory.ShFam.EigMet.smoothOn_of_locally <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodgeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_metric_smooth_of_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} → (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | exact GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.smoothOn_eigMetAt_some <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
end

