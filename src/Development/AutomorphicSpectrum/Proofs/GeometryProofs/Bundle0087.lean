import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0039

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundles
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ExtraBlocks

section Charts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isLocalRing_regAt (p : Cpt ξ) : IsLocalRing (regAt ξ p) :=
  IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem exists_unit_gen {B : Type} [Fintype B] (A : Subring Ω) [IsLocalRing A] (z : B → Ω) {f : Ω} (hf : f ≠ 0)
    (h : Submodule.span A (Set.range z) = Submodule.span A {f}) :
    ∃ l, z l ≠ 0 ∧ ∀ l', z l' / z l ∈ A := by
  classical
  have hz : ∀ i, ∃ a : A, (a : Ω) * f = z i := fun i => by
    have hi : z i ∈ Submodule.span A {f} := h ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hi
    exact ⟨a, ha⟩
  choose a ha using hz
  have hf' : f ∈ Submodule.span A (Set.range z) := h ▸ Submodule.mem_span_singleton_self f
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hf'
  have hsum : ∑ i, c i * a i = 1 := by
    have h1 : (∑ i, (c i : Ω) * a i) * f = 1 * f := by
      rw [Finset.sum_mul, _root_.one_mul]
      conv_rhs => rw [← hc]
      exact Finset.sum_congr rfl fun i _ => by rw [_root_.mul_assoc, ha]; rfl
    have h2 := mul_right_cancel₀ hf h1
    exact Subtype.ext (by simpa using h2)
  obtain ⟨l, hl⟩ : ∃ l, IsUnit (a l) := by
    by_contra hn
    push_neg at hn
    have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hn i))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal A).ne_top h1
  obtain ⟨b, hb⟩ := hl.exists_right_inv
  have hb' : (a l : Ω) * b = 1 := by simpa using congrArg (Subtype.val) hb
  have ha0 : (a l : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
  refine ⟨l, by rw [← ha]; exact mul_ne_zero ha0 hf, fun l' => ?_⟩
  have e : z l' / z l = ((a l' * b : A) : Ω) := by
    rw [← ha, ← ha, mul_div_mul_right _ _ hf]
    push_cast
    field_simp
    have : (b : Ω) = (a l : Ω)⁻¹ := eq_inv_of_mul_eq_one_right hb'
    rw [this]
    field_simp
  rw [e]
  exact (a l' * b).2

theorem inChart_pair {α β : Type} {u : α → Ω} {v : β → Ω} {c : α} {e : β} {p : Cpt ξ}
    (hu : InChart ξ u c p) (hv : InChart ξ v e p) :
    InChart ξ (fun q : α × β => u q.1 * v q.2) (c, e) p :=
  ⟨mul_ne_zero hu.1 hv.1, fun q => by
    show u q.1 * v q.2 / (u c * v e) ∈ _
    rw [mul_div_mul_comm]
    exact mul_mem (hu.2 _) (hv.2 _)⟩

theorem inChart_pi {A : Type} [Fintype A] {B : A → Type} {z : ∀ a, B a → Ω} {l : ∀ a, B a} {p : Cpt ξ}
    (h : ∀ a, InChart ξ (z a) (l a) p) : InChart ξ (fun l' : ∀ a, B a => ∏ a, z a (l' a)) l p :=
  ⟨Finset.prod_ne_zero_iff.2 fun a _ => (h a).1, fun l' => by
    show (∏ a, z a (l' a)) / ∏ a, z a (l a) ∈ _
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun a _ => (h a).2 _⟩

theorem inChart_equiv_iff {κ κ₂ : Type} {x : κ → Ω} (e : κ₂ ≃ κ) (c : κ₂) (p : Cpt ξ) :
    InChart ξ (fun c' => x (e c')) c p ↔ InChart ξ x (e c) p :=
  ⟨fun h => ⟨h.1, fun c' => by simpa using h.2 (e.symm c')⟩, fun h => ⟨h.1, fun c' => h.2 _⟩⟩

theorem coordTie_equiv {o : Type} [CommRing o] [Algebra o Ω] {κ κ₂ : Type} {x : κ → Ω} (e : κ₂ ≃ κ)
    (h : CoordTie o ξ x) : CoordTie o ξ (fun c => x (e c)) where
  gen := h.gen
  cover p := by
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (inChart_equiv_iff e _ p).2 (by simpa using hc)⟩
  affine c hc := by
    obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (inChart_equiv_iff e c _).symm)⟩
  ring c hc a := by
    have hr : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      e.surjective.range_comp fun j => x j / x (e c)
    show a ∈ Algebra.adjoin o (Set.range fun j => x (e j) / x (e c)) ↔ _
    rw [hr, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (inChart_equiv_iff e c p).symm Iff.rfl

theorem isCohOn_of_isVBOn {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVBOn T r V) : L.IsCohOn T := fun p hp => by
  obtain ⟨U, hU, b, -, hb⟩ := h p hp
  exact ⟨U, hU, r, b, fun q hq hqU => (hb q hq hqU).2⟩

variable {κ : Type} {x : κ → Ω} {Λ : Lat ξ Ω} {d n : ℕ} {z : Fin n → Ω}

theorem exists_inChart_of_twist (hc : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p)
    (H : ∀ c (p : Cpt ξ), InChart ξ x c p →
      Λ p = Submodule.span (regAt ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k))
    (hv : Λ.IsVB 1 ⊤) (p : Cpt ξ) : ∃ l, InChart ξ z l p := by
  obtain ⟨c, hcp⟩ := hc p
  obtain ⟨e, he, hL, -⟩ := Flat.exists_gen_of_isVB_one hv p
  haveI := isLocalRing_regAt p
  obtain ⟨l, hl0, hl⟩ := exists_unit_gen (regAt ξ p) _ he ((H c p hcp).symm.trans hL)
  have hx : (x c ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hcp.1)
  refine ⟨l, fun h0 => hl0 (by simp [h0]), fun l' => ?_⟩
  have h1 := hl l'
  simp only [smul_eq_mul] at h1
  rwa [mul_div_mul_left _ _ hx] at h1

theorem stalk_eq_of_twist
    (H : ∀ c (p : Cpt ξ), InChart ξ x c p →
      Λ p = Submodule.span (regAt ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k))
    {c : κ} {l : Fin n} {p : Cpt ξ} (hx : InChart ξ x c p) (hz : InChart ξ z l p) :
    Λ p = Submodule.span (regAt ξ p) {(x c ^ d)⁻¹ * z l} := by
  rw [H c p hx]
  have h0 := hz.1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.mem_span_singleton.2 ⟨⟨z k / z l, hz.2 k⟩, ?_⟩
    show (z k / z l) * ((x c ^ d)⁻¹ * z l) = (x c ^ d)⁻¹ • z k
    rw [smul_eq_mul]
    field_simp
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨l, rfl⟩

end Charts

section Blocks

variable {K A : Type} (J : K → Type) (κ : Type) (n : A → ℕ)

def BJ : K ⊕ Option A → Type
  | .inl k => J k
  | .inr none => κ
  | .inr (some a) => Fin (n a)

def fintypeBJ [∀ k, Fintype (J k)] [Fintype κ] : ∀ k, Fintype (BJ J κ n k)
  | .inl k => inferInstanceAs (Fintype (J k))
  | .inr none => inferInstanceAs (Fintype κ)
  | .inr (some a) => inferInstanceAs (Fintype (Fin (n a)))

def blockCo {Ω : Type} (y : (Σ k, J k) → Ω) (x : κ → Ω) (z : ∀ a, Fin (n a) → Ω) :
    (Σ k, BJ J κ n k) → Ω
  | ⟨.inl k, j⟩ => y ⟨k, j⟩
  | ⟨.inr none, c⟩ => x c
  | ⟨.inr (some a), l⟩ => z a l

def blockDeg [DecidableEq A] (d : A → ℕ) (a : A) : K ⊕ Option A → ℤ
  | .inl _ => 0
  | .inr none => -(d a : ℤ)
  | .inr (some a') => if a' = a then 1 else 0

def blockEquiv : ((k : K ⊕ Option A) → BJ J κ n k) ≃ κ × (((k : K) → J k) × ((a : A) → Fin (n a))) where
  toFun c := (c (.inr none), (fun k => c (.inl k), fun a => c (.inr (some a))))
  invFun t := fun k => match k with
    | .inl k => t.2.1 k
    | .inr none => t.1
    | .inr (some a) => t.2.2 a
  left_inv c := by funext k; rcases k with k | _ | a <;> rfl
  right_inv t := rfl

variable {J κ n} {Ω : Type} [Field Ω] [Fintype K] [Fintype A]

theorem segre_blockCo (y : (Σ k, J k) → Ω) (x : κ → Ω) (z : ∀ a, Fin (n a) → Ω)
    (c : (k : K ⊕ Option A) → BJ J κ n k) :
    ∏ k, blockCo J κ n y x z ⟨k, c k⟩ =
      x (c (.inr none)) * ((∏ k, y ⟨k, c (.inl k)⟩) * ∏ a, z a (c (.inr (some a)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_option]
  show (∏ k, y ⟨k, c (.inl k)⟩) * (x (c (.inr none)) * ∏ a, z a (c (.inr (some a)))) = _
  ring

theorem deg_blockCo [DecidableEq A] (y : (Σ k, J k) → Ω) (x : κ → Ω) (z : ∀ a, Fin (n a) → Ω) (d : A → ℕ) (a : A)
    (c : (k : K ⊕ Option A) → BJ J κ n k) :
    ∏ k, blockCo J κ n y x z ⟨k, c k⟩ ^ blockDeg d a k =
      (x (c (.inr none)) ^ d a)⁻¹ * z a (c (.inr (some a))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_option]
  have h1 : ∏ k : K, blockCo J κ n y x z ⟨.inl k, c (.inl k)⟩ ^ blockDeg (K := K) d a (.inl k) = 1 :=
    Finset.prod_eq_one fun k _ => zpow_zero _
  have h2 : ∏ a' : A, blockCo J κ n y x z ⟨.inr (some a'), c (.inr (some a'))⟩ ^ blockDeg (K := K) d a (.inr (some a')) =
      z a (c (.inr (some a))) := by
    rw [Finset.prod_eq_single a]
    · show z a _ ^ (if a = a then (1 : ℤ) else 0) = _
      simp
    · intro b _ hb
      show z b _ ^ (if b = a then (1 : ℤ) else 0) = 1
      simp [hb]
    · simp
  rw [h1, h2, _root_.one_mul]
  show x _ ^ (-(d a : ℤ)) * _ = _
  rw [zpow_neg, zpow_natCast]

end Blocks

theorem exists_blocks_of_lines : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : Type) [Finite A] (Λ : A → Lat M.ξ Ω), (∀ p : Cpt M.ξ, ∃ c₀, InChart M.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p) → (∀ a, (Λ a).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (deg : A → K' → ℤ), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ CoordTie o M.ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ a, (Λ a).IsDegOn Set.univ y' (deg a) 1 := by
  intro o _ Ω _ _ κ _ x M K _ J _ y A _ Λ hy hv
  classical
  haveI := Fintype.ofFinite κ
  haveI := Fintype.ofFinite A
  have hs : ∀ a, ∃ (d n : ℕ) (z : Fin n → Ω), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p →
      Λ a p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) :=
    fun a => GlobalTheory.T.coherent_lattice_chart_span o Ω κ x M Ω (Λ a) (isCohOn_of_isVBOn (hv a))
  choose d n z H using hs
  let w : ((k : K) → J k) × ((a : A) → Fin (n a)) → Ω := fun q =>
    (∏ k, y ⟨k, q.1 k⟩) * ∏ a, z a (q.2 a)
  have hw : ∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p := by
    intro p
    obtain ⟨c₀, h₀⟩ := hy p
    choose l hl using fun a => exists_inChart_of_twist M.tie.cover (H a) (hv a) p
    exact ⟨(c₀, l), inChart_pair h₀ (inChart_pi hl)⟩
  have ht := coordTie_equiv (blockEquiv J κ n) (GlobalTheory.T.join_coords_coordTie o Ω κ x M _ w hw)
  refine ⟨K ⊕ Option A, inferInstance, BJ J κ n, fintypeBJ J κ n, blockCo J κ n y x z, Sum.inl,
    fun k => Equiv.refl _, fun a => blockDeg d a, Sum.inl_injective, fun _ _ => rfl, ?_,
    fun a => ⟨one_ne_zero, fun p _ c hc => ?_⟩⟩
  · have e : (fun c' : (k : K ⊕ Option A) → BJ J κ n k => ∏ k, blockCo J κ n y x z ⟨k, c' k⟩) =
        fun c => joinCo (RingHom.id Ω) x w (blockEquiv J κ n c) :=
      funext fun c => segre_blockCo y x z c
    rw [e]
    exact ht
  · have hx : InChart M.ξ x (c (.inr none)) p :=
      ⟨Lat.block_coord_ne_zero hc (.inr none), fun i => Lat.block_ratio_mem hc (.inr none) i⟩
    have hz : InChart M.ξ (z a) (c (.inr (some a))) p :=
      ⟨Lat.block_coord_ne_zero hc (.inr (some a)), fun i => Lat.block_ratio_mem hc (.inr (some a)) i⟩
    rw [stalk_eq_of_twist (H a) hx hz, deg_blockCo, smul_eq_mul, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.ExtraBlocks
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpMapEqFromSpecStalk
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.StalkPt

theorem spMap_eq_fromSpecStalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens), IsAffineOpen U → ∀ (R : Type) [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap φ ≫ x = ξ → (∀ z, x z ∈ U) → ∀ (q : Cpt ξ), q.1 ∈ U → ∀ ψ : R →+* X.presheaf.stalk q.1, (genMap ξ q).comp ψ = φ → spMap ψ ≫ x = X.fromSpecStalk q.1 :=
  @PositivityTheory.Xgn.stalk_point_factorization

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.StalkPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem aeval_const_mul {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_homog {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (c₀ : σ) (h1 : r c₀ = 1)
    (t : Algebra.adjoin ℚ (Set.range r)) :
    ∃ (m : ℤ) (n : ℕ) (G : MvPolynomial σ ℤ), m ≠ 0 ∧ G.IsHomogeneous n ∧
      aeval r G = (m : Ω) * (t : Ω) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, 1, X j, one_ne_zero, isHomogeneous_X _ _, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [map_intCast, eq_intCast, eq_ratCast, Int.cast_natCast]
    rw [Rat.cast_def]
    field_simp
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add, map_mul, map_pow, aeval_X, h1, one_pow, mul_one, eq_intCast, map_intCast, e₁, e₂]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, G₁ * G₂, mul_ne_zero hm₁ hm₂, hG₁.mul hG₂, ?_⟩
    simp only [map_mul, e₁, e₂]
    push_cast
    ring

theorem smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)

theorem eval_map_int {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))

theorem blockRatio_eq (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (p : Σ k, ι k) [DecidableEq K] :
    y p / y ⟨p.1, E c₀ p.1⟩ =
      (∏ k, y ⟨k, E (E.symm (Function.update (E c₀) p.1 p.2)) k⟩) / ∏ k, y ⟨k, E c₀ k⟩ := by
  obtain ⟨k₀, i⟩ := p
  simp only [Equiv.apply_symm_apply]
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [div_eq_div_iff (hc k₀) h0,
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, E c₀ k⟩) (Finset.mem_univ k₀),
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, Function.update (E c₀) k₀ i k⟩) (Finset.mem_univ k₀)]
  have e : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, Function.update (E c₀) k₀ i k⟩ =
      ∏ k ∈ Finset.univ.erase k₀, y ⟨k, E c₀ k⟩ :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, Function.update_self]
  ring

theorem aeval_blockRatio_mem [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by
  classical
  induction β using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem _ n
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    refine mul_mem hp (Algebra.subset_adjoin ⟨E.symm (Function.update (E c₀) i.1 i.2), ?_⟩)
    exact (blockRatio_eq y E c₀ hc i).symm

theorem aeval_eq_prod_mul (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b) :
    aeval y β = (∏ k, y ⟨k, E c₀ k⟩ ^ b k) *
      aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := by
  have h := GlobalTheory.CompanionTheory.Ar.aeval_blockScale hb (fun k => y ⟨k, E c₀ k⟩) (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩)
  have e : (fun p : Σ k, ι k => y ⟨p.1, E c₀ p.1⟩ * (y p / y ⟨p.1, E c₀ p.1⟩)) = y :=
    funext fun p => mul_div_cancel₀ _ (hc p.1)
  rwa [e] at h

theorem mConeMap_segre (j : Fin (N + 1)) :
    mConeMap y (∏ k, (X ⟨k, E j k⟩ : MRing ι)) =
      (∏ k, (X k : MvPolynomial K Ω)) * C (∏ k, y ⟨k, E j k⟩) := by
  simp only [map_prod, mConeMap, aeval_X, Finset.prod_mul_distrib]
  rw [mul_comm]

theorem vanish_of_value (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hx : aeval (fun j => ∏ k, y ⟨k, E j k⟩) G * ∏ k, y ⟨k, E c₀ k⟩ ^ b k =
      (m : Ω) * aeval y β * (∏ k, y ⟨k, E c₀ k⟩) ^ n := by
    have e : (fun j => ∏ k, y ⟨k, E j k⟩) = fun j => (∏ k, y ⟨k, E c₀ k⟩) *
        ((∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :=
      funext fun j => (mul_div_cancel₀ _ h0).symm
    rw [e, aeval_const_mul hG, hval, aeval_eq_prod_mul y E c₀ hc hb]
    ring
  let P₁ : MRing ι := aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G * ∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k
  let P₂ : MRing ι := C m * β * (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι)) ^ n
  have hmem : P₁ - P₂ ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.2 ?_
    have hG' : mConeMap y (aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G) =
        (∏ k, (X k : MvPolynomial K Ω)) ^ n * C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) := by
      rw [comp_aeval_apply]
      simp only [mConeMap_segre]
      rw [aeval_const_mul hG]
      congr 1
      exact (comp_aeval_apply _ (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) G).symm
    have hX : mConeMap y (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k) =
        (∏ k, (X k : MvPolynomial K Ω) ^ b k) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k) := by
      simp only [map_prod, map_pow, mConeMap, aeval_X, mul_pow, Finset.prod_mul_distrib]
      rw [mul_comm]
    have hC : mConeMap y (C m) = C (m : Ω) := by
      simp [mConeMap]
    have hS := mConeMap_segre y E c₀
    simp only [P₁, P₂, map_sub, map_mul, map_pow, hG', hX, hC, hS,
      GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hb]
    rw [sub_eq_zero]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hx
    simp only [map_mul, map_pow] at this
    calc _ = (∏ k, (X k : MvPolynomial K Ω)) ^ n * (∏ k, (X k : MvPolynomial K Ω) ^ b k) *
          (C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k)) := by ring
      _ = _ := by rw [this]; ring
  have hzero := hz.2 _ hmem
  have hev : aeval z (P₁ - P₂) = 0 := by rw [← eval_map_int]; exact hzero
  have hβ' : aeval z β = 0 := by rw [← eval_map_int]; exact hβ
  have hP : aeval (fun j => ∏ k, z ⟨k, E j k⟩) G * ∏ k, z ⟨k, E c₀ k⟩ ^ b k = 0 := by
    simp only [P₁, P₂, map_sub, map_mul, map_pow, map_prod, aeval_X, hβ', comp_aeval_apply] at hev
    simpa using hev
  rcases mul_eq_zero.1 hP with h | h
  · exact Or.inr h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine Or.inl (Finset.prod_eq_zero_iff.2 ⟨k, Finset.mem_univ _, ?_⟩)
    by_contra h'
    exact pow_ne_zero _ h' hk

end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes in

theorem GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  intro Ω _ _ K _ ι _ y e β b hb hβ N E c₀ hc s hs _
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have h1 : (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) c₀ = 1 := div_self h0
  obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := SegreForm.exists_homog _ c₀ h1 s
  obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := SegreForm.exists_homog _ c₀ h1
    ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩
  have hbt : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ≠ 0 := by
    intro h
    apply hβ
    rw [form_mem_mCoordIdeal_iff y hb, SegreForm.aeval_eq_prod_mul y E c₀ hc hb, h, mul_zero]
  have hm₁' : (m₁ : Ω) ≠ 0 := by exact_mod_cast hm₁
  have hm₂' : (m₂ : Ω) ≠ 0 := by exact_mod_cast hm₂
  have hs' : (s : Ω) ≠ 0 := fun h => hs (Subtype.ext h)
  refine ⟨n₁ + n₂, X c₀ * G₁ * G₂,
    s * (((m₁ * m₂ : ℤ) : Algebra.adjoin ℚ _) * ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩),
    ?_, ?_, ?_, ?_, SegreForm.smooth_away_mul s _ e, ?_⟩
  · have := ((isHomogeneous_X ℤ c₀).mul hG₁).mul hG₂
    convert this using 1
    ring
  · rw [mul_assoc]
    exact dvd_mul_right _ _
  · have e₂' : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G₂ =
        (m₂ : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := e₂
    rw [map_mul, map_mul, aeval_X, e₁, e₂', div_self h0]
    push_cast
    ring
  · intro h
    have h' := congrArg (Subtype.val) h
    have h'' : (s : Ω) * (((m₁ : Ω) * m₂) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β) = 0 := by
      simpa using h'
    exact mul_ne_zero hs' (mul_ne_zero (mul_ne_zero hm₁' hm₂') hbt) h''
  · intro z hz hzβ
    rw [SegreForm.eval_map_int, map_mul, map_mul, aeval_X]
    rcases SegreForm.vanish_of_value y E c₀ hc hb hG₂ e₂ hz hzβ with h | h
    · simp only [h, zero_mul]
    · simp only [h, mul_zero]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSubgroupBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChange

theorem torsion_isBaseChange : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F :=
  @PositivityTheory.Xgn.torsion_group_base_change

end GlobalTheory.CompanionTheory.Ar.BT.BaseChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivflagNefFibre
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivflag_nef_fibre : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 :=
  @PositivityTheory.HtPt.Gf.trivflag_nef

end GlobalTheory.CompanionTheory.Ar.HT
end

