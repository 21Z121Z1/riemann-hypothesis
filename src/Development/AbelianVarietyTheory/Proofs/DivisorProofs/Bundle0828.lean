import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroupStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_diagonalSliceLevelSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  first | exact @GlobalTheory.SliceTwo.isOpen_levelSub | exact GlobalTheory.SliceTwo.isOpen_levelSub | (intros; apply GlobalTheory.SliceTwo.isOpen_levelSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixOpen

variable {A₀ X T : Scheme.{0}} {N : LB A₀} {mA mB : ℕ}

theorem isUnit_comb_chart (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (z : X) {q q' : N.ι} (hq : φ z ∈ N.U q) (hq' : φ z ∈ N.U q') (j : Fin mB) :
    IsUnit (comb a φ p c z q j) ↔ IsUnit (comb a φ p c z q' j) := by
  have e : comb a φ p c z q j = (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    simp only [comb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_compat (a i) φ z hq hq', mul_left_comm]
  rw [e, Units.isUnit_units_mul]

theorem comb_comp {Y : Scheme.{0}} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (h : Y ⟶ X) (y : Y) (q : N.ι) (hq : φ (h y) ∈ N.U q) (j : Fin mB) :
    comb a (h ≫ φ) (h ≫ p) c y q j = (h.stalkMap y).hom (comb a φ p c (h y) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp h p y ⊤ trivial, gs_comp h φ y (N.U q) hq]

theorem gs_top {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X) (c : Γ(Z, ⊤)) :
    gs f z ⊤ (g.appTop.hom c) = gs (f ≫ g) z ⊤ c :=
  gs_pull f g z ⊤ trivial c

theorem gs_sum' {Y : Scheme.{0}} (f : X ⟶ Y) (z : X) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (b : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, b i) = ∑ i, gs f z U (b i) := by
  simp only [gs_eq f z U h, map_sum]

def good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Set X :=
  {z | ∃ q, φ z ∈ N.U q ∧ ∃ j, IsUnit (comb a φ p c z q j)}

def combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) : Γ(X, φ ⁻¹ᵁ N.U q) :=
  ∑ i, (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (c i j)) * (φ.app (N.U q)).hom ((a i).f q)

theorem gs_combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) (z : X) (hz : φ z ∈ N.U q) : gs (𝟙 X) z _ (combFn a φ p c q j) = comb a φ p c z q j := by
  have hz' : (𝟙 X) z ∈ φ ⁻¹ᵁ N.U q := hz
  rw [combFn, gs_sum' (𝟙 X) z _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hz', gs_res _ z le_top hz', gs_top, gs_pull (𝟙 X) φ z (N.U q) hz, Category.id_comp,
    Category.id_comp]

theorem isOpen_good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) :
    IsOpen (good a φ p c) := by
  have e : good a φ p c = ⋃ q, ⋃ j, (X.basicOpen (combFn a φ p c q j) : Set X) := by
    ext z
    simp only [good, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, j, hu⟩
      refine ⟨q, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq] at hu
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).1 hu
    · rintro ⟨q, j, hz⟩
      have hq : φ z ∈ N.U q := X.basicOpen_le _ hz
      refine ⟨q, hq, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq]
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).2 hz
  rw [e]
  exact isOpen_iUnion fun q => isOpen_iUnion fun j => (X.basicOpen _).isOpen

end GlobalTheory.HomFixOpen

namespace GlobalTheory.HomFixOpen

theorem main : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  intro Rg _ A₀ f _ N mA mB a hN
  let π₁ := pullback.fst f (affπ Rg (mA * mB))
  let π₂ := pullback.snd f (affπ Rg (mA * mB))
  let G := good a π₁ π₂ (matOf (𝟙 (Sp (MvPolynomial (Fin (mA * mB)) Rg))))
  have hG : IsOpen G := isOpen_good _ _ _ _
  have hC : IsClosed (π₂ '' Gᶜ) := π₂.isClosedMap _ hG.isClosed_compl
  refine ⟨⟨(π₂ '' Gᶜ)ᶜ, hC.isOpen_compl⟩, fun T X' g φ p hP => ?_⟩
  have w : φ ≫ f = (p ≫ g) ≫ affπ Rg (mA * mB) := by rw [Category.assoc]; exact hP.w
  let h := pullback.lift φ (p ≫ g) w
  have h1 : h ≫ π₁ = φ := pullback.lift_fst _ _ _
  have h2 : h ≫ π₂ = p ≫ g := pullback.lift_snd _ _ _
  have hπ₁ : ∀ z, π₁ (h z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, h1]
  have key : ∀ z q j, φ z ∈ N.U q → comb a φ p (matOf g) z q j =
      (h.stalkMap z).hom (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j) := by
    intro z q j hq
    rw [← comb_comp a π₁ π₂ _ h z q (by rw [hπ₁]; exact hq) j]
    simp only [comb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [h2, matOf, matOf, coord, coord, gs_top, gs_top, Category.comp_id]
  have unitIff : ∀ z q j, φ z ∈ N.U q → (IsUnit (comb a φ p (matOf g) z q j) ↔
      IsUnit (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j)) := by
    intro z q j hq; rw [key z q j hq]; exact isUnit_map_iff _ _
  have stepA : Generates a φ p (matOf g) ↔ ∀ z, h z ∈ G := by
    constructor
    · intro hg z
      obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hN (φ z)
      obtain ⟨j, hj⟩ := hg z q hq
      exact ⟨q, by rw [hπ₁]; exact hq, j, (unitIff z q j hq).1 hj⟩
    · intro hg z q hq
      obtain ⟨q', hq', j, hj⟩ := hg z
      exact ⟨j, (unitIff z q j hq).2 ((isUnit_comb_chart a π₁ π₂ _ (h z) hq' (by rw [hπ₁]; exact hq) j).1 hj)⟩
  rw [stepA]
  have hP' : IsPullback h p π₂ g := IsPullback.of_right (by rw [h1]; exact hP) h2 (IsPullback.of_hasPullback _ _)
  constructor
  · intro hg τ
    show g τ ∈ (π₂ '' Gᶜ)ᶜ
    rintro ⟨w', hw, he⟩
    obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π₂) (g := g) w' τ he
    apply hw
    have e : h (hP'.isoPullback.inv y) = w' := by
      rw [← Scheme.Hom.comp_apply, hP'.isoPullback_inv_fst, hy1]
    rw [← e]; exact hg _
  · intro hg z
    by_contra hz
    exact hg (p z) ⟨h z, hz, by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]⟩

end GlobalTheory.HomFixOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPullStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_of_isPull1_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  first | exact @GlobalTheory.CechPer.Nat.isPer_pull | exact GlobalTheory.CechPer.Nat.isPer_pull | (intros; apply GlobalTheory.CechPer.Nat.isPer_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_unique' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  first | exact @GlobalTheory.CechPer.isPer_unique | exact GlobalTheory.CechPer.isPer_unique | (intros; apply GlobalTheory.CechPer.isPer_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAt
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.UnifVal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isUnit_iff_v_eq_one (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    have : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this; exact lt_irrefl _ this
  · intro h
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
      show Valued.v ((a : v.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    show (a : v.adicCompletion K) * (a : v.adicCompletion K)⁻¹ = 1
    exact mul_inv_cancel₀ ha0

theorem isUniformiserAt_iff_isUnifAt (x : (v.adicCompletion K)ˣ) :
    IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  unfold IsUniformiserAt Formalism.L2.Host.IsUnifAt
  have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
  have hv0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simpa using hx0
  set m := WithZero.log (Valued.v (x : v.adicCompletion K)) with hm
  have hx : Valued.v (x : v.adicCompletion K) = WithZero.exp m := (WithZero.exp_log hv0).symm
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  constructor
  · rintro ⟨hmem, hirr⟩
    have hle : Valued.v (x : v.adicCompletion K) ≤ 1 := hmem
    have hnu : Valued.v (x : v.adicCompletion K) ≠ 1 := fun h =>
      hirr.not_isUnit ((isUnit_iff_v_eq_one v _).2 h)
    rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    rw [hx, ← WithZero.exp_zero, Ne, WithZero.exp_inj] at hnu
    rw [hx]
    by_contra hne
    rw [WithZero.exp_inj] at hne
    have hm2 : m ≤ -2 := by omega
    have ha : π ∈ v.adicCompletionIntegers K := by
      show Valued.v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    have hbv : Valued.v ((x : v.adicCompletion K) / π) = WithZero.exp (m + 1) := by
      rw [map_div₀, hx, hπ, ← WithZero.exp_sub, sub_neg_eq_add]
    have hb : (x : v.adicCompletion K) / π ∈ v.adicCompletionIntegers K := by
      show Valued.v ((x : v.adicCompletion K) / π) ≤ 1
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hprod : (⟨(x : v.adicCompletion K), hmem⟩ : v.adicCompletionIntegers K) =
        ⟨π, ha⟩ * ⟨(x : v.adicCompletion K) / π, hb⟩ := by
      apply Subtype.ext
      show (x : v.adicCompletion K) = π * ((x : v.adicCompletion K) / π)
      field_simp
    rcases hirr.isUnit_or_isUnit hprod with h | h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v π = 1 at h
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_inj] at h
      norm_num at h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v ((x : v.adicCompletion K) / π) = 1 at h
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_inj] at h
      omega
  · intro h
    have hmem : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      show Valued.v (x : v.adicCompletion K) ≤ 1
      rw [h, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    refine ⟨hmem, irreducible_iff.2 ⟨?_, ?_⟩⟩
    · intro hu
      rw [isUnit_iff_v_eq_one] at hu
      change Valued.v (x : v.adicCompletion K) = 1 at hu
      rw [h, ← WithZero.exp_zero, WithZero.exp_inj] at hu
      norm_num at hu
    · intro a b hab
      have hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
        have hab' : (x : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K) :=
          congrArg Subtype.val hab
        rw [← map_mul, ← hab', h]
      have ha0 : Valued.v (a : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
      have hb0 : Valued.v (b : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
      have hale : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      have hble : Valued.v (b : v.adicCompletion K) ≤ 1 := b.2
      rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hale
      rw [← WithZero.exp_log hb0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hble
      rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.exp_inj] at hv
      by_cases hi : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0
      · left
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log ha0, hi, WithZero.exp_zero]
      · right
        have hj : WithZero.log (Valued.v (b : v.adicCompletion K)) = 0 := by omega
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log hb0, hj, WithZero.exp_zero]

end GlobalTheory.UnifVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnramifiedAtOfInertiaEqBot
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem isUnramifiedAt_of_inertia_eq_bot (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M] (P : Ideal (𝓞 M)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : P.inertia (M ≃ₐ[K] M) = ⊥) : Algebra.IsUnramifiedAt (𝓞 K) P := by
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  haveI : (P.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) P
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (M ≃ₐ[K] M),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) (P.under (𝓞 K)) P, h]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixNorm

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem gs_npow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem one_comp_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hφ (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem stalkMap_gm_pow {Z Y : Scheme.{0}} (t : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : t z ∈ V) (a : Γ(Y, V)ˣ) (n : ℕ) :
    (t.stalkMap z).hom ((gm (𝟙 Y) (t z) V a) ^ n).val = gs t z V a.val ^ n := by
  rw [Units.val_pow_eq_pow_val, ← gs_unit (𝟙 Y) (t z) V h, map_pow, ← gs_stalkMap t z V h]

theorem norm_at_zero : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c u hcov hA hB hT hN hrel p
  obtain ⟨gA, gB, hΦ, -⟩ := hT
  haveI : IsMonHom Φ' := hΦ
  have e₀ : zeroPt A' ≫ A'.hom = 𝟙 _ := by simp [zeroPt]
  have eΦ : zeroPt A' ≫ Φ'.left = zeroPt B' := by rw [zeroPt, zeroPt, ← Over.comp_left, IsMonHom.one_hom]
  have eA' : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by
    rw [← Category.assoc, zeroPt, one_comp_of_isGrpPullback gA, Category.assoc]; rfl
  have eB' : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by
    rw [← Category.assoc, eΦ, ← Category.assoc, zeroPt, one_comp_of_isGrpPullback gB, Category.assoc]; rfl
  refine fn_ext fun z hz => ?_

  have hz0 := hz
  obtain ⟨⟨hzU', hzA'⟩, hzB'⟩ := hz
  have hzU : zeroPt A' z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := hzU'
  have hzA : t z ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) := hzA'
  have hzB : t z ∈ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := hzB'
  have pA : eSec A (t z) ∈ L.U (p.2 0) := Set.mem_iInter.1 hzA PUnit.unit
  have pB : eSec B (t z) ∈ M.U (p.1 0) := Set.mem_iInter.1 hzB PUnit.unit
  have mA : (eSec A ≫ θ A) (t z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) A).left ((eSec A ≫ θ A) (t z)) ∈ L.U (p.2 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pA
  have mB : (eSec B ≫ θ B) (t z) ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) B).left ((eSec B ≫ θ B) (t z)) ∈ M.U (p.1 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pB
  have sB : ∀ j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((Φ'.left ≫ (φB' ≫ θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs t z ⊤ (βB j) * gs t z (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)) (eB.s (fun _ => p.1 0)).val ^ k := by
    intro j
    have v := hB j (t z) p.1 mB
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eB']
    erw [gs_comp t _ z _ mB]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzB, ← gs_stalkMap t z ⊤ trivial]
  have sA : ∀ i, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    intro i
    have v := hA i (t z) p.2 mA
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eA']
    erw [gs_comp t _ z _ mA]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzA, ← gs_stalkMap t z ⊤ trivial]
  have sC : ∀ i j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      ((A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom (c i j)) =
        gs (𝟙 _) z ⊤ (c i j) := by
    intro i j
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [e₀]
  have gt : ∀ x : Γ(Sp Rg, ⊤), gs t z ⊤ x = gs (𝟙 _) z ⊤ (t.appTop x) := by
    intro x
    have e := gs_pull (𝟙 (Sp R)) t z ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have nN : ∀ j, ∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i) = gs t z ⊤ (βB j) := by
    intro j
    rw [gt, hN j, gs_finsum _ z ⊤ trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [gt, gs_mul _ z ⊤ trivial]
  have hcz : (eSec B ≫ θ B) (t z) ∈ (⨆ j, nonzeroLocus (bB j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hcz
  have hu := (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) (eSec B ≫ θ B) (t z) mB).1 hj
  erw [hB j (t z) p.1 mB] at hu
  have hβ : IsUnit (gs t z ⊤ (βB j)) := by
    rw [gs_stalkMap t z ⊤ trivial]
    exact (isUnit_of_mul_isUnit_left hu).map _
  have E := congrArg (gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)) (hrel j p)
  rw [sB j, gs_mul _ _ _ hzU, gs_finsum _ _ _ hzU] at E
  simp only [gs_mul _ _ _ hzU, sC, sA] at E
  have hs : ∑ i, gs (𝟙 _) z ⊤ (c i j) * (gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k) =
      (∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i)) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hs, nN j] at E
  rw [gs_mul _ z _ hz0, gs_npow _ z _ hz0, gs_npow _ z _ hz0]
  erw [gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0]
  simp only [Category.id_comp]
  exact hβ.mul_left_cancel (by rw [E]; ring)

end GlobalTheory.HomFixNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBlockBoundLeExpKernelBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  first | exact @GlobalTheory.BlockNumber.tmax_le_exp_kernelBound | exact GlobalTheory.BlockNumber.tmax_le_exp_kernelBound | (intros; apply GlobalTheory.BlockNumber.tmax_le_exp_kernelBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFinsetLinearCombinationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_finset_linear_combination : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  first | exact @GlobalTheory.ColNorms.jetC_sum_mul | exact GlobalTheory.ColNorms.jetC_sum_mul | (intros; apply GlobalTheory.ColNorms.jetC_sum_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFiniteStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelConstant_exponents_finite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  first | exact @GlobalTheory.ExponentsFinite.yFinite | exact GlobalTheory.ExponentsFinite.yFinite | (intros; apply GlobalTheory.ExponentsFinite.yFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPtsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyGeneric_of_keyClosedPts' : GlobalTheory.LocAcyc.KeyClosedPts → GlobalTheory.LocAcyc.KeyGeneric := by
  first | (exact @GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (exact GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (intros; apply GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRepUniversalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_pt_of_isGrpPullback : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧ ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  first | exact @GlobalTheory.EndLoc.HomGlue.localRep_universal | exact GlobalTheory.EndLoc.HomGlue.localRep_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.localRep_universal; all_goals assumption)
end

