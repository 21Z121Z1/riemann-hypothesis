import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

theorem exists_int_basis_of_fg {V : Type} [AddCommGroup V] [Module ℚ V] (Z : Submodule ℤ V)
    (hZ : Z.FG) {n : ℕ} (hn : Module.finrank ℚ (Submodule.span ℚ (Z : Set V)) = n) :
    ∃ bs : Fin n → V, LinearIndependent ℤ bs ∧ Submodule.span ℤ (Set.range bs) = Z := by
  haveI : Module.Finite ℤ Z := Module.Finite.iff_fg.2 hZ
  haveI : IsAddTorsionFree V := IsAddTorsionFree.of_module_rat V
  haveI : Module.Free ℤ Z := inferInstance
  let b := Module.finBasis ℤ Z
  have hli : LinearIndependent ℤ (Z.subtype ∘ b) :=
    b.linearIndependent.map' Z.subtype Z.ker_subtype
  have hsp : Submodule.span ℤ (Set.range (Z.subtype ∘ b)) = Z := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hq : LinearIndependent ℚ (Z.subtype ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have h1 := finrank_span_eq_card hq
  have h2 : Submodule.span ℚ (Set.range (Z.subtype ∘ b)) = Submodule.span ℚ (Z : Set V) := by
    conv_rhs => rw [← hsp]
    rw [Submodule.span_span_of_tower]
  rw [h2, hn, Fintype.card_fin] at h1
  subst h1
  exact ⟨_, hli, hsp⟩

theorem latZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (Comp : Type) (X : Comp → Data E r), FJ.LatZ X ρ := by
  intro E _ _ _ r ρ Comp X cu
  obtain ⟨c, cu⟩ := cu
  have hZ : (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E)) =
      FJ.zGam (X c) cu := by
    have := Submodule.span_eq (AddSubgroup.toIntSubmodule (zGamSub (X c) cu))
    exact congrArg (fun S : Submodule ℤ (Matrix (Fin ρ) (Fin ρ) E) =>
      (S : Set (Matrix (Fin ρ) (Fin ρ) E))) this
  have hdim := GlobalTheory.T.finrank_rat_skewHermitian_matrices_cmField E ρ (X c).Ψ (X c).cmType
    (Submodule.span ℚ (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E))) (by
      rw [hZ]
      intro β
      constructor
      · intro h
        induction h using Submodule.span_induction with
        | mem x hx => exact hx.1
        | zero => intro a b; simp [cc_zero']
        | add x y _ _ hx hy =>
          intro a b
          rw [Matrix.add_apply, Matrix.add_apply, cc_add', hx, hy]; ring
        | smul q x _ hx =>
          intro a b
          have hq : cc (q : E) = q := by simp [cc]
          rw [Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def, Rat.smul_def, cc_mul', hq, hx]
          ring
      · intro h
        obtain ⟨n, hn, hm⟩ := GlobalTheory.T.skew_matrix_multiple_in_lattice E r ρ (X c) cu β h
        have h1 := Submodule.smul_mem (Submodule.span ℚ (FJ.zGam (X c) cu)) ((n : ℚ)⁻¹)
          (Submodule.subset_span hm)
        rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
          one_smul] at h1)
  obtain ⟨bs, h1, h2⟩ := exists_int_basis_of_fg _ (GlobalTheory.T.span_cuspCentre_arithmeticGroup_fg E r ρ (X c) cu) hdim
  refine ⟨bs, h1, fun β => ?_⟩
  exact ((Set.ext_iff.1 hZ β).symm).trans (SetLike.ext_iff.1 h2 β).symm

end GlobalTheory.CuspCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenBasis_iff_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  first | exact @GlobalTheory.Frames.eigBasis_iff_tanBasis | exact GlobalTheory.Frames.eigBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.eigBasis_iff_tanBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionPowMulBaseChangeAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreSection_pow_mul_baseChange_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (g : S) (s' : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), ∃ (N : ℕ) (s : LB.Sec (PPx x)) (s₁ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x))), SecBC (algebraMap S (Localization.Away g)) 1 x _ s s₁ ∧ ∀ i, s₁.f i = scal _ ((algebraMap S (Localization.Away g)) g ^ N) i * s'.f i := by
  first | exact @GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | exact GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul | (intros; apply GlobalTheory.Frames.SecLoc.exists_secBC_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriods
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem exists_framePeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hg hb hn k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hg hb hn k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hφa : ∀ a, φ a = (M.φ k a : Fin r → E) := fun a => rfl
  obtain ⟨-, hφ'⟩ := hφ φ hφa
  have hemb : ∀ (τ : E →+* ℂ) (v w : Fin r → E), Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by
    intro τ v w
    funext a
    simp [Data.emb]
  let Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)) := fun x =>
    AddMonoidHom.mk' (fun a j => perFr (M.X k) x (φ a) (relab c σ (e j).1) (e j).2) (by
      intro a b
      funext j
      simp only [Pi.add_apply, hper, map_add, hemb]
      split_ifs
      · simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      · rw [Matrix.mulVec_add, Pi.add_apply])
  have hPf : IsPerFr e F M k Pf := fun x a j => rfl
  have hPf' : ∀ x v j, Pf x v j = if ((idx j).2 : ℕ) < (F.Di k).q then
      hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ v))
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ v)) (idx j).2 :=
    fun x v j => (hPf x v j).trans (hper x _ j)
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by rw [← hp0]
  obtain ⟨h1, h2⟩ := GlobalTheory.periods_eq_frame_periods E H Dw l Xo _ g _ F k r _ (M.X k).Gm φ (M.X k).Ψ idx Pf
    (hb.type k).2 hty hξ hpos hφ' hr hPf'
  have h3 := (GlobalTheory.per_move E H (F.Di k) r _ (M.X k).Gm φ (M.X k).Ψ (hb.type k).2 g idx _ hty hξ hpos hφ').1
    Pf hPf'
  rw [hdom]
  refine ⟨Pf, hPf, fun Pf' h' => ?_, fun x hx => (h1 x hx).1, h3, h2⟩
  funext x
  exact AddMonoidHom.ext fun a => funext fun j => (h' x a j).trans (hPf x a j).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelAllPrimes

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    ((c : 𝓞 E) + H.rt) * (c - H.rt) = ((c ^ 2 + H.d : ℕ) : 𝓞 E) := by
  push_cast
  linear_combination (-1 : 𝓞 E) * H.rt_sq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by
  have h2 : Nat.Coprime 2 (c ^ 2 + H.d) := (Nat.coprime_two_left).2 ho
  have hc' : Nat.Coprime c (c ^ 2 + H.d) := by
    rw [sq, add_comm]
    exact (Nat.coprime_add_mul_right_right c H.d c).2 hc
  have hcop : IsCoprime ((2 * c : ℕ) : ℤ) ((c ^ 2 + H.d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul h2 hc')
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Int.cast : ℤ → 𝓞 E) huv
  push_cast at key
  refine ⟨(u : 𝓞 E) + v * (c - H.rt), u, ?_⟩
  linear_combination key - (v : 𝓞 E) * H.rt_sq

end GlobalTheory.LevelAllPrimes

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem host_bar_rt' (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : starRingEnd ℂ (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz : z ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa [z] using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hx : z.re = 0 := by
      rcases mul_eq_zero.1 (by linarith : z.re * z.im = 0) with h | h
      · exact h
      · rw [h] at hre; nlinarith
    apply Complex.ext <;> simp [hx]
  have key : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
    rw [H.bar_eq]
    apply φ.injective
    simpa [IsCMField.complexEmbedding_complexConj] using hconj
  exact RingOfIntegers.coe_injective key

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem natCast_add_rt_mem_adjoin_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    (c : 𝓞 E) + H.rt ∈ Algebra.adjoin ℤ {H.w0} := by
  rw [show (c : 𝓞 E) + H.rt = ((c : 𝓞 E) - 1) + 2 * H.w0 by linear_combination -H.two_weight_eq_one_add_root]
  have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ H.w0
  have h2 : (2 : 𝓞 E) ∈ Algebra.adjoin ℤ {H.w0} := by
    simpa using natCast_mem (Algebra.adjoin ℤ {H.w0}) 2
  exact add_mem (sub_mem (natCast_mem _ c) (one_mem _)) (mul_mem h2 hw)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem three_le_mul_div_prime_pow_factorization {a b : ℕ} (p : ℕ) (hab : Nat.Coprime a b)
    (ha : 3 ≤ a) (hb : 3 ≤ b) : 3 ≤ a * b / p ^ (a * b).factorization p := by
  have key : ∀ {x y : ℕ}, 3 ≤ x → 0 < y → x.factorization p = 0 →
      3 ≤ x * y / p ^ (x * y).factorization p := by
    intro x y hx hy hxp
    rw [Nat.factorization_mul (by omega) hy.ne', Finsupp.add_apply, hxp, zero_add,
      Nat.mul_div_assoc x (Nat.ordProj_dvd y p)]
    have : 1 ≤ y / p ^ y.factorization p :=
      Nat.div_pos (Nat.le_of_dvd hy (Nat.ordProj_dvd y p)) (Nat.ordProj_pos y p)
    nlinarith
  by_cases hap : a.factorization p = 0
  · exact key ha (by omega) hap
  · have hbp : b.factorization p = 0 := by
      by_contra hbp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.2 hap)
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos hap
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos hbp
      have hg := Nat.dvd_gcd hpa hpb
      rw [hab.gcd_eq_one] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.1 hg)
    rw [mul_comm]
    exact key hb (by omega) hbp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.exists_level_goodAt_all_primes_and_idx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (A : ℕ), 0 < A →
      ∃ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.A = A ∧ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧
        ∀ p : ℕ, p.Prime → ∃ i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Idx H p, i.l = l := by
  intro E _ _ _ H A hA
  obtain ⟨k, hk⟩ : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  have h2d : Nat.Coprime 2 H.d := (Nat.coprime_two_left).2 ⟨k, hk⟩
  have h4d : Nat.Coprime (2 ^ 2 + H.d) H.d := by
    rw [Nat.coprime_add_self_left]
    exact Nat.Coprime.pow_left 2 h2d
  have hc1 : Nat.Coprime 2 H.d := h2d
  have hc2 : Nat.Coprime (2 * (2 ^ 2 + H.d)) H.d := Nat.Coprime.mul h2d h4d
  have ho1 : Odd (2 ^ 2 + H.d) := ⟨2 + k, by rw [hk]; ring⟩
  have ho2 : Odd ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    refine Even.add_odd ?_ ⟨k, hk⟩
    rw [sq]
    exact (even_two_mul _).mul_right _
  have hM : Nat.Coprime (2 ^ 2 + H.d) ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    rw [show (2 * (2 ^ 2 + H.d)) ^ 2 + H.d = H.d + (4 * (2 ^ 2 + H.d)) * (2 ^ 2 + H.d) by ring,
      Nat.coprime_add_mul_right_right]
    exact h4d
  have e1 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H 2
  have e2 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H (2 * (2 ^ 2 + H.d))
  set M₁ := 2 ^ 2 + H.d with hM₁
  set c := 2 * M₁ with hc
  set M₂ := c ^ 2 + H.d with hM₂
  have hMcop : IsCoprime (M₁ : 𝓞 E) (M₂ : 𝓞 E) := by
    have := (Nat.isCoprime_iff_coprime.2 hM).map (Int.castRingHom (𝓞 E))
    simpa using this
  set al := ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) with hal
  have hbar : H.bar al = ((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt) := by
    simp only [hal, map_mul, map_add, map_natCast, host_bar_rt', sub_eq_add_neg]
  have hmem : al ∈ Algebra.adjoin ℤ {H.w0} :=
    mul_mem (natCast_add_rt_mem_adjoin_w0 H 2) (natCast_add_rt_mem_adjoin_w0 H c)
  have hprod : al * H.bar al = ((M₁ * M₂ : ℕ) : 𝓞 E) := by
    rw [hbar, hal, show ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) * (((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt))
      = (((2 : ℕ) + H.rt) * ((2 : ℕ) - H.rt)) * (((c : 𝓞 E) + H.rt) * ((c : 𝓞 E) - H.rt)) by ring,
      e1, e2]
    exact (Nat.cast_mul _ _).symm
  have hcop : IsCoprime al (H.bar al) := by
    rw [hbar, hal]
    refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc1 ho1
    · exact (hMcop.of_isCoprime_of_dvd_left (Dvd.intro _ e1)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e2)
    · exact (hMcop.symm.of_isCoprime_of_dvd_left (Dvd.intro _ e2)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e1)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc2 ho2
  have h3₁ : 3 ≤ M₁ := by omega
  have h3₂ : 3 ≤ M₂ := by have := Nat.zero_le (c ^ 2); have := H.d_prime.two_le; omega
  obtain ⟨l, hlM, hlA, -⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).1 E H al (M₁ * M₂) A
    hmem hprod hcop (le_trans h3₁ (Nat.le_mul_of_pos_right _ (by omega)))
    (Nat.odd_mul.2 ⟨ho1, ho2⟩) hA
  have hgood : ∀ p : ℕ, p.Prime → l.GoodAt p := by
    intro p _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    rw [hlM]
    exact three_le_mul_div_prime_pow_factorization p hM h3₁ h3₂
  refine ⟨l, hlA, hgood, fun p hp => ?_⟩
  obtain ⟨cf⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).2.2 E H l
  exact ⟨{ l := l, c := cf, good := hgood p hp }, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPrimeOutsideLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_split_prime_outside_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (𝔓 : Ideal (𝓞 E)) (p : ℕ), 𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M' := by
  intro E _ _ _ H l
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  set c : ℕ := 2 * l.M' with hc
  have hd := H.d_prime.pos
  have hn : c ^ 2 * H.d + 1 ≠ 1 := by
    have : 0 < c ^ 2 * H.d := by positivity
    omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
  have hpc : ¬ p ∣ c := fun h => by
    have h1 : p ∣ c ^ 2 * H.d := (h.trans (dvd_pow_self c two_ne_zero)).mul_right _
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpn))
  have hp2 : ¬ p ∣ 2 := fun h => hpc (h.mul_right _)
  have hpM : ¬ p ∣ l.M' := fun h => hpc (h.mul_left _)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ)
      (by simpa using hp.ne_zero)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 E)).injective_int]
      exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hQc]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨Q, p, hQ, ?_, hp, hpQ, hpM⟩
  have hprod : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) ∈ Q := by
    obtain ⟨k, hk⟩ := hpn
    have h1 : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) = (p : 𝓞 E) * (k : 𝓞 E) := by
      have h2 : (c : 𝓞 E) ^ 2 * (H.d : 𝓞 E) + 1 = (p : 𝓞 E) * (k : 𝓞 E) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hk
      linear_combination h2 - (c : 𝓞 E) ^ 2 * H.rt_sq
    rw [h1]
    exact Q.mul_mem_right _ hpQ
  have key : ∀ β ∈ Q, β + H.bar β = 2 →
      Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    intro β hβ h2
    have hm2 : (2 : 𝓞 E) ∈ Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hβ)
        (Ideal.mem_sup_right (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hβ))
    have hcop : IsCoprime (p : 𝓞 E) ((2 : ℕ) : 𝓞 E) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hp2)
    obtain ⟨a, b, hab⟩ := hcop
    rw [Ideal.eq_top_iff_one, ← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hpQ))
      (Ideal.mul_mem_left _ _ ?_)
    simpa using hm2
  rcases hQ.isPrime.mem_or_mem hprod with h | h
  · refine key _ h ?_
    rw [map_add, map_mul, map_one, map_natCast, HostModel.bar_rt]; ring
  · refine key _ h ?_
    rw [map_sub, map_mul, map_one, map_natCast, HostModel.bar_rt]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponential
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.LieFrame

theorem sum_single_apply {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (a : Fin (m τ) → ℂ) (i : Fin (m τ)) :
    (∑ i', a i' • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ, i⟩) = a i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩ := fun h =>
      hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
    simp [Pi.single_eq_of_ne this]
  · simp

theorem eq_sum_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∑ i, w (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ) = w := by
  funext j
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  by_cases h : τ' = τ
  · subst h
    exact sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i
  · have h0 : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h0
      exact h (by simpa using hw _ h0)
    rw [h0, Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩ := fun h' => h (Sigma.mk.inj (e.symm.injective h')).1
    simp [Pi.single_eq_of_ne this]

theorem exists_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v := fun τ i => (h2 _).exists
  choose u hu using hu
  refine ⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩
  · refine (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_
    by_cases hji : j = e.symm ⟨τ, i⟩
    · subst hji
      simp
    · exact absurd (Pi.single_eq_of_ne hji _) hj
  · obtain ⟨z, hz, huniq⟩ := h3 w hw
    have hs := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew
    have hc := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)
    refine ⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩
    · rw [eq_sum_single e τ z hs]
      exact hz
    · have h4 := huniq _ ((hc a w).1 ha)
      funext i
      exact (sum_single_apply e τ a i).symm.trans (congrFun h4 _)

end GlobalTheory.LieFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  first | exact @GlobalTheory.Frames.lieBasis_iff_tanBasis | exact GlobalTheory.Frames.lieBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.lieBasis_iff_tanBasis <;> assumption)
end

