import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspaces
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem eig_map_equivariant : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O), (∀ l, X * ρ l = ρ' l * X) → (∀ σ : Λ →+* O, (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C))) ≤ eig C ρ' σ) ∧ ((⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → ∀ σ : Λ →+* O, LinearMap.range (Matrix.toLin' (X.map (algebraMap O C))) ⊓ eig C ρ' σ = (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C)))) := by
  intro C _ O _ _ Λ _ h ρ ρ' X hX
  set f := Matrix.toLin' (X.map (algebraMap O C)) with hf
  have hcomm : ∀ (l : Λ) (v : Fin h → C), f (Matrix.toLin' ((ρ l).map (algebraMap O C)) v) =
      Matrix.toLin' ((ρ' l).map (algebraMap O C)) (f v) := by
    intro l v
    have e : X.map (algebraMap O C) * (ρ l).map (algebraMap O C) =
        (ρ' l).map (algebraMap O C) * X.map (algebraMap O C) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hX l]
    simp only [hf, Matrix.toLin'_apply, Matrix.mulVec_mulVec, e]
  have h1 : ∀ σ : Λ →+* O, (eig C ρ σ).map f ≤ eig C ρ' σ := by
    intro σ y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro a
    rw [← hcomm, hx a, map_smul]
  refine ⟨h1, fun htop hind σ => le_antisymm ?_ ?_⟩
  · rintro y ⟨⟨z, rfl⟩, hy⟩
    have hz : z ∈ eig C ρ σ ⊔ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j := by
      rw [← iSup_split_single (fun j : Λ →+* O => eig C ρ j) σ, htop]
      trivial
    obtain ⟨x, hx, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
    have hfx : f x ∈ eig C ρ' σ := h1 σ (Submodule.mem_map_of_mem hx)
    have hother : f z' ∈ ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j := by
      have hle : (⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ j).map f ≤
          ⨆ (j : Λ →+* O) (_ : j ≠ σ), eig C ρ' j := by
        rw [Submodule.map_iSup]
        refine iSup_le fun j => ?_
        rw [Submodule.map_iSup]
        exact iSup_le fun hj => (h1 j).trans (le_iSup₂_of_le j hj le_rfl)
      exact hle (Submodule.mem_map_of_mem hz')
    have hself : f z' ∈ eig C ρ' σ := by
      have e : f z' = f (x + z') - f x := by simp
      rw [e]
      exact Submodule.sub_mem _ hy hfx
    have h0 : f z' = 0 := by
      have := (hind σ).le_bot (Submodule.mem_inf.mpr ⟨hself, hother⟩)
      simpa using this
    refine Submodule.mem_map.mpr ⟨x, hx, ?_⟩
    simp [h0]
  · exact le_inf (LinearMap.map_le_range) (h1 σ)

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlatStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertible_of_faithfully_flat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  first | exact @GlobalTheory.FFDescent.invertible_of_invertible_baseChange | exact GlobalTheory.FFDescent.invertible_of_invertible_baseChange | (intros; apply GlobalTheory.FFDescent.invertible_of_invertible_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdealStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (I : Ideal R), I ≤ maximalIdeal R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_maximalIdeal | exact GlobalTheory.isAdicComplete_of_le_maximalIdeal | (intros; apply GlobalTheory.isAdicComplete_of_le_maximalIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

theorem preimage_spMap_comp_eq_top {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by
  rw [Scheme.Hom.comp_preimage, h, Scheme.Hom.preimage_top]

theorem chartHom_spMap_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (u : Sp S ⟶ Y) (h : u ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ u) ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V (spMap g ≫ u) h' x = g (chartHom V u h x) := by
  have e1 : ((spMap g ≫ u).appLE V ⊤ h'.ge).hom x = (spMap g).appTop.hom ((u.appLE V ⊤ h.ge).hom x) := by
    have e : (spMap g).appTop = (spMap g).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [e]
    exact (congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE (spMap g) u V ⊤ ⊤ h.ge le_top)).symm
  have e2 := congrArg (fun q => q.hom ((u.appLE V ⊤ h.ge).hom x))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g))
  simp only [chartHom, RingHom.comp_apply]
  rw [e1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
  exact e2

theorem isCombIn_spMap_comp (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S']
    (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) (hC : IsCombIn V u c w a) :
    IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  obtain ⟨hu, hc, hw, hx⟩ := hC
  refine ⟨preimage_spMap_comp_eq_top g hu, preimage_spMap_comp_eq_top g hc,
    fun i => preimage_spMap_comp_eq_top g (hw i), fun x => ?_⟩
  rw [chartHom_spMap_comp V g c hc, chartHom_spMap_comp V g u hu, hx x, map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [chartHom_spMap_comp V g (w i) (hw i), map_mul, map_sub]

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartUnique
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

theorem eq_of_chartHom_eq {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type}
    [CommRing S] (c c' : Sp S ⟶ Y) (hc : c ⁻¹ᵁ V = ⊤) (hc' : c' ⁻¹ᵁ V = ⊤)
    (e : ∀ x, chartHom V c hc x = chartHom V c' hc' x) : c = c' := by
  have e₁ : c.appLE V ⊤ hc.ge = c'.appLE V ⊤ hc'.ge := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of S)).hom]
    exact CommRingCat.hom_ext (RingHom.ext e)
  have a := IsAffineOpen.SpecMap_appLE_fromSpec c hV (isAffineOpen_top (Sp S)) hc.ge
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec c' hV (isAffineOpen_top (Sp S)) hc'.ge
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem combIn_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  intro Y V hV S _ ι _ u c c' w a h h'
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hV c c' hc hc' fun x => ?_
  rw [e x, e' x]

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  first | exact @GlobalTheory.BoundedGL.isCompact_bounded | exact GlobalTheory.BoundedGL.isCompact_bounded | (intros; apply GlobalTheory.BoundedGL.isCompact_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBounds
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem isCompact_pi_upperHalfPlane_im_bounds :
    ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  intro ι _ L hL hpos
  obtain ⟨C, hC⟩ := hL.isBounded.exists_norm_le
  have hup : ∀ z ∈ L, ∀ i, (z i).im ≤ C := fun z hz i =>
    (Complex.im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hC z hz))
  rcases L.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, 0, one_pos, by simp [hE]⟩
  have hm : ∀ i, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ L, m ≤ (z i).im := by
    intro i
    have hc : Continuous fun z : ι → ℂ => (z i).im :=
      Complex.continuous_im.comp (continuous_apply i)
    obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hne hc.continuousOn
    exact ⟨(x i).im, hpos x hx i, fun z hz => hmin hz⟩
  choose m hm0 hmle using hm
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, C, one_pos, fun z _ i => isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty m, C, ?_, fun z hz i => ⟨?_, hup z hz i⟩⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hm0 i
  · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hmle i z hz)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

theorem isField_stalk_genPt :
    ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ _ hW
  haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)
  refine isField_stalk_of_forall_specializes _ fun z hz => ?_
  obtain ⟨y, rfl⟩ : z ∈ Set.range π := hz.mem_open hW ⟨_, rfl⟩
  exact (hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  first | (exact @GlobalTheory.HilbAff.good_xI) | (exact GlobalTheory.HilbAff.good_xI) | (intros; apply GlobalTheory.HilbAff.good_xI  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartTwistedInductionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInCharacterIsotypicPart_twistedInduction : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (τ : G → G) (φ Y : H → ℂ), Kills φ Y → Kills (fun x => (Nat.card H : ℂ)⁻¹ * ∑ᶠ y : G, ext0 H φ (y⁻¹ * x * τ y)) (ind H Y) := by
  first | (exact @GlobalTheory.Shin.IndIso.kills_ind) | (exact GlobalTheory.Shin.IndIso.kills_ind) | (intros; apply GlobalTheory.Shin.IndIso.kills_ind  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegerOfMaximalIdealPowSmulIsIntegerStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInteger_of_maximalIdeal_pow_smul_isInteger' : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k, IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  first | exact @GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | exact GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger | (intros; apply GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma one_sub_mul_sum_range_natCast_mul_pow_add (x : ℂ) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, (i : ℂ) * x ^ i + n * x ^ n =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one (ζ : ℂ) (M : ℕ) (hζ : IsIntegral ℤ ζ)
    (hM : ζ ^ M = 1) (h1 : ζ ≠ 1) : IsIntegral ℤ ((M : ℂ) / (1 - ζ)) := by
  have hsub : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ (i + 1) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, geom_sum_eq h1, hM, sub_self, zero_div, zero_mul]
  have key := one_sub_mul_sum_range_natCast_mul_pow_add ζ M
  rw [hgeom, hM, mul_one] at key
  have hq : (M : ℂ) / (1 - ζ) = -∑ i ∈ Finset.range M, (i : ℂ) * ζ ^ i := by
    rw [div_eq_iff hsub]
    linear_combination key
  rw [hq]
  exact (IsIntegral.sum _ fun i _ => (isIntegral_natCast i).mul (hζ.pow i)).neg

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

theorem _root_.GlobalTheory.WpFam.isIntegral_coefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
  intro N _ M x k _ hx
  obtain ⟨-, -, hzero, -, hpow, -, -, hint⟩ :=
    _root_.GlobalTheory.WpFam.AddCharZMod.main N
  have h12 : IsIntegral ℤ (12 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 12
  have htw : ∀ (a : ℕ) (s : ℂ), IsIntegral ℤ s →
      IsIntegral ℤ (_root_.GlobalTheory.WpFam.cSum N a s x k) := by
    intro a s hs
    unfold _root_.GlobalTheory.WpFam.cSum
    refine IsIntegral.sum _ fun m _ => ((isIntegral_natCast m).pow a).mul ?_
    refine IsIntegral.add ?_ (hs.mul ?_)
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
  have hG : IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
    unfold _root_.GlobalTheory.WpFam.cG
    split_ifs
    · rw [show (12 : ℂ) * (-1 / 12) = -1 by norm_num]
      exact isIntegral_one.neg
    · exact h12.mul ((isIntegral_natCast 2).mul (isIntegral_natCast _))
    · simp [isIntegral_zero]
  have hB : IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) := by
    unfold _root_.GlobalTheory.WpFam.cB _root_.GlobalTheory.WpFam.cD
    split_ifs with hk h0
    · by_cases h1 : _root_.GlobalTheory.WpFam.ch N (x 1) = 1
      · simp [h1, isIntegral_zero]
      · have hζM : _root_.GlobalTheory.WpFam.ch N (x 1) ^ M = 1 := by
          have hx1 := congr_fun hx 1
          simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hx1
          rw [← hpow, hx1, hzero]
        have hq := isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one _ M (hint (x 1)) hζM h1
        constructor
        · rw [show (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.ch N (x 1) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 2)
              = _root_.GlobalTheory.WpFam.ch N (x 1) * ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 2 by
              rw [div_pow]; ring]
          exact (hint _).mul (hq.pow 2)
        · rw [show (M : ℂ) ^ 3 * (_root_.GlobalTheory.WpFam.ch N (x 1) * (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) /
              (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 3) = _root_.GlobalTheory.WpFam.ch N (x 1) *
              (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) *
              ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 3 by rw [div_pow]; ring]
          exact ((hint _).mul (isIntegral_one.add (hint _))).mul (hq.pow 3)
    · simp [isIntegral_zero]
    · exact ⟨((isIntegral_natCast M).pow 2).mul (htw 1 1 isIntegral_one),
        ((isIntegral_natCast M).pow 3).mul (htw 2 (-1) isIntegral_one.neg)⟩
  refine ⟨hB.1, hB.2, ?_, hG⟩
  unfold _root_.GlobalTheory.WpFam.cP
  split_ifs
  · simp [isIntegral_zero]
  · rw [show 12 * (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.cB N x k - _root_.GlobalTheory.WpFam.cG N k)
        = 12 * ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) -
          (M : ℂ) ^ 2 * (12 * _root_.GlobalTheory.WpFam.cG N k) by ring]
    exact (h12.mul hB.1).sub (((isIntegral_natCast M).pow 2).mul hG)

end GlobalTheory.WpFam
end

