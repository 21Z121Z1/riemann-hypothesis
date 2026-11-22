import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecInjectiveRingMapCancellation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem spec_localInjective_cancel_left (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
    (φ : R →+* R') [IsLocalHom φ] (hφ : Function.Injective φ) (Y : Scheme.{0}) (a a' : Sp R ⟶ Y)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  obtain ⟨hcomp, -, -, hloc, hext, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint φ
  have hy : a (IsLocalRing.closedPoint R) = a' (IsLocalRing.closedPoint R) := by
    have := congrArg (fun f : Sp R' ⟶ Y => f (IsLocalRing.closedPoint R')) h
    exact (congrArg a hc).symm.trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (this.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg a' hc))))
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := a (IsLocalRing.closedPoint R))
    (U := ⊤) trivial
  have h1 : ⊤ ≤ a ⁻¹ᵁ U := (hloc R Y a U).2 hyU
  have h2 : ⊤ ≤ a' ⁻¹ᵁ U := (hloc R Y a' U).2 (hy ▸ hyU)
  have h1' : ⊤ ≤ (spMap φ ≫ a) ⁻¹ᵁ U := (hloc R' Y _ U).2 (((Scheme.Hom.comp_apply _ _ _).trans (congrArg a hc)) ▸ hyU)
  have h2' : ⊤ ≤ (spMap φ ≫ a') ⁻¹ᵁ U := h ▸ h1'
  have key : ∀ (b b' : Sp R' ⟶ Y) (_ : b = b') (hb : ⊤ ≤ b ⁻¹ᵁ U) (hb' : ⊤ ≤ b' ⁻¹ᵁ U),
      evAt b hb = evAt b' hb' := by
    rintro b _ rfl _ _; rfl
  refine hext R Y a a' U hU h1 h2 (RingHom.ext fun f => hφ ?_)
  rw [← hcomp R R' Y φ a U h1 h1' f, ← hcomp R R' Y φ a' U h2 h2' f, key _ _ h h1' h2']

theorem spec_injective_cancel_left_of_separated (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (hφ : Function.Injective φ)
    (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y) (hp : a ≫ p = a' ≫ p)
    (h : spMap φ ≫ a = spMap φ ≫ a') : a = a' := by
  let d : Sp R ⟶ pullback p p := pullback.lift a a' hp
  have e1 : a = d ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
  have e2 : a' = d ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
  let i : pullback d (pullback.diagonal p) ⟶ Sp R := pullback.fst _ _
  have hfac : spMap φ ≫ d = (spMap φ ≫ a) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, ← e2, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  let g : Sp R' ⟶ pullback d (pullback.diagonal p) := pullback.lift (spMap φ) (spMap φ ≫ a) hfac
  have hg : g ≫ i = spMap φ := pullback.lift_fst _ _ _
  have key : (spMap φ).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality]; simp
  have h2 : Function.Injective (spMap φ).appTop := by
    rw [key]
    exact ((Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.injective.comp hφ).comp
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
  have hinj : Function.Injective i.appTop := by
    rw [← hg, Scheme.Hom.comp_appTop] at h2
    exact Function.Injective.of_comp h2
  have : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have hd : d = inv i ≫ pullback.snd _ _ ≫ pullback.diagonal p := by
    rw [← pullback.condition]; simp [i]
  rw [e1, e2, hd]; simp

theorem spMap_injective_cancel : (∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ], Function.Injective φ → ∀ (Y : Scheme.{0}) (a a' : Sp R ⟶ Y), spMap φ ≫ a = spMap φ ≫ a' → a = a') ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R'), Function.Injective φ → ∀ (S Y : Scheme.{0}) (p : Y ⟶ S) [IsSeparated p] (a a' : Sp R ⟶ Y), a ≫ p = a' ≫ p → spMap φ ≫ a = spMap φ ≫ a' → a = a') :=
  ⟨fun R R' _ _ _ _ φ _ hφ Y a a' h => spec_localInjective_cancel_left R R' φ hφ Y a a' h,
    fun R R' _ _ φ hφ S Y p _ a a' hp h => spec_injective_cancel_left_of_separated R R' φ hφ S Y p a a' hp h⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem completed_eq {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L) {s : ℂ}
    (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) : Λ s = archFactor n s * L s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  let g : ℂ → ℂ := fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹)
  have key : ∀ z : ℂ, (∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) → archFactor n z *
      ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := fun z hz => by
    unfold archFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz i), one_mul]
  have hg : Differentiable ℂ g := by
    refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hgL : g = L := entire_eq_of_halfPlane hg hL.1 1 fun z hz => by
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      have := abs_nonneg (n i)
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      linarith)
    show Λ z * _ = L z
    rw [h.eq_mul hL hz, mul_comm (archFactor n z), mul_assoc, key z hz', mul_one]
  calc Λ s = Λ s * (archFactor n s * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹)) := by rw [key s hs, mul_one]
    _ = archFactor n s * g s := by ring
    _ = archFactor n s * L s := by rw [hgL]

end GlobalTheory.LValNe

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem nonempty_of_isCMType {φ : I → E →+* ℂ} (hφ : IsCMType φ) : Nonempty I := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := hφ w.embedding
  exact ⟨i⟩

theorem exists_heckeL [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ)
    (hm : HasInf χ φ m) (hpos : ∀ i, 0 < m i) : ∃ Λ, IsHeckeL χ Λ := by
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  exact GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ m χ hφ hu hm ⟨i₀, (hpos i₀).ne'⟩

theorem gamma_int_ne_zero {k : ℤ} (hk : 0 < k) : Complex.Gamma (k : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.intCast_re]; exact_mod_cast hk)

theorem half_abs_two_mul (a : ℤ) (ha : 0 < a) : ((|2 * a| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_of_pos (by omega)]; push_cast; ring

theorem half_abs_neg_two_mul (a : ℤ) (ha : 0 < a) : ((|-(2 * a)| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_neg, half_abs_two_mul a ha]

theorem archFactor_ne_zero {n : I → ℤ} {s : ℂ} (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) :
    archFactor n s ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (hs i)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

theorem heckeL_ne_zero_int (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 := by
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  have hn : ∃ i, 2 * m i ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hn' : ∃ i, -(2 * m i) ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hm' : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -(2 * m i)) := GlobalTheory.Published.HeckeFEModel.hasInf_inv hm
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hmi : HasInf χ⁻¹ φ (fun i => -m i) := by
    have e : (fun i => 2 * -m i) = fun i => -(2 * m i) := funext fun i => by ring
    show Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => 2 * -m i)
    rw [e]; exact hm'
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ (fun i => 2 * m i) hu hm hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -(2 * m i)) hu' hm' hn'
  obtain ⟨L', hL'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ (fun i => -m i) χ⁻¹ hφ hu' hmi
    ⟨i₀, by have := hpos i₀; omega⟩

  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-(2 * m i)| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_neg_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (k := 1 - s + m i) (by have := hpos i; omega)
    push_cast at this; exact this
  have e1 := completed_eq hΛ' hL' g1
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 =>
    hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hm hn hΛ hΛ' s).1 h0)

  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|2 * m i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (hs i)
    push_cast at this; exact this
  rw [completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end GlobalTheory.LValNe

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem squareBottomHalfRankDiff_le_halfRank (D : D7) (i j : ℕ) : e0 D i j ≤ halfRank D i j := by
  unfold e0 halfRank botBig botSmall
  omega

theorem lNe_square (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := by
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  have hpos : ∀ τ, 0 < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := fun τ => by
    have := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).2
    omega
  have fam_ok : ∀ χ : HChar D.host.E, IsValChar (cmPhi D) 0 (kap D sc.cGap i j 0) (condF G.pl) ∅ χ →
      ∃ Λ, IsHeckeL χ Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := fun χ h => by
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ h.1 h.2.2.1 hpos
    exact ⟨Λ, hΛ, fun s hs => hΛ.ne_zero_nat h.1 hs⟩
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
      simp only [nuH, hL.xi_base, mul_one]
      exact mul_div_right_comm _ _ _
    obtain ⟨n, hn, hf⟩ := hL.xi_fin t
    have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
    have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
      intro k
      rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (Lc.xiH t) hn hf k, mul_one]
      exact hv.1.2.2.1 k
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ hu hm hpos
    refine ⟨Λ, hΛ, fun s hs1 hs2 => GlobalTheory.LValNe.heckeL_ne_zero_int hFE hB hφ hu hm hpos hΛ s fun τ => ?_⟩
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 := squareBottomHalfRankDiff_le_halfRank D i j
    omega
  · cases c with
    | none => exact fam_ok _ hv.1
    | some c => exact fam_ok _ (hv.2 c)

theorem lNe_of_functionalEquation :
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe := by
  intro hFE hB hFD
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, -, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  exact fun i j => lNe_square hFE hB hφ hL G i j

end GlobalTheory.SqTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
section
open GlobalTheory.SqTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest

namespace GlobalTheory.SqTop

theorem exists_coord_ne_of_norm_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}
    (P : GlobalTheory.NormSum.Pair D cc δ t0 Q) (h : P.norm ≠ 0) : ∃ g T, P.coord g T ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [GlobalTheory.NormSum.Pair.norm, GlobalTheory.NormSum.Pair.sq, hc]

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  simp only [h0, botBig, botSmall, halfRank]
  omega

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsSmallReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BotSmall

theorem bottom_small : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  intro D T L sc μ₀ hL G δ t0 Q P P' i j 𝔪 hB
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hB.rank
  have hd : P.d ≤ 2 * bigN D := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    have hj := j.2
    obtain ⟨e1, e2, -⟩ := ranks_exact D i j
    have h1 : rankV D (i + 1) (j + 1) ≤ bigN D - 1 := by
      simp only [rankV, bigN, Ranks.r]
      have : (↑i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
      have : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
      omega
    have h2 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by
      simp only [rankV]
      have : (↑i) * sLen D ≤ (↑i + 1) * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j) * D.R.t ≤ (↑j + 1) * D.R.t := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

  have key : ∀ (R : Pair D ⊤ δ t0 Q) (χ : Formalism.L2.Host.HChar D.host.E),
      HasChars R χ (nuH G μ₀ i j)⁻¹ → R.d = botBig D i j + botSmall D i j → ∀ τ, (R.n τ : ℝ) ≤ 2 * (maxWt D sc.cGap : ℝ) := by
    intro R χ hc hRd τ
    have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType R.W.chV' R.W.ep' (nuH G μ₀ i j)⁻¹ _ R.W.ep_pm.2 hc.2
      (nuH_inv_hasInf hL G i j) τ
    have hw := R.wt τ
    have hsub := two_mul_wtA_sub D sc.cGap i j τ
    set E := (num D sc.cGap τ).e (↑j + 1) + cen D sc.cGap τ (D.R.m - ↑i)
    have hA : (wtA D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap ∧ (wtA' D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap := by
      have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
      have h2 := le_max_right 1 (Finset.univ.sup fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs)
      simp only at this
      exact ⟨le_trans (le_max_left _ _) (this.trans h2), le_trans (le_max_right _ _) (this.trans h2)⟩
    have hA1 : |wtA D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.1
    have hA2 : |wtA' D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.2
    have hep : |(R.W.ep' : ℤ) * R.W.chV'.n τ| = |2 * E| := by
      rw [abs_mul, ← habs]
      rcases R.W.ep_pm.2 with h | h <;> rw [h] <;> simp
    have hdz : (R.d : ℤ) = (botBig D i j : ℤ) + (botSmall D i j : ℤ) := by rw [hRd]; push_cast; ring
    have hn : (R.n τ : ℤ) ≤ 2 * (maxWt D sc.cGap : ℤ) := by
      have hnn : (0 : ℤ) ≤ R.n τ := Nat.cast_nonneg _
      have hpos : 0 ≤ (R.W.ep' : ℤ) * R.W.chV'.n τ := by push_cast at hw; omega
      rw [abs_of_nonneg hpos] at hep
      have h1 := abs_le.1 hA1
      have h2 := abs_le.1 hA2
      rcases le_or_gt 0 E with hE | hE
      · rw [abs_of_nonneg (by omega)] at hep
        push_cast at hw hsub; omega
      · rw [abs_of_neg (by omega)] at hep
        push_cast at hw hsub; omega
    exact_mod_cast hn
  exact ⟨⟨hd, key P _ hB.chars hr3⟩, ⟨hr4 ▸ hd, key P' _ hB.chars' (hr4.trans hr3)⟩⟩

end GlobalTheory.BotSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamTwist

theorem unramAt_of_div {D : D7} {ε : AF D.host.F} {a b c : (AE D)ˣ →* Circle}
    (h : GlobalTheory.WeilParts.UnramAt ε (a * b / c)) (ha : GlobalTheory.WeilParts.UnramAt ε a) (hc : GlobalTheory.WeilParts.UnramAt ε c) :
    GlobalTheory.WeilParts.UnramAt ε b := by
  intro x h1 h2 h3
  have e := h x h1 h2 h3
  rw [MonoidHom.div_apply, MonoidHom.mul_apply, ha x h1 h2 h3, hc x h1 h2 h3, one_mul, div_one] at e
  exact e

theorem not_overP_g {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ G.pl.S0) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (hPP : PP.under (𝓞 D.host.F) = v) (k : Fin 2) : ¬ Formalism.L2.Host.OverP D.host (D.host.g k) PP := by
  intro h
  have hk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    subst hPP
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rw [map_natCast]
    exact h
  refine hv (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)

end GlobalTheory.RamTwist

open GlobalTheory.RamTwist in

theorem GlobalTheory.SqTop.not_unramAt_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hμ t v e he hv PP hPP hPv i j hU
  have hmi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hmi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ hmi1 hmi2) v e he fun P hP =>
      G.ch.unr _ hmi1 hmi2 P (hP ▸ hv)
  have hmu : GlobalTheory.WeilParts.UnramAt e (Lc.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hμ.mu0 j) v e he fun P hP =>
      (Lc.C.isMu0 j).unr P (not_overP_g G hv P hP)
  have hxi : GlobalTheory.WeilParts.UnramAt e (Lc.xi t) := by
    refine unramAt_of_div (a := Lc.mu0 ((j : ℕ) + 1)) (c := G.ch.chi (D.R.m - i)) ?_ hmu hchi
    exact hU
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D (Lc.xi t) v e he hxi PP hPv
  exact (hμ.Q_ram t PP).2 (Or.inl hPP) ((GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ.xi t) PP).1 h1)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
section
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem nuH_not_unrAt_twPl : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  intro D T L sc G μ₀ hL t i j P hP
  classical
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hxi : ¬ (L.xiH t).UnrAt P := (hL.Q_ram t P).2 (Or.inl hP'.1)
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 ?_)
  · have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
    intro hnu
    apply hxi
    have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

end GlobalTheory.SqTop
end

