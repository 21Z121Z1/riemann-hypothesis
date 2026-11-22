import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uIsLab_onto_and_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR', G, _, α, β, -, -, -, y₀, hy₀, u, lb, j, -, hyy, -⟩ := hl
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = lb.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one ct.cen ((X.M.O z).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u lb hint
  rw [hker, ← hcl.2]
  obtain ⟨x₀, hx₀⟩ := X.hasDiv z
  set val := X.M.val (gPt p ≫ ct.y) with hval
  have hsp : ∀ w, (gPt p ≫ ct.y) w ⤳ (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z :=
    RatModel.gPt_specializes ct.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X.S.th x, hth x⟩ = val (c₀ * X.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X.S.th x)‖ = ‖val (X.S.th x / X.S.th x₀)‖ * ‖val (c₀ * X.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one ct.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X.S.supI X.M z ↔
      ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X.M.Div X.S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff ct.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan.KSUniv

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

noncomputable def reparam {K : Type} [Field K] (F : Type) [Field F] [Algebra F K] {ι : Type} [Fintype ι]
    (P : Matrix ι ι K) : TrivSqZeroExt K (ι → K) →ₐ[F] TrivSqZeroExt K (ι → K) :=
  (TrivSqZeroExt.map (Matrix.mulVecLin P.transpose)).restrictScalars F

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {ι : Type} [Fintype ι] {X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X} (h1 : X ≫ Xo.s = sOf c _)
    (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) (M : ι → K) :
    GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, sOf, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (GlobalTheory.FlagTan.dir c M).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp

theorem dir_comp_reparam {K : Type} [Field K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} {c : Coeff l} [Algebra c.F K] {ι : Type} [Fintype ι] (P : Matrix ι ι K) (M : ι → K) :
    (GlobalTheory.FlagTan.dir c M).toRingHom.comp (reparam c.F P).toRingHom = (GlobalTheory.FlagTan.dir c (P.mulVec M)).toRingHom := by
  ext z
  · simp [reparam]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir, reparam,
      AlgHom.restrictScalars_apply, GlobalTheory.FlagTan.fst_dir, TrivSqZeroExt.snd_map, Matrix.mulVecLin_apply]
    have e := Matrix.dotProduct_mulVec z.snd P M
    rw [← Matrix.mulVec_transpose] at e
    simpa [dotProduct, mul_comm] using e.symm

open GlobalTheory.FlagTan in

theorem ksUniv : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := GlobalTheory.T.tangent_flag_hodge_index_vanishing hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((GlobalTheory.T.kodaira_spencer_zero_tangent_trivial hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this

end GlobalTheory.FlagTan.KSUniv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAll
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceRingExists

theorem norm_le_one_of_isIntegral_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_prime_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)

theorem exists_isPlaceOver : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ R : Subring ℂ, IsPlaceOver l lam k R := by
  intro l _ lam k hk
  haveI : NumberField k := { }
  have hle : k ≤ algebraicClosure ℚ ℂ := fun x hx =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)
  let f : k →+* ℂ_[l] := lam.comp (IntermediateField.inclusion hle).toRingHom
  have hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1 := fun a =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe a) using 1 <;>
        first | exact Subsingleton.elim _ _ | rfl)
  let P : Ideal (𝓞 k) :=
    { carrier := {a | ‖f a‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        calc ‖f c‖ * ‖f a‖ ≤ 1 * ‖f a‖ := by gcongr; exact hO c
          _ < 1 := by simpa using ha }
  have hmemP : ∀ a, a ∈ P ↔ ‖f a‖ < 1 := fun _ => Iff.rfl
  have hPp : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmemP]; simp
    · have e : ((a * b : 𝓞 k) : k) = (a : k) * b := rfl
      rw [hmemP, e, map_mul, norm_mul] at hab
      by_contra h
      push_neg at h
      rw [hmemP, hmemP, not_lt, not_lt] at h
      nlinarith [hO a, hO b]
  have hlP : ((l : ℕ) : 𝓞 k) ∈ P := by
    have e : (((l : ℕ) : 𝓞 k) : k) = ((l : ℕ) : k) := by simp
    rw [hmemP, e, map_natCast]; exact norm_prime_lt_one l
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hlP
    exact (Fact.out : l.Prime).ne_zero hlP
  have hS : P.primeCompl ≤ nonZeroDivisors (𝓞 k) := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField k P.primeCompl hS
  haveI : IsLocalization.AtPrime A P := Localization.subalgebra.isLocalization_ofField k _ hS
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) hP0 A
  haveI : IsFractionRing A k := Localization.subalgebra.isFractionRing_ofField k _ hS
  have hS1 : ∀ s : 𝓞 k, s ∈ P.primeCompl → ‖f s‖ = 1 := fun s hs =>
    le_antisymm (hO s) (not_lt.1 hs)
  have hA : ∀ x : k, x ∈ A ↔ ‖f x‖ ≤ 1 := by
    intro x
    constructor
    · rintro ⟨r, s, hs, rfl⟩
      rw [map_mul, map_inv₀, norm_mul, norm_inv]
      change ‖f (r : k)‖ * ‖f (s : k)‖⁻¹ ≤ 1
      rw [hS1 s hs, inv_one, _root_.mul_one]; exact hO r
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem A
      rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
      · rw [← ha]; exact a.2
      · obtain ⟨r, s, hs, hrs⟩ := a.2
        have ha' : (a : k) = x⁻¹ := ha
        rw [ha'] at hrs
        have hs0 : (s : k) ≠ 0 := by
          intro h0; apply hs; rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact P.zero_mem
        have hr0 : (r : k) ≠ 0 := by
          intro h0
          have h0' : algebraMap (𝓞 k) k r = 0 := h0
          rw [h0', zero_mul, inv_eq_zero] at hrs; exact hx0 hrs
        have hxe : x = (s : k) * (r : k)⁻¹ := by
          rw [← inv_inv x, hrs, mul_inv, inv_inv, mul_comm]
        have hr1 : ‖f r‖ = 1 := by
          refine le_antisymm (hO r) ?_
          have := hx
          rw [hxe, map_mul, map_inv₀, norm_mul, norm_inv] at this
          change ‖f (s : k)‖ * ‖f (r : k)‖⁻¹ ≤ 1 at this
          rw [hS1 s hs, _root_.one_mul] at this
          have hpos : 0 < ‖f (r : k)‖ := norm_pos_iff.2 ((map_ne_zero f).2 hr0)
          rwa [inv_le_one₀ hpos] at this
        exact ⟨s, r, fun h => by have h' := (hmemP r).1 h; rw [hr1] at h'; exact lt_irrefl _ h', hxe⟩

  let g : k →+* ℂ := k.val.toRingHom
  let R : Subring ℂ := A.toSubring.map g
  let e : A.toSubring ≃+* R := Subring.equivMapOfInjective A.toSubring g g.injective
  haveI : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)
  haveI : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  refine ⟨R, this, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxA, rfl⟩ := Subring.mem_map.1 hz
    refine ⟨hle x.2, ?_⟩
    rw [Real.rpow_zero]
    exact (hA x).1 hxA
  · rintro z hz ⟨h, hn⟩
    rw [Real.rpow_zero] at hn
    exact Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩

end GlobalTheory.PlaceRingExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSectionUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnitValuedLeadingSection

variable (R : Type) [CommRing R] [IsDomain R]

def thK (z : (TK R).left) : FractionRing R →+* (TK R).left.presheaf.stalk z :=
  ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

def uK (z : (TK R).left) : Rˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  Units.map ((thK R z).comp (algebraMap R (FractionRing R))).toMonoidHom

variable {R}

def TopGood (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) : Prop :=
  Good P.L z J ∧ ∀ x : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x ⁻¹ᵁ P.L.U (J (jK R ≫ x)) = ⊤

theorem gm_top_unit {R : Type} [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (v : Γ(Spec (CommRingCat.of R), V)ˣ) (z : (TK R).left) : ∃ u : Rˣ, gm (jK R) z V v = uK R z u := by
  subst hV
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom v, Units.ext ?_⟩
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  simp only [gm, dif_pos hz]
  have e := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v : Γ(Spec (CommRingCat.of R), ⊤))))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp [uK, thK, pullU]
  rw [CommRingCat.hom_ofHom] at e
  have hv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (v : Γ(Spec (CommRingCat.of R), ⊤))) = v := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e, hv]
  rfl

theorem val_section_unit {R : Type} [CommRing R] [IsDomain R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) (hJ : TopGood P z J) {Y : Scheme.{0}} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb P.L φ ε))
    (q : Spec (CommRingCat.of R) ⟶ Y) (hq : ∀ k, (q ≫ φ k) ≫ P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, val t (jK R ≫ q) z J = uK R z u := by
  have htop : q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) = ⊤ := by
    refine eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => ?_
    have h := hJ.2 (q ≫ φ k) (hq k)
    have : p ∈ (q ≫ φ k) ⁻¹ᵁ P.L.U (J (jK R ≫ q ≫ φ k)) := by rw [h]; trivial
    show q p ∈ (φ k) ⁻¹ᵁ P.L.U (J ((jK R ≫ q) ≫ φ k))
    rw [Category.assoc]
    exact this
  have hz : q (jK R z) ∈ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by
    have : jK R z ∈ q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by rw [htop]; trivial
    exact this
  obtain ⟨u, hu⟩ := gm_top_unit _ htop (pullU q _ (t.s (fun k => J ((jK R ≫ q) ≫ φ k)))) z
  exact ⟨u, (gm_pull (jK R) q z _ hz _).symm.trans hu⟩

theorem exists_topGood (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) : ∃ J, TopGood P z J := by
  classical
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have hext : ∀ x x' : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x' ≫ P.A.hom = 𝟙 _ →
      jK R ≫ x = jK R ≫ x' → x = x' := fun x x' hx hx' h =>
    ext_of_isDominant_of_isSeparated P.A.hom (hx.trans hx'.symm) (jK R) h
  choose top htop using fun x : Spec (CommRingCat.of R) ⟶ P.A.left =>
    ReciprocityTheory.ChartRestriction.G.DVR.GC.exists_chart_top P.L P.isLB x
  choose d hd using fun φ : (TK R).left ⟶ P.A.left => exists_chart P.isLB (φ z)
  refine ⟨fun φ => if h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ then top h.choose else d φ,
    fun φ => ?_, fun x hx => ?_⟩
  · by_cases h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ
    · simp only [dif_pos h]
      have m : jK R z ∈ h.choose ⁻¹ᵁ P.L.U (top h.choose) := by rw [htop]; trivial
      have m' : (jK R ≫ h.choose) z ∈ P.L.U (top h.choose) := m
      rwa [h.choose_spec.2] at m'
    · simp only [dif_neg h]; exact hd φ
  · have h : ∃ x', x' ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x' = jK R ≫ x := ⟨x, hx, rfl⟩
    simp only [dif_pos h]
    rw [hext _ _ h.choose_spec.1 hx h.choose_spec.2]
    exact htop x

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocalTrivial
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

theorem GlobalTheory.VB.exists_common_trivialization : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ x : B, ∃ U : B.Opens, x ∈ U ∧ ∀ a, Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅ GlobalTheory.QCoh.freeModule (X := U.toScheme) (Fin (r a))) := by
  intro B ι _ E r hE x
  choose U e hx he using fun a => hE a x
  let V : B.Opens := Finset.univ.inf U
  have hxV : x ∈ V := by
    show x ∈ ((Finset.univ.inf U : B.Opens) : Set B)
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hx
  have hV (a : ι) : V ≤ U a := Finset.inf_le (Finset.mem_univ a)
  refine ⟨V, hxV, fun a => ⟨?_⟩⟩
  have hle : V.ι ''ᵁ ⊤ ≤ U a := (V.ι_image_le ⊤).trans (hV a)
  exact ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)).symm ≪≫
    ((GlobalTheory.VB.isFrame_freeFrame _ _).iso
      ((GlobalTheory.VB.isFrame_restrict_iff V.ι _).2 ((he a).res hle))).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlagStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_over_field_has_flag : ∀ (K : Type) [Field K] (E : (Spec (CommRingCat.of K)).Modules) (n : ℕ), GlobalTheory.VB.IsVB E n → Nonempty (Vert.Flag E n) := by
  first | exact @GlobalTheory.Vert.Flag.nonempty_of_field | exact GlobalTheory.Vert.Flag.nonempty_of_field | (intros; apply GlobalTheory.Vert.Flag.nonempty_of_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelModStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_depends_on_label_mod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  first | exact @GlobalTheory.Poinc.GSum.part_eq_of_congMod | exact GlobalTheory.Poinc.GSum.part_eq_of_congMod | (intros; apply GlobalTheory.Poinc.GSum.part_eq_of_congMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRuleStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubledTarget_siegelRule : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
        ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
        ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
          SiegelRule (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)
            (GlobalTheory.WeilSchrodinger.transD (cA σ) co) χS
            ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
            (omp.comp (MonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | exact GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget | (intros; apply GlobalTheory.WeilSchrodinger.DblTargetF.siegelRule_dblTarget <;> assumption)
end

