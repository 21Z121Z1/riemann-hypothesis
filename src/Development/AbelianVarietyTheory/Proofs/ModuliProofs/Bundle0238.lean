import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFamilyPointWithFramesOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProof
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem arcFam_closed : GlobalTheory.LN.ArcFamSt :=
  GlobalTheory.T.exists_arc_family_point_with_frames_of_laws GlobalTheory.lawsAndExpansions GlobalTheory.allSixLaws.2.2.2.2.2 GlobalTheory.T.uniformisation_triples_complete_DVR_torsion GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing
    GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.1 GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion.2 GlobalTheory.thetaUnifAV_closed

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelAmpleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ringGenerators (x y : 𝓞 E) : ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J),
    a w = x ∧ a w' = y ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let b := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun j => Option.elim j x (fun j' => Option.elim j' y b), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact Subring.subset_closure ⟨some (some i), rfl⟩
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul m u _ hu => exact zsmul_mem hu m

theorem RZ.coe_rt (H : Host E) (S A : ℕ) : (RZ H S A).subtype (RZ.rt H S A) = H.rt0 := by
  rw [RZ.rt, map_sub, map_mul, map_ofNat, map_one]
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem exists_tBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) :
    ∃ b : TBase (RZ H n N) N, (b.ζ : RZ H n N) = RZ.ze H n N := by
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact pow_ne_zero _ hn.ne'
  have hζ : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN0
  have hpow : (RZ.ze H n N) ^ N = 1 := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hζ.pow_eq_one
  have hinv : ((n : ℂ))⁻¹ ∈ RZ H n N := Subring.subset_closure (Or.inr (Or.inl rfl))
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit_n : IsUnit (n : RZ H n N) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.val_injective
    simp [hn']
  have hunit : IsUnit (N : RZ H n N) := by
    have h : (N : RZ H n N) = (n : RZ H n N) ^ e := by rw [← Nat.cast_pow, ← hN]
    rw [h]
    exact hunit_n.pow e
  have key : ∀ {S : Type} [CommRing S] (f : RZ H n N →+* S),
      (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom S) (f (RZ.ze H n N)) =
        f ((Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N)) := by
    intro S _ f
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have h0 : (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N) = 0 := by
    apply Subtype.val_injective
    show (RZ H n N).subtype _ = (RZ H n N).subtype 0
    rw [map_zero, ← key]
    have hr := ((Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (Nat.pos_of_ne_zero hN0)).mpr hζ).eq_zero
    rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map] at hr
    exact hr
  refine ⟨⟨Units.ofPowEqOne _ N hpow hN0, hunit, ?_⟩, rfl⟩
  intro K _ β
  have : NeZero ((N : ℕ) : K) := ⟨by simpa [map_natCast] using (hunit.map β).ne_zero⟩
  show IsPrimitiveRoot (β (RZ.ze H n N)) N
  apply Polynomial.isRoot_cyclotomic_iff.mp
  show Polynomial.eval _ _ = 0
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, key, h0, map_zero]

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) : ArBase (RZ H n N).subtype := by
  have hN0 : 0 < N := by
    rw [hN]
    exact pow_pos hn e
  have hrt2 : H.rt ^ 2 = -(H.d : 𝓞 E) := H.5
  have hw0 : 2 * H.w0 = 1 + H.rt := H.7
  have hd16 : H.d % 16 = 7 := H.2
  have hconj : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E) := H.9
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast H.3.pos

  have hbar_rt : H.bar H.rt = -H.rt := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
      have h := congrArg ((↑) : 𝓞 E → E) hrt2
      push_cast at h
      exact h
    have hz2 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hE, map_neg, map_natCast]
    set z := φ (H.rt : E) with hz
    have hx : z.re = 0 := by
      have h1 := congrArg Complex.re hz2
      have h2 := congrArg Complex.im hz2
      simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
      have h3 : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg z.re]
    have hc : φ (IsCMField.complexConj E (H.rt : E)) = φ (-(H.rt : E)) := by
      rw [IsCMField.complexEmbedding_complexConj, map_neg, ← hz]
      apply Complex.ext <;> simp [hx]
    have h4 : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
      rw [hconj, φ.injective hc]
      norm_cast
    exact_mod_cast h4
  obtain ⟨m, hm⟩ : ∃ m, H.d = 16 * m + 7 := ⟨H.d / 16, by omega⟩
  have hdE : (H.d : 𝓞 E) = 16 * m + 7 := by
    rw [hm]
    push_cast
    ring
  have hbal : H.bar (2 + H.rt) = 2 - H.rt := by
    rw [map_add, map_ofNat, hbar_rt]
    ring
  have hal : (2 + H.rt) ∈ Algebra.adjoin ℤ {H.w0} := by
    have h : 2 + H.rt = 1 + H.w0 + H.w0 := by linear_combination -hw0
    rw [h]
    have hw := Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton H.w0)
    exact add_mem (add_mem (one_mem _) hw) hw

  obtain ⟨l, hl⟩ : ∃ l : Level H, l.A = N := by
    refine ⟨⟨H.d + 4, by omega, ⟨H.d / 2 + 2, by omega⟩, Ideal.span {2 + H.rt}, ?_, ?_, ?_, N, hN0⟩, rfl⟩
    · exact le_antisymm
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (Ideal.subset_span ⟨Ideal.subset_span (Set.mem_singleton _), hal⟩)))
        (Ideal.span_le.mpr fun a ha => ha.1)
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
      congr 2
      rw [RingEquiv.coe_toRingHom, hbal]
      push_cast
      linear_combination -hrt2
    · rw [Ideal.map_span, Set.image_singleton, Ideal.eq_top_iff_one]
      have h1 : (1 : 𝓞 E) = ((4 * m + 3 : 𝓞 E) - (2 - H.rt)) * (2 + H.rt) +
          (4 * m + 3 : 𝓞 E) * H.bar (2 + H.rt) := by
        rw [hbal]
        linear_combination -hrt2 + hdE
      rw [h1]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  subst hl
  obtain ⟨⟨β, hβ⟩, hft, hded⟩ := BaseRing.isDedFrac_RZ E H l n e hn ⟨1, by rw [hN, Nat.mul_one]⟩
  obtain ⟨⟨_, hD⟩, -, -⟩ := hded β hβ
  exact ⟨hD, hft, Subtype.val_injective⟩

theorem one_le_finrank_div_two : 1 ≤ Module.finrank ℚ E / 2 := by
  have h1 := NumberField.IsTotallyComplex.finrank (K := E)
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem topAmpExists : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  intro hHE hL hL2 hSR hTU hUT hZG hRed hGen hTh
  unfold TopAmpExists
  intro E _ _ _ H D hpq Xo n hn
  have hnp : n.Prime := hn.1
  have hno : Odd n := hn.2.1
  have hn0 : 0 < n := hnp.pos
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', haw, haw', hcl⟩ := exists_ringGenerators H.w0 (H.bar H.w0)
  have := hJ
  have hg1 : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) :=
    calc 1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul (one_le_finrank_div_two (E := E)) hpq
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre hL hL2 hRed hGen hTh E H D _ J a w w' bas hpq hbas haw haw' hcl n hnp hno
  obtain ⟨k, j₂, hj₂⟩ := GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily hL hL2 hSR hTU hUT hZG E H D n hpq hnp hno
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level hL hL2 hGen hTh _ n hg1 hnp hno
  obtain ⟨j, hj1, hj2, hj3, hj⟩ : ∃ j, j₁ ≤ j ∧ j₂ ≤ j ∧ j₃ ≤ j ∧ 1 ≤ j :=
    ⟨max (max j₁ j₂) (max j₃ 1), by omega, by omega, by omega, by omega⟩
  have hNe : (n ^ j) ^ 2 = n ^ (j * 2) := (pow_mul n j 2).symm
  obtain ⟨b, hb⟩ := exists_tBase_RZ H hn0 hNe
  have hAr := arBase_RZ H hn0 hNe
  obtain ⟨F, τ, hPEL, hsm⟩ := hj₁ j hj1 (RZ H n ((n ^ j) ^ 2)) b (RZ H n ((n ^ j) ^ 2)).subtype
    (RZ.rt H n ((n ^ j) ^ 2)) (RZ.coe_rt H n _) hAr
  obtain ⟨C⟩ := hj₂ j hj2 (n ^ j) rfl _ J a bas b F τ hbas hcl ⟨w, w', haw, haw'⟩ hb hPEL hsm
  obtain ⟨lev, hcore⟩ := GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily hL hL2 E H D n (n ^ j) _ J a bas b F τ hbas hcl
    ⟨w, w', haw, haw'⟩ hb hPEL hsm hpq hnp hno ⟨j, hj, rfl⟩
  have hcl2 := GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily hHE hL hL2 E H D n ((n ^ j) ^ 2) F.MM F.s τ lev hpq hnp hno
    ⟨j * 2, by omega, hNe⟩ hcore (hj₃ j hj3)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel hHE hL hL2 E H D Xo n ((n ^ j) ^ 2) F.MM F.s τ lev (n ^ k) C hpq hn
    ⟨j * 2, by omega, hNe⟩ (pow_pos hn0 k) hcore hcl2
  refine ⟨j * 2, k, ?_⟩
  rw [← hNe]
  exact ⟨T, by omega, hT⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level : N1ab := by
  first | exact @GlobalTheory.Moduli.moduli_scheme_exists | exact GlobalTheory.Moduli.moduli_scheme_exists | (intros; apply GlobalTheory.Moduli.moduli_scheme_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem kerSet_of_isPullback {S : Scheme.{0}} {G G' C : Over S} [GrpObj G'] {ψ : G ⟶ G'} {j : C ⟶ G}
    [IsClosedImmersion j.left] (hP : IsPullback j (toUnit C) ψ η[G']) : KerSet ψ (Set.range j.left) := by
  intro k _ _ x z
  constructor
  · intro h
    have hl := hP.lift_fst z (toUnit _) h
    rintro _ ⟨a, rfl⟩
    exact ⟨(hP.lift z (toUnit _) h).left a, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl]⟩
  · intro h
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec _))
    have h4 : j.left.ker ≤ z.left.ker := ker_le_ker_of_range_subset_of_isReduced _ _ h
    have h3 := IsClosedImmersion.lift_fac _ _ h4
    let l : Over.mk x ⟶ C := Over.homMk (IsClosedImmersion.lift _ _ h4) (by
      rw [← Over.w j, ← Category.assoc, h3, Over.w])
    have hl : l ≫ j = z := Over.OverMorphism.ext h3
    rw [← hl, Category.assoc, hP.w, ← Category.assoc, toUnit_unique (l ≫ _) (toUnit _)]
    rfl

theorem existsUnique_heckeQuot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (C : Over S) (j : C ⟶ o.t.G), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsReduced S → IsFinite C.hom → Etale C.hom → IsClosedImmersion j.left → HeckeSet D o.t 𝔓 p i (Set.range j.left) → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ∧ ∃ (o' : Ob D l s) (_ : ObjMap o' Xo.univ f) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ IsPullback j (toUnit C) ψ η[o'.t.G] := by
  intro E _ _ _ H D l Xo 𝔓 p i S s o C j hD hA hS hf he hj hK
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo 𝔓 p i hD hA
  obtain ⟨h, ⟨hs, n, hn⟩, -⟩ := Z.rep S s hS o (Set.range j.left) ⟨C, j, hf, he, hj, rfl⟩ hK
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨o', ⟨n'⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _
    (Z.π₁ ≫ Xo.s) s h rfl rfl (by rw [hid, Category.comp_id, hs]) Z.o₂
  obtain ⟨⟨ψ, hψ, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ Z.o₂ o o' n n' Z.ψ
  obtain ⟨hi, hk⟩ := hall ψ hψ
  have hi := hi Z.isog
  have hk := hk Z.K Z.isog.1.1 Z.ker
  rw [← hn] at hk
  obtain ⟨m, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₂ o').2 Z.π₂ h Z.m₂).1 n'
  have hfs : (h ≫ Z.π₂) ≫ Xo.s = s := by rw [Category.assoc, Z.base₂, hs]
  have := o'.proper
  refine ⟨h ≫ Z.π₂, ⟨hfs, o', m, ψ, hi, ?_⟩, ?_⟩
  · exact (etSet_of_kerSet S _ _ ψ _ inferInstance hi.1.2.1 hi.1.2.2.1 hk).2 hS C j he hj rfl
  · rintro f ⟨hf₁, o₁, m₁, ψ₁, hi₁, hP⟩
    exact (GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i S s o o₁ o' ψ₁ ψ _ f _ m₁ m hA hK hf₁ hfs hi₁ hi
      (kerSet_of_isPullback hP) hk).1

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam.Swap

theorem id_pow_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (𝟙 G' ^ n).left ≫ φ = φ ≫ (𝟙 G ^ n).left := by
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  let Φ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ hw
  have key : ∀ m : ℕ, (Φ ^ m).left = (𝟙 G' ^ m).left ≫ φ := by
    intro m
    induction m with
    | zero =>
      let Ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have hΨ : Ψ * Ψ = Ψ * 1 := by
        rw [_root_.mul_one]
        apply Over.OverMorphism.ext
        have := h.2 G' 1 1 Ψ Ψ rfl rfl
        rw [this, _root_.mul_one]
        rfl
      have h1 : Ψ = 1 := mul_left_cancel hΨ
      simp only [pow_zero]
      rw [← h1]
      rfl
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact h.2 G' (𝟙 G' ^ m) (𝟙 G') (Φ ^ m) Φ ih (by simp [Φ])
  have hc : Φ ≫ 𝟙 G ^ n = Φ ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  calc (𝟙 G' ^ n).left ≫ φ = (Φ ^ n).left := (key n).symm
    _ = (Φ ≫ 𝟙 G ^ n).left := by rw [hc]
    _ = φ ≫ (𝟙 G ^ n).left := by simp [Φ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {P P' : Ideal (𝓞 E)} {p i : ℕ}

theorem isAdmissibleSplitHeckePrime_conj (h : admitted l P p) : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := by
  obtain ⟨hmax, hcop, hp, hpP, hl⟩ := h
  refine ⟨?_, ?_, hp, ?_, hl⟩
  · exact Ideal.map_isMaximal_of_equiv H.bar (p := P)
  · rw [GlobalTheory.HeckeDual.map_bar_map_bar, sup_comm]
    exact hcop
  · have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this

theorem isReduced_Hk (Z : Corr Xo P p i) : IsReduced Z.Hk := by
  have : Etale Z.π₁ := Z.et₁
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Z.Hk
    (Z.π₁ ≫ Xo.s) inferInstance).1

theorem isHecke (Z : Corr Xo P p i) : IsHecke Z.o₁ Z.o₂ P p i Z.ψ := ⟨Z.isog, Z.K, Z.ker, Z.hecke⟩

private theorem oAct_act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : OAct (𝓞 E) G) (n : ℕ) :
    A.act (n : 𝓞 E) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h0 := A.5 0 0
    rw [add_zero] at h0
    have h1 : A.act 0 * A.act 0 = A.act 0 * 1 := by rw [_root_.mul_one]; exact h0.symm
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel h1
  | succ n ih => rw [Nat.cast_succ, A.5, ih, A.3, pow_succ]

theorem exists_dual (Z : Corr Xo P p i) (h : admitted l P p) : ∃ χ : Z.o₂.t.G ⟶ Z.o₁.t.G,
    Z.ψ ≫ χ = 𝟙 Z.o₁.t.G ^ p ^ 2 ∧ χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2 ∧
      IsHecke Z.o₂ Z.o₁ (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i χ := by
  have hh := h
  obtain ⟨-, -, hp, -, hl⟩ := hh
  have := isReduced_Hk Z
  have hpb : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := (isAdmissibleSplitHeckePrime_conj h).2.2.2.1
  have hker : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.Hk) (z : Over.mk x ⟶ Z.o₁.t.G),
      z ≫ Z.ψ = 1 → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hK⟩ := Z.hecke k x
    have hzC : z ∈ C := (hC z).2 ((Z.ker k x z).1 hz)
    have hmem : ((p : 𝓞 E) * p) ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hpb
    have h1 : z ≫ Z.o₁.t.act.act ((p : 𝓞 E) * p) = 1 := hK.2.2.1 hzC _ hmem
    rw [← Nat.cast_mul, oAct_act_natCast, MonObj.comp_pow, Category.comp_id, ← sq] at h1
    exact h1
  obtain ⟨χ, h1, h2, h3⟩ :=
    exists_dual_isogeny E H D l p Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.o₂ Z.ψ hp hl Z.isog hker
  exact ⟨χ, h1, h2, GlobalTheory.isHecke_dual E H D l P p i Z.Hk _ Z.o₁ Z.o₂ Z.ψ χ h (isHecke Z) h3 h1⟩

def Exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (a : Z.Hk ⟶ Z'.Hk) : Prop :=
  a ≫ Z'.π₁ ≫ Xo.s = Z.π₁ ≫ Xo.s ∧ ∃ (n₁ : ObjMap Z.o₂ Z'.o₁ a) (n₂ : ObjMap Z.o₁ Z'.o₂ a),
    χ.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ Z'.ψ.left ∧ Z.ψ.left ≫ n₁.toSABMap.φ = n₂.toSABMap.φ ≫ χ'.left

theorem exists_exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (h : χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2) (h' : Z'.ψ ≫ χ' = 𝟙 Z'.o₁.t.G ^ p ^ 2) (hχ : IsHecke Z.o₂ Z.o₁ P' p i χ) :
    ∃ a, Exch Z Z' χ χ' a := by
  have := isReduced_Hk Z
  obtain ⟨a, ⟨ha1, n₁, n₂, hn⟩, -⟩ := Z'.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂ Z.o₁ χ hχ
  refine ⟨a, ha1, n₁, n₂, hn, ?_⟩
  obtain ⟨⟨⟨-, hfin, het, hsurj, -⟩, -⟩, -⟩ := hχ
  have : Epi χ.left := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi χ.left]
  have hp1 : IsGrpPullback Z.o₂.t.G Z'.o₁.t.G a n₁.toSABMap.φ := n₁.toSABMap.2
  calc χ.left ≫ Z.ψ.left ≫ n₁.toSABMap.φ = (χ ≫ Z.ψ).left ≫ n₁.toSABMap.φ := by simp
    _ = (𝟙 Z.o₂.t.G ^ p ^ 2).left ≫ n₁.toSABMap.φ := by rw [h]
    _ = n₁.toSABMap.φ ≫ (𝟙 Z'.o₁.t.G ^ p ^ 2).left := id_pow_left_comp hp1 (p ^ 2)
    _ = n₁.toSABMap.φ ≫ (Z'.ψ ≫ χ').left := by rw [h']
    _ = χ.left ≫ n₂.toSABMap.φ ≫ χ'.left := by rw [Over.comp_left, ← Category.assoc, ← hn, Category.assoc]

theorem Exch.comp_eq_id {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} {b : Z'.Hk ⟶ Z.Hk} (ha : Exch Z Z' χ χ' a)
    (hb : Exch Z' Z χ' χ b) : a ≫ b = 𝟙 _ := by
  obtain ⟨ha1, n₁, n₂, -, hn2⟩ := ha
  obtain ⟨hb1, m₁, m₂, hm1, -⟩ := hb
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Z.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₁ Z.o₂ Z.ψ (isHecke Z)
  obtain ⟨c₁, hc₁⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z'.o₂ Z.o₁).2
    b a m₁).1 n₂
  obtain ⟨c₂, hc₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z'.o₁ Z.o₂).2
    b a m₂).1 n₁
  obtain ⟨i₁, hi₁⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z.o₁ Z.o₁).1
  obtain ⟨i₂, hi₂⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z.o₂ Z.o₂).1
  have e1 := huniq (a ≫ b) ⟨by rw [Category.assoc, hb1, ha1], c₁, c₂, by
    rw [hc₁, hc₂, ← Category.assoc, hn2, Category.assoc, hm1, Category.assoc]⟩
  have e2 := huniq (𝟙 _) ⟨by rw [Category.id_comp], i₁, i₂, by rw [hi₁, hi₂, Category.id_comp, Category.comp_id]⟩
  exact e1.trans e2.symm

theorem Exch.comp_π₁ {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} (ha : Exch Z Z' χ χ' a) : a ≫ Z'.π₁ = Z.π₂ := by
  obtain ⟨ha1, n₁, n₂, -, -⟩ := ha
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Xo.rep Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂
  obtain ⟨c, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z'.o₁ Z.o₂).2
    Z'.π₁ a Z'.m₁).1 n₁
  have e1 := huniq (a ≫ Z'.π₁) ⟨by rw [Category.assoc]; exact ha1, ⟨c⟩⟩
  have e2 := huniq Z.π₂ ⟨Z.base₂, ⟨Z.m₂⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.HkFam.Swap

namespace GlobalTheory.HkFam

open Swap

theorem second_projection_finite_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsFinite Z.π₂ ∧ Etale Z.π₂ ∧ (i ≤ D.p + D.q → Surjective Z.π₂) := by
  intro E _ _ _ H D l Xo P p i Z hpq h
  have h' : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := isAdmissibleSplitHeckePrime_conj h
  obtain ⟨Z'⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i hpq h'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := exists_dual Z h
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := exists_dual Z' h'
  rw [GlobalTheory.HeckeDual.map_bar_map_bar] at hχ'3
  obtain ⟨a, ha⟩ := exists_exch Z Z' χ χ' hχ2 hχ'1 hχ3
  obtain ⟨b, hb⟩ := exists_exch Z' Z χ' χ hχ'2 hχ1 hχ'3
  have : IsIso a := ⟨b, Exch.comp_eq_id ha hb, Exch.comp_eq_id hb ha⟩
  have := Z'.fin₁
  have := Z'.et₁
  rw [← Exch.comp_π₁ ha]
  refine ⟨inferInstance, inferInstance, fun hi => ?_⟩
  have := (GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels E H D l Xo _ p i Z'.toKerScheme h').2 hi
  infer_instance

end GlobalTheory.HkFam

end
end

