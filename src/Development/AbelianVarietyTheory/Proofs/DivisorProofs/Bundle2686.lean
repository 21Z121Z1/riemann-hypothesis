import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.range_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') :
    (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧
    (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  constructor
  · intro g hg
    obtain ⟨p, hp⟩ : ∃ p, p = E.H.ι g := ⟨_, rfl⟩
    rw [← hp] at hg
    let Ω := G'.left.residueField p
    let x0 : Sp Ω ⟶ G'.left := G'.left.fromSpecResidueField p
    let x : Sp Ω ⟶ S := x0 ≫ G'.hom
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, x0, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hg
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    let w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x) :=
      pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])
    let w0 : Sp Ω' := closedPoint Ω'
    have hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hlw : l (w w0) = g := by
      apply E.H.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl1, ← hp]
      exact hw
    refine ⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩
    rw [← hlw, ← Scheme.Hom.comp_apply, hl2]
    simp only [Scheme.Hom.comp_apply]
  · intro hπ y
    obtain ⟨s, hs⟩ := hπ.surj (closedPoint R)
    let Ω := S.residueField s
    let x : Sp Ω ⟶ S := S.fromSpecResidueField s
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    obtain ⟨w', hw'⟩ := (pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y
    let w := e.inv.left w'
    have hew : e.hom.left w = w' := by
      simp only [w]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
      rfl
    refine ⟨l w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply l E.H.ι, hl1,
        ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]
      simp only [Scheme.Hom.comp_apply, x]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    · rw [← Scheme.Hom.comp_apply, hl2]
      simp only [Scheme.Hom.comp_apply]
      rw [hew, hw']

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDiagNatCastSmul
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RealMultKernel

theorem cls_diag_add {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S) (c c' : 𝔠.elt) :
    cls (X.diag (c + c')) (pull_isLB (X.isLB _) _) =
      cls (X.diag c) (pull_isLB (X.isLB _) _) + cls (X.diag c') (pull_isLB (X.isLB _) _) := by
  have e : cls (X.P c') (X.isLB c') = cls (X.P (c + c')) (X.isLB _) - cls (X.P c) (X.isLB c) := by
    rw [← cls_div (X.isLB _) (X.isLB _) (LB.isLB_div (X.isLB _) (X.isLB _))]
    exact (cls_eq_iff _ _).2 (X.add c c')
  show CechPic.pull _ (cls (X.P (c + c')) (X.isLB _)) =
    CechPic.pull _ (cls (X.P c) (X.isLB c)) + CechPic.pull _ (cls (X.P c') (X.isLB c'))
  rw [e, map_sub]; abel

theorem cls_diag_natCast_smul {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S)
    (c : 𝔠.elt) (n : ℕ) :
    cls (X.diag ((n : 𝓞 F) • c)) (pull_isLB (X.isLB _) _) = n • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
  induction n with
  | zero =>
    have h := cls_diag_add X 0 0
    simp only [add_zero] at h
    simp only [Nat.cast_zero, zero_smul]
    exact left_eq_add.1 h
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, cls_diag_add, ih, succ_nsmul]

theorem card_ker_act_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (X : Obj F 𝔠 (Sp Ω)), ∃ C : ℕ, ∀ (b : 𝓞 F) (k : ℕ), ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 →
      IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) →
      Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ∧
      Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ≤ C * k ^ (2 * Module.finrank ℚ F) := by
  intro F _ _ _ 𝔠 Ω _ _ X
  have hB := X.ab
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral X.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral X.A.left := GeometricallyIntegral.isIntegral_of_subsingleton X.A.hom
  obtain ⟨c, hc⟩ := fracId_exists_totPos F 𝔠
  have hLc : (X.diag c).IsLB := pull_isLB (X.isLB c) _
  obtain ⟨m, hm, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A (X.diag c) hLc).1 (X.pos c hc)
  have hH : (pw (X.diag c) m).IsLB := isLB_pw hLc _
  obtain ⟨hfin, -, c₀, C₀, -, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth Ω X.A.left X.A.hom _ X.dim _ n s hH hs
  refine ⟨c₀ * C₀, fun b k hb hpos => ?_⟩
  obtain ⟨hfinφ, hetφ, hker⟩ := GlobalTheory.T.real_mult_isogeny_finite_etale X b hb
  refine ⟨hker, ?_⟩
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale Ω X.A hB (X.rm.act b)
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
      have h0 := hpos (v.embedding_of_isReal (IsTotallyReal.isReal v))
      simp at h0
      nlinarith [sq_nonneg ((v.embedding_of_isReal (IsTotallyReal.isReal v)) (b : F))]
    · exact h
  set e : 𝓞 F := (k : 𝓞 F) ^ 2 - b ^ 2 with he
  have hce : IsTotPos (((e • c : 𝔠.elt)) : F) := by
    intro τ
    have h1 := hpos τ
    have h2 := hc τ
    have h3 : (((e • c : 𝔠.elt)) : F) = ((k : F) ^ 2 - (b : F) ^ 2) * (c : F) := by
      rw [Submodule.coe_smul, Algebra.smul_def, he]
      first | simp | (push_cast; norm_cast) | (congr 1; simp)
    rw [h3, map_mul]
    exact mul_pos h1 h2
  have hDe : (X.diag (e • c)).IsLB := pull_isLB (X.isLB _) _
  obtain ⟨m', hm', n', s', hs'⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A _ hDe).1 (X.pos _ hce)
  obtain ⟨x₀⟩ : Nonempty X.A.left := inferInstance
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show x₀ ∈ ⨆ i, Out.nonzeroLocus (s' i) by rw [hs'.1]; trivial)
  obtain ⟨n'', s'', hs''⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw Ω X.A.left X.A.hom _ n s hH hs m' hm'
  have hsum : cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) + cls (X.diag (e • c)) (pull_isLB (X.isLB _) _) =
      (k ^ 2 : ℕ) • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
    rw [← cls_diag_add, ← add_smul, ← cls_diag_natCast_smul]
    congr 3
    rw [he]; push_cast; ring
  have hφ : (X.rm.act b).left ≫ X.A.hom = X.A.hom := Over.w _
  have key : ∀ t : ℕ,
      Module.Finite Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ∧
      Module.finrank Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ≤
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) ⊤) := by
    intro t
    rw [hφ]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_power_nonvanishing s' i₀ hi₀ (m * t)
    have hLp : ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left).IsLB :=
      pull_isLB (isLB_pw (isLB_pw hH _) _) _
    have hD2 : (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ)).IsLB := isLB_pw (isLB_pw hDe _) _
    have hT : (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)).IsLB := isLB_pw hH _
    have hiso : LBIso (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) := by
      rw [← cls_eq_iff (isLB_tens hLp hD2) hT, cls_tens hLp hD2,
        cls_pull (isLB_pw (isLB_pw hH _) _), GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hH _),
        GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc, GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hDe _),
        GlobalTheory.AmpleStabFinite.cls_pw hDe, GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc,
        map_zsmul, map_zsmul, map_zsmul, GlobalTheory.T.real_mult_pullback_polarization_class,
        eq_sub_of_add_eq hsum]
      push_cast
      module
    obtain ⟨w, hw⟩ := hiso
    have eqv := SecOnR.linEquiv X.A.hom (SecOn.congr (isLB_tens hLp hD2) hT w hw ⊤)
    haveI := hfin (k ^ 2 * (m' * t))
    haveI : Module.Finite Ω (SecOnR X.A.hom (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) ⊤) := Module.Finite.equiv eqv.symm
    obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_sections_mono_tensor_effective X.A.hom hLp hD2 σ hσ inferInstance
    exact ⟨h1, h2.trans eqv.finrank_eq.le⟩
  have hpw : ∀ t : ℕ, pw (pw (pw (X.diag c) m) m') (t : ℤ) = pw (pw (X.diag c) m) ((m' * t : ℕ) : ℤ) := fun t => by
    rw [GlobalTheory.UU.TorsionCount.pw_pw, Nat.cast_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich Ω X.A.left X.A.left X.A.hom (X.rm.act b).left
    (pw (pw (X.diag c) m) m') n'' s'' (isLB_pw hH _) hs'' _ hcard (fun t => by rw [hpw]; exact hfin _)
    (fun t => (key t).1)
  refine GlobalTheory.T.le_of_eventual_polynomial_growth _ _ a (Module.finrank ℚ F) fun N => ⟨max N 1, le_max_left _ _, ?_⟩
  set s₁ := max N 1 with hs₁
  have hs1 : 1 ≤ s₁ := le_max_right _ _
  have g1 := (hgrow (m' * s₁) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1
  have g2 := (ha s₁).1
  rw [hpw] at g2
  have g3 := (key (s₁ + a)).2
  have g4 := (hgrow (k ^ 2 * (m' * (s₁ + a)))
    (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (by omega) (by omega))))).2
  have hm'f : 0 < m' ^ Module.finrank ℚ F := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hm'f
  calc Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * s₁ ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F
      = Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * (m' * s₁) ^ Module.finrank ℚ F := by ring
    _ ≤ Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        (c₀ * Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := Nat.mul_le_mul_left _ g1
    _ = c₀ * (Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := by ring
    _ ≤ c₀ * (C₀ * (k ^ 2 * (m' * (s₁ + a))) ^ Module.finrank ℚ F) :=
        Nat.mul_le_mul_left _ ((g2.trans g3).trans g4)
    _ = c₀ * C₀ * k ^ (2 * Module.finrank ℚ F) * (s₁ + a) ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

end GlobalTheory.RealMultKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGoodStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_reduction_good : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
      (c₀ : FR E) ≠ 0 → IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) → Function.Bijective ψ₀ →
      (∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h')) →
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  first | exact @GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul | exact GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul | (intros; apply GlobalTheory.LatModel.HalfFormUnit.halfForm_eq_unit_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamPeriodMapEquivariantStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_de_rham_period_map_equivariant : GlobalTheory.Published.PeriodComparison →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ P : E →+ HdR X.A, Submodule.span ℂ (Set.range P) = ⊤ ∧
      ∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
        ∀ x, push (dp0 ℂ) (𝟙 _) α (P x) = P (a * x) := by
  first | exact @GlobalTheory.PeriodLattice.periods_unif | exact GlobalTheory.PeriodLattice.periods_unif | (intros; apply GlobalTheory.PeriodLattice.periods_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToL
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatticeUp

theorem exists_mul_integral : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime →
    OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  intro E _ _ l c y hl hy
  obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele E l (y : Af E) hl fun w hw => by rw [hy w hw, map_one]
  refine ⟨M, hM, fun x hx => ?_⟩
  have hx' : algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := hx
  have key : algebraMap E (Af E) ((M : E) * x) =
      (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (algebraMap E (Af E) (M : E) * (y : Af E)) := by
    have hyy : (↑y⁻¹ : Af E) * (y : Af E) = 1 := y.inv_mul
    rw [map_mul]
    calc algebraMap E (Af E) (M : E) * algebraMap E (Af E) x
        = algebraMap E (Af E) (M : E) * algebraMap E (Af E) x * ((↑y⁻¹ : Af E) * (y : Af E)) := by rw [hyy, mul_one]
      _ = _ := by ring
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((M : E) * x) fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((M : E) * x)]
    have h1 := GlobalTheory.CMVal.ObjModel.hatO_integral hx' v
    have h2 := hMv v
    have : (algebraMap E (Af E) ((M : E) * x)) v =
        (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) v * (algebraMap E (Af E) (M : E) * (y : Af E)) v := by
      rw [key]; rfl
    rw [show ((((M : E) * x : E)) : v.adicCompletion E) = (algebraMap E (Af E) ((M : E) * x)) v from rfl, this, map_mul]
    exact mul_le_one' h1 h2
  rw [← hb]
  exact (b.isIntegral_coe)

end GlobalTheory.HilbFam.LatticeUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFg
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

theorem lat_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, hG, hdet⟩ := GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite E H hH K ρ σ₁ p X
  set N : 𝓞 E := H.bar.symm gP.det with hNdef
  have hN0 : N ≠ 0 := fun h => hdet (by simpa [hNdef] using congrArg H.bar h)
  have hN : (N : E) ≠ 0 := by exact_mod_cast hN0
  have key : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ b, ∃ z : 𝓞 E, (z : E) = (N : E) * c b := by
    rintro c ⟨n, hn, x, hx, f, hf, hfx⟩ b
    choose y hy using GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow E H hH K ρ σ₁ p 0 X gP gQ hG n x f hn hf hfx
    have hmv : gP.mulVec (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * y a := by
      funext a; simp [Matrix.mulVec, dotProduct, hy]
    have hadj : gP.det • (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * gP.adjugate.mulVec y a := by
      have := congrArg gP.adjugate.mulVec hmv
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [this]; funext a; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    have hb := congrArg H.bar.symm (congrFun hadj b)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, map_natCast] at hb
    refine ⟨H.bar.symm (gP.adjugate.mulVec y b), ?_⟩
    have hnE : ((n : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hnE
    have h2 : ((N : 𝓞 E) : E) * ((x b : 𝓞 E) : E) =
        (n : E) * ((H.bar.symm (gP.adjugate.mulVec y b) : 𝓞 E) : E) := by
      rw [hNdef]; exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hb
    push_cast
    rw [← h2, hx b]; ring
  let incl : (Fin p → 𝓞 E) →ₗ[𝓞 E] (Fin p → E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)
  let scal : (Fin p → E) →ₗ[𝓞 E] (Fin p → E) := N • LinearMap.id
  have hscal : Function.Injective scal := by
    intro v w h
    funext i
    have := congrFun h i
    simp only [scal, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hN this
  apply Submodule.fg_of_fg_map_injective scal hscal
  refine Submodule.FG.of_le (T := LinearMap.range incl) ?_ ?_
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map incl
  · rw [GlobalTheory.FlatCM.HomLat.lat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    choose z hz using key c hc
    refine ⟨z, ?_⟩
    funext b
    simp [incl, scal, hz, Algebra.smul_def]

end GlobalTheory.FlatCM.HomLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddingsAltBis
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_of_isCMType_of_ne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) := by
  first | exact @GlobalTheory.CMSep.exists_int_ne' | exact GlobalTheory.CMSep.exists_int_ne' | (intros; apply GlobalTheory.CMSep.exists_int_ne' <;> assumption)
end

