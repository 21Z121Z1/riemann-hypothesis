import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import GroundTheory.GlobalFields.Adele.Discrete
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsometryConjPointSplitUpToIndex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjSplitIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nsmul_cancel {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {N : ℕ} (hN : 0 < N) {u u' : D.La} (h : N • u = N • u') : u = u' := by
  apply hP.2.1
  have h' := congrArg P h
  rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h'
  exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') h'

theorem form_nsmul_nsmul (D : Datum H) (N : ℕ) (x y : D.La) : D.EF (N • x) (N • y) = (N * N : ℤ) * D.EF x y := by
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

end GlobalTheory.ConjSplitIndex

namespace GlobalTheory.CompRat

open ConjIsometry in

theorem exists_isometry_of_conj_split_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P') (N : ℕ), 0 < N → (∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → C.ActsBy τ io N (1, 0) → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) ∧ (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) ∧ ∀ n : ℕ, 0 < n → C.ActsBy τ io (N * n) (1, 0) → ∀ v, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P v)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ v))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' N hN hNv hu hAN
  obtain ⟨f, hadd, hw, -, hact, hf⟩ := GlobalTheory.ConjSplit.exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := GlobalTheory.ConjSplitAnyLevel.exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun n s hA a => ?_⟩
    rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex,
      GlobalTheory.ConjSplit.ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (GlobalTheory.ConjSplit.rt0_ne_neg (H := H)))

  have hsum : ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) =
        F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp (wE H s • a) + Φm (H.bar (wE H s) • b))) := by
    intro n s hA a b
    rw [map_smul, map_smul, map_add P', GlobalTheory.ConjSplit.period_wE hP' (hp a),
      GlobalTheory.ConjSplit.period_bar_wE hP' (hm b), smul_add, F.ex_add i' P' hP', ← tp n s hA, ← tm n s hA,
      ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
  have hsum1 : ∀ n : ℕ, C.ActsBy τ io n (1, 0) → ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      U ≫ F.ex i P ((n : ℂ)⁻¹ • P (a.1 + b.1)) = F.ex i' P' ((n : ℂ)⁻¹ • P' (Φp a + Φm b)) := by
    intro n hA a b
    rw [hsum n (1, 0) hA a b]
    simp [wE]

  have hiso₀ : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)),
      (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') = (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
    intro a a' b b'
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1) := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.CompRat.Acts.main E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (congrArg (fun m => m.left) (hsum n s hs a b))
        (congrArg (fun m => m.left) (hsum n s hs a' b'))
      have hM := GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = M at hM hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = M := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP' H.rt0, ∀ v ∈ lat hP' (-H.rt0),
          (F.Di i').EF u v = 0 ∧ (F.Di i').EF v u = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' hu hv
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φp (wE H s • a) + Φm (H.bar (wE H s) • b)) (Φp (wE H s • a') + Φm (H.bar (wE H s) • b')) =
          M * (F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') := by
        simp only [map_add, LinearMap.add_apply]
        rw [(o _ (hp _) _ (hm _)).1, (o _ (hp _) _ (hm _)).2, (o _ (hp a) _ (hm b')).1, (o _ (hp a') _ (hm b)).2,
          map_smul Φp, map_smul Φp, map_smul Φm, map_smul Φm, form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hM] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φp a + Φm b) (Φp a' + Φm b') - (F.Di i).EF (a.1 + b.1) (a'.1 + b'.1)).natAbs + 1)
      (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this
      (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hdec : ∀ v, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v := fun v => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hNv v)
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
  have huniq : ∀ (a a' : lat hP H.rt0) (b b' : lat hP (-H.rt0)), a.1 + b.1 = a'.1 + b'.1 → a = a' ∧ b = b' := by
    intro a a' b b' h
    have e : a.1 - a'.1 = b'.1 - b.1 := by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have z : a.1 - a'.1 = 0 := hd _ (sub_mem a.2 a'.2) (e ▸ sub_mem b'.2 b.2)
    exact ⟨Subtype.ext (sub_eq_zero.1 z), Subtype.ext (sub_eq_zero.1 (e ▸ z)).symm⟩
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hdiv : ∀ v, ∃ u : (F.Di i').La, ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v →
      Φp a + Φm b = N • u := by
    intro v
    obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 N hAN a b
    rw [hab, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hNc, (F.ex_ker i P hP _).2 ⟨v, rfl⟩,
      MonObj.comp_one] at e
    obtain ⟨u, hu'⟩ := (F.ex_ker i' P' hP' _).1 e.symm
    refine ⟨u, fun a' b' h => ?_⟩
    obtain ⟨rfl, rfl⟩ := huniq a a' b b' (hab.trans h.symm)
    apply hP'.2.1
    rw [map_nsmul, hu', ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hNc]
  choose Ψ hΨ using hdiv
  let Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La :=
    { toFun := Ψ
      map_add' := fun v w => by
        obtain ⟨a, b, hab⟩ := hdec v
        obtain ⟨a', b', hab'⟩ := hdec w
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [smul_add, ← hΨ v a b hab, ← hΨ w a' b' hab', ← hΨ (v + w) (a + a') (b + b')
          (by rw [smul_add, ← hab, ← hab', Submodule.coe_add, Submodule.coe_add]; abel), map_add, map_add]
        abel
      map_smul' := fun c v => by
        obtain ⟨a, b, hab⟩ := hdec v
        refine GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN ?_
        rw [RingHom.id_apply, smul_comm N c, ← hΨ v a b hab, ← hΨ (c • v) (c • a) (c • b)
          (by rw [smul_comm N c, ← hab, Submodule.coe_smul, Submodule.coe_smul, smul_add]), map_smul, map_smul,
          smul_add] }
  have hΦ : ∀ v (a : lat hP H.rt0) (b : lat hP (-H.rt0)), a.1 + b.1 = N • v → Φp a + Φm b = N • Φ v := hΨ
  have hiso : ∀ v w, (F.Di i').EF (Φ v) (Φ w) = (F.Di i).EF v w := by
    intro v w
    obtain ⟨a, b, hab⟩ := hdec v
    obtain ⟨a', b', hab'⟩ := hdec w
    have e := hiso₀ a a' b b'
    rw [hΦ v a b hab, hΦ w a' b' hab', hab, hab', GlobalTheory.ConjSplitIndex.form_nsmul_nsmul,
      GlobalTheory.ConjSplitIndex.form_nsmul_nsmul] at e
    have hz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact mul_left_cancel₀ (mul_ne_zero hz hz) e
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).2 fun v hv =>
    (F.Di i).unimod.1 (by
      ext z
      rw [← hiso, hv]; simp)
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, fun a ha => ?_, fun b hb => ?_, fun n hn hA v => ?_⟩
  · have e := hΦ a (N • ⟨a, ha⟩) 0 (by simp)
    rw [map_zero, add_zero, map_nsmul] at e
    show Φ a ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hp _
  · have e := hΦ b 0 (N • ⟨b, hb⟩) (by simp)
    rw [map_zero, zero_add, map_nsmul] at e
    show Φ b ∈ _
    rw [← GlobalTheory.ConjSplitIndex.nsmul_cancel hP' hN e]
    exact hm _
  · obtain ⟨a, b, hab⟩ := hdec v
    have e := hsum1 (N * n) hA a b
    have hc : ∀ x : Fin g → ℂ, ((N * n : ℕ) : ℂ)⁻¹ • N • x = (n : ℂ)⁻¹ • x := fun x => by
      rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ hNc]
    rw [hΦ v a b hab, hab, map_nsmul, map_nsmul, hc, hc] at e
    exact congrArg (fun m => m.left) e

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieFrame

theorem one_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushPt h.1.w (1 : T ⟶ G') = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  refine (congrArg Over.Hom.left e').trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact Category.assoc _ _ _

theorem exists_hom {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ') :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  refine ⟨F, hF, ?_⟩
  rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]

theorem dual_w {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pull {V O : Type} [CommRing V] [CommRing O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
    {f : V →+* O} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) π) {u : epsOver V V ⟶ G} (hu : IsTan u) :
    ∃ x : LieG G', x.1.left ≫ π = spMap (dualMap f) ≫ u.left := by
  have w : (spMap (dualMap f) ≫ u.left) ≫ G.hom = spMap (algebraMap O (DualNumber O)) ≫ spMap f := by
    rw [Category.assoc, Over.w u, ← dual_w]
    rfl
  refine ⟨⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_⟩, h.1.lift_fst _ _ w⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine Eq.trans ?_ (one_comp h (specO O O)).symm
  change (spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ h.1.lift _ _ w) ≫ π = spMap (algebraMap O O) ≫ _
  have e : spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (dualMap f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
    rw [spMap_spMap, spMap_spMap]
    congr 1
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, h.1.lift_fst, ← Category.assoc, e, Category.assoc, hu, Hom.one_def, Over.comp_left,
    Over.toUnit_left]
  change spMap f ≫ spMap (algebraMap V V) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]

theorem exists_lieTie_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∃ x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt, ∀ τ j, LieTie P ψ (x τ j) (z.u τ j) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz
  letI := io.toAlgebra
  obtain ⟨hk, G, t', m₁, m₂, π, φ, hπ, -, hφ, h4, rfl, -⟩ := hP
  obtain ⟨G₀, t₀, n₁, n₂, ⟨ub, ht, -, -, hub⟩, -⟩ := y₀.2.2
  obtain ⟨e, he, h₁⟩ := grpPullback_iso n₁.cart m₁.cart
  have h₂ : IsGrpPullback t₀.G G.G (spMap (algebraMap T.V T.Fr)) (e.hom.left ≫ m₂.φ) :=
    ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl
  obtain ⟨F, hF, h₃⟩ := exists_hom G₀.semi G.semi n₂.cart h₂
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  suffices h : ∀ τ j, ∃ x : LieG P.Gt, LieTie P (φ ≫ m₁.φ) x (z.u τ j) by
    choose x hx using h
    exact ⟨x, hx⟩
  intro τ j
  obtain ⟨u', h5, h6⟩ := hub τ j
  have ht' : IsTan (ub τ j ≫ F) := by
    unfold IsTan
    rw [Over.comp_left, ← Category.assoc, ht τ j, ← Over.comp_left, MonObj.one_comp]
  obtain ⟨xG, hx⟩ := exists_pull hπ ht'
  obtain ⟨x, hc, -⟩ := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p) xG.1
  have h7 := hc.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h7
  have hu : (u' ≫ e.hom.left) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    haveI : Mono (spMap (algebraMap T.V T.Fr)) :=
      haveI : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
      inferInstance
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, Category.assoc, ← m₂.cart.1.w,
      ← Category.assoc e.hom.left, ← h₃, Category.assoc, Over.w F, ← Category.assoc, h6, Category.assoc,
      Over.w (ub τ j), ← dual_w]
    rfl
  have w : (spMap (dualMap k.toRingHom) ≫ u' ≫ e.hom.left) ≫ t'.G.hom =
      spMap (algebraMap C (DualNumber C)) ≫ spMap k.toRingHom := by
    rw [Category.assoc, hu, dual_w]
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique h7 Corr.one⟩, xG,
    Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w), hc, ?_, hπ.1.hom_ext ?_ ?_⟩
  · change hφ.1.lift _ _ w ≫ _ = _
    rw [hφ.1.lift_fst_assoc, hz.2.1, ← h5, Category.assoc, Category.assoc, h₁]
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, ← h4, hφ.1.lift_fst_assoc, Category.assoc, Category.assoc, ← h₃, ← Category.assoc u', h6,
      Category.assoc, Category.assoc, hx, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap,
      spMap_spMap, Over.comp_left]
    congr 2
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_
    · simpa [dualMap] using (hk s.fst).symm
    · simpa [dualMap, Algebra.algebraMap_eq_smul_one] using (hk s.snd).symm
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, P.gen_pull.1.w, hφ.1.lift_snd_assoc, Category.assoc, Over.w xG.1]
    exact (dual_w _).symm

end GlobalTheory.CompHt.TieFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePos
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_sec_lbPow_vanishing_of_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB →
      0 < interNum k (GlobalTheory.structureModule C) ![L] →
      ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  intro k _ C _ hC L hL hpos
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hC.1
  obtain ⟨hprop, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k C)).1 hC.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  set O := GlobalTheory.structureModule C with hO
  set d := interNum k O ![L] with hdd
  set f := chiPic k O with hf

  have hdeg : ∀ (M : LB C) (hM : M.IsLB), interNum k O ![M] = f 0 - f (-cls M hM) := by
    intro M hM
    rw [interNum_one k O hM, chi_twistZ k O hM, hf, chiPic_zero, neg_one_zsmul]

  have hchi : ∀ m : ℕ, f ((m : ℤ) • cls L hL) = f 0 + m * d := by
    intro m
    obtain ⟨N, hN, hc⟩ := cls_surj (-((m : ℤ) • cls L hL))
    have hLm := isLB_lbPow hL m
    have e : cls _ (LB.isLB_triv C) = cls N hN + cls _ hLm := by
      rw [hc, cls_lbPow hL m hLm, cls_triv, natCast_zsmul, neg_add_cancel]
    have hadd := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hN hLm e
    rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m, hdeg _ (LB.isLB_triv C), hdeg N hN, hc,
      cls_triv, neg_zero, neg_neg] at hadd
    have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
    linarith
  set m : ℕ := (f 0).natAbs + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hLm := isLB_lbPow hL m
  have hqc := Twist.isQuasicoherent_twist (F := O) hLm
  have hvan : ∀ n, 2 ≤ n → Subsingleton (coh (twist O (lbPow L m)) n) := by
    intro n hn
    refine hH.subsingleton_coh_of_dim_lt _ ?_
    rw [hd]
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hχ : chi k (twist O (lbPow L m)) = f 0 + m * d := by
    rw [← chiPic_cls k O hLm, cls_lbPow hL m hLm, ← natCast_zsmul, ← hf, hchi m]
  have hχpos : 0 < chi k (twist O (lbPow L m)) := by
    rw [hχ]
    have h1 : (1 : ℤ) ≤ d := hpos
    have h2 : -(f 0) ≤ ((f 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs (f 0)
    have h3 : (m : ℤ) = (f 0).natAbs + 1 := by rw [hm]; push_cast; ring
    nlinarith
  have hh0 : 0 < hdim k (twist O (lbPow L m)) 0 := by
    have := chi_eq_hdim_zero_sub_hdim_one k hvan
    omega
  have hnt : Nontrivial (coh (twist O (lbPow L m)) 0) := Module.nontrivial_of_finrank_pos hh0
  obtain ⟨σ, hσ⟩ := hasNonzeroSec_iff_nontrivial.2 hnt
  refine ⟨m, σ, ?_⟩
  by_contra! hall
  have htop : Out.nonzeroLocus σ = ⊤ := top_unique fun c _ ↦ (hall c hm0 hσ)
  have h0 : cls _ hLm = 0 := (cls_eq_zero_iff hLm).2 (exists_isGen_of_nonzeroLocus_eq_top σ htop)
  have hz := interNum_eq_zero_of_cls_eq_zero k O (isLB_vecOne hLm) 0 h0
  rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m] at hz
  have : (0 : ℤ) < m * d := mul_pos (by exact_mod_cast hm0) hpos
  have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
  rw [hd'] at hz
  omega

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.Mem.HeckeLevel

open GlobalTheory.Mem.Chr

theorem exists_level_nat : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  intro L _ _ χ
  classical
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  choose n hn using hlev
  refine ⟨∏ P ∈ hfin.toFinset, (Ideal.absNorm P.asIdeal) ^ (n P), ?_, ?_⟩
  · refine Finset.prod_pos fun P _ => pow_pos (Nat.pos_of_ne_zero fun h => P.ne_bot ?_) _
    exact Ideal.absNorm_eq_zero_iff.1 h
  · intro a ha h1 hv
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local L χ.1 χ.2.1 a ha h1 fun P x hx => ?_
    have hxu : IsUnitAt P x := by
      unfold IsUnitAt
      rw [hx]
      exact ha P
    by_cases hP : P ∈ hfin.toFinset
    · refine hn P x hxu ?_
      rw [hx]
      refine (hv P).trans ?_
      have e : (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : L) : P.adicCompletion L) =
          (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : 𝓞 L) : L) := by
        push_cast
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_dvd]
      have hd : (Ideal.absNorm P.asIdeal) ^ (n P) ∣ ∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) :=
        Finset.dvd_prod_of_mem _ hP
      have hd' := Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (α := 𝓞 L) hd)
      refine Ideal.dvd_iff_le.2 (le_trans hd' ?_)
      rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem P.asIdeal
    · have hu : χ.UnrAt P := by
        by_contra h
        exact hP (hfin.mem_toFinset.2 h)
      exact hu x hxu

end GlobalTheory.Mem.HeckeLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegAdelicSchwartzBumpTestStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  first | exact @GlobalTheory.AdelicBumpTest.exists_nonneg_test | exact GlobalTheory.AdelicBumpTest.exists_nonneg_test | (intros; apply GlobalTheory.AdelicBumpTest.exists_nonneg_test <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapCancel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct
open GlobalTheory.UPel.HT GlobalTheory.IwLevel GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_objMap_cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) :
    ∃ m' : ObjMap o₁ o₂ f, m'.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

end GlobalTheory.IwLevel
end
end

