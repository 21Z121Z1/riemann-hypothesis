import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0053
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ZeroSetSpecialFibreConnected
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullLevelFiniteExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR.LevelPt

theorem exists_finite_subfield {F k : Type} [Field F] [Field k] [Algebra F k] [Algebra.IsAlgebraic F k]
    {X : Scheme.{0}} (s : X ⟶ Sp F) [LocallyOfFiniteType s] (p : Sp k ⟶ X)
    (hp : p ≫ s = spMap (algebraMap F k)) :
    ∃ K : IntermediateField F k, FiniteDimensional F K ∧ ∃ q : Sp K ⟶ X, spMap (algebraMap K k) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint k))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, U) ⟶ CommRingCat.of k, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum k) y (IsLocalRing.closedPoint k)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of F ⟶ Γ(X, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap F k) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : F, f.hom (g.hom r) = algebraMap F k r := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra F Γ(X, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType F Γ(X, U) from hft).out
  let S : Set k := (t.image f.hom : Finset k)
  let K := IntermediateField.adjoin F S
  refine ⟨K, IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin F (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F S (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem epi_spMap {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_reps (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (N : ℕ) (hN : 0 < N) :
    ∃ (T : Type) (_ : Finite T) (r : M → T) (u : T → M), ∀ a, ∃ b, a = u (r a) + N • b := by
  let S : Submodule ℤ M := LinearMap.range ((N : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))
  have hfin : Finite (M ⧸ S) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro x
    obtain ⟨a, rfl⟩ := S.mkQ_surjective x
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
    show (N : ℤ) • S.mkQ a = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero S).2 ⟨a, by simp⟩
  refine ⟨M ⧸ S, hfin, S.mkQ, fun t => Function.surjInv S.mkQ_surjective t, fun a => ?_⟩
  have h : S.mkQ (Function.surjInv S.mkQ_surjective (S.mkQ a)) = S.mkQ a :=
    Function.surjInv_eq _ _
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq S).1 h.symm
  refine ⟨b, ?_⟩
  have hb' : (N : ℤ) • b = a - Function.surjInv S.mkQ_surjective (S.mkQ a) := by simpa using hb
  have : N • b = (N : ℤ) • b := by simp
  rw [this, hb']
  abel

theorem exists_extend {L K C : Type} [Field L] [Field K] [Algebra L K] [Algebra.IsAlgebraic L K] [Field C] [IsAlgClosed C]
    (f : L →+* C) : ∃ g : K →+* C, ∀ x, g (algebraMap L K x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : K →ₐ[L] C), fun x => (IsAlgClosed.lift : K →ₐ[L] C).commutes x⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem finite_La (D : Datum H) : Module.Finite ℤ D.La :=
  haveI := D.fin
  Module.Finite.trans (𝓞 E) D.La

theorem exists_of_tateIso {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] [CharZero L] (y : Sp K ⟶ Xo.XF c) (N : ℕ) (hN : 1 ≤ N)
    (I : TateIsoAt D Y.oF.t (spMap (algebraMap K L) ≫ y)) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ)
      (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)),
      FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  classical
  have hN0 : 0 < N := hN
  haveI := Y.oF.proper

  let q : pullback Y.oF.t.G.hom y ⟶ Sp K := pullback.snd _ _
  have hw : ∀ a, (I.ev N a).left ≫ Y.oF.t.G.hom = spMap (algebraMap K L) ≫ y := fun a =>
    Over.w (I.ev N a)
  let g : D.La → (Sp L ⟶ pullback Y.oF.t.G.hom y) := fun a =>
    pullback.lift (I.ev N a).left (spMap (algebraMap K L)) (hw a)
  have hg : ∀ a, g a ≫ q = spMap (algebraMap K L) := fun a => pullback.lift_snd _ _ _
  have hgf : ∀ a, g a ≫ pullback.fst _ _ = (I.ev N a).left := fun a => pullback.lift_fst _ _ _
  haveI := finite_La D
  obtain ⟨T, _, r, u, hru⟩ := exists_reps D.La N hN0
  choose F hF e he using fun τ : T => exists_finite_subfield q (g (u τ)) (hg _)

  let Fz : IntermediateField K L := IntermediateField.adjoin K {((I.ζ N : Lˣ) : L)}
  haveI : FiniteDimensional K Fz := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : ∀ τ, FiniteDimensional K (F τ) := hF
  let Ω : IntermediateField K L := Fz ⊔ ⨆ τ, F τ
  have hΩfin : FiniteDimensional K Ω := by
    haveI : FiniteDimensional K (⨆ τ, F τ : IntermediateField K L) :=
      IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_sup _ _
  have hFΩ : ∀ τ, F τ ≤ Ω := fun τ => (le_iSup F τ).trans le_sup_right
  have hz : ((I.ζ N : Lˣ) : L) ∈ Ω :=
    (le_sup_left : Fz ≤ Ω) (IntermediateField.subset_adjoin K _ rfl)
  let z : (↥Ω)ˣ := Units.mk0 ⟨_, hz⟩ (fun h => (I.ζ N).ne_zero (congrArg Subtype.val h))
  let eΩ : T → (Sp Ω ⟶ pullback Y.oF.t.G.hom y) := fun τ =>
    spMap (IntermediateField.inclusion (hFΩ τ)).toRingHom ≫ e τ
  have heΩ : ∀ τ, spMap (algebraMap Ω L) ≫ eΩ τ = g (u τ) := fun τ => by
    rw [← he τ]
    simp only [eΩ]
    rw [← Category.assoc, spMap_comp_spMap]
    rfl
  haveI := epi_spMap (algebraMap Ω L)
  have hover : ∀ τ, eΩ τ ≫ q = spMap (algebraMap K Ω) := fun τ => by
    rw [← cancel_epi (spMap (algebraMap Ω L)), ← Category.assoc, heΩ, hg, spMap_comp_spMap]
    rfl
  have hpull : ∀ τ, eΩ τ ≫ pullback.fst _ _ ≫ Y.oF.t.G.hom = spMap (algebraMap K Ω) ≫ y := fun τ => by
    calc eΩ τ ≫ pullback.fst _ _ ≫ Y.oF.t.G.hom = eΩ τ ≫ q ≫ y := congrArg (eΩ τ ≫ ·) pullback.condition
      _ = (eΩ τ ≫ q) ≫ y := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ y) (hover τ)

  have hφ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
  have hevw : ∀ τ, (eΩ τ ≫ pullback.fst _ _ ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap K Ω) ≫ y ≫ Y.j := fun τ => by
    have h := congrArg (· ≫ Y.j) (hpull τ)
    simp only [Category.assoc] at h ⊢
    rw [hφ]
    exact h
  let ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G) := fun a =>
    Over.homMk (eΩ (r a) ≫ pullback.fst _ _ ≫ Y.m.φ) (hevw (r a))
  refine ⟨Ω, inferInstance, inferInstance, z, ev, hΩfin, ?_⟩
  intro k _ _ i

  haveI : Algebra.IsAlgebraic Ω L := Algebra.IsAlgebraic.tower_top (K := K) Ω
  obtain ⟨i', hi'⟩ : ∃ i' : L →+* k, ∀ x : Ω, i' (algebraMap Ω L x) = i x := exists_extend i
  have hcomp : i'.comp (algebraMap Ω L) = i := RingHom.ext hi'
  have hprop : IsProper (pullback.snd Y.oF.t.G.hom (spMap (algebraMap K L) ≫ y)) := inferInstance
  obtain ⟨I', hI'⟩ := GlobalTheory.T.tate_iso_base_change E H D (Xo.XF c) Y.oF.t L k i' _ hprop I
  have hx : spMap i ≫ spMap (algebraMap K Ω) ≫ y ≫ Y.j =
      (spMap i' ≫ spMap (algebraMap K L) ≫ y) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    have h1 : spMap i ≫ spMap (algebraMap K Ω) = spMap i' ≫ spMap (algebraMap K L) := by
      rw [spMap_comp_spMap, spMap_comp_spMap, ← hcomp]
      rfl
    rw [← Category.assoc, h1]
    simp only [Category.assoc]
    rfl
  obtain ⟨I'', hζ, hev⟩ := (GlobalTheory.T.tate_iso_pullback_equiv E H D Y.X (Xo.XF c) Y.t Y.oF.t _ Y.m k _ _ hx).2 I'
  refine ⟨I'', ?_, fun a => ?_⟩
  · rw [← hζ]
    rw [(hI' N hN0).1]
    exact hi' z
  · obtain ⟨b, hb⟩ := hru a
    have hev1 : I.ev N a = I.ev N (u (r a)) := by
      have : I.ev N (N • b) = 1 := (I.ker N hN0 _).2 ⟨b, rfl⟩
      conv_lhs => rw [hb]
      rw [I.add, this, _root_.mul_one]
    have h2 : (I.ev N a).left = spMap (algebraMap Ω L) ≫ eΩ (r a) ≫ pullback.fst _ _ := by
      rw [← Category.assoc, heΩ, hgf, hev1]
    rw [← hev, (hI' N hN0).2 a, h2]
    show _ = spMap i ≫ eΩ (r a) ≫ pullback.fst _ _ ≫ Y.m.φ
    simp only [Category.assoc]
    rw [← Category.assoc (spMap i'), spMap_comp_spMap, hcomp]

end GlobalTheory.CompanionTheory.Ar.XR.LevelPt

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem exists_fullLevel_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (N : ℕ), 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ) (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)), FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  intro E _ _ _ H D l Xo c O _ β Y K _ y N hN

  haveI hK : CharZero K := by
    let f : c.F →+* K := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    exact charZero_of_injective_ringHom f.injective
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let xb : Sp (AlgebraicClosure K) ⟶ Xo.XF c := spMap (algebraMap K (AlgebraicClosure K)) ≫ y
  let f : CommRingCat.of (KA l) ⟶ CommRingCat.of (AlgebraicClosure K) :=
    Spec.preimage (xb ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hf : xb ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap f.hom :=
    (Spec.map_preimage _).symm
  obtain ⟨-, I, -⟩ := Y.oF.geom (AlgebraicClosure K) xb f.hom hf
  exact LevelPt.exists_of_tateIso Y y N hN I

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullbackStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_level_structure_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X'), ξ' ≫ f = spMap i ≫ ξ → ∀ (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ ev' : D.La → (Over.mk ξ' ⟶ t'.G), IsFullLevelAt D t' ξ' N (Units.map i.toMonoidHom z) ev' ∧ ∀ a, (ev' a).left ≫ m.φ = spMap i ≫ (ev a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isFullLevelAt_move <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorsPull

theorem spMap_cancel {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of Ω) ⟶ Z) (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom i)) :=
    GlobalTheory.CompanionTheory.Ar.LieEx.std_of_inj (CommRingCat.ofHom i) i.injective
  refine GlobalTheory.CompanionTheory.Ar.LieEx.epi_of_surj (Spec.map (CommRingCat.ofHom i)) ?_ a b h
  intro y
  have hs : Subsingleton (Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of Ω')) :=
    inferInstanceAs (Nonempty (PrimeSpectrum Ω'))
  exact ⟨x, Subsingleton.elim _ _⟩

theorem tr_pow {S : Scheme.{0}} {T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (n : ℕ) (u : Over.mk a ⟶ G) (hu : u ^ n = 1) :
    ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
  subst h
  exact ⟨u, rfl, hu⟩

theorem torsion_of_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ _ φ h n hf
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  let u : Over.mk (ξ' ≫ f) ⟶ Over.mk ξ := Over.homMk (spMap i) (by simpa using hd'.symm)
  let P : (Over.mk ξ' ⟶ G') →* (Over.mk (ξ' ≫ f) ⟶ G) := pushHom h (Over.mk ξ')
  let Q : (Over.mk ξ ⟶ G) →* (Over.mk (ξ' ≫ f) ⟶ G) := preHom u
  have rel : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → P a = Q c :=
    fun a c e => Over.OverMorphism.ext e
  have lerp : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), P a = Q c → a.left ≫ φ = spMap i ≫ c.left :=
    fun a c e => congrArg (fun z => z.left) e
  have Pinj : Function.Injective P := by
    intro a a' e
    have e1 : a.left ≫ φ = a'.left ≫ φ := congrArg (fun z => z.left) e
    have w : ∀ b : Over.mk ξ' ⟶ G', b.left ≫ G'.hom = ξ' := fun b => by simpa using Over.w b
    exact Over.OverMorphism.ext (h.1.hom_ext e1 ((w a).trans (w a').symm))
  have Qinj : Function.Injective Q := by
    intro c c' e
    have e1 : spMap i ≫ c.left = spMap i ≫ c'.left := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (spMap_cancel i _ _ e1)
  refine ⟨GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates X X' Ω Ω' ξ ξ' f i G G' φ n hd h hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hxw : y.left ≫ G.hom = ξ := by simpa using Over.w y
    have hw : (spMap i ≫ y.left) ≫ G.hom = ξ' ≫ f := by rw [Category.assoc, hxw, hd']
    let y' : Over.mk ξ' ⟶ G' := Over.homMk (h.1.lift (spMap i ≫ y.left) ξ' hw) (h.1.lift_snd _ _ _)
    have e : y'.left ≫ φ = spMap i ≫ y.left := h.1.lift_fst _ _ _
    refine ⟨y', Pinj ?_, e⟩
    rw [map_pow, map_one, rel y' y e, ← map_pow, hy, map_one]
  · intro y' hy'
    have hP : (P y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    obtain ⟨g, hl, hg⟩ := tr_pow hd' n (P y') hP
    obtain ⟨y, hy⟩ := hf Ω' i g hg
    have e : y'.left ≫ φ = spMap i ≫ y.left := hl.symm.trans hy
    refine ⟨y, Qinj ?_, e⟩
    rw [map_pow, map_one, ← rel y' y e, hP]
  · intro a a' c c' e e'
    apply lerp
    rw [map_mul, map_mul, rel a c e, rel a' c' e']
  · intro a a' c e e'
    exact Pinj ((rel a c e).trans (rel a' c e').symm)
  · intro a c c' e e'
    exact Qinj ((rel a c e).symm.trans (rel a c' e'))

end GlobalTheory.CompanionTheory.Ar.TorsPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricPowerFreeFunctorialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_power_free_functorial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), (∀ (k k₂ : Type) [Field k] [Field k₂] (f : k →+* k₂) (x : Sp k ⟶ X0), GeomPF t x → GeomPF t (spMap f ≫ x)) ∧ ∀ (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (k : Type) [Field k] (x : Sp k ⟶ X₂), GeomPF t₂ x ↔ GeomPF t (x ≫ f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeomBC.geomPF_baseChange | exact GlobalTheory.CompanionTheory.Ar.GeomBC.geomPF_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.GeomBC.geomPF_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlag
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp

theorem exists_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (i : R →+* R') (x : Sp R ⟶ S) (y : Sp R' ⟶ S) (hy : spMap i ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = spMap (dualMap i) ≫ (M.pt e).left) ∧ IsExtOver i j ∧
      Submodule.span R' (Set.range j) = ⊤ := by
  subst hy
  letI := i.toAlgebra
  obtain ⟨j, hj, hl, hsp⟩ := GlobalTheory.T.lie_model_base_change_map S G R R' x E E' M M'
  have hbc := hsp hs
  obtain ⟨m, ⟨b₁⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring S G hs R x E M
  refine ⟨j, hj, ⟨hl, fun n b hb => LiePull.indep_of_bases b₁ j (fun m B => (hbc m B).1) b hb⟩, ?_⟩
  refine top_le_iff.1 ((hbc m b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

variable {Ω Ω₀ F F₀ : Type} [Field Ω] [Field Ω₀] [AddCommGroup F] [Module Ω F] [AddCommGroup F₀] [Module Ω₀ F₀]

theorem span_span (W A : Subring Ω) (h : ∀ a ∈ A, a ∈ W) (T : Set F) :
    Submodule.span W ((Submodule.span A T : Submodule A F) : Set F) = Submodule.span W T := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ (⟨(a : Ω), h _ a.2⟩ : W) hx

theorem span_image_span (i : Ω₀ →+* Ω) (ι : F₀ →+ F) (hι : ∀ (a : Ω₀) (e : F₀), ι (a • e) = i a • ι e)
    (W : Subring Ω) (A : Subring Ω₀) (h : ∀ a ∈ A, i a ∈ W) (T : Set F₀) :
    Submodule.span W (ι '' ((Submodule.span A T : Submodule A F₀) : Set F₀)) = Submodule.span W (ι '' T) :=
  _root_.UpperTheory.Reformulated.B.DYha5.main i ι hι W A h T

theorem lie_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ Fl₀ i hh
  have hs : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨ι, hpt, hext, hspan⟩ := exists_ext hs i (𝔐₀.ξ ≫ 𝔐₀.f) (𝔐.ξ ≫ 𝔐.f) hh.symm
    (LieMove.pushModel 𝔐₀.m.cart 𝔐₀.M) (LieMove.pushModel 𝔐.m.cart 𝔐.M)
  have hpt' : ∀ e, (𝔐.M.pt (ι e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ := hpt
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ₀ 𝔐.f (i.comp 𝔐₀.fn) := by
    have h₀ : 𝔐₀.ξ ≫ 𝔐₀.f = Spec.map (CommRingCat.ofHom 𝔐₀.fn) ≫ 𝔐₀.ξ₀ := 𝔐₀.fn_over
    show 𝔐.ξ ≫ 𝔐.f = _
    rw [hh, h₀, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hj' : ∀ e, (𝔐.M.pt ((ι.comp Fl₀.j) e)).left ≫ 𝔐.m.φ =
      Spec.map (CommRingCat.ofHom (dualMap (i.comp 𝔐₀.fn))) ≫ (Fl₀.M₀.pt e).left := by
    intro e
    rw [AddMonoidHom.comp_apply, hpt', Fl₀.j_pt, ← LiePull.dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]
  have m₀ := (LiePull.main Y.X 𝔐₀.X 𝔐₀.Ω₀ Ω₀ 𝔐₀.ξ₀ 𝔐₀.ξ 𝔐₀.f 𝔐₀.fn Y.t.G 𝔐₀.t.G 𝔐₀.m.φ Fl₀.Li₀ 𝔐₀.Li Fl₀.M₀ 𝔐₀.M
    Fl₀.j 𝔐₀.gen₀ 𝔐₀.tie.gen 𝔐₀.fn_over 𝔐₀.m.cart hs Fl₀.j_pt).2.2
  have m₁ := (LiePull.main Y.X 𝔐.X 𝔐₀.Ω₀ Ω 𝔐₀.ξ₀ 𝔐.ξ 𝔐.f (i.comp 𝔐₀.fn) Y.t.G 𝔐.t.G 𝔐.m.φ Fl₀.Li₀ 𝔐.Li Fl₀.M₀ 𝔐.M
    (ι.comp Fl₀.j) 𝔐₀.gen₀ 𝔐.tie.gen hd 𝔐.m.cart hs hj').2.2
  refine ⟨ι, hext, hspan, fun e e' => ⟨fun h => ?_, ?_⟩, fun W q q₀ hq hq₀ hf => ?_⟩
  · exact (LieMove.pushModel 𝔐.m.cart 𝔐.M).inj (Over.OverMorphism.ext (h.trans (hpt' e).symm))
  · rintro rfl
    exact hpt' e
  · have a₁ := congrFun m₁ q
    rw [Lat.pull_apply _ hd] at a₁
    have a₀ := congrFun m₀ q₀
    rw [Lat.pull_apply _ 𝔐₀.fn_over] at a₀
    have es : (⟨𝔐.f q.1, hd.specializes q⟩ : Cpt 𝔐₀.ξ₀) = ⟨𝔐₀.f q₀.1, 𝔐₀.fn_over.specializes q₀⟩ := Subtype.ext hf
    rw [a₁, a₀, es, span_span W _ hq, span_image_span i ι hext.1 W _ hq₀, Set.image_image]
    rfl

end GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_conjugate : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hcpt_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) :=
  @PositivityTheory.HtPt.Hcptgen.hcpt_generic

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_open_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion x] (κ : FractionRing R ≃+* Ω), spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x n i → ∀ (L₀ : Type) [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E), (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) → ∀ (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E), y ^ n = 1 → (∀ (t : T) (g : Over.mk ξ ⟶ G), spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → κ (algebraMap R _ (χ t : R)) = e y g) → Γ.IsHT i M₀ n χ w₀ → (∀ v, w (j v) = κ (algebraMap R _ (w₀ v))) → ∀ q : Cpt ξ, q.1 ∈ Set.range x → M.IsHTAt L n y q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | exact GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isConnected_zeroSet_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) :=
  @PositivityTheory.Xgn.zero_set_special_fibre_connected

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sections_affine_model : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | exact GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_eval_at_local_ring : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER), IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER, (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧ (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧ Submodule.span R (Set.range ev) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_val | exact GlobalTheory.CompanionTheory.Ar.lieLat_val | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_val <;> assumption)
end

