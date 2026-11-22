import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem existsUnique_hom_extension_smConn_semiAbelian_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  intro T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨hcomm, hsm, hsep, hqc, hgc⟩ := hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one
    AbelianSubgroupFinite.finite_of_torsionFree (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hsm hgc hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.DivisiblePart

open RationalPoint

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y)
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) :
    Surjective f.left := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hC := (isConstructible_image_of_isClosed f isClosed_univ).compl
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible
    continuous_id hC
  rw [Set.preimage_id] at h1 h2
  have hne : (V ∩ closure (f.left '' Set.univ)ᶜ).Nonempty := by
    rw [← closure_nonempty_iff, h2, closure_nonempty_iff]
    exact ⟨y, fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩⟩
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨z, hz⟩ := exists_pt_mem (X := Y) (Z := {c}) hc ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := h z
  exact h1 hcZ ⟨pt x, trivial, hz⟩

theorem geometricallyConnected_of_surjective {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [GeometricallyConnected (f ≫ g)] : GeometricallyConnected g := by
  refine ⟨fun K _ y W fst snd hW => ?_⟩
  have h1 := (IsPullback.of_hasPullback f fst).paste_vert hW
  have : ConnectedSpace ↥(pullback f fst) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h1
  exact (pullback.snd f fst).surjective.connectedSpace (pullback.snd f fst).continuous

theorem isIso_of_dim_le {k : Type} [Field k] {N G : Scheme.{0}} (ν : N ⟶ G) (s : G ⟶ Sp k)
    [IsClosedImmersion ν] [IsIntegral G] [IsReduced N] [Nonempty N] {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g s) (hg' : SmoothOfRelativeDimension g' (ν ≫ s))
    (hle : g ≤ g') : IsIso ν := by
  suffices Surjective ν from isIso_of_isClosedImmersion_of_surjective ν
  refine ⟨fun y => ?_⟩
  by_contra hy
  obtain ⟨n⟩ := ‹Nonempty N›
  obtain ⟨_, ⟨U, hU, rfl⟩, hnU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ν n)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let W : G.Opens := ⟨(Set.range ν)ᶜ, ν.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨z, hzU, hzW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨_, hnU⟩ ⟨y, hy⟩
  obtain ⟨r, hrW, hzr⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hzU
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hzr
  have hr1 : (ν.app U).hom r = 0 := by
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    exact (hrW ht ⟨t, rfl⟩).elim
  have : Nonempty U := ⟨⟨_, hnU⟩⟩
  have h1 := ringKrullDim_succ_le_of_surjective (ν.app U).hom (ν.app_surjective U hU)
    (mem_nonZeroDivisors_of_ne_zero hr0) hr1
  rw [SmoothDim.ringKrullDim_affineOpen k G s g hg U hU ⟨_, hnU⟩,
    SmoothDim.ringKrullDim_affineOpen k N _ g' hg' _ (hU.preimage ν) ⟨n, hnU⟩] at h1
  have : g' + 1 ≤ g := by exact_mod_cast h1
  omega

theorem exists_divisiblePart : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ G), SmConn N ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ (∀ y : (𝟙_ (Over (Sp k)) ⟶ N), ∃ x : (𝟙_ (Over (Sp k)) ⟶ N), x ^ p = y) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) (n : ℕ), n.Coprime p → n ≠ 0 → x ^ n = 1 → ∃ y, y ≫ ν = x) ∧ (∀ F : G ⟶ G, IsMonHom F → ∃ F' : N ⟶ N, IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ g', SmoothOfRelativeDimension g' N.hom ∧ (g ≤ g' → IsIso ν) := by
  intro k _ _ p G _ ⟨hc, hs, hsep, hqc, hgc⟩
  obtain ⟨a, ha⟩ := TorsionDense.exists_pow_stable G p ⊤ Set.univ isClosed_univ (by simp)
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  obtain ⟨Z, hZ, h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ (p ^ a))
    (hpow _) inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ
    (by simp)
  replace h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, (∃ x, x ^ (p ^ a) = y) ↔ Set.range y.left ⊆ Z := by
    intro y
    rw [← h]
    simp only [MonObj.comp_pow, Category.comp_id, Subgroup.mem_top, true_and]
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    have := hpow (p ^ a)
    MonoidHom.mk' (fun x => x ≫ 𝟙 G ^ (p ^ a)) fun x y => MonObj.mul_comp x y _
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance φ.range Z hZ (fun x => by
      rw [← h, MonoidHom.mem_range]
      simp only [φ, MonoidHom.mk'_apply, MonObj.comp_pow, Category.comp_id])
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hw : N.hom = ν.left ≫ G.hom := (Over.w ν).symm
  have hNsep : IsSeparated N.hom := by rw [hw]; infer_instance
  have hNqc : QuasiCompact N.hom := by rw [hw]; infer_instance
  have hGi : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have hNr : IsReduced N.left :=
    have := isNormalScheme_of_smooth N.hom
    IsNormalScheme.isReduced
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ G),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, ∃ y, y ^ (p ^ a) = x ≫ g) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset g.left ν.left
      (hr ▸ ReducedSubgroup.range_subset_of_points g hZ fun x => (h _).1 (hg x))
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, g.w]
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, ∃ y, y ^ (p ^ a) = x ≫ ν := fun x => by
    rw [h, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  obtain ⟨l, hl⟩ := hlift (𝟙 G ^ (p ^ a)) fun x => ⟨x, by rw [MonObj.comp_pow, Category.comp_id]⟩
  have hl' : ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (x ≫ l) ≫ ν = x ^ (p ^ a) := fun x => by
    rw [Category.assoc, hl, MonObj.comp_pow, Category.comp_id]
  have : Surjective l.left := surjective_of_rationalPoints l fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, by rw [← cancel_mono ν, hl', hx]⟩
  have hNgc : GeometricallyConnected N.hom := by
    have : GeometricallyConnected (l.left ≫ N.hom) := by rw [Over.w l]; exact hgc
    exact geometricallyConnected_of_surjective l.left N.hom
  refine ⟨N, _, ν, ⟨AbelianSubgroupFinite.isCommMonObj_of_mono ν, hNs, hNsep, hNqc, hNgc⟩, hν, hνc,
    fun y => ?_, fun x n hn hn0 hx => ?_, fun F hF => ?_, fun g hg => ?_⟩
  · obtain ⟨x, hx⟩ := hmem y
    obtain ⟨z, -, hz⟩ := ha x trivial
    refine ⟨z ≫ l, ?_⟩
    rw [← cancel_mono ν, MonObj.pow_comp, hl', ← pow_mul, ← pow_succ, hz, hx]
  · have hco : (p ^ a).Coprime (orderOf x) :=
      (Nat.Coprime.pow_left a hn.symm).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
    exact ⟨(x ^ m) ≫ l, by rw [hl', ← pow_mul, mul_comm, pow_mul, hm]⟩
  · obtain ⟨F', hF'⟩ := hlift (ν ≫ F) fun x => by
      obtain ⟨y, hy⟩ := hmem x
      exact ⟨y ≫ F, by rw [← MonObj.pow_comp, hy, Category.assoc]⟩
    refine ⟨F', ⟨?_, ?_⟩, hF'⟩
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hF']
  · have hNi : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
    obtain ⟨g', hg'⟩ := exists_dim_of_preconnected N.hom (Classical.arbitrary _)
    refine ⟨g', hg', fun hle => ?_⟩
    have : IsIso ν.left := isIso_of_dim_le ν.left G.hom hg (hw ▸ hg') hle
    have : IsIso ((Over.forget _).map ν) := this
    exact isIso_of_reflects_iso ν (Over.forget _)

end GlobalTheory.DivisiblePart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.GenSpread

section Rings

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isFractionRing_of_forall_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem isNoetherianRing_of_fg [IsNoetherianRing o] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R :=
  have : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 h
  Algebra.FiniteType.isNoetherianRing o R

theorem exists_shrink {R : Subalgebra o Ω} (hR : R.FG) {J : Type} [Finite J] (a : J → R) (ha : ∀ i, a i ≠ 0)
    {X X₀ : Scheme.{0}} {f : X ⟶ Sp R} {f₀ : X₀ ⟶ Sp Ω} {φ : X₀ ⟶ X}
    (h : IsPullback φ f₀ f (spMap (algebraMap R Ω))) :
    ∃ (R' : Subalgebra o Ω) (g : R →+* R'), R ≤ R' ∧ R'.FG ∧ (algebraMap R' Ω).comp g = algebraMap R Ω ∧
      (∀ i, IsUnit (g (a i))) ∧ ∃ φ' : X₀ ⟶ pullback f (spMap g), φ' ≫ pullback.fst _ _ = φ ∧
        IsPullback φ' f₀ (pullback.snd f (spMap g)) (spMap (algebraMap R' Ω)) := by
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (Set.range fun i => (a i : Ω)⁻¹)
  have hle : R ≤ R' := le_sup_left
  let g : R →+* R' := (Subalgebra.inclusion hle).toRingHom
  have e : spMap (algebraMap R' Ω) ≫ spMap g = spMap (algebraMap R Ω) := by
    rw [← Spec.map_comp]; rfl
  refine ⟨R', g, hle, hR.sup ?_, rfl, fun i => ?_,
    pullback.lift φ (f₀ ≫ spMap (algebraMap R' Ω)) (by rw [Category.assoc, e, h.w]), pullback.lift_fst _ _ _, ?_⟩
  · exact (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  · have hm : (a i : Ω)⁻¹ ∈ R' := (le_sup_right : _ ≤ R') (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext ?_)
    exact mul_inv_cancel₀ (fun h0 => ha i (Subtype.ext h0))
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (spMap g))
    rwa [pullback.lift_fst, e]

end Rings

theorem comp_linComb {S : Scheme.{0}} {A : Over S} [GrpObj A] {T T' : Over S} (t : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : t ≫ linComb y c = linComb (fun i => t ≫ y i) c := by
  have := map_list_prod (preHom (G := A) t) (List.ofFn fun i => y i ^ c i)
  simp only [List.map_ofFn, Function.comp_def, map_pow] at this
  exact this

theorem polAV_spreads_out : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), IsUnit (M : o) → HypS P.A P.L → ∀ lev : Out.Level P M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze)), Laws → ∃ (R : Subalgebra o Ω) (P' : PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left) (lev' : Out.Level P' M (unitOn (Units.map (algebraMap o R).toMonoidHom ze))), R₀ ≤ R ∧ R.FG ∧ P'.g = P.g ∧ HypS P'.A P'.L ∧ IsGrpPullback P.A P'.A (spMap R.val.toRingHom) φ ∧ LBIso P.L (P'.L.pull φ) ∧ ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev.pt i).left ≫ φ = spMap R.val.toRingHom ≫ (lev'.pt i').left := by
  intro o Ω _ _ _ hB R₀ hR₀ hfr P M ze hM hS lev hL
  have := hB.ded
  obtain ⟨w₀, wd₀, hw₀, hwd₀, hww, hS₁, hS₂⟩ := hS
  have := P.isAb.proper
  have := P.isAb.smooth

  have := isFractionRing_of_forall_div hfr
  have := isNoetherianRing_of_fg hR₀
  obtain ⟨X₀, f₀, φ₀, H₀, N, hf₀, p₀, hH₀, aH₀, hN, eH₀⟩ := exists_projective_model (R := R₀) P.A.hom
    (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample) P.isLB
  obtain ⟨a₀, ha₀, Hsm⟩ := GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre R₀ Ω P.g X₀ _ f₀ _ φ₀ p₀ hf₀ P.smoothDim
  obtain ⟨R₁, g₁, le₁, hR₁, c₁, u₁, φ₁, e₁, p₁⟩ := exists_shrink hR₀ (fun _ : PUnit => a₀) (fun _ => ha₀) p₀
  have hsm₁ := Hsm R₁ g₁ (u₁ ⟨⟩) _ _ _ (IsPullback.of_hasPullback f₀ (spMap g₁))
  have hH₁ := pull_isLB hH₀ (pullback.fst f₀ (spMap g₁))
  have aH₁ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₀ (pullback.fst f₀ (spMap g₁))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f₀ (spMap g₁)).flip inferInstance)
  have eH₁ := LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₀ _) (pull_isLB hH₁ _) eH₀
    (lbIso_pull_pull hH₀ φ₁ e₁.symm)
  have hf₁ : IsProper (pullback.snd f₀ (spMap g₁)) := inferInstance
  generalize H₀.pull (pullback.fst f₀ (spMap g₁)) = H₁ at hH₁ aH₁ eH₁
  clear e₁
  generalize pullback.snd f₀ (spMap g₁) = f₁ at hsm₁ hf₁ p₁
  generalize pullback f₀ (spMap g₁) = X₁ at f₁ φ₁ H₁ hsm₁ hf₁ p₁ hH₁ aH₁ eH₁
  have hfr₁ : ∀ x : Ω, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr x
    exact ⟨a, le₁ ha, b, le₁ hb, e⟩
  clear Hsm u₁ c₁ eH₀ aH₀ hH₀ p₀ ha₀

  have := isFractionRing_of_forall_div hfr₁
  have := isNoetherianRing_of_fg hR₁
  have hs₁ : Smooth f₁ := SmoothOfRelativeDimension.smooth P.g f₁
  have : LocallyOfFinitePresentation f₁ := inferInstance
  obtain ⟨a₁, ha₁, Hconn⟩ := GlobalTheory.T.exists_geometricallyConnected_away_of_genericFibre R₁ Ω X₁ _ f₁ _ φ₁ p₁ hs₁
    ((ProjSpace.isProjBy_iff_isProjOver f₁).2 (aH₁.isProjOver f₁)) P.isAb.geomConnected
  obtain ⟨a₂, ha₂, Hgrp⟩ := GlobalTheory.T.exists_group_law_smooth_proper_model_of_generic R₁ Ω X₁ f₁ P.A φ₁ p₁ hs₁ hf₁
  obtain ⟨a₃, ha₃, Hlb⟩ := GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper R₁ Ω X₁ _ f₁ _ φ₁ p₁ inferInstance hf₁ P.L P.isLB
  obtain ⟨a₄, ha₄, Hw⟩ := exists_hom f₁ f₁ p₁ (w₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  obtain ⟨a₅, ha₅, Hwd⟩ := exists_hom f₁ f₁ p₁ (wd₀.left ≫ φ₁) (by rw [Category.assoc, p₁.w, Over.w_assoc])
  choose b hb Hpt using fun i => exists_hom (𝟙 (Sp R₁)) f₁ (φ := spMap (algebraMap R₁ Ω)) (p₀ := 𝟙 (Sp Ω))
    (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₁) (by
      rw [Category.assoc, p₁.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, φ₂, e₂, p₂⟩ := exists_shrink hR₁ (Sum.elim ![a₁, a₂, a₃, a₄, a₅] b)
    (by rintro (i | i); · fin_cases i <;> assumption
        · exact hb i) p₁
  have es₂ : spMap (algebraMap R₂ Ω) ≫ spMap g₂ = spMap (algebraMap R₁ Ω) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have q₂ := IsPullback.of_hasPullback f₁ (spMap g₂)
  let G : Over (Sp R₂) := Over.mk (pullback.snd f₁ (spMap g₂))
  obtain ⟨_, hcomm, hG⟩ := Hgrp R₂ g₂ (u₂ (.inl 1)) (algebraMap R₂ Ω) Subtype.val_injective c₂ G
    (pullback.fst _ _) φ₂ q₂ e₂ p₂.w
  obtain ⟨L₂, hL₂, eL₂⟩ := Hlb R₂ g₂ (u₂ (.inl 2)) _ _ _ q₂.w
  replace eL₂ := eL₂ φ₂ e₂
  have endo : ∀ v₀ : P.A ⟶ P.A, (∃ u : G.left ⟶ X₁, u ≫ f₁ = pullback.fst f₁ (spMap g₂) ≫ f₁ ∧
      ∀ φ' : P.A.left ⟶ G.left, φ' ≫ pullback.fst f₁ (spMap g₂) = φ₁ → φ' ≫ u = v₀.left ≫ φ₁) →
      ∃ v : G ⟶ G, φ₂ ≫ v.left = v₀.left ≫ φ₂ := by
    rintro v₀ ⟨u, hu, hu'⟩
    refine ⟨Over.homMk (q₂.lift u G.hom (hu.trans q₂.w)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact hu' φ₂ e₂
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      exact p₂.w
  obtain ⟨w, hw⟩ := endo w₀ (Hw R₂ g₂ (u₂ (.inl 3)) _ _ _ q₂.w)
  obtain ⟨wd, hwd⟩ := endo wd₀ (Hwd R₂ g₂ (u₂ (.inl 4)) _ _ _ q₂.w)
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ G, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω) ≫ y.left := fun i => by
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ (.inr i)) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, e₂]
      exact (hu' _ es₂).symm
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, p₂.w, Over.w_assoc]
      simp
  choose y hy using pts
  have hsm₂ : SmoothOfRelativeDimension P.g G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₂ hsm₁
  have hab : IsAbelianScheme G :=
    { comm := hcomm
      smooth := SmoothOfRelativeDimension.smooth P.g G.hom
      proper := inferInstanceAs (IsProper (pullback.snd f₁ (spMap g₂)))
      geomConnected := Hconn R₂ g₂ (u₂ (.inl 0)) _ _ _ q₂ }
  have hH₂ := pull_isLB hH₁ (pullback.fst f₁ (spMap g₂))
  have aH₂ := @IsAmpleLB.pull_of_isAffineHom _ _ _ aH₁ (pullback.fst f₁ (spMap g₂))
    (MorphismProperty.of_isPullback (P := @IsAffineHom) q₂.flip inferInstance)
  have eH₂ := LBIso.trans (isLB_lbPow P.isLB N) (pull_isLB hH₁ _) (pull_isLB hH₂ _) eH₁
    (lbIso_pull_pull hH₁ φ₂ e₂.symm)
  have hfr₂ : ∀ x : Ω, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₁ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩

  have := isFractionRing_of_forall_div hfr₂
  have := isNoetherianRing_of_fg hR₂
  have := hab.proper
  obtain ⟨d₀, hd₀, Hrig⟩ := GlobalTheory.T.exists_rigidification_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.rigid
  obtain ⟨d₁, hd₁, Hsym⟩ := GlobalTheory.T.exists_symmetric_spread_out_lineBundle_abelian_scheme R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ P.sym
  obtain ⟨d₂, hd₂, Hk⟩ := GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation hL.globalFns R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂
    ((ProjSpace.isProjBy_iff_isProjOver G.hom).2 (aH₂.isProjOver G.hom)) P.ktriv
  obtain ⟨d₃, hd₃, Hs⟩ := GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre R₂ Ω G P.A φ₂ L₂ P.L hab hG hL₂ P.isLB eL₂ w wd w₀ wd₀ hw hwd hw₀ hwd₀ hww hS₁ hS₂
  obtain ⟨d₄, hd₄, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω G P.A φ₂ inferInstance hG _ M y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω) (spMap (algebraMap Ω _)) c c' ?_
    rw [← comp_linComb, ← comp_linComb, h]
  obtain ⟨d₅, hd₅, Ha⟩ := exists_isAmpleLB G.hom hG.1 hL₂ hH₂ P.isLB aH₂ hN eL₂ eH₂
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, φ₃, e₃, p₃⟩ := exists_shrink hR₂ ![d₀, d₁, d₂, d₃, d₄, d₅]
    (by intro i; fin_cases i <;> assumption) hG.1
  have es₃ : spMap (algebraMap R₃ Ω) ≫ spMap g₃ = spMap (algebraMap R₂ Ω) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := isGrpPullback_pullback G (spMap g₃)
  have hL₃ := pull_isLB hL₂ (pullback.fst G.hom (spMap g₃))
  have hab₃ := PolPull.isAbelianScheme_of_isGrpPullback hab q₃
  have := hab₃.comm
  have := hab₃.proper
  let P' : PolAV (Sp R₃) :=
    { A := (Over.pullback (spMap g₃)).obj G
      isAb := hab₃
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback q₃.1 hsm₂
      L := L₂.pull (pullback.fst G.hom (spMap g₃))
      isLB := hL₃
      rigid := Hrig R₃ g₃ (u₃ 0) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      sym := Hsym R₃ g₃ (u₃ 1) _ _ _ q₃ hL₃ (lbIso_refl hL₃)
      ample := (relAmple_iff_isAmpleLB_of_isAffine _ hL₃).2 (Ha R₃ g₃ (u₃ 5) _ _ _ q₃.1)
      ktriv := Hk R₃ g₃ (u₃ 2) _ _ _ q₃ hL₃ (lbIso_refl hL₃) }
  have hG₃ : IsGrpPullback P.A P'.A (spMap (algebraMap R₃ Ω)) φ₃ :=
    IsGrpPullback.cancel q₃ (hG.congr es₃.symm e₃.symm) p₃.w
  have eL₃ : LBIso P.L (P'.L.pull φ₃) := LBIso.trans P.isLB (pull_isLB hL₂ _) (pull_isLB hL₃ _) eL₂
    (lbIso_pull_pull hL₂ φ₃ e₃.symm)
  let y' : Fin (2 * P.g) → (baseOver (Sp R₃) ⟶ P'.A) := fun i =>
    Over.homMk (q₃.1.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.1.lift_fst _ _ _
  have hy₃ : ∀ (i₀ : Fin (2 * P.g)) (i : Fin (2 * P'.g)), (i₀ : ℕ) = i →
      (lev.pt i₀).left ≫ φ₃ = spMap (algebraMap R₃ Ω) ≫ (y' i).left := by
    intro i₀ i hi
    obtain rfl : i₀ = i := Fin.ext hi
    refine q₃.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hy', e₃, hy, reassoc_of% es₃]
    · rw [Category.assoc, Category.assoc, hG₃.1.w, Over.w_assoc, Over.w]
      simp
  have hfr₃ : ∀ x : Ω, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := isFractionRing_of_forall_div hfr₃
  have := isNoetherianRing_of_fg hR₃
  obtain ⟨lev', hlev⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep hL R₃ Ω P' P φ₃ hG₃ eL₃ rfl M (Units.map (algebraMap o R₃).toMonoidHom ze) _
    (by simpa using hM.map (algebraMap o R₃)) rfl lev y' hy₃ (Hi R₃ g₃ (u₃ 4) _ _ y' q₃ hy')
  refine ⟨R₃, P', φ₃, lev', le₁.trans (le₂.trans le₃), hR₃, rfl, Hs R₃ g₃ (u₃ 3) _ _ _ q₃ hL₃ (lbIso_refl hL₃),
    hG₃, eL₃, ?_⟩
  rw [hlev]
  exact hy₃

end GlobalTheory.GenSpread
end
end

