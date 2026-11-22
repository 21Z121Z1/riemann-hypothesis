import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionFiniteFlatIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogeny

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem descend_to_theta_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K₀ K _ _ _ β e s t v hs hsh hpr hth => ?_⟩
  subst hs

  have hdense : VeryDense (objPrimes b Mat κ β v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    have hker : RingHom.ker e = q := by
      rw [hq0]; exact (RingHom.injective_iff_ker_eq_bot e).mp e.injective
    exact ⟨q, ⟨K, inferInstance, inferInstance, e, t, hker, hsh, hth⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, hth₀, hu⟩ := hj₀ j hj o b K₀ β v hdense

  have hmap : TMap t t₀ (spMap e) := hu K e t hsh hth
  obtain ⟨-, -, hdesc⟩ := GlobalTheory.shape_prim_pull_and_descend o g ((n ^ j) ^ 2) J b Mat κ w w' _ _ _ _ _ t₀ t hmap
  obtain ⟨hS, hP⟩ := hdesc K₀ rfl inferInstance inferInstance
  exact ⟨t₀, hmap, hS hsh, hP inferInstance hpr, hth₀⟩

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.ega_holds : GlobalTheory.LN.Ega :=
  GlobalTheory.T.extension_of_abelian_schemes GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)), admitted l 𝔓 p → (∀ j, σ j ^ p ^ 2 = 1) → ∃ V : S.Opens, IsClosed (V : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Set.range x ⊆ V ↔ (Function.Injective fun j => x ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ o.t.G), (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ σ j) ∧ o.t.HeckeKer (Over.mk x) D 𝔓 p i C := by
  first | exact @GlobalTheory.exists_clopen_heckeKer_iff | exact GlobalTheory.exists_clopen_heckeKer_iff | (intros; apply GlobalTheory.exists_clopen_heckeKer_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_tObj_near | exact GlobalTheory.ZM.NearBuild.exists_tObj_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_tObj_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionPairRepresentativeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_pair_representative : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y : P.D.toPre.X, ∃ (N : Over W.toScheme) (p₀ : QkPtW P.D.toPre W ψW k N), PairRep ψW k y N p₀ := by
  first | exact @GlobalTheory.PairScheme.pairRep_exists | exact GlobalTheory.PairScheme.pairRep_exists | (intros; apply GlobalTheory.PairScheme.pairRep_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_image_generic : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  first | exact @GlobalTheory.FinitePartGeneric.main | exact GlobalTheory.FinitePartGeneric.main | (intros; apply GlobalTheory.FinitePartGeneric.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_descendedBundle_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  first | exact @GlobalTheory.relAmple_kTriv_of_descent_family | exact GlobalTheory.relAmple_kTriv_of_descent_family | (intros; apply GlobalTheory.relAmple_kTriv_of_descent_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type}
    (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

theorem TObj.HasTh.unit_smul {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (H : t.HasTh x v) {c : R} (hc : IsUnit c) :
    t.HasTh x (c • v) := by
  have h := isThetaPt_unit_mul t.pol N' (T := Over.mk x) _ _ _
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) H
  unfold TObj.HasTh
  convert h using 2 with a
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem tmap_of_hasTh_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b em t t' v c hc hs hs' hv hv' => ?_⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  have hv'' : t'.HasTh (𝟙 _) v := by
    have h := hv'.unit_smul (IsUnit.mk0 c⁻¹ (inv_ne_zero hc))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have key : ∀ s : Sp ℂ ⟶ Sp o, s = spMap (RingHom.id ℂ) ≫ spMap em →
      ∀ t t' : TObj g ((n ^ j) ^ 2) J b s, t.Shape Mat κ → t'.Shape Mat κ →
        t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
    intro s hs t t' h1 h1' h2 h2'
    subst hs
    have hvd : VeryDense (objPrimes b Mat κ em v) := by
      intro q f hq hf
      have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
      subst hq0
      refine ⟨⊥, ⟨ℂ, inferInstance, inferInstance, RingHom.id ℂ, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
      exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id ℂ).injective
    obtain ⟨t₀, -, h₀⟩ := H j hj o b ℂ em v hvd
    have m := h₀ ℂ (RingHom.id ℂ) t h1 h2
    have m' := h₀ ℂ (RingHom.id ℂ) t' h1' h2'
    refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
    rwa [Category.id_comp]
  exact key _ (by rw [hid, Category.id_comp]) t t' hs hs' hv hv''

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionRepresentableFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.TorsOverOpen

open GlobalTheory.TorsionRepresent GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (k : ℕ)

theorem isPullback_incl :
    IsPullback (incl G k).left (torsScheme G k).hom ((𝟙 G : G ⟶ G) ^ k).left η[G].left := by
  have h := (IsPullback.of_hasPullback ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).left = (torsScheme G k).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem pullback_map_pow :
    (Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k) = (𝟙 ((Over.pullback f).obj G)) ^ k := by
  rw [← (Over.pullback f).map_id]
  exact map_pow (Over.pullback f).homMonoidHom _ _

theorem prop_snd (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    (h : P ((𝟙 ((Over.pullback f).obj G)) ^ k : (Over.pullback f).obj G ⟶ _).left) :
    P (pullback.snd (torsScheme G k).hom f) := by
  rw [← pullback_map_pow] at h
  have hη : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  have hι : (incl G k).left ≫ G.hom = (torsScheme G k).hom := Over.w _
  have hm : ((𝟙 G : G ⟶ G) ^ k).left ≫ G.hom = G.hom := Over.w _
  let s : S' ⟶ pullback G.hom f := pullback.lift (f ≫ η[G].left) (𝟙 _) (by
    rw [Category.assoc, hη]; simp)
  let a : pullback (torsScheme G k).hom f ⟶ pullback G.hom f :=
    pullback.lift (pullback.fst _ _ ≫ (incl G k).left) (pullback.snd _ _) (by
      rw [Category.assoc, hι, pullback.condition])
  let m : pullback G.hom f ⟶ pullback G.hom f := ((Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k)).left
  have m1 : m ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ ((𝟙 G : G ⟶ G) ^ k).left := pullback.lift_fst _ _ _
  have m2 : m ≫ pullback.snd G.hom f = pullback.snd G.hom f := pullback.lift_snd _ _ _
  have a1 : a ≫ pullback.fst G.hom f = pullback.fst _ _ ≫ (incl G k).left := pullback.lift_fst _ _ _
  have a2 : a ≫ pullback.snd G.hom f = pullback.snd _ _ := pullback.lift_snd _ _ _
  have s1 : s ≫ pullback.fst G.hom f = f ≫ η[G].left := pullback.lift_fst _ _ _
  have s2 : s ≫ pullback.snd G.hom f = 𝟙 _ := pullback.lift_snd _ _ _
  have hr : IsPullback (pullback.fst G.hom f) m ((𝟙 G : G ⟶ G) ^ k).left (pullback.fst G.hom f) := by
    refine IsPullback.of_bot ?_ m1.symm (IsPullback.of_hasPullback G.hom f)
    rw [hm, m2]
    exact IsPullback.of_hasPullback G.hom f
  have ho := (IsPullback.of_hasPullback (torsScheme G k).hom f).paste_horiz (isPullback_incl G k)
  have hl : IsPullback a (pullback.snd (torsScheme G k).hom f) m s := by
    refine IsPullback.of_right ?_ ?_ hr
    · rw [a1, s1]
      exact ho
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, m1, s1, ← Category.assoc, a1]
        exact ho.w
      · rw [Category.assoc, Category.assoc, m2, s2, a2, Category.comp_id]
  exact MorphismProperty.of_isPullback hl h

noncomputable def toTors : (Over.map f).obj ((Over.pullback f).obj (torsScheme G k)) ⟶ torsScheme G k :=
  Over.homMk (pullback.fst (torsScheme G k).hom f) pullback.condition

theorem univ (T : Over S') (x : (Over.map f).obj T ⟶ G) (hx : x ^ k = 1) :
    ∃! h : T ⟶ (Over.pullback f).obj (torsScheme G k), (Over.map f).map h ≫ toTors f G k ≫ incl G k = x := by
  obtain ⟨l, hl⟩ := exists_lift G k x hx
  have hw : l.left ≫ (torsScheme G k).hom = T.hom ≫ f := Over.w l
  refine ⟨Over.homMk (pullback.lift l.left T.hom hw) (pullback.lift_snd _ _ _), ?_, ?_⟩
  · beta_reduce
    rw [← hl, ← Category.assoc]
    congr 1
    ext1
    exact pullback.lift_fst _ _ _
  · intro h hh
    rw [← hl, ← Category.assoc, cancel_mono] at hh
    ext1
    apply pullback.hom_ext
    · exact (congrArg CommaMorphism.left hh).trans (pullback.lift_fst _ _ _).symm
    · exact (Over.w h).trans (pullback.lift_snd _ _ _).symm

end

theorem isAbelianScheme_restrict {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (W : S.Opens)
    (hp : IsProper (G.hom ∣_ W)) : IsAbelianScheme ((Over.pullback W.ι).obj G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hr := isPullback_morphismRestrict G.hom W
  refine ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom W.ι)), ?_,
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom W.ι))⟩
  change IsProper (pullback.snd G.hom W.ι)
  rw [← hr.flip.isoPullback_inv_snd]
  infer_instance

theorem torsion_finFlatEt : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => IsAbelianScheme ((Over.pullback W.ι).obj t.G) ∧ TorsFiniteFlat t.G W k ∧ ∃ (Z : Over W.toScheme) (n : overW W Z ⟶ t.G), FinFlatEt Z ∧ n ^ k = 1 ∧ ∀ (T : Over W.toScheme) (x : overW W T ⟶ t.G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ hp ψW k hk
  have hA := isAbelianScheme_restrict t.G t.semi W hp
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing (CommRingCat.of R) := hR.1
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme _ _ hA k hk
  have hfin := prop_snd W.ι t.G k @IsFinite h₁
  have hflat := prop_snd W.ι t.G k @Flat h₂
  have hs := t.semi.smooth
  have hsK : Smooth ((Over.pullback (jK R)).obj t.G).hom := inferInstanceAs (Smooth (pullback.snd t.G.hom (jK R)))
  have hu : IsUnit (k : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.2 (by omega) : (k : FractionRing R) ≠ 0).isUnit
    simpa using this.map (Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom
  have het : Etale (pullback.snd (torsScheme t.G k).hom (jK R)) :=
    prop_snd (jK R) t.G k @Etale (GlobalTheory.GrpTangent.etale_id_pow _ hu)
  have hn : (toTors W.ι t.G k ≫ incl t.G k) ^ k = 1 := comp_incl_pow t.G k _
  refine ⟨hA, ⟨_, _, hfin, hflat, hn, univ W.ι t.G k⟩, _, _, ⟨hfin, hflat, ?_⟩, hn, univ W.ι t.G k⟩
  have ho : IsOpenImmersion ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _
      (inferInstanceAs (IsOpenImmersion (pullback.fst (torsScheme t.G k).hom W.ι)))
  have e : ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left ≫ pullback.snd (torsScheme t.G k).hom (jK R) =
      pullback.snd (overW W ((Over.pullback W.ι).obj (torsScheme t.G k))).hom (jK R) :=
    Over.w ((Over.pullback (jK R)).map (toTors W.ι t.G k))
  rw [← e]
  infer_instance

end GlobalTheory.TorsOverOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) (N : LB (B ⊗ B).left) (n : ℕ), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → 0 < n → IsUnit (n : Γ(S, ⊤)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ^ n = 1) → (∃ t : (N.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (N.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → (∃ t : (N.pull (ψ ⊗ₘ ψ).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | exact GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny | (intros; apply GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny <;> assumption)
end

