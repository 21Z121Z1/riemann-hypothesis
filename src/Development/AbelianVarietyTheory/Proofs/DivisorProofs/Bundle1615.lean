import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingAutFixingSmallFieldFixesDeltaValues
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.SeriesTie
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.JoinChr (IsPlIdem locE)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DeltaFixed

theorem aut_fixes_delta_values : ∀ {D : D7} (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (χ : HChar D.host.E),
    ChrEq (ρ.B i j b).de.chi χ → χ.ValuesIn 0 (embLL0 D) → ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (embLL0 D y) = embLL0 D y) →
    ∀ σ, τ (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  intro D ρ hρ i j b χ hχ hval τ hτ σ
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  set f : D.ntw.O0 i →+* ℂ := (ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hf

  have hker : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := by
    cases b
    · have e : (ψ.ker : Set (G D.host.E D.nd.Om)) = ((D.ntw.delta i).ker : Set _) := by
        ext g
        simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
      rw [e]
      exact D.ntw.delta_open i
    · simpa [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt] using D.ntw.delta_open i

  have hram : ∀ v, v ∉ D.ntw.pD i → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ g ∈ Ine (F := D.host.E) A, ψ g = 1 := by
    intro v hv A hA g hg
    have h1 : D.ntw.delta i g = 1 := by
      by_contra h
      exact hv ((D.ntw.delta_ram i v A hA).1 ⟨g, hg, h⟩)
    cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h1]

  haveI : Finite (G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpow : ∀ g, ψ g ^ ψ.ker.index = 1 := fun g => by
    rw [← map_pow]
    exact (MonoidHom.mem_ker).1 (Subgroup.pow_index_mem _ g)

  have hchi : ChrEq (charOf ρ.rc f ψ) χ := by
    have := hχ
    rw [hρ.delta i j b] at this
    exact this

  let r' : G D.host.E D.nd.Om →* ℂˣ := (Units.map f.toMonoidHom).comp ψ
  let r : G D.host.E D.nd.Om →* ℂˣ := (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom).comp ψ
  have hr' : Continuous r' := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map f.toMonoidHom)
  have hr : Continuous r := GlobalTheory.DeltaGal.continuous_comp_of_isOpen_ker ψ hker (Units.map ((τ : ℂ →+* ℂ).comp f).toMonoidHom)
  have hart : IsGlobalArtin ρ.rc.art := hρ.rc.artin
  obtain ⟨_, _, _, _, hidem, _⟩ := GlobalTheory.EtaProduct.exists_ev D
  have key : r = r' := by
    refine GlobalTheory.GalChar.eq_of_frob hart hr hr' ?_
    have h1 := GlobalTheory.GalChar.unr_ae χ
    have h2 : ∀ᶠ v in Filter.cofinite, v ∉ D.ntw.pD i :=
      Filter.eventually_cofinite.2 (by simpa using (D.ntw.pD i).finite_toSet)
    filter_upwards [h1, h2] with v hunr hv A hA s hs

    obtain ⟨x0, hx0, hx0a⟩ := (hart.frob v A hA (toAb D.host.E D.nd.Om s⁻¹)).2 ⟨s, hs, rfl⟩

    set k := unif v
    have hk : IsUnifAt v (atFin v k) := unif_spec v
    have hu : IsUnitAt v (x0 * (atFin v k)⁻¹) := by
      unfold IsUnitAt
      unfold IsUnifAt at hx0 hk
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx0, hk]
      exact mul_inv_cancel₀ (by simp)
    obtain ⟨t, ht, hta⟩ := GlobalTheory.GalChar.exists_ine hart hA hu
    have hψt : ψ t = 1 := hram v hv A hA t ht

    obtain ⟨e, he⟩ := hidem v
    let xe : (Formalism.L2.Theta.AE D)ˣ := (Formalism.L2.JoinChr.isUnit_locE he.1 k).unit
    have hxe : ρ.rc.sym xe = toAb D.host.E D.nd.Om (t⁻¹ * s⁻¹) := by
      have e1 : Units.map ρ.rc.κ.toMonoidHom xe = Neutral.B1.localIdele D.host.E v (atFin v k) := by
        apply Units.ext
        exact hρ.rc.loc v e he k
      have e2 : atFin v k = (x0 * (atFin v k)⁻¹)⁻¹ * x0 := by group
      change ρ.rc.art (Units.map ρ.rc.κ.toMonoidHom xe) = _
      rw [e1, e2, map_mul, map_mul, map_inv, map_inv, hta, hx0a, ← map_inv, ← map_mul]
    have hc := charOf_eq ρ.rc f hker hxe hn (hpow _)
    have hc2 := hchi.2 v e he k xe rfl
    have hloc : χ.locK v k = χ.val v := χ.val_eq hunr _ hk
    obtain ⟨y, hy⟩ := hval v hunr
    have hy' : embLL0 D y = ((χ.val v : ℂˣ) : ℂ) := by
      rw [hy, HChar.valTw]
      simp
    have hfs : f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y⁻¹ := by
      have h3 : f ((ψ (t⁻¹ * s⁻¹) : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = embLL0 D y := by
        rw [← hc, hc2, hloc, hy']
      rw [map_mul, map_inv, map_inv, hψt, inv_one, one_mul, map_units_inv] at h3
      rw [map_inv₀, ← h3, inv_inv]
    apply Units.ext
    show τ (f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) = f ((ψ s : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)
    rw [hfs]
    exact hτ _
  have := congrArg (fun φ : G D.host.E D.nd.Om →* ℂˣ => ((φ σ : ℂˣ) : ℂ)) key
  exact this

end GlobalTheory.DeltaFixed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LineConst

open Polynomial

variable (k : Type) [Field k]

def scaleHom (R : Type) [CommRing R] [Algebra k R] (u : R) : Polynomial k →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap k R)) (Polynomial.C u * Polynomial.X)

theorem scaleHom_algebraMap (R : Type) [CommRing R] [Algebra k R] (u : R) :
    (scaleHom k R u).comp (algebraMap k (Polynomial k)) = algebraMap k (Polynomial R) := by
  ext a
  simp [scaleHom, Polynomial.algebraMap_apply]

def lineOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Polynomial R)))

variable {k}

def scaled (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) :
    lineOver k R ⟶ B :=
  Over.homMk (spMap (scaleHom k R u) ≫ f) (by
    change spMap (scaleHom k R u) ≫ f ≫ B.hom = spMap (algebraMap k (Polynomial R))
    rw [hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_algebraMap])

def famMap (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) : Sp (Polynomial R) ⟶ B.left :=
  (scaled B f hf R u * (scaled B f hf R 1)⁻¹).left

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

theorem scaleHom_comp_map {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') (u : R) :
    (Polynomial.mapRingHom (φ : R →+* R')).comp (scaleHom k R u) = scaleHom k R' (φ u) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [scaleHom]
  · simp [scaleHom]

def lineMap {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') : lineOver k R' ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.mapRingHom (φ : R →+* R'))) (by
    change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (algebraMap k (Polynomial R)) =
      spMap (algebraMap k (Polynomial R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a; simp [Polynomial.algebraMap_apply])

theorem lineMap_scaled {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    lineMap φ ≫ scaled B f hf R u = scaled B f hf R' (φ u) := by
  ext1
  change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f =
    spMap (scaleHom k R' (φ u)) ≫ f
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]

theorem famMap_base {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ famMap B f hf R u = famMap B f hf R' (φ u) := by
  have h := congrArg CommaMorphism.left
    (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) =
      scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])
  exact h

theorem famMap_one {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] :
    famMap B f hf R 1 = spMap (algebraMap k (Polynomial R)) ≫ (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left := by
  unfold famMap
  rw [mul_inv_cancel, Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

def linePt {k : Type} [Field k] (a : k) : 𝟙_ (Over (Sp k)) ⟶ lineOver k k :=
  Over.homMk (spMap (Polynomial.evalRingHom a)) (by
    change spMap (Polynomial.evalRingHom a) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

theorem linePt_scaled_left {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (a c : k) :
    (linePt a ≫ scaled B f hf k c).left = spMap (Polynomial.evalRingHom (c * a)) ≫ f := by
  change spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Polynomial.ringHom_ext
  · intro z; simp [scaleHom]
  · simp [scaleHom]

theorem scale_inv_of_famMap {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (c : k)
    (h : famMap B f hf k c = spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c)
    (a : k) : spMap (Polynomial.evalRingHom (c * a)) ≫ f = spMap (Polynomial.evalRingHom a) ≫ f := by
  have hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
    intro b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c =
      spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c := by
    conv_lhs => rw [h]
    rw [← Category.assoc, hpt, Category.id_comp]
  have hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹ := by
    intro b; rw [MonObj.comp_mul, GrpObj.comp_inv]
  have h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1 := by
    ext1
    rw [linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]
  have hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) := by
    ext1
    exact hleft
  rw [hq, hq, h0, mul_inv_cancel] at hall
  have hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1 :=
    mul_inv_eq_one.mp hall
  have h2 := congrArg CommaMorphism.left hall'
  have e1 := linePt_scaled_left B f hf a c
  have e2 := linePt_scaled_left B f hf a 1
  rw [_root_.one_mul] at e2
  rw [← e1, ← e2]
  exact h2

end GlobalTheory.LineConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
section
open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsOfPulledBackLineBundlesOnFramesStatement
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_of_pulled_back_line_bundles_on_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  first | exact @GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk | exact GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk | (intros; apply GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepClosureFiniteExtPowMemRange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem sepClosure_finiteExt_pow_mem_range :
    ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L]
      [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω']
      [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω') (y : Ω'),
      ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m := by
  intro K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable L Ω' := IsSepClosure.separable
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'
  set S := separableClosure K Ω'
  set q := ringExpChar K
  haveI : ExpChar Ω' q := expChar_of_injective_algebraMap (algebraMap K Ω').injective q
  haveI : ExpChar S q := expChar_of_injective_algebraMap (algebraMap K S).injective q
  obtain ⟨n, ⟨z, hz⟩⟩ := (isPurelyInseparable_iff_pow_mem S q).1 inferInstance y

  have hzsep : IsSeparable K (z : Ω') := mem_separableClosure_iff.1 z.2
  have hsplit : ((minpoly K (z : Ω')).map (algebraMap K Ω)).Splits :=
    IsSepClosed.splits_codomain _ hzsep
  have hroot : (((minpoly K (z : Ω')).map (algebraMap K Ω)).map (j : Ω →+* Ω')).IsRoot (z : Ω') := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
    simp [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  obtain ⟨x, hx⟩ := hsplit.mem_range_of_isRoot
    (Polynomial.map_ne_zero (minpoly.ne_zero hzsep.isIntegral)) hroot
  refine ⟨q ^ n, x, pow_pos (expChar_pos K q) n, ?_, fun a b => sub_pow_expChar_pow a b n⟩
  rw [← hz]
  simpa using hx.symm

end GlobalTheory.Published.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

theorem smooth_of_relSnc :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X)
      (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  intro R _ X f d s L σ h
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose C hC using h.chart
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) (fun x => (C x).U) ?_
    fun x => ?_
  · rw [← top_le_iff]
    rintro x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  · exact GlobalTheory.ChartSmooth.smooth_of_etale f (C x).affine (C x).t (C x).etale

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

theorem tate_lev_surj : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  intro l _ M _ hroot n x hx
  choose r hr using hroot
  have key : ∀ (m : ℕ) (y : M), (r^[m] y) ^ l ^ m = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, hr]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun m => (r^[m] x) ^ l ^ n) fun m => ⟨?_, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, key, hx]
  · rw [← pow_mul, mul_comm, pow_mul, Function.iterate_succ_apply', hr]
  · rw [GlobalTheory.HTLat.Tate.lev_mk, key]

end GlobalTheory.Published
end

