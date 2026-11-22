import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChowRigid

open GlobalTheory.Spread

theorem factor_finite (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, _root_.IsIntegral K b → b ∈ i.range)
    (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T) (ht : t ≫ p = spMap (algebraMap K B)) :
    ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u :=
  GlobalTheory.T.exists_factor_through_integral_subalgebra K B E i hι hint T p t ht

theorem torsion_factor (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : 0 < n) (B E : Type) [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, IsIntegral K b → b ∈ i.range)
    (T : Over (Sp K)) (y : T ⟶ A) (hy : y ^ n = 1) (t : Sp B ⟶ T.left)
    (ht : t ≫ T.hom = spMap (algebraMap K B)) :
    ∃ x : Over.mk (spMap (algebraMap K E)) ⟶ A, x ^ n = 1 ∧ t ≫ y.left = spMap i.toRingHom ≫ x.left := by
  have := hA.comm; have := hA.smooth; have := hA.proper
  have hu : IsUnit ((n : Γ(Sp K, ⊤))) := by
    have : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have := GlobalTheory.GrpTangent.isFinite_torsion A hu
  obtain ⟨hη1, huniv⟩ := GlobalTheory.LamF.torsion_universal A n
  obtain ⟨w, hw⟩ := huniv T y hy
  obtain ⟨u, hu1, hu2⟩ := factor_finite K B E i hι hint (torsion A n).left (torsion A n).hom (t ≫ w.left)
    (by rw [Category.assoc, Over.w w, ht])
  refine ⟨Over.homMk u hu1 ≫ torsion.ι A n, ?_, ?_⟩
  · rw [← comp_pow, hη1, comp_one]
  · rw [← hw, Over.comp_left, ← Category.assoc, hu2, Over.comp_left, Category.assoc]
    rfl

theorem compare (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (S : Type) [CommRing S] [Algebra K S]
    (i : algebraicClosure K Ω →ₐ[K] S) (j : S →ₐ[K] Ω) (ρ : S →ₐ[K] algebraicClosure K Ω)
    (hj : Function.Injective j) (hji : ∀ x, j (i x) = x) (hρi : ∀ x, ρ (i x) = x)
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (gS : (Over.pullback (spMap (algebraMap K S))).obj A ⟶ (Over.pullback (spMap (algebraMap K S))).obj A')
    [IsMonHom gS]
    (g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶
      (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A')
    [IsMonHom g] (hg : g.left ≫ pullback.fst _ _ = bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _) :
    bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ =
      bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _ := by
  have hι : Function.Injective i := fun a b h => Subtype.ext (by rw [← hji a, ← hji b, h])
  have hint : ∀ s : S, _root_.IsIntegral K s → s ∈ i.range := fun s hs => by
    have h1 : j s ∈ (algebraicClosure K Ω) := mem_algebraicClosure_iff'.mpr (hs.map j)
    exact ⟨⟨j s, h1⟩, hj (hji _)⟩
  have hintΩ : ∀ b : Ω, _root_.IsIntegral K b → b ∈ (algebraicClosure K Ω).val.range := fun b hb =>
    ⟨⟨b, mem_algebraicClosure_iff'.mpr hb⟩, rfl⟩
  have hLinj : Function.Injective (algebraicClosure K Ω).val := Subtype.val_injective
  obtain ⟨h, hh, hhe⟩ := GlobalTheory.HomDescent.exists_specialise g (algebraicClosure K Ω).val
  obtain ⟨f, hf, hfe⟩ := GlobalTheory.HomDescent.exists_specialise gS j
  have semi := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A hA)
  have semi' := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A' hA')
  have e : f = h := by
    have := hf; have := hh
    refine GlobalTheory.HomExtNormal.hom_eq_of_torsion semi semi' f h fun y n hn hy => ?_

    let P := pushHom (isGrpPullback_pullback A (spMap (algebraMap K Ω))) (𝟙_ (Over (Sp Ω)))
    have hPn : P y ^ n = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨x, hxn, hx⟩ := torsion_factor K A hA n hn Ω (algebraicClosure K Ω) (algebraicClosure K Ω).val hLinj hintΩ _ (P y) hPn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hx' : y.left ≫ pullback.fst _ _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ x.left := by
      rw [← hx, Category.id_comp]; rfl
    have hys : y.left ≫ pullback.snd _ _ = 𝟙 _ := Over.w y
    have hxw : x.left ≫ A.hom = spMap (algebraMap K (algebraicClosure K Ω)) := Over.w x
    have eji : spMap j.toRingHom ≫ spMap i.toRingHom = spMap (algebraicClosure K Ω).val.toRingHom := by
      rw [GlobalTheory.HomDescent.spMap_comp]; congr 1; exact RingHom.ext hji
    have eρi : spMap ρ.toRingHom ≫ spMap i.toRingHom = 𝟙 _ := by
      rw [GlobalTheory.HomDescent.spMap_comp, show ρ.toRingHom.comp i.toRingHom = RingHom.id _ from RingHom.ext hρi]
      exact Spec.map_id _
    let xS : Sp S ⟶ pullback A.hom (spMap (algebraMap K S)) :=
      pullback.lift (spMap i.toRingHom ≫ x.left) (𝟙 _) (by
        rw [Category.assoc, hxw, Category.id_comp, spMap_algHom_comp])
    let xL : Sp (algebraicClosure K Ω) ⟶ pullback A.hom (spMap (algebraMap K (algebraicClosure K Ω))) :=
      pullback.lift x.left (𝟙 _) (by rw [hxw, Category.id_comp])
    have c1 : y.left ≫ bcMap A.hom j = spMap j.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst, ← Category.assoc, eji]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c2 : y.left ≫ bcMap A.hom (algebraicClosure K Ω).val = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c3 : xL ≫ bcMap A.hom ρ = spMap ρ.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
          eρi, Category.id_comp]
      · rw [Category.assoc, bcMap_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]

    let xS' : 𝟙_ (Over (Sp S)) ⟶ (Over.pullback (spMap (algebraMap K S))).obj A :=
      Over.homMk xS (pullback.lift_snd _ _ _)
    let PS := pushHom (isGrpPullback_pullback A (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hPSinj : Function.Injective PS := fun a b e =>
      Over.OverMorphism.ext ((isGrpPullback_pullback A (spMap (algebraMap K S))).1.hom_ext
        (congrArg (fun z => z.left) e) (by rw [Over.w a, Over.w b]))
    let q : Over.mk ((𝟙_ (Over (Sp S))).hom ≫ spMap (algebraMap K S)) ⟶ Over.mk (spMap (algebraMap K (algebraicClosure K Ω))) :=
      Over.homMk (spMap i.toRingHom) (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]; exact spMap_algHom_comp i)
    have hPS : PS xS' = q ≫ x := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have hxSn : xS' ^ n = 1 := hPSinj (by rw [map_pow, hPS, ← comp_pow, hxn, comp_one, map_one])
    let P' := pushHom (isGrpPullback_pullback A' (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hzn : P' (xS' ≫ gS) ^ n = 1 := by rw [← map_pow, ← pow_comp, hxSn, one_comp, map_one]
    obtain ⟨c, -, hc⟩ := torsion_factor K A' hA' n hn S (algebraicClosure K Ω) i hι hint _ (P' (xS' ≫ gS)) hzn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hz : xS ≫ gS.left ≫ pullback.fst _ _ = spMap i.toRingHom ≫ c.left := by
      rw [← hc, Category.id_comp]; rfl
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hfe, hhe]
      calc y.left ≫ bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _
          = spMap j.toRingHom ≫ xS ≫ gS.left ≫ pullback.fst _ _ := by rw [reassoc_of% c1]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ c.left := by rw [hz, reassoc_of% eji]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ spMap ρ.toRingHom ≫ spMap i.toRingHom ≫ c.left := by
          rw [reassoc_of% eρi]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL ≫ bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _ := by
          rw [reassoc_of% c3, hz]
        _ = y.left ≫ bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ := by
          rw [hg, reassoc_of% c2]
    · have e1 : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
      have e2 : h.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w h
      simp only [Over.comp_left, Category.assoc]
      rw [e1, e2]
  rw [← hhe, ← hfe, e]

theorem chow_rigidity : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A', IsMonHom f → ∃ g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A', IsMonHom g ∧ GlobalTheory.Spread.bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ _ _ A A' _ _ hA hA' f hf
  have := hA.proper; have := hA.smooth; have := hA'.proper; have := hA'.smooth
  have := hf
  obtain ⟨R, gR, ⟨s, hs⟩, hgR, hR⟩ := GlobalTheory.HomDescent.exists_fg_isMonHom f
  have := hgR
  haveI : IsAlgClosed (algebraicClosure K Ω) := IsAlgClosure.isAlgClosed K
  let S : Subalgebra (algebraicClosure K Ω) Ω := Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)
  haveI : Algebra.FiniteType (algebraicClosure K Ω) S := ⟨(Subalgebra.fg_top S).mpr ⟨s, rfl⟩⟩
  obtain ⟨ρ₀⟩ := GlobalTheory.Ex.ThetaDescent.nonempty_algHom (algebraicClosure K Ω) S
  have hRS : ∀ r ∈ R, r ∈ S := fun r hr => by
    have h1 : Algebra.adjoin K (s : Set Ω) ≤
        (Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)).restrictScalars K :=
      Algebra.adjoin_le Algebra.subset_adjoin
    rw [← hs] at hr
    exact h1 hr
  let inc : R →ₐ[K] S :=
    { toFun := fun r => ⟨r, hRS r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let i : algebraicClosure K Ω →ₐ[K] S := IsScalarTower.toAlgHom K (algebraicClosure K Ω) S
  let j : S →ₐ[K] Ω := S.val.restrictScalars K
  let ρ : S →ₐ[K] algebraicClosure K Ω := ρ₀.restrictScalars K
  obtain ⟨gS, hgS, hgSe⟩ := GlobalTheory.HomDescent.exists_specialise gR inc
  have := hgS
  obtain ⟨g, hg, hge⟩ := GlobalTheory.HomDescent.exists_specialise gS ρ
  have := hg
  refine ⟨g, hg, ?_⟩
  rw [compare K Ω S i j ρ Subtype.val_injective (fun _ => rfl) (fun x => ρ₀.commutes x) A A' hA hA' gS g hge,
    hgSe, ← hR, bcMap_comp_of_eq_assoc A.hom inc j R.val fun _ => rfl]

end GlobalTheory.ChowRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverLaUnder
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.PlaceBelow

theorem exists_overLa_under : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (i : K →+* K') (q : ℕ) (la' : HeightOneSpectrum (𝓞 K')), q.Prime → ((q : ℕ) : 𝓞 K') ∈ la'.asIdeal → ∀ (T : CDVR) (io' : K' →+* T.Fr) (e' : ℕ), OverLa la' T.V io' e' → ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), ((q : ℕ) : 𝓞 K) ∈ la.asIdeal ∧ OverLa la T.V (io'.comp i) e := by
  intro K K' _ _ _ _ i q la' hq hmem T io' e' h
  letI : Algebra K K' := i.toAlgebra

  set la : HeightOneSpectrum (𝓞 K) := la'.under (𝓞 K) with hla
  set r : ℕ := la.asIdeal.ramificationIdx' la'.asIdeal with hr
  have hr0 : r ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la'.asIdeal la.ne_bot
  refine ⟨la, e' * r, ?_, ?_⟩
  ·
    show ((q : ℕ) : 𝓞 K) ∈ la'.asIdeal.under (𝓞 K)
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  · unfold OverLa vLa at h ⊢
    obtain ⟨he', hv⟩ := h
    refine ⟨Nat.mul_pos he' (Nat.pos_of_ne_zero hr0), fun a => ?_⟩

    have key : la.valuation K a ^ r = la'.valuation K' (algebraMap K K' a) :=
      HeightOneSpectrum.valuation_liesOver K' la la' a
    rw [RingHom.comp_apply, hv, show i a = algebraMap K K' a from rfl, ← key, WithZero.log_pow]
    push_cast
    ring

end GlobalTheory.PlaceBelow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightDecomposition
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.WtMatchArith

theorem add_le_of_gap {n : ℕ} (f : Fin n → ℤ) (hf : ∀ k : ℕ, k + 1 < n → 1 ≤ GlobalTheory.CompHS.gap f k) :
    ∀ (d i : ℕ) (h : i + d < n), f ⟨i + d, h⟩ + d ≤ f ⟨i, by omega⟩ := by
  intro d
  induction d with
  | zero => intro i h; simp
  | succ d ih =>
    intro i h
    have h1 := hf (i + d) (by omega)
    unfold GlobalTheory.CompHS.gap at h1
    rw [dif_pos (by omega)] at h1
    have h2 := ih i (by omega)
    have e : (⟨i + d + 1, by omega⟩ : Fin n) = ⟨i + (d + 1), h⟩ := Fin.ext (by simp; omega)
    rw [e] at h1
    push_cast
    linarith

theorem le_of_gap {n : ℕ} (f : Fin n → ℤ) (hf : ∀ k : ℕ, k + 1 < n → 1 ≤ GlobalTheory.CompHS.gap f k)
    (i j : Fin n) (hij : i ≤ j) : f j ≤ f i := by
  have h := add_le_of_gap f hf ((j : ℕ) - i) i (by omega)
  have e1 : (⟨(i : ℕ) + ((j : ℕ) - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  have e2 : (⟨(i : ℕ), by omega⟩ : Fin n) = i := rfl
  rw [e1, e2] at h
  have : (0 : ℤ) ≤ (((j : ℕ) - i : ℕ) : ℤ) := Int.natCast_nonneg _
  linarith

theorem exists_shift {p q : ℕ} (f : Fin (p + q) → ℤ) (hf : ∀ k : ℕ, k + 1 < p + q → 1 ≤ GlobalTheory.CompHS.gap f k)
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set B : ℤ := ∑ i, |f i| with hB
  have hBi : ∀ i, |f i| ≤ B := fun i => Finset.single_le_sum (f := fun i => |f i|) (fun j _ => abs_nonneg (f j))
    (Finset.mem_univ i)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg (f j)
  by_cases hp : p = 0
  · refine ⟨-(((k : ℤ) + 1) * B + M), fun i hi => by omega, fun i _ => ?_⟩
    have h1 := (abs_le.1 (hBi i)).2
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * B := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (0 : ℤ) ≤ ((k : ℤ) + 1) * B := mul_nonneg (by linarith) hB0
    have h4 : ((k : ℤ) + 1) * B + M ≤ N * (((k : ℤ) + 1) * B + M) := le_mul_of_one_le_left (by linarith) hN'
    linarith
  by_cases hq : q = 0
  · refine ⟨((k : ℤ) + 1) * B + M, fun i _ => ?_, fun i hi => by omega⟩
    have h1 := (abs_le.1 (hBi i)).1
    have h2 : ((k : ℤ) + 1) * (-B) ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (0 : ℤ) ≤ ((k : ℤ) + 1) * B := mul_nonneg (by linarith) hB0
    have h4 : ((k : ℤ) + 1) * B + M ≤ N * (((k : ℤ) + 1) * B + M) := le_mul_of_one_le_left (by linarith) hN'
    linarith
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f ⟨p - 1, by omega⟩ ≤ f i := le_of_gap f hf i _ (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := le_of_gap f hf _ i (by simp [Fin.le_def]; omega)
    have hg := hf (p - 1) (by omega)
    unfold GlobalTheory.CompHS.gap at hg
    rw [dif_pos (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith

end GlobalTheory.WtMatchArith

namespace GlobalTheory.WtMatchArith

open GlobalTheory.AllWt in

theorem exists_dom_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), GapGe 1 la → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hla N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift (la σ) (fun j hj => hla σ j hj) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ => le_of_gap (la σ) (fun j hj => hla σ j hj)
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring

  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open GlobalTheory.ZeroDimSystem in

theorem exists_sec_nonzero_on_finite_of_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  intro k _ _ X _ p L _ n u hu S hS
  classical
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hne : ∀ x ∈ hS.toFinset, vanishAt (k := k) u x ≠ ⊤ := fun x _ h => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact single_notMem_vanishAt (k := k) u hi (h.symm ▸ Submodule.mem_top)
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := Fin n → k)
    (s := hS.toFinset.image (vanishAt (k := k) u)) (by
      rw [Finset.mem_image]
      rintro ⟨x, hx, h⟩
      exact hne x hx h)
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 h
  refine ⟨comb u c, fun x hx => ?_⟩
  by_contra hxc
  exact hc (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))
    ((mem_vanishAt u x c).2 hxc))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtensionOfDenseLocalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extension_of_dense_local : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsReduced Y] (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (O : Y.Opens), Dense (O : Set Y) → ∀ (m : H0 p B O), (∀ y : Y, y ∉ O → ∃ (W : Y.Opens) (i : B.ι) (hi : W ≤ B.U i) (b : Γ(Y, W)), y ∈ W ∧ (∀ y' (h : y' ∈ W) (h' : y' ∈ O), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∉ O → ger y' h b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y')) → ∃ s : H0 p B ⊤, H0.restr le_top s = m ∧ ∀ y : Y, y ∉ O → ∀ (i : B.ι) (hi : y ∈ B.U i), H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  first | exact @GlobalTheory.CompHS.exists_ext_of_dense_local | exact GlobalTheory.CompHS.exists_ext_of_dense_local | (intros; apply GlobalTheory.CompHS.exists_ext_of_dense_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAffineChartBoundaryZeroSetStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  first | exact @GlobalTheory.CompHS.ChartBd.exists_chart_bd | exact GlobalTheory.CompHS.ChartBd.exists_chart_bd | (intros; apply GlobalTheory.CompHS.ChartBd.exists_chart_bd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedRuleOfFlagComponentSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedRule_of_flagComponentSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  first | exact @GlobalTheory.CompHS.exists_suppOn_sec₀_eq | exact GlobalTheory.CompHS.exists_suppOn_sec₀_eq | (intros; apply GlobalTheory.CompHS.exists_suppOn_sec₀_eq <;> assumption)
end

