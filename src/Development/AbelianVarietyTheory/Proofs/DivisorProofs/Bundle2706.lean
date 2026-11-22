import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympRep

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def PtC {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type) [Field k]
    (y : Sp k ⟶ S) (z : kˣ) (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)) : Prop :=
  (∀ a, f a = 1 ↔ ∃ c, a = M • c) ∧ (∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, f a = g) ∧
    ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (f a) (f c) (unitOn (z ^ (2 * omegaStd a c)))

theorem ptC_congr {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type)
    [Field k] (z : kˣ) {y y' : Sp k ⟶ S} (hy : y = y') (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A))
    (f' : (Fin h ⊕ Fin h → ℤ) → (Over.mk y' ⟶ o.A)) (hf : ∀ a, (f a).left = (f' a).left) :
    PtC o h M k y z f ↔ PtC o h M k y' z f' := by
  subst hy
  obtain rfl : f = f' := funext fun a => Over.OverMorphism.ext (hf a)
  rfl

theorem lemCyc : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover

theorem lemKer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric

theorem lemOnto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint

theorem lemWeil : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := GlobalTheory.T.weilPairing_condition_locus_isClopen

theorem exists_sympLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  intro p _ D R _ b N h M hM hcop S t o
  have hM0 : M ≠ 0 := hM.ne'
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (b.unit M hcop).map (GlobalTheory.LevCover.fnOn t)
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, eadd, epow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A M (Fin h ⊕ Fin h → ℤ) o.ab hMS
  haveI := hfin
  haveI := het
  obtain ⟨S', t₀, hS1, hS2, hSu⟩ := lemCyc M S hM hMS
  haveI := hS1
  haveI := hS2
  obtain ⟨hW1, hW2⟩ := GlobalTheory.LevCover.finiteEtale_tensor Z S'
  haveI := hW1
  haveI := hW2
  let W : Over S := Z ⊗ S'
  let e : (Fin h ⊕ Fin h → ℤ) → (W ⟶ o.A) := fun a => fst Z S' ≫ et a
  let τ : W.left ⟶ Sp (cycAway M) := (snd Z S').left ≫ t₀
  have eadd' : ∀ a c, e (a + c) = e a * e c := fun a c => by simp only [e, eadd, MonObj.comp_mul]
  have epow' : ∀ a, e a ^ M = 1 := fun a => by simp only [e]; rw [← MonObj.comp_pow, epow, MonObj.comp_one]
  let C : Prop := M = 1 ∨ 2 * h = Module.finrank ℤ D.La
  obtain ⟨Vs, hVs, HV⟩ := (lemKer S o.A o.ab M h hM hMS W e eadd' epow').and
    ((GlobalTheory.HkClopen.Loc.const (S := W.left) C).and (lemWeil p D R b N h M hM hcop S t o W τ e eadd' epow'))
  let U : W.left.Opens := ⟨Vs, hVs.isOpen⟩
  obtain ⟨Y, i, hY1, hY2, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub U hVs.isClosed
  have memIff : ∀ (T : Over S) (w : T ⟶ W) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left)
      (β : cycAway M →+* k) (z : kˣ), (x ≫ w.left) ≫ τ = spMap β → (z : k) = β (zetaAway M) →
      ((x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs ↔
        PtC o h M k (x ≫ T.hom) z (fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ w ≫ e a)) := by
    intro T w k _ _ x β z hβ hz
    rw [HV k (x ≫ w.left), ← ptC_congr o h M k z (show (x ≫ w.left) ≫ W.hom = x ≫ T.hom by
      rw [Category.assoc, Over.w w]) (fun a => (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a)
      _ (fun a => by simp)]
    have ha : ∀ a c, (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e (a + c) =
        ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) *
          ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e c) := fun a c => by
      rw [eadd', MonObj.comp_mul]
    have hp : ∀ a, ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) ^ M = 1 :=
      fun a => by rw [← MonObj.comp_pow, epow', MonObj.comp_one]
    constructor
    · rintro ⟨hk, hC, hw⟩
      exact ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).2 hC, hw β z hβ hz⟩
    · rintro ⟨hk, ho, hw⟩
      refine ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).1 ho, fun β' z' hβ' hz' => ?_⟩
      obtain rfl : β' = β := GlobalTheory.LevCover.spMap_inj' (hβ'.symm.trans hβ)
      obtain rfl : z' = z := Units.ext (hz'.trans hz.symm)
      exact hw
  have unitζ : ∀ (k : Type) [Field k] (β : cycAway M →+* k), IsUnit (β (zetaAway M)) := fun k _ β =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, GlobalTheory.HTSympCover.zetaAway_pow_self M hM0, map_one]) hM0
  refine ⟨Y, i.left ≫ τ, fun a => i ≫ e a, hY1, hY2, fun T t₁' lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hpow, hgeo⟩ := hL
    obtain ⟨u, hu, huu⟩ := huniv T lv hadd hpow
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hSu T.left T.hom t₁'
    let v : T ⟶ S' := Over.homMk g hg1
    let w : T ⟶ W := lift u v
    have hwe : ∀ a, w ≫ e a = lv a := fun a => by
      simp only [w, e]
      rw [← Category.assoc, lift_fst, hu]
    have hwτ : w.left ≫ τ = t₁' := by
      simp only [τ]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact hg2
    have hr : Set.range w.left ⊆ U := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left q
      obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (x ≫ t₁')
      have hm : (x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs := by
        refine (memIff T w k x β (unitζ k β).unit (by rw [Category.assoc, hwτ, hβ]) rfl).2 ?_
        have := hgeo k x β (unitζ k β).unit hβ rfl
        simp only [hwe]
        exact this
      have hp' : x (default : PrimeSpectrum k) = q := by
        have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
        rwa [hx] at this
      exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left q by rw [← hp']; rfl) ▸ hm
    obtain ⟨f, hf⟩ := (Hi T w).1 hr
    refine ⟨f, ⟨by rw [← Category.assoc, ← Over.comp_left, hf, hwτ], fun a => by
      rw [← Category.assoc, hf, hwe]⟩, fun f' ⟨hf'1, hf'2⟩ => ?_⟩
    have e1 : f' ≫ i ≫ fst Z S' = u := huu _ fun a => by
      have := hf'2 a
      simp only [e, Category.assoc] at this ⊢
      exact this
    have e2 : f' ≫ i ≫ snd Z S' = v := by
      apply Over.OverMorphism.ext
      refine hgu _ ⟨Over.w (f' ≫ i ≫ snd Z S'), ?_⟩
      rw [← hf'1]
      simp [τ]
    have e3 : f' ≫ i = w := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, e1]; exact (lift_fst u v).symm
      · rw [Category.assoc, e2]; exact (lift_snd u v).symm
    exact (cancel_mono i).1 (e3.trans hf.symm)
  · obtain ⟨f, hf1, hf2⟩ := hex
    have hlv : ∀ a, lv a = (f ≫ i) ≫ e a := fun a => by rw [Category.assoc]; exact (hf2 a).symm
    refine ⟨fun a c => by rw [hlv, hlv, hlv, eadd', MonObj.comp_mul],
      fun a => by rw [hlv, ← MonObj.comp_pow, epow', MonObj.comp_one], fun k _ _ x β z hx hz => ?_⟩
    have hr : Set.range (f ≫ i).left ⊆ U := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hm : (x ≫ (f ≫ i).left) (default : PrimeSpectrum k) ∈ Vs := hr ⟨x (default : PrimeSpectrum k), rfl⟩
    have hG := (memIff T (f ≫ i) k x β z (by rw [← hx, ← hf1]; simp) hz).1 hm
    simp only [← hlv] at hG
    exact hG

end GlobalTheory.HTSympRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionFractionFieldUniform
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatTors

open Polynomial in

theorem exists_split_ext (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C) (hφ : φ.Finite) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        ψ.comp φ = j.comp (e.comp (algebraMap K E)) → ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | (apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points ..)

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem exists_finite_tors (K : Type) [Field K] (A : PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : Type) (_ : CommRing C) (φ : K →+* C) (p : Sp C ⟶ A.A.left), φ.Finite ∧ p ≫ A.A.hom = spMap φ ∧
      ∀ (Ω : Type) [Field Ω] (y : Sp Ω ⟶ A.A.left),
        y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left → ∃ ψ : C →+* Ω, y = spMap ψ ≫ p := by
  have hF : IsFinite (mulA A.A n).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp K) A n hn).1
  haveI : IsAffine ((𝟙_ (Over (Sp K))).left) := (inferInstance : IsAffine (Sp K))
  let f := (mulA A.A n).left
  let g := (η[A.A]).left
  haveI : IsFinite f := hF
  haveI hY : IsFinite (pullback.snd f g) := inferInstance
  haveI : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  let Y := pullback f g
  let q : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd f g
  let φ₀ := Spec.preimage q
  have hq : spMap φ₀.hom = q := Spec.map_preimage q
  have hfst : pullback.fst f g ≫ A.A.hom = pullback.snd f g := by
    have h1 : f ≫ A.A.hom = A.A.hom := Over.w (mulA A.A n)
    have h2 : g ≫ A.A.hom = 𝟙 _ := Over.w (η[A.A])
    rw [← h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]
  refine ⟨Γ(Y, ⊤), inferInstance, φ₀.hom, Y.isoSpec.inv ≫ pullback.fst f g, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff]
    change IsFinite (spMap φ₀.hom)
    rw [hq]
    infer_instance
  · rw [hq, Category.assoc, hfst]
  · intro Ω _ y hy
    let z : Sp Ω ⟶ Y := pullback.lift y (y ≫ A.A.hom) (by rw [hy, Category.assoc])
    let w : Sp Ω ⟶ Sp Γ(Y, ⊤) := z ≫ Y.isoSpec.hom
    refine ⟨(Spec.preimage w).hom, ?_⟩
    change y = Spec.map (Spec.preimage w) ≫ _
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

section Push
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mulA_push (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e2 : (pushHom h G' (𝟙 G')) ^ n = pushHom h G' (𝟙 G') ≫ mulA G n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e2] at e
  calc (mulA G' n).left ≫ φ = (pushHom h G' (𝟙 G' ^ n)).left := rfl
    _ = (pushHom h G' (𝟙 G') ≫ mulA G n).left := e
    _ = (𝟙 G'.left ≫ φ) ≫ (mulA G n).left := rfl
    _ = _ := by rw [Category.id_comp]

theorem eta_push (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (Over.mk (𝟙 S'))))
  have e' : (𝟙 S' ≫ (η[G']).left) ≫ φ = (𝟙 S' ≫ f) ≫ (η[G]).left := e
  rwa [Category.id_comp, Category.id_comp] at e'

end Push

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem spMap_inj {P Q : Type} [CommRing P] [CommRing Q] {u v : P →+* Q} (h : spMap u = spMap v) : u = v :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem torsion_rational : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  intro R₁ _ _ _ _ A n hn
  obtain ⟨C, _, φ, p, hφ, hp, hpt⟩ := exists_finite_tors _ A n hn
  obtain ⟨E, hE, hEs⟩ := exists_split_ext (FractionRing R₁) C φ hφ
  refine ⟨E, hE, ?_⟩
  rintro R₂ _ _ _ i₁₂ e _ he A₂ a ⟨ga, hga, hpb, -⟩ x hx
  let j := algebraMap (FractionRing R₂) (Kb R₂)
  have hge : ga = e.comp (algebraMap (FractionRing R₁) E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hga, RingHom.comp_apply, he])
  let y := x.left ≫ a
  have hxh : x.left ≫ A₂.A.hom = spMap j := Over.w x
  have hyh : y ≫ A.A.hom = spMap j ≫ spMap ga := by
    change (x.left ≫ a) ≫ A.A.hom = _
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hxh]
  have h1 : x.left ≫ (mulA A₂.A n).left = spMap j ≫ (η[A₂.A]).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]
    rfl
  have htors : y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left := by
    change (x.left ≫ a) ≫ _ = (x.left ≫ a) ≫ _
    rw [Category.assoc, ← mulA_push hpb, ← Category.assoc, h1, Category.assoc, eta_push hpb,
      ← Category.assoc (x.left ≫ a), hyh, Category.assoc]
  obtain ⟨ψ, hψ⟩ := hpt (Kb R₂) y htors
  have hψφ : ψ.comp φ = j.comp ga := by
    refine spMap_inj ?_
    rw [GlobalTheory.Ex.spMap_comp', GlobalTheory.Ex.spMap_comp', ← hp, ← Category.assoc, ← hψ, hyh]
  obtain ⟨ψ₀, hψ₀⟩ := hEs (FractionRing R₂) (Kb R₂) e j ψ (by rw [hψφ, hge])
  have hψ₀φ : ψ₀.comp φ = ga := by
    refine RingHom.ext fun r => j.injective ?_
    have := RingHom.congr_fun hψφ r
    rw [← hψ₀] at this
    exact this
  let y₀ : Sp (FractionRing R₂) ⟶ A.A.left := spMap ψ₀ ≫ p
  have hy₀ : y₀ ≫ A.A.hom = 𝟙 _ ≫ spMap ga := by
    change (spMap ψ₀ ≫ p) ≫ _ = _
    rw [Category.assoc, hp, ← GlobalTheory.Ex.spMap_comp', hψ₀φ, Category.id_comp]
  refine ⟨hpb.1.lift y₀ (𝟙 _) hy₀, hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hpb.1.lift_fst]
    change y = _
    rw [hψ, ← hψ₀, GlobalTheory.Ex.spMap_comp', Category.assoc]
  · rw [Category.assoc, hpb.1.lift_snd, Category.comp_id, hxh]

end GlobalTheory.Mum.RatTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_finite_rep_linLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ _ hab hN actH
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI : IsSeparated AH.hom := by haveI := hab.proper; infer_instance
  obtain ⟨Z, et, hZf, -, eadd, epow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom H AH N D.La hab hN
  let bO := Module.Free.chooseBasis ℤ D.O
  let bL := Module.Free.chooseBasis ℤ D.La
  obtain ⟨Y, i, hYf, hieq, hiu⟩ := GlobalTheory.T.exists_finite_agreementLocus_separated H Z AH hZf inferInstance
    (Module.Free.ChooseBasisIndex ℤ D.O × Module.Free.ChooseBasisIndex ℤ D.La)
    (fun k => et (bO k.1 • bL k.2)) (fun k => et (bL k.2) ≫ actH.act (bO k.1))
  let u : D.La → (Y ⟶ AH) := fun x => i ≫ et x
  have uadd : ∀ x y, u (x + y) = u x * u y := fun x y => by
    simp only [u, eadd, MonObj.comp_mul]
  have ulin : ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c :=
    GlobalTheory.T.oLinear_of_basis_products_additive_points p D H Y AH actH u uadd _ _ bO bL fun j k => by
      have := hieq (j, k)
      simp only [u]
      rw [this, Category.assoc]
  have ukill : ∀ x, u (N • x) = 1 := fun x => by
    simp only [u]
    rw [GlobalTheory.LevCover.add_map_nsmul eadd, epow, MonObj.comp_one]
  have uuniv : ∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) →
      (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) →
      ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x := by
    intro T u' hadd hlin hkill
    have hpow : ∀ x, u' x ^ N = 1 := fun x => by rw [← GlobalTheory.LevCover.add_map_nsmul hadd, hkill]
    obtain ⟨h₀, hh₀, hu₀⟩ := huniv T u' hadd hpow
    have heq : ∀ k, h₀ ≫ (fun k : _ × _ => et (bO k.1 • bL k.2)) k =
        h₀ ≫ (fun k : _ × _ => et (bL k.2) ≫ actH.act (bO k.1)) k := by
      rintro ⟨j, k⟩
      simp only
      rw [hh₀, hlin, ← Category.assoc, hh₀]
    obtain ⟨h, hh, hu⟩ := hiu T h₀ heq
    refine ⟨h, fun x => by simp only [u]; rw [← Category.assoc, hh, hh₀], fun h' hh' => hu h' ?_⟩
    exact hu₀ _ fun x => by rw [Category.assoc]; exact hh' x
  obtain ⟨AE, _, _, φE, actE, ηE, hE, hact, heta, hηu⟩ := GlobalTheory.T.exists_pullback_group_oLinear_torsion_level p D N H AH actH Y u uadd ulin ukill
  exact ⟨Y.left, Y.hom, AE, inferInstance, inferInstance, φE, actE, ηE, hYf, hE, hact, heta,
    fun T g AT _ φ act eta hT hTact hTeta =>
      GlobalTheory.T.oLinearLevel_pullback_universal_factorisation p D N H AH actH Y u AE φE ηE hE hηu uuniv T g AT φ act eta hT hTact hTeta⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinCover

theorem exists_finite_union {X : Scheme.{0}} {T : Type} (N : T → Scheme.{0}) (p : ∀ t, N t ⟶ X)
    (hp : ∀ t, IsFinite (p t)) (S : Finset T) :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ (∀ t ∈ S, Set.range (p t) ⊆ Set.range q) ∧
      ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (z : Sp K ⟶ N t), z ≫ p t = y' ≫ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨∅, Scheme.emptyTo X, inferInstance, by simp, fun K _ y' => ?_⟩
    exact (show PEmpty from y' (closedPoint K)).elim
  | insert a S _ ih =>
    obtain ⟨Y, q, hq, hr, hK⟩ := ih
    have := hp a
    refine ⟨N a ⨿ Y, coprod.desc (p a) q, inferInstance, fun t ht => ?_, fun K _ y' => ?_⟩
    · rintro _ ⟨x, rfl⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨(coprod.inl : N t ⟶ N t ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
      · obtain ⟨y, hy⟩ := hr t ht ⟨x, rfl⟩
        exact ⟨(coprod.inr : Y ⟶ N a ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc, hy]⟩
    · have hsub : ∀ x : Sp K, x = closedPoint K := fun x =>
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      have hc := (isCompl_range_inl_inr (N a) Y).sup_eq_top
      have hm : y' (closedPoint K) ∈ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) ∪
          Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
        have h : y' (closedPoint K) ∈ (⊤ : Set (N a ⨿ Y : Scheme.{0})) := trivial
        rw [← hc] at h
        exact h
      rcases hm with hm | hm
      · have hs : Set.range y' ⊆ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        refine ⟨a, IsOpenImmersion.lift _ y' hs, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inl_desc]
      · have hs : Set.range y' ⊆ Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        obtain ⟨t, z, hz⟩ := hK K (IsOpenImmersion.lift _ y' hs)
        refine ⟨t, z, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inr_desc, hz]

theorem exists_finite_surjective_cover : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  intro X Z i T _ M U g hg hU hx
  have hU' : ∀ t, Set.range i ⊆ Set.range (U t).ι := fun t => by
    rw [Scheme.Opens.range_ι]; exact hU t
  have := Fintype.ofFinite T
  let i' : ∀ t, X ⟶ (U t).toScheme := fun t => IsOpenImmersion.lift (U t).ι i (hU' t)
  have hi' : ∀ t, i' t ≫ (U t).ι = i := fun t => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨Y, q, hq, hr, hK⟩ := exists_finite_union (fun t => pullback (g t) (i' t))
    (fun t => pullback.snd (g t) (i' t)) (fun t => by have := hg t; infer_instance) Finset.univ
  refine ⟨Y, q, hq, ⟨fun x => ?_⟩, fun K _ y' => ?_⟩
  · obtain ⟨t, w, hw⟩ := hx x
    have := hg t
    refine hr t (Finset.mem_univ t) ?_
    rw [Scheme.Pullback.range_snd]
    rw [← hi' t, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      (U t).ι.isOpenEmbedding.isInducing.specializes_iff] at hw
    exact hw.mem_closed (g t).isClosedMap.isClosed_range ⟨w, rfl⟩
  · obtain ⟨t, z, hz⟩ := hK K y'
    refine ⟨t, z ≫ pullback.fst (g t) (i' t), ?_⟩
    rw [Category.assoc, pullback.condition_assoc, hi' t, ← Category.assoc, hz, Category.assoc]

end GlobalTheory.FinCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundleStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_bundle_proj_vector_bundle : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (E : B.Modules) (r : ℕ), IsProjOver q → GlobalTheory.VB.IsVB E r → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj E) r), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fl ∧ IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | exact GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | (intros; apply GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  first | exact @GlobalTheory.VarFlag.exists_rel_of_mem_Vo | exact GlobalTheory.VarFlag.exists_rel_of_mem_Vo | (intros; apply GlobalTheory.VarFlag.exists_rel_of_mem_Vo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatProjectiveModelOverRingOfIntegersStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_projective_model_over_ringOfIntegers : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
    IsProjOver q → topologicalKrullDim Y = D → (⨆ k, nonzeroLocus (t k) = ⊤) → Function.Bijective ψ →
    (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i), ψ (y k) * fnOf _ h ((t l).f i) = ψ (y l) * fnOf _ h ((t k).f i)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X.functionField),
      g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) := by
  first | exact @GlobalTheory.SpreadModel.exists_spread | exact GlobalTheory.SpreadModel.exists_spread | (intros; apply GlobalTheory.SpreadModel.exists_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_quotient_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∃ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ ∧ IsAffineHom π ∧ Surjective π ∧ (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) ∧ (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) ∧ ∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom := by
  first | exact @GlobalTheory.Mum.exists_galois_quotient | exact GlobalTheory.Mum.exists_galois_quotient | (intros; apply GlobalTheory.Mum.exists_galois_quotient <;> assumption)
end

