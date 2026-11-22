import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0421
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionLiftVal

theorem sections_restrict_bijective (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k)
    {X : Scheme.{0}} (p : X ⟶ Sp U) [IsFinite p] [Etale p] :
    Function.Bijective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
  have inj : Function.Injective (fun s : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} =>
      (⟨spMap h ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩ : {x : Sp k ⟶ X // x ≫ p = spMap h})) := by
    rintro ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ e
    have e' : spMap h ≫ s₁ = spMap h ≫ s₂ := congrArg Subtype.val e
    haveI : LocallyOfFiniteType (Over.mk p).hom := inferInstanceAs (LocallyOfFiniteType p)
    haveI : FormallyUnramified (Over.mk p).hom := inferInstanceAs (FormallyUnramified p)
    haveI : IsSeparated (Over.mk p).hom := inferInstanceAs (IsSeparated p)
    let f₁ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₁ h₁
    let f₂ : Over.mk (𝟙 (Sp U)) ⟶ Over.mk p := Over.homMk s₂ h₂
    have hr := (FinEt.comp_eq_comp_iff_range f₁ f₂ (spMap h)).1 e'
    haveI : PreconnectedSpace (Over.mk (𝟙 (Sp U))).left := inferInstanceAs (PreconnectedSpace (Sp U))
    have hc : IsClopen (Set.range (FinEt.agreeι f₁ f₂)) :=
      ⟨(FinEt.agreeι f₁ f₂).isClosedEmbedding.isClosed_range, (FinEt.agreeι f₁ f₂).isOpenEmbedding.isOpen_range⟩
    obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
    have hu : Set.range (FinEt.agreeι f₁ f₂) = Set.univ := hc.eq_univ ⟨_, hr ⟨z, rfl⟩⟩
    have := (FinEt.comp_eq_comp_iff_range f₁ f₂ (𝟙 _)).2 (by rw [hu]; exact Set.subset_univ _)
    apply Subtype.ext
    simpa [f₁, f₂] using this
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨hBfin, hB⟩ := FinEt.card_points_eq_finrank p (spMap h) z
  obtain ⟨-, hC⟩ := FinEt.card_points_eq_finrank p (spMap (algebraMap U Ω)) w
  haveI := hBfin
  haveI : Finite {s : Sp U ⟶ X // s ≫ p = 𝟙 _} := Finite.of_injective _ inj
  have hv : ValuativeCriterion p := by
    have hp : IsProper p := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let r : {s : Sp U ⟶ X // s ≫ p = 𝟙 _} → {x : Sp Ω ⟶ X // x ≫ p = spMap (algebraMap U Ω)} :=
    fun s => ⟨spMap (algebraMap U Ω) ≫ s.1, by rw [Category.assoc, s.2, Category.comp_id]⟩
  have hrs : Function.Surjective r := by
    rintro ⟨x, hx⟩
    let Q : ValuativeCommSq p :=
      { R := U, K := Ω, i₁ := x, i₂ := 𝟙 _, commSq := ⟨hx.trans (Category.comp_id _).symm⟩ }
    obtain ⟨W⟩ := hv Q
    exact ⟨⟨W.default.l, W.default.fac_right⟩, Subtype.ext W.default.fac_left⟩
  have hle := Nat.card_le_card_of_surjective r hrs
  have hrank := (Scheme.Hom.isLocallyConstant_finrank p).apply_eq_of_preconnectedSpace (spMap h z)
    (spMap (algebraMap U Ω) w)
  refine inj.bijective_of_nat_card_le ?_
  rw [hB, hrank, ← hC]
  exact hle

theorem torsion_lift_unique : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u n hn y hy
  letI : GrpObj ((Over.pullback u).obj G) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback u).obj G) G u (pullback.fst G.hom u) := isGrpPullback_pullback G u
  haveI : IsAbelianScheme ((Over.pullback u).obj G) := GlobalTheory.isAbelianScheme_pullback_obj u G hA
  have hnU : IsUnit (n : Γ(Sp U, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion ((Over.pullback u).obj G) hnU
  have key : ∀ {X : Scheme.{0}} (t : X ⟶ Sp U) (b : X ⟶ S), b = t ≫ u →
      ∃ Φ : (Over.mk t ⟶ torsion ((Over.pullback u).obj G) n) → (Over.mk b ⟶ G),
        Function.Injective Φ ∧ (∀ a, Φ a ^ n = 1) ∧ (∀ w : Over.mk b ⟶ G, w ^ n = 1 → ∃ a, Φ a = w) ∧
        ∀ a, (Φ a).left = a.left ≫ (torsion.ι ((Over.pullback u).obj G) n).left ≫ pullback.fst G.hom u := by
    intro X t b hb
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hgp t b hb
    refine ⟨fun a => e ((TorsionUnram.torsionEquiv _ n _) a).1, ?_, ?_, ?_, ?_⟩
    · intro a₁ a₂ h12
      exact (TorsionUnram.torsionEquiv _ n _).injective (Subtype.ext (e.injective h12))
    · intro a
      rw [← map_pow, ((TorsionUnram.torsionEquiv _ n _) a).2, map_one]
    · intro w hw
      refine ⟨(TorsionUnram.torsionEquiv _ n _).symm ⟨e.symm w, by rw [← map_pow, hw, map_one]⟩, ?_⟩
      simp
    · intro a
      rw [he, ← Category.assoc]
      rfl
  obtain ⟨Φk, injk, -, surjk, hk⟩ := key (spMap h) (spMap h ≫ u) rfl
  obtain ⟨ΦU, -, powU, surjU, hUl⟩ := key (𝟙 (Sp U)) u (Category.id_comp u).symm
  obtain ⟨τ, rfl⟩ := surjk y hy
  have hb := sections_restrict_bijective U Ω k h (torsion ((Over.pullback u).obj G) n).hom
  obtain ⟨⟨s, hs⟩, hs'⟩ := hb.2 ⟨τ.left, Over.w τ⟩
  have hs'' : spMap h ≫ s = τ.left := congrArg Subtype.val hs'
  let σ : Over.mk (𝟙 (Sp U)) ⟶ torsion ((Over.pullback u).obj G) n := Over.homMk s hs
  refine ⟨ΦU σ, ⟨powU σ, ?_⟩, ?_⟩
  · rw [hk, hUl, ← hs'']
    simp [σ]
  · rintro P ⟨hP, hPy⟩
    obtain ⟨σ', rfl⟩ := surjU P hP
    have hσ' : σ'.left ≫ (torsion ((Over.pullback u).obj G) n).hom = 𝟙 _ := Over.w σ'
    let τ' : Over.mk (spMap h) ⟶ torsion ((Over.pullback u).obj G) n :=
      Over.homMk (spMap h ≫ σ'.left) (by rw [Category.assoc, hσ']; exact Category.comp_id _)
    have e0 : Φk τ' = Φk τ := by
      apply Over.OverMorphism.ext
      rw [hk, hPy, hUl]
      simp [τ']
    have e1 : spMap h ≫ σ'.left = τ.left := congrArg (fun q => q.left) (injk e0)
    have e2 := hb.1 (a₁ := ⟨σ'.left, hσ'⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext (e1.trans hs''.symm))
    have e3 : σ' = σ := Over.OverMorphism.ext (congrArg Subtype.val e2)
    rw [e3]

end GlobalTheory.TorsionLiftVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupSchemes
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTorsRep

theorem absNorm_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] (𝔟 : Ideal (𝓞 K))
    (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : (Ideal.absNorm 𝔟).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
  obtain ⟨β, hβ, z, hz, hβz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  by_cases h0 : 𝔟 = ⊥
  · subst h0
    have hβ0 : β = 0 := (Submodule.mem_bot _).1 hβ
    subst hβ0
    rw [zero_add] at hβz
    have hu : IsUnit (p : 𝓞 K) := ⟨⟨(p : 𝓞 K), y, by rw [mul_comm]; exact hβz, hβz⟩, rfl⟩
    have hu' := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
    rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at hu'
    have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := (Module.finrank_pos).ne'
    rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu'
    rcases hu' with h' | h'
    · exact hp.out.one_lt.ne' (by exact_mod_cast h')
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · have hne : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne hdvd
    have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hne
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have h1' : (Ideal.Quotient.mk 𝔟 y) * (p : 𝓞 K ⧸ 𝔟) = 1 := by
      have := congrArg (Ideal.Quotient.mk 𝔟) hβz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
    have hx0 : x = 0 := by
      rw [← _root_.one_mul x, ← h1', _root_.mul_assoc, hpx, MulZeroClass.mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx

section Tors

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem mono_of_unit {X : Over S} (e : 𝟙_ (Over S) ⟶ X) : Mono e := ⟨fun g h _ => toUnit_unique g h⟩

theorem ι_mulN : torsion.ι A n ≫ mulN A n = toUnit _ ≫ η[A] := by
  exact (pullback.condition (f := mulN A n) (g := (η : 𝟙_ (Over S) ⟶ A))).trans
    (congrArg (· ≫ η[A]) (toUnit_unique _ _))

def torsEta : 𝟙_ (Over S) ⟶ torsion A n :=
  pullback.lift η[A] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

@[reassoc (attr := simp)] theorem torsEta_ι : torsEta n ≫ torsion.ι A n = η[A] := pullback.lift_fst _ _ _

theorem mono_ι : Mono (torsion.ι A n) := by
  have := mono_of_unit η[A]
  exact pullback.fst_of_mono

def torsAct (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) : torsion A n ⟶ torsion A n :=
  pullback.lift (torsion.ι A n ≫ f) (toUnit _) (by
    rw [Category.assoc, hf, ← Category.assoc, ι_mulN, Category.assoc, IsMonHom.one_hom])

@[reassoc (attr := simp)] theorem torsAct_ι (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) :
    torsAct n f hf ≫ torsion.ι A n = torsion.ι A n ≫ f := pullback.lift_fst _ _ _

theorem exists_openClosed {Ix : Type} [DecidableEq Ix] (act : Ix → (A ⟶ A)) [∀ a, IsMonHom (act a)]
    (hc : ∀ a, act a ≫ mulN A n = mulN A n ≫ act a) [Etale (torsion A n).hom] [IsSeparated (torsion A n).hom]
    (t : Finset Ix) :
    ∃ (Z : Over S) (j : Z ⟶ torsion A n), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ torsion A n), (∃ z, z ≫ j = y) ↔ ∀ a ∈ t, y ≫ torsion.ι A n ≫ act a = 1 := by
  have hsec : IsOpenImmersion (torsEta (A := A) n).left ∧ IsClosedImmersion (torsEta (A := A) n).left :=
    GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion A n).hom _ (Over.w (torsEta n))
  have := hsec.1; have := hsec.2
  have := mono_of_unit (torsEta (A := A) n)
  have := mono_ι (A := A) n
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨_, 𝟙 _, inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance, fun W y =>
      ⟨fun _ a ha => absurd ha (Finset.notMem_empty a), fun _ => ⟨y, Category.comp_id y⟩⟩⟩
  | insert a t hat ih =>
    obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := ih
    let g := j ≫ torsAct n (act a) (hc a)
    have hP := (IsPullback.of_hasPullback g (torsEta n)).map (Over.forget S)
    have ho : IsOpenImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1
    have hcl : IsClosedImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2
    refine ⟨pullback g (torsEta n), pullback.fst g (torsEta n) ≫ j, inferInstance, ?_, ?_, fun W y => ?_⟩
    · rw [Over.comp_left]; infer_instance
    · rw [Over.comp_left]; infer_instance
    constructor
    · rintro ⟨z, rfl⟩ b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · have e : j ≫ torsion.ι A n ≫ act b = g ≫ torsion.ι A n := by simp [g]
        simp only [Category.assoc]
        rw [e, ← Category.assoc (pullback.fst g _), pullback.condition]
        simp only [Category.assoc, torsEta_ι]
        rw [← Category.assoc, toUnit_unique (z ≫ pullback.snd g (torsEta n)) (toUnit W)]; rfl
      · exact (hpts W _).1 ⟨z ≫ pullback.fst _ _, Category.assoc _ _ _⟩ b hb
    · intro h
      obtain ⟨w, hw⟩ := (hpts W y).2 (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hwg : w ≫ g = toUnit W ≫ torsEta n := by
        rw [← cancel_mono (torsion.ι A n)]
        simp only [g, Category.assoc, torsAct_ι, torsEta_ι]
        rw [← Category.assoc w j, hw, h a (Finset.mem_insert_self a t)]; rfl
      exact ⟨pullback.lift w (toUnit W) hwg, by rw [← Category.assoc, pullback.lift_fst, hw]⟩

end Tors

open GlobalTheory.IwLevel in

theorem exists_finiteEtale_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o 𝔟 h𝔟
  classical
  set n := Ideal.absNorm 𝔟 with hn_def
  have hcop := absNorm_coprime p 𝔟 h𝔟
  have hnR : IsUnit ((n : ℕ) : R) := b.unit n hcop
  have hnS : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
    have := hnR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hnS
  have hactN : ∀ k : ℕ, o.act.act (k : D.O) = mulN o.A k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one]; rfl
  have hc : ∀ a : D.O, o.act.act a ≫ mulN o.A n = mulN o.A n ≫ o.act.act a := by
    intro a
    rw [← hactN, ← o.act.mul, ← o.act.mul, Nat.cast_comm]
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : IsSeparated (torsion o.A n).hom := inferInstance
  have : Module.Finite ℤ D.O := D.finO
  have : IsNoetherian D.O D.O := isNoetherian_of_tower ℤ inferInstance
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (𝔟.map (algebraMap (𝓞 D.F) D.O))
  obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := exists_openClosed n o.act.act hc t
  have := mono_ι (A := o.A) n
  refine ⟨Z, j ≫ torsion.ι o.A n, inferInstance, ?_, ?_, fun T x => ?_⟩
  · rw [← Over.w j]; infer_instance
  · rw [← Over.w j]; infer_instance
  rw [← ht]
  refine Iff.trans ?_ (killedBy_span (htAct o) (t : Set D.O) x).symm
  simp only [htAct_act]
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simpa only [Category.assoc] using (hpts T (z ≫ j)).1 ⟨z, rfl⟩ a ha
  · intro hx
    have hn𝔟 : ((n : ℕ) : 𝓞 D.F) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
    have hnO : ((n : ℕ) : D.O) ∈ Submodule.span D.O (t : Set D.O) := by
      rw [ht]; simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) hn𝔟
    have hxn : x ≫ mulN o.A n = toUnit T ≫ η[o.A] := by
      rw [← hactN]
      have := (killedBy_span (htAct o) (t : Set D.O) x).2 (by simpa only [htAct_act] using hx) _ hnO
      exact this
    let y : T ⟶ torsion o.A n := pullback.lift x (toUnit T) hxn
    have hy : y ≫ torsion.ι o.A n = x := pullback.lift_fst _ _ _
    obtain ⟨z, hz⟩ := (hpts T y).2 (fun a ha => by rw [← Category.assoc, hy]; exact hx a ha)
    exact ⟨z, by rw [← Category.assoc, hz, hy]⟩

end GlobalTheory.HTTorsRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Hk3 (Core IsSF SchurAll EEc Wcc)

namespace GlobalTheory.TrLevMult

theorem level_eq_trivial {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot_eq {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem pg_over {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) : ∀ PP ∈ R.Pg, ∃ v ∈ SF,
    PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal :=
  fun PP hPP => ⟨Formalism.IndefR.Fin.belowPl PP, (hSF _).2 ⟨PP, hPP, rfl⟩, rfl⟩

theorem trAt_of_dim (hC : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) (Pe Pw : LevelP R.Pg D.R.r ℂ)
    (hdim : ∀ c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e : Submodule ℂ _)) :
    GlobalTheory.TrCopy.TRAt R SF i Pe Pw := by
  intro c
  have hE : R.EEat Pe ≤ R.EEat R.triv := GlobalTheory.PartDims.goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hW : R.Wat i (sg0 D A) Pw ≤ R.Wat i (sg0 D A) R.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have kE : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF Q d B ↔
      Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Yc D 0) (R.βY 0) (R.dat0 R.triv) Pe R.triv SF (pg_over hSF)
  have kW : ∀ Q d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF Q d B ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Wc D i) (R.βW i) (R.datWp i R.triv) Pw R.triv SF (pg_over hSF)
  have eqE : GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c =
      R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => c Q (dualLab d)) := by
    ext x
    show (x ∈ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF
        (fun Q d => c Q (dualLab d)) ∧ x ∈ R.EEat Pe) ↔ (x ∈ R.EEat Pe ∧ x ∈ partFull R.θ (R.MY 0)
        (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d)))
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hE h2).1, fun Q d B hB => h1 Q d B ((kE Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kE Q d B).1 hB)⟩, h2⟩
  have eqW : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c =
      R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) SF c := by
    ext x
    show (x ∈ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF c ∧
        x ∈ R.Wat i (sg0 D A) Pw) ↔ (x ∈ R.Wat i (sg0 D A) Pw ∧ x ∈ partFull R.θ (R.MW i (sg0 D A))
        (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hW h2).1, fun Q d B hB => h1 Q d B ((kW Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kW Q d B).1 hB)⟩, h2⟩
  have fE := GlobalTheory.PartDims.finrank_comap hC.models.HE (U := R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE)
  have fW := GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) Pw ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left))
  have cE : (R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))).comap R.HE.e =
      EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  have cW : (R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e =
      Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  haveI := fE.2
  haveI := fW.2
  show Module.rank ℂ (GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c) =
    Module.rank ℂ (GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c)
  rw [eqE, eqW, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← fE.1, ← fW.1, cE, cW, hdim c]

end GlobalTheory.TrLevMult

open GlobalTheory.TrLevMult in

theorem GlobalTheory.TrLevMult.trLev_of_multEq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF
  have key : ∀ i (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      GlobalTheory.TrCopy.TRAt R SF i (levPOf R.eG D.what₂.embLL P ψ) (levPOf R.eG (sg0 D A) P ψ⁻¹) :=
    fun i P ψ => trAt_of_dim hC hSF i _ _ (fun c => GlobalTheory.DimFull.dim_parts_full R F hs hC hS hX hD hM SF hSF P ψ i c)
  intro i
  refine ⟨?_, fun b => key i _ _⟩
  have h := key i ⊥ 1
  rwa [inv_one, levPOf_bot_eq, levPOf_bot_eq] at h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountCharPoly
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TwClassCount

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → Nat.card {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} * 2 ^ nfac P = 2 ^ (n * Fintype.card (InfinitePlace E)) := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    GlobalTheory.T.twisted_class_count_torus_decomposition E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.T.almost_norm_class_count (K i) (L i) (hR i) (hC i) (x i) (hA i)

end GlobalTheory.BCT.TwClassCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLattice
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
end

