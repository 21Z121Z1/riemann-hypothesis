import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def TateAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k] (x : Sp k ⟶ S)
    (l : D.La → (Over.mk x ⟶ o.A)) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, l y = I.ev N' y

theorem tateAt_congr {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k]
    {x x' : Sp k ⟶ S} (e : x = x') (l : D.La → (Over.mk x ⟶ o.A)) (l' : D.La → (Over.mk x' ⟶ o.A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ l a = l' a) :
    TateAt o N' x l → TateAt o N' x' l' := by
  subst e
  have h' : ∀ a, l a = l' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

theorem comp_actN_nsmul {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {T : Over S}
    (x : T ⟶ A) (n : ℕ) (c : D.O) : x ≫ act.act (n • c) = (x ^ n) ≫ act.act c := by
  have := act.hom c
  rw [add_map_nsmul act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_liftHom {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (hc : N'.Coprime p)
    (hd : N ∣ N') :
    ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧
      (∀ a, et (N' • a) = 1) ∧ (∀ (c : D.O) a, et (c • a) = et a ≫ o.act.act c) ∧
      (∀ a, et ((N' / N) • a) = toUnit Z ≫ o.eta a) ∧
      ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N' • a) = 1) →
        (∀ (c : D.O) a, lv (c • a) = lv a ≫ o.act.act c) → (∀ a, lv ((N' / N) • a) = toUnit T ≫ o.eta a) →
          ∃! h : T ⟶ Z, ∀ a, h ≫ et a = lv a := by
  have hN' := levelPos_of_coprime hc
  have hNS : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit N' hc).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨Z, y, hfin, het, yadd, ypow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A N' D.La o.ab hNS
  have R : RepTors o.A N' D.La Z y := ⟨hfin, het, yadd, ypow, huniv⟩
  haveI := hfin
  haveI := het
  have ymod : ∀ a c, y (a + N' • c) = y a := fun a c => by
    rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have etaN : ∀ a, o.eta (N' • a) = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hd, mul_smul, o.eta_ker]
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod D.O hN'
  have c1 : ClopenCond Z fun _ h => ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := o.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ o.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := o.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, o.act.add, MonObj.comp_mul, comp_actN_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond Z fun _ h => ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) :=
    R.clopenCond (fun a => y ((N' / N) • a)) (fun a => toUnit Z ≫ o.eta a) (fun a a' => by rw [smul_add, yadd])
      (fun a => ypow _) (fun a a' => by rw [o.eta_add, MonObj.comp_mul]) fun a => by
        rw [← MonObj.comp_pow, ← add_map_nsmul o.eta_add, etaN, MonObj.comp_one]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU W i).2 ((Hi W i).2 ⟨𝟙 W, Category.id_comp i⟩)
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [add_map_nsmul yadd, ypow, MonObj.comp_one],
    fun c a => by beta_reduce; rw [hi.1, Category.assoc], fun a => ?_, fun T lv hadd hker hlin hlev => ?_⟩
  · beta_reduce
    rw [hi.2, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have hpow : ∀ a, lv a ^ N' = 1 := fun a => by rw [← add_map_nsmul hadd, hker]
  obtain ⟨h, hh, -⟩ := huniv T lv hadd hpow
  have hP1 : ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := fun c a => by
    rw [hh, hlin, ← hh a, Category.assoc]
  have hP2 : ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) := fun a => by
    rw [hh, hlev, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 ⟨hP1, hP2⟩)
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
  have : g ≫ i = h' ≫ i := R.ext fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hh]
  exact (cancel_mono i).1 this

theorem exists_liftScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  intro p _ D R _ b N N' hc hd S _ s o
  obtain ⟨Z, et, hZf, hZe, eadd, eker, elin, elev, huniv⟩ := exists_liftHom o N' hc hd
  haveI := hZf
  haveI := hZe
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsp : ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ Z.left)
      (x' : Sp k' ⟶ Z.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u →
      (TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        TateAt o N' (x' ≫ Z.hom) (fun a => (Over.homMk x' rfl : Over.mk (x' ≫ Z.hom) ⟶ Z) ≫ et a)) :=
    fun x x' u u' h => GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc S s o Z et eadd eker elin x x' u u' h
  let U : Set Z.left := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ Z.left),
    z ∈ Set.range x.base ∧
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a)}
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.left),
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        Set.range x.base ⊆ U := by
    intro k _ _ x
    refine ⟨fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩, fun hx => ?_⟩
    let pt : Sp k := (⊥ : PrimeSpectrum k)
    obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
    exact (hsp x x' pt u' (hu' ▸ specializes_rfl)).2 hG'
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff Z.left U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  let U' : Z.left.Opens := ⟨U, hclo.isOpen⟩
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U' hclo.isClosed
  refine ⟨V, fun a => i ≫ et a, hV1, hV2, fun T lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hker, hlin, hlev, hgeo⟩ := hL
    obtain ⟨h, hh, hu⟩ := huniv T lv hadd hker hlin hlev
    have hr : Set.range h.left ⊆ U' := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := FinEt.exists_algClosed_point T.left t
      obtain ⟨u, hu⟩ : t ∈ Set.range x.base := by rw [show Set.range x.base = {t} from hx]; rfl
      have hG := tateAt_congr o N' (x' := (x ≫ h.left) ≫ Z.hom)
        (by rw [Category.assoc, Over.w h]) _
        (fun a => (Over.homMk (x ≫ h.left) rfl : Over.mk ((x ≫ h.left) ≫ Z.hom) ⟶ Z) ≫ et a)
        (fun a => by rw [← hh a, ← Category.assoc, ← Category.assoc]; congr 1; try (ext; simp)) (hgeo k x)
      refine (key k (x ≫ h.left)).1 hG ⟨u, ?_⟩
      rw [Scheme.Hom.comp_apply, hu]
    obtain ⟨h', hh'⟩ := (Hi T h).1 hr
    refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
    have : g ≫ i = h := hu _ fun a => by rw [Category.assoc]; exact hg a
    exact (cancel_mono i).1 (this.trans hh'.symm)
  · obtain ⟨f, hf⟩ := hex
    have hf' : ∀ a, lv a = (f ≫ i) ≫ et a := fun a => by rw [Category.assoc]; exact (hf a).symm
    refine ⟨fun a c => by rw [hf', hf', hf', eadd, MonObj.comp_mul], fun a => by rw [hf', eker, MonObj.comp_one],
      fun c a => by rw [hf', hf', elin]; simp only [Category.assoc], fun a => ?_, fun k _ _ x => ?_⟩
    · rw [hf', elev, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have hr : Set.range (f ≫ i).left ⊆ U' := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hG := (key k (x ≫ (f ≫ i).left)).2 fun z ⟨u, hu⟩ => hr ⟨x.base u, by rw [← hu, Scheme.Hom.comp_apply]⟩
    refine tateAt_congr o N' (by rw [Category.assoc, Over.w (f ≫ i)]) _ _ ?_ hG
    intro a
    rw [hf' a]
    simp only [← Category.assoc]
    congr 1
    try (ext; simp)

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwoTorsionDescent

theorem exists_finite_ext_of_sq_eq_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  intro K Ω _ _ _ ga A G _ α h x hx

  set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT
  let zo : T ⟶ A.A := pushHom h (𝟙_ (Over (Sp Ω))) x
  have hzo : zo * zo = 1 := by
    show pushHom h _ x * pushHom h _ x = 1
    rw [← map_mul, hx, map_one]
  have hzl : zo.left = x.left ≫ α := rfl
  have hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A] := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]
    rfl
  let t : T ⟶ torsion A.A 2 := pullback.lift zo (toUnit T) hmul
  have ht : t ≫ torsion.ι A.A 2 = zo := pullback.lift_fst _ _ _

  have h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K) := by
      rw [map_ofNat]; rfl
    rw [e]
    exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  haveI := A.isAb
  have hfin : IsFinite (torsion A.A 2).hom := (GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1
  set X := (torsion A.A 2).left
  set p := (torsion A.A 2).hom
  let tl : Sp Ω ⟶ X := t.left
  let w : X := tl (IsLocalRing.closedPoint Ω)
  let φ : X.residueField w ⟶ CommRingCat.of Ω := X.descResidueField (Scheme.stalkClosedPointTo tl)
  have htl : Spec.map φ ≫ X.fromSpecResidueField w = tl :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl

  let s : Sp K := p w
  haveI : s.asIdeal.IsPrime := s.isPrime
  haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal
  let c : K →+* (Sp K).residueField s :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)
  have hc : spMap c = (Sp K).fromSpecResidueField s := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  have hcfin : c.Finite := by
    refine RingHom.Finite.of_surjective _ ?_
    refine (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_
    have hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal) := Ideal.Quotient.mk_surjective
    have hb := Ideal.bijective_algebraMap_quotient_residueField s.asIdeal
    have e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal) := by
      ext a; rfl
    rw [e]
    exact hb.2.comp hq
  let io : K →+* X.residueField w := (p.residueFieldMap w).hom.comp c
  have hio : io.Finite := (GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin
  have hsio : spMap io = X.fromSpecResidueField w ≫ p := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]
    rfl

  have hu : X.fromSpecResidueField w ≫ p = spMap io := hsio.symm
  let u : Over.mk (spMap io) ⟶ torsion A.A 2 := Over.homMk (X.fromSpecResidueField w) hu
  let y : Over.mk (spMap io) ⟶ A.A := u ≫ torsion.ι A.A 2
  have hy : y * y = 1 := by
    have e1 : y * y = y ≫ mulN A.A 2 := by
      rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]
    have e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A] :=
      pullback.condition
    rw [e1, Category.assoc, e2]
    show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]
    rw [toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]
  have hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga := by
    rw [← Category.assoc, htl]
    exact Over.w t
  refine ⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩
  · have e : spMap (φ.hom.comp io) = spMap ga := by
      rw [← hlo, ← hsio]
      show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)
      erw [← Spec.map_comp]
      rfl
    have e' := Spec.map_inj.mp e
    exact congrArg CommRingCat.Hom.hom e'
  · show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α
    rw [CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]
    rfl

end GlobalTheory.TwoTorsionDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDescent

theorem qc_qs_tensor {S : Scheme.{0}} (A : Over S) [IsProper A.hom] :
    QuasiCompact (A ⊗ A).hom ∧ QuasiSeparated (A ⊗ A).hom := by
  have e : (A ⊗ A).hom = pullback.fst A.hom A.hom ≫ A.hom := rfl
  rw [e]; exact ⟨inferInstance, inferInstance⟩

theorem exists_galois_polAV : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∀ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB → Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) → Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP Ω _ _ _ _ κ hκ L hL hS hΛ hAmp hKT
  haveI := hA.proper
  haveI := hA.smooth
  let σΩ : K →+* Ω := algebraMap K Ω
  let AΩ := (Over.pullback (spMap σΩ)).obj A
  have hAΩ : IsAbelianScheme AΩ := isAbelianScheme_pullback_obj _ A hA
  have hpΩ : IsGrpPullback AΩ A (spMap σΩ) (pullback.fst A.hom (spMap σΩ)) := isGrpPullback_pullback A _

  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω A.left AΩ.left A.hom AΩ.hom
    (pullback.fst A.hom (spMap σΩ)) hpΩ.1 L hL
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let AF := (Over.pullback f).obj A
  have hAF : IsAbelianScheme AF := isAbelianScheme_pullback_obj f A hA
  have hpF : IsGrpPullback AF A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap σΩ := by
    simp only [f, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpΩ.1.w
  let jm : AΩ.left ⟶ AF.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst A.hom f = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjs : jm ≫ AF.hom = AΩ.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback AΩ AF (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hpF (hpΩ.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H AF.left AF.hom (pullback.fst A.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff hL (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm

  have hPPlb : PP.IsLB := hPP
  obtain ⟨κF, hκF⟩ : ∃ κF : (G2 AF).left ⟶ (G2 A).left, IsSquare (pullback.fst A.hom f) κF :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hpF.1.w⟩
  obtain ⟨jm₂, hjm₂⟩ : ∃ jm₂ : (G2 AΩ).left ⟶ (G2 AF).left, IsSquare jm jm₂ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hj.1.w⟩
  have hΛF : (abelian₂ AF L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have hΛΩ : (abelian₂ AΩ L).IsLB := DVR.linComb_isLB _ hL _ _
  have hNF : (PP.pull κF).IsLB := pull_isLB hPPlb κF
  have eΩ : κ = jm₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hjm₂ hκF
    rw [hjf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ h
  have isoΩ : LBIso ((abelian₂ AF L₁).pull jm₂) ((PP.pull κF).pull jm₂) :=
    LBIso.trans (pull_isLB hΛF _) hΛΩ (pull_isLB hNF _)
      (GlobalTheory.LamPull.lbIso_lam_pull hj hL₁ hL hw hjm₂).symm
      (LBIso.trans hΛΩ (pull_isLB hPPlb _) (pull_isLB hNF _) hΛ
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF jm₂ eΩ).symm)
  haveI := hAF.proper
  haveI := hAF.smooth
  have hqq := qc_qs_tensor AF
  obtain ⟨s, hs⟩ := GlobalTheory.lbIso_descends_to_subfield_containing_finset F Ω (algebraMap F Ω) (G2 AF) (G2 AΩ) jm₂
    (abelian₂ AF L₁) (PP.pull κF) (GlobalTheory.SiegelDescent.isPullback_square hj.1 jm₂ hjm₂) hqq.1 hqq.2 hΛF hNF isoΩ

  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let F' : IntermediateField K Ω := F ⊔ IntermediateField.adjoin K (s : Set Ω)
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  haveI : FiniteDimensional K F' := IntermediateField.finiteDimensional_sup _ _
  let E : IntermediateField K Ω := IntermediateField.normalClosure K F' Ω
  haveI hEf : FiniteDimensional K E := normalClosure.is_finiteDimensional K F' Ω
  haveI hEg : IsGalois K E := by
    haveI : Normal K E := inferInstance
    exact IsGalois.mk
  have hFE : F ≤ E := le_sup_left.trans F'.le_normalClosure
  have hsE : (s : Set Ω) ⊆ E := fun y hy =>
    F'.le_normalClosure (le_sup_right (a := F) (IntermediateField.subset_adjoin K _ hy))
  let α : F →+* E := (IntermediateField.inclusion hFE).toRingHom
  let e : Sp E ⟶ Sp K := spMap (algebraMap K E)
  let AE := (Over.pullback e).obj A
  have hAE : IsAbelianScheme AE := isAbelianScheme_pullback_obj e A hA
  have hpE : IsGrpPullback AE A e (pullback.fst A.hom e) := isGrpPullback_pullback A e
  have hcα : spMap α ≫ f = e := by
    simp only [f, e, α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wE : pullback.fst A.hom e ≫ A.hom = (AE.hom ≫ spMap α) ≫ f := by
    rw [Category.assoc, hcα]
    exact hpE.1.w
  let χ : AE.left ⟶ AF.left := pullback.lift (pullback.fst A.hom e) (AE.hom ≫ spMap α) wE
  have hχf : χ ≫ pullback.fst A.hom f = pullback.fst A.hom e := pullback.lift_fst _ _ _
  have hχs : χ ≫ AF.hom = AE.hom ≫ spMap α := pullback.lift_snd _ _ _
  have hχ : IsGrpPullback AE AF (spMap α) χ := IsGrpPullback.cancel hpF (hpE.congr hcα.symm hχf.symm) hχs
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : (G2 AE).left ⟶ (G2 AF).left, IsSquare χ χ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hχ.1.w⟩
  have isoE : LBIso ((abelian₂ AF L₁).pull χ₂) ((PP.pull κF).pull χ₂) :=
    hs E α (algebraMap E Ω) (RingHom.ext fun _ => rfl) (fun y hy => ⟨⟨y, hsE hy⟩, rfl⟩) (G2 AE) χ₂
      (GlobalTheory.SiegelDescent.isPullback_square hχ.1 χ₂ hχ₂)

  let LE : LB AE.left := L₁.pull χ
  have hLE : LE.IsLB := pull_isLB hL₁ χ
  have hcE : spMap (algebraMap E Ω) ≫ e = spMap σΩ := by
    simp only [e, σΩ, spMap]
    rw [← Spec.map_comp]
    congr 1
  have wΩ : pullback.fst A.hom (spMap σΩ) ≫ A.hom = (AΩ.hom ≫ spMap (algebraMap E Ω)) ≫ e := by
    rw [Category.assoc, hcE]
    exact hpΩ.1.w
  let jE : AΩ.left ⟶ AE.left := pullback.lift (pullback.fst A.hom (spMap σΩ)) (AΩ.hom ≫ spMap (algebraMap E Ω)) wΩ
  have hjEf : jE ≫ pullback.fst A.hom e = pullback.fst A.hom (spMap σΩ) := pullback.lift_fst _ _ _
  have hjEs : jE ≫ AE.hom = AΩ.hom ≫ spMap (algebraMap E Ω) := pullback.lift_snd _ _ _
  have hjE : IsGrpPullback AΩ AE (spMap (algebraMap E Ω)) jE :=
    IsGrpPullback.cancel hpE (hpΩ.congr hcE.symm hjEf.symm) hjEs
  have hαΩ : spMap (algebraMap E Ω) ≫ spMap α = spMap (algebraMap F Ω) := by
    simp only [α, spMap]
    rw [← Spec.map_comp]
    congr 1
  have ejm : jm = jE ≫ χ := by
    apply pullback.hom_ext
    · rw [hjf, Category.assoc, hχf, hjEf]
    · show jm ≫ AF.hom = (jE ≫ χ) ≫ AF.hom
      rw [hjs, Category.assoc, hχs, ← Category.assoc, hjEs, Category.assoc, hαΩ]
  have hwE : LBIso L (LE.pull jE) :=
    LBIso.trans hL (pull_isLB hL₁ jm) (pull_isLB hLE jE) hw
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ jE ejm).symm
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend E Ω (algebraMap E Ω) AE AΩ jE LE L hAE hjE hLE hL hwE
  haveI := hAE.proper
  haveI := hAE.smooth
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension E Ω (algebraMap E Ω) AE AΩ jE hjE LE L hLE hL
    hwE hAΩ.proper hAmp hKT
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim E AE hAE
  have hrig : Out.Rigidified AE LE := by
    have : Subsingleton (𝟙_ (Over (Sp E))).left := inferInstanceAs (Subsingleton (PrimeSpectrum E))
    exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum E) (pull_isLB hLE _)
  let A₁ : Out.PolAV (Sp E) :=
    { A := AE, isAb := hAE, g := g, smoothDim := hg, L := LE, isLB := hLE, rigid := hrig,
      sym := hd.2.1 hS, ample := ha.2.1, ktriv := ha.2.2 }
  refine ⟨E, inferInstance, inferInstance, hEf, hEg, A₁, Iso.refl _, ?_, fun κ' hκ' => ?_⟩
  · show IsMonHom (𝟙 AE); infer_instance
  have e' : κ' = χ₂ ≫ κF := by
    have h := GlobalTheory.ZM.SiegPull.isSquare_comp hχ₂ hκF
    rw [hχf] at h
    exact GlobalTheory.LamPull.isSquare_unique hκ' h
  have hLE' : (LE.pull (𝟙 AE.left)).IsLB := pull_isLB hLE _
  have k₁ : LBIso (abelian₂ AE (LE.pull (𝟙 AE.left))) ((abelian₂ AF L₁).pull χ₂) :=
    GlobalTheory.LamPull.lbIso_lam_pull hχ hL₁ hLE' (GlobalTheory.ArcDataDescent.lbIso_pull_pull hL₁ χ (𝟙 _) (Category.id_comp χ).symm) hχ₂
  have k₂ : LBIso ((PP.pull κF).pull χ₂) (PP.pull κ') := GlobalTheory.ArcDataDescent.lbIso_pull_pull hPPlb κF χ₂ e'
  exact LBIso.trans (DVR.linComb_isLB _ hLE' _ _) (pull_isLB hΛF _) (pull_isLB hPPlb _) k₁
    (LBIso.trans (pull_isLB hΛF _) (pull_isLB hNF _) (pull_isLB hPPlb _) isoE k₂)

end GlobalTheory.MumDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamilyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B))), P.IsLB → τ.IsGen → ∀ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ, DescCompat (q ▷ B).left P φ → ∃ u : Γ(pullback (q ▷ B).left (q ▷ B).left, ⊤)ˣ, NormAlong q P τ (twist (q ▷ B).left P φ u) := by
  first | exact @GlobalTheory.DescNormU.normalise | exact GlobalTheory.DescNormU.normalise | (intros; apply GlobalTheory.DescNormU.normalise <;> assumption)
end

