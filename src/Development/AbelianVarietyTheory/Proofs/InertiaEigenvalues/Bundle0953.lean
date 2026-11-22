import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0949
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0950
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0951
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFrameIntAnyField
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkAnyField

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39 GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem pow_eq_one_of_mem {T : Over Xo.X} {C : Subgroup (T ⟶ Xo.univ.t.G)} (hpP : (p : 𝓞 E) ∈ P)
    (hC : Xo.univ.t.HeckeKer T Dw P p i C) {u : T ⟶ Xo.univ.t.G} (hu : u ∈ C) : u ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => hC.2.2.1 hu a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
  rwa [map_natCast] at this

theorem exists_isPair (hP : IsHeckePrime H l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' C f.left ψp) : ∃ f', IsPair (p ^ 2) f f' := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM hC h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib x
  have hB := isAbelianScheme_fib x'
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv x'
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    exact ρ.injective (by rw [map_pow, map_one, pow_eq_one_of_mem hpP hC hx])
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo x) ^ m) (𝟙 _) ≫ μ[Fib Xo x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨π, hom, homπ, hπ, ?_, lin, fun a => ?_⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

section Ext

variable {K L : Type} [Field K] [Field L] (φ : K →+* L)

def down {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) : (Over.mk w : Over Xo.X) ⟶ Over.mk x :=
  Over.homMk (spMap φ) hw.symm

def up {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) :
    (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk w ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun z => down φ hw ≫ z) fun _ _ => MonObj.comp_mul _ _ _

variable {φ} {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}

theorem up_injective (hw : w = spMap φ ≫ x) : Function.Injective (up φ hw) := fun _ _ h =>
  TorsionRat.comp_injective φ (down φ hw) rfl h

theorem weilIs_up (hw : w = spMap φ ≫ x) {n : ℤ} {a b : Over.mk x ⟶ Xo.univ.t.G} {v : Kˣ}
    (h : WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v)) :
    WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (up φ hw a) (up φ hw b) (unitOn (Units.map φ.toMonoidHom v)) := by
  have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds (UnivPol.pol Xo).isAb Xo.univ.t.PP.isLB (down φ hw) h
  have e' : Units.map (down φ hw).left.appTop.hom.toMonoidHom (unitOn v) = unitOn (Units.map φ.toMonoidHom v) :=
    Units.ext (congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  exact e' ▸ h₁

variable [IsAlgClosed K]

theorem exists_weilIs {n : ℕ} (hn : 0 < n) {a b : Over.mk x ⟶ Xo.univ.t.G} (ha : a ^ n = 1) (hb : b ^ n = 1) :
    ∃ v : Kˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, rfl⟩ := (I.onto _ hn a).1 ha
  obtain ⟨b, rfl⟩ := (I.onto _ hn b).1 hb
  exact ⟨_, I.isom _ hn a b⟩

variable [IsAlgClosed L]

theorem exists_up (hw : w = spMap φ ≫ x) {n : ℕ} (hn : 0 < n) (u : Over.mk w ⟶ Xo.univ.t.G) (hu : u ^ n = 1) :
    ∃ a, a ^ n = 1 ∧ up φ hw a = u :=
  TorsionRat.exists_eq_comp_of_isAlgClosed Xo hn φ (down φ hw) rfl u hu

theorem heckeKer_down (hw : w = spMap φ ≫ x) (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C) :
    Xo.univ.t.HeckeKer (Over.mk x) Dw P p i (C.comap (up φ hw)) := by
  refine GlobalTheory.HkSetDesc.heckeKer_comap Dw P p i Xo.univ.t (down φ hw) (up φ hw) (fun _ => rfl) hpP (up_injective hw)
    (fun u hu => (exists_up hw (pow_pos hp 2) u hu).imp fun _ h => h.2) (fun a b ha hb h => ?_) C hC
  obtain ⟨v, hv⟩ := exists_weilIs (pow_pos hp 2) ha hb
  rw [Nat.cast_pow] at hv
  have e := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ 1 (weilIs_up hw hv)
    (by rw [unitOn, map_one]; exact h)
  obtain rfl : v = 1 := Units.ext (φ.injective ((congrArg Units.val e).trans (map_one φ).symm))
  rwa [unitOn, map_one] at hv

theorem isHkIsog_up (hP : IsHeckePrime H l P p) (hw : w = spMap φ ≫ x)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' (C.comap (up φ hw)) f.left ψp) {g : Fib Xo w ⟶ Fib Xo w'} {g' : Fib Xo w' ⟶ Fib Xo w}
    (hg : IsBC φ f g) (hgg : IsPair (p ^ 2) g g') : ∃ χp, IsHkIsog p w w' C g.left χp := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  have hw' := hg.2.1
  obtain ⟨⟨hfin, -, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM
    (heckeKer_down hw hp.pos hpP hC) h
  obtain ⟨hs, h0, hf, -, -, hker, hweil, hlev⟩ := h
  obtain ⟨π, p₁, p₂, hπ⟩ := PairBC.exists_proj Xo.univ.t.G x w hw
  obtain ⟨π', p₁', p₂', hπ'⟩ := PairBC.exists_proj Xo.univ.t.G x' w' hw'
  have sq := hg.2.2 π π' p₁ p₂ p₁' p₂'
  have cart : IsPullback π g.left f.left π' := by
    refine IsPullback.of_bot ?_ sq.symm hπ'.1
    rw [Over.w g, Over.w f]
    exact hπ.1
  have : IsFinite g.left := MorphismProperty.of_isPullback (P := @IsFinite) cart hfin
  have : Surjective g.left := MorphismProperty.of_isPullback (P := @Surjective) cart hsur
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv w
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv w'
  have := hgg.1
  have := hgg.2.1
  let m : (𝟙_ (Over (Sp L)) ⟶ Fib Xo w) →* (𝟙_ (Over (Sp L)) ⟶ Fib Xo w') :=
    MonoidHom.mk' (fun z => z ≫ g) fun a b => MonObj.mul_comp a b g
  let χ := σ.toMonoidHom.comp (m.comp ρ.symm.toMonoidHom)
  have hχ : ∀ u, χ (ρ u) = σ (u ≫ g) := fun u => congrArg (fun z => σ (z ≫ g)) (ρ.symm_apply_apply u)
  have hfib : ∀ u, fibPt _ u ≫ g.left = fibPt _ (χ u) := fun u => by
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [hχ, e₁, s₁]; rfl
  have hup : ∀ a, fibPt _ (up φ hw a) ≫ π = spMap φ ≫ fibPt _ a := fun a => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, p₁, fibPt, fibPt, pullback.lift_fst, pullback.lift_fst]; rfl
    · rw [Category.assoc, Category.assoc, p₂, fibPt, fibPt, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.id_comp, Category.comp_id]
  have key : ∀ a, χ (up φ hw a) = up φ hw' (ψp a) := fun a => by
    refine Over.OverMorphism.ext ?_
    have e := congrArg (fun q => fibPt _ (up φ hw a) ≫ q ≫ pullback.fst _ _) sq
    simp only [Category.assoc] at e
    rw [p₁', reassoc_of% (hfib (up φ hw a)), reassoc_of% (hup a), reassoc_of% (hf a), fibPt, fibPt,
      pullback.lift_fst, pullback.lift_fst] at e
    exact e
  have unit : ∀ {y : Sp K ⟶ Xo.X} {y' : Sp L ⟶ Xo.X} (hy : y' = spMap φ ≫ y) (a : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      toUnit _ ≫ a = up φ hy (toUnit _ ≫ a) := fun hy a => by
    show _ = down φ hy ≫ toUnit _ ≫ a
    rw [comp_toUnit_assoc]
  refine ⟨χ, by rw [hw, hw', Category.assoc, Category.assoc, hs], Over.w g, hfib, fun a u => ?_, fun v => ?_,
    Subgroup.ext fun u => ?_, fun n a b v hn hv => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [← e₂, hχ, hχ, ← s₂, Category.assoc, Category.assoc, hgg.2.2.2.2.1 a]
  · obtain ⟨v, rfl⟩ := σ.surjective v
    obtain ⟨b, hb⟩ := exists_lift_pt g.left v.left
    let u : 𝟙_ (Over (Sp L)) ⟶ Fib Xo w := Over.homMk b (by rw [← Over.w g, reassoc_of% hb, Over.w v])
    exact ⟨ρ u, (hχ u).trans (congrArg σ (Over.OverMorphism.ext hb))⟩
  · have mem : ∀ a, up φ hw a ∈ χ.ker ↔ up φ hw a ∈ C := fun a => by
      rw [MonoidHom.mem_ker, key, map_eq_one_iff _ (up_injective hw'), ← MonoidHom.mem_ker, hker, Subgroup.mem_comap]
    have tor : u ^ p ^ 2 = 1 → (u ∈ χ.ker ↔ u ∈ C) := fun hu => by
      obtain ⟨a, -, rfl⟩ := exists_up hw (pow_pos hp.pos 2) u hu
      exact mem a
    refine ⟨fun hu => (tor ?_).1 hu, fun hu => (tor (pow_eq_one_of_mem hpP hC hu)).2 hu⟩
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [MonoidHom.mem_ker, hχ, map_eq_one_iff _ σ.injective] at hu
    have e := congrArg (u ≫ ·) hgg.2.2.1
    simp only [← Category.assoc, hu, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
    rw [← map_pow, ← e, map_one]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero fun e => hp.one_lt.ne' (by simpa [e] using hn)
    obtain ⟨ta, tb⟩ := GlobalTheory.PairingLawsCompare.mem_tors_of_weilIs (UnivPol.pol Xo) n hv
    obtain ⟨a, ha, rfl⟩ := exists_up hw hn0 a ta
    obtain ⟨b, hb, rfl⟩ := exists_up hw hn0 b tb
    obtain ⟨v₀, hv₀⟩ := exists_weilIs hn0 ha hb
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ _ (weilIs_up hw hv₀) hv
    rw [key, key, ← map_pow]
    exact weilIs_up hw' (hweil n a b v₀ hn hv₀)
  · rw [unit hw, unit hw, key, key, (hlev p' hp' a).1, (hlev p' hp' a).2, ← unit, ← unit]
    exact ⟨rfl, rfl⟩

end Ext

theorem exists_hkRelFr_down (hP : IsHeckePrime H l P p) {K L : Type} [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {y : FrPt Xo c K} {w z : FrPt Xo c L}
    (hw : FrMap φ y w) (C : hkKer (Xo := Xo) P p i L w) (hz : hkRelFr P p i (hkTr Xo c p) L w C z) :
    ∃ (C₀ : hkKer (Xo := Xo) P p i K y) (z₀ : FrPt Xo c K), hkRelFr P p i (hkTr Xo c p) K y C₀ z₀ ∧ FrMap φ z₀ z := by
  have hp := hP.2.2.1.pos
  obtain ⟨hT, hU⟩ := GlobalTheory.T.heckeIsogeny_thetaGenerator_transport E H Dw l Xo c P p i hP
  let C₀ : hkKer (Xo := Xo) P p i K y := ⟨_, heckeKer_down hw.1 hp hP.2.2.2.1 C.2⟩
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.HeckePointLaw.exists_hkRelFr hP hT K y C₀
  obtain ⟨z₁, hz₁⟩ := exists_frMap φ z₀
  refine ⟨C₀, z₀, hz₀, ?_⟩
  obtain ⟨ψ, ψp, h, hLie, hTr⟩ := hz₀
  let f : Fib Xo y.x ⟶ Fib Xo z₀.x := Over.homMk ψ h.2.1
  obtain ⟨f', hf⟩ := exists_isPair (f := f) hP C₀.2 h
  obtain ⟨g, hg⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom y.x z₀.x w.x z₁.x).1 hw.1 hz₁.1 f
  obtain ⟨g', hg'⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom z₀.x y.x z₁.x w.x).1 hz₁.1 hw.1 f'
  have e : spMap (algebraMap K K) = 𝟙 (Sp K) := Spec.map_id _
  have hR : AllRat Xo y.x (p ^ 2) := TorsionRat.allRat_of_isAlgClosure Xo (pow_pos hp 2) (F := K) y.x y.x
    (by rw [e, Category.id_comp]) fun a _ => ⟨a, by rw [e, Category.id_comp]⟩
  obtain ⟨a₁, a₂, a₃⟩ := (hkWith_iff φ hp hw hz₁ hg hg' hR).1 ⟨hf, hLie, hTr⟩
  obtain ⟨χ, hχ⟩ := isHkIsog_up (f := f) hP hw.1 C.2 h hg a₁
  rwa [GlobalTheory.HeckePointLaw.hkRelFr_unique hP hU L w C z z₁ hz ⟨g.left, χ, hχ, a₂, a₃⟩]

theorem isIntegralUpToUnits_up {cls : PtClass Xo c} {T : CDVR} {io : c.F →+* T.Fr} {K L : Type} [Field K] [Field L]
    [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {k : T.Fr →+* K} {z₀ : FrPt Xo c K} {z : FrPt Xo c L}
    (hz : FrMap φ z₀ z) (h : IsIntegralUpToUnits cls T io k z₀) :
    IsIntegralUpToUnits cls T io (φ.toRingHom.comp k) z := by
  obtain ⟨T', i, hi, j, rfl, y', h₁, h₂, w, u, hw, hb⟩ := h
  letI := (i.comp io).toAlgebra
  obtain ⟨w', hw'⟩ := exists_frMap φ w
  exact ⟨T', i, hi, φ.comp j, rfl, y', h₁, h₂, w', u, frMap_comp hw hw' fun _ => rfl, frBor_map φ hb hw' hz⟩

end GlobalTheory.HkAnyField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.WtDescent

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    GlobalTheory.T.isAlgWeight_of_contragredient_highestWeight L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := GlobalTheory.T.exists_irreducible_algebraicWeight_subrep L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := GlobalTheory.T.nonzero_matrix_intertwiner_descends_to_subfield K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparableStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_match_of_dense_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ), IsTest f' → IsTest f → ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧ (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  first | exact @GlobalTheory.JR.DenseMatch.match_of_dense | exact GlobalTheory.JR.DenseMatch.match_of_dense | (intros; apply GlobalTheory.JR.DenseMatch.match_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNormStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | exact GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | (intros; apply GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  first | (exact @GlobalTheory.RamShift.condOne_condExp) | (exact GlobalTheory.RamShift.condOne_condExp) | (intros; apply GlobalTheory.RamShift.condOne_condExp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacterStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  first | exact @GlobalTheory.JSW.whit_mul_locGL_tD_shift | exact GlobalTheory.JSW.whit_mul_locGL_tD_shift | (intros; apply GlobalTheory.JSW.whit_mul_locGL_tD_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDualityStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  first | exact @GlobalTheory.TwistedPlaceBound.closing | exact GlobalTheory.TwistedPlaceBound.closing | (intros; apply GlobalTheory.TwistedPlaceBound.closing <;> assumption)
end

