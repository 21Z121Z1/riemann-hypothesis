import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPushedTraitPointLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorSecLocal

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem pow_comp_of_isMonHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem toric_torsion_section_overLocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H R _ _ _ t P k s hs1 hs2 hs3 X' _ ρ V _ _ ψ tV mV j _ t₀ m₀ h₀ m₀' hφ hpull
    U _ _ u hu hk τU τ h hτU hττ z hz
  have hg : spMap (u.comp ψ) = (Over.mk (spMap u)).hom ≫ spMap ψ := spMap_comp_ringHom ψ u
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv mV.cart (Over.mk (spMap u)) (spMap (u.comp ψ)) hg

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun m => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have e1 := hz (Multiplicative.toAdd m)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at e1
    rw [e1]
    have e2 : τU m ^ k = 1 := by rw [← MonoidHom.pow_apply, hτU, MonoidHom.one_apply]
    simp only [unitOn, ← map_pow, e2, map_one]
  have hx : s U (u.comp ψ) τ h = e (z ≫ j) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth U (spMap (u.comp ψ)) k hk _ _ ?_
      (ResidueField U) (residue U) inferInstance ?_
    · rw [hs1, ← map_pow, ← pow_comp_of_isMonHom, hzk, MonObj.one_comp, map_one]
    · let cU := residue U
      let τ₀ : Multiplicative P.D.toPre.X →* (ResidueField U)ˣ :=
        (Units.map (cU : U →* ResidueField U)).comp τ
      have h' : τ₀ ^ k = 1 := by
        refine MonoidHom.ext fun m => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        show Units.map _ (τ m) ^ k = 1
        rw [← map_pow, ← MonoidHom.pow_apply, h, MonoidHom.one_apply, map_one]
      have n1 := hs2 U (ResidueField U) (u.comp ψ) (cU.comp (u.comp ψ)) cU τ h τ₀ h' rfl (fun χ => rfl)
      let w₁ : Multiplicative X' →* Γ(Sp (ResidueField U), ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField U))).inv.hom.toMonoidHom).comp
          ((Units.map (cU : U →* ResidueField U)).comp τU)
      let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
        (GlobalTheory.splitTorusPointsEquiv _ X' _).symm w₁
      have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = w₁ (Multiplicative.ofAdd χ) := fun χ => by
        simp only [GlobalTheory.UU.chV, z₁, MulEquiv.apply_symm_apply]
      let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap _ ρ
      have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        apply Units.ext
        rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
          GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
          ← GlobalTheory.UU.chV_val, hz₁]
        show _ = (unitOn ((Units.map (cU : U →* ResidueField U)) (τ (Multiplicative.ofAdd χ)))).val
        rw [hττ]; rfl
      have hres : cU.comp u = (ResidueField.map u).comp (residue V) := by
        ext r; simp [cU, ResidueField.map_residue]
      have hcomp : cU.comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
        rw [← RingHom.comp_assoc, hres, RingHom.comp_assoc]
      have n2 := hs3 (ResidueField V) (ResidueField U) ((residue V).comp ψ) h₀ (cU.comp (u.comp ψ))
        (ResidueField.map u) t₀ m₀' τ₀ h' z₀ hcomp hz₀
      have hzz : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap cU ≫ z.left := by
        refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
        · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w z₁, Category.assoc,
            Over.w z]
          show spMap (ResidueField.map u) ≫ spMap (residue V) = spMap cU ≫ spMap u
          rw [← spMap_comp_ringHom, ← spMap_comp_ringHom, hres]
        · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
            Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← GlobalTheory.UU.chV_val,
            ← GlobalTheory.UU.chV_val, hz₁, hz]
          show (Scheme.ΓSpecIso _).inv.hom (cU (τU _).val) =
            (Spec.map (CommRingCat.ofHom cU)).appTop.hom ((Scheme.ΓSpecIso _).inv.hom (τU _).val)
          rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
      rw [he, ← n1, n2, hφ]
      have hz₀t : z₀ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus m₀.cart j := by
        rw [hpull, Category.assoc]
      rw [hz₀t, Over.comp_left, Category.assoc, ← Category.assoc (GlobalTheory.TorusPart.pullTorus m₀.cart j).left,
        GlobalTheory.TorusPart.pullTorus_left]
      have k3 := congrArg (· ≫ j.left ≫ mV.φ) hzz
      simp only [Category.assoc, Over.comp_left] at k3 ⊢
      exact k3
  rw [hx, he]

end GlobalTheory.TorSecLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPoints
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.TransUniq

open GlobalTheory.ModelCompare GlobalTheory.TransitionUnique

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}

theorem phi_eq_on_fibre {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {t : SAB H S'} {r : S' ⟶ S} (ν ν' : SABMap t o.t r)
    (hM : ∀ a, ∃ x : MonoidalCategoryStruct.tensorUnit (Over S') ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (o.eta a).left ∧ x.left ≫ ν'.φ = r ≫ (o.eta a).left)
    (hA : ∀ a, ∃ x : MonoidalCategoryStruct.tensorUnit (Over S') ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (o.etaA a).left ∧ x.left ≫ ν'.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (y : Sp k ⟶ S') {T : Scheme.{0}} (u : T ⟶ Sp k) (g : T ⟶ t.G.left)
    (hg : g ≫ t.G.hom = u ≫ y) : g ≫ ν.φ = g ≫ ν'.φ := by
  let o₁ := objOfSABMap o ν
  let n : ObjMap o₁ o r := objMapOfSABMap o ν
  let n' : ObjMap o₁ o r := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h'⟩
  obtain ⟨o₂, ⟨q⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) _ _ (r ≫ s) (y ≫ r ≫ s) y rfl rfl
    ((Category.comp_id _).symm.trans (congrArg ((y ≫ r ≫ s) ≫ ·) (Spec.map_id _).symm)) o₁
  obtain ⟨m, hm⟩ := ObjComp.objMap_comp n q
  obtain ⟨m', hm'⟩ := ObjComp.objMap_comp n' q
  have e : q.toSABMap.φ ≫ ν.φ = q.toSABMap.φ ≫ ν'.φ :=
    hm.symm.trans ((objMap_unique_of_field firstFiveLaws.1.serre m m').trans hm')
  have hp : IsPullback q.toSABMap.φ o₂.t.G.hom t.G.hom y := q.toSABMap.cart.1
  rw [← hp.lift_fst g u hg]
  exact (Category.assoc _ _ _).trans ((congrArg (hp.lift g u hg ≫ ·) e).trans (Category.assoc _ _ _).symm)

theorem trans_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i i₂ : Idx H p) (τ τ' : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) (mu' : SABMap (Y i₂).t (Y i).t τ'), i.c.F ≤ i₂.c.F → IsTrans i i₂ τ mu → IsTrans i i₂ τ' mu' → τ = τ' ∧ ∀ (k : Type) [Field k] (y : Sp k ⟶ (Xo i₂.l).XF i₂.c) (T : Scheme.{0}) (s : T ⟶ Sp k) (g : T ⟶ (Y i₂).t.G.left), g ≫ (Y i₂).t.G.hom = s ≫ y ≫ (Y i₂).j → g ≫ mu.φ = g ≫ mu'.φ := by
  intro E _ _ _ H Dw Xo p W Y i i₂ τ τ' mu mu' hc h h'
  obtain ⟨b, π, r, hb, h₁, h₂, hf, h₃, h₄, h₅⟩ := h
  obtain ⟨b', π', r', hb', h₁', h₂', hf', h₃', h₄', h₅'⟩ := h'
  obtain rfl : b = b' := RingHom.ext fun x => Subtype.ext (Subtype.ext ((hb x).trans (hb' x).symm))
  obtain rfl : τ = τ' := isTransition_unique E H Dw _ _ _ _ _ _ W (Y i) (Y i₂) b τ τ' hc hb
    ⟨π, mu, r, h₁, h₂, hf, h₃, h₄, h₅⟩ ⟨π', mu', r', h₁', h₂', hf', h₃', h₄', h₅'⟩
  refine ⟨rfl, fun k _ y T s g hg => ?_⟩
  have := mono_spMap_subtype (i.c.V W)
  have := (Y i).jQ_open
  have : Mono (Y i).j := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j
    infer_instance
  obtain rfl : r = r' := by rw [← cancel_mono (Y i).j, ← h₃, ← h₃']
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp (Y i₂).m mu' h₃'
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel (Y i).m n' r rfl
  have hp : IsPullback (Y i₂).m.φ (Y i₂).oF.t.G.hom (Y i₂).t.G.hom (Y i₂).j := (Y i₂).m.cart.1
  have hg' : g ≫ (Y i₂).t.G.hom = (s ≫ y) ≫ (Y i₂).j := by rw [hg, Category.assoc]
  have e := phi_eq_on_fibre (Y i).oF ν ν'
    (fun a => ⟨_, LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a),
      LevelCover.sec_cancel ν' (Y i).m _ _ (by rw [hν', hn']; exact h₄' a)⟩)
    (fun a => ⟨_, LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a),
      LevelCover.sec_cancel ν' (Y i).m _ _ (by rw [hν', hn']; exact h₅' a)⟩)
    y s (hp.lift g (s ≫ y) hg') (hp.lift_snd _ _ _)
  rw [← hp.lift_fst g (s ≫ y) hg', Category.assoc, Category.assoc, ← hn, ← hn', ← hν, ← hν', ← Category.assoc, e,
    Category.assoc]

end GlobalTheory.TransUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartsHyperspecialStabiliseLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

namespace GlobalTheory.Mem.Top.KerTwLv

set_option maxHeartbeats 4000000 in

theorem hyp_charts_tw : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      (Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T) →
      ∀ (Cd : GlobalTheory.Mem.Top.KerTwLv.ChData tt.ch t.g.herm u ((w.D Z).what₂.muAt v) v hg) j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.HypTJ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) ∧
        Formalism.MainNotions.G.CmpJ.PStabEq.HypTJC ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β) := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ Fl hfl _ u v hg hμ tt _ hok Cd j hj β
  exact ⟨GlobalTheory.Port.hypTJ_stepLevelQ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β)
      (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) _ hj β) rfl rfl (GlobalTheory.Port.not_dvd_g hg) hok.1,
    GlobalTheory.Port.hypTJC_stepLevelQ ((Cd.Lc t.Gt (Fl u v hg) (hfl u v hg).1 j hj).t β)
      (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) _ hj β) rfl rfl⟩

end GlobalTheory.Mem.Top.KerTwLv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.TwoMarkings

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ}

theorem linearIndependent_dirs {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ}
    {y : Sp ℂ ⟶ Xo.XF c} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hy : y ≫ pullback.fst _ _ = Fu.u i P) (hj : y ≫ Z.jQ = a.1.1)
    {v₀ : Letter Dw → (Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left)}
    (h1 : ∀ z, v₀ z ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (h2 : ∀ z, v₀ z ≫ Z.m.φ = a.2.v z.1 z.2)
    (h3 : ∀ z, IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ z ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have hty : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ z.1 (h3 z)).1 fun b =>
      (eig_iff Z.m0.toSABMap (h1 z) b _).2 ((eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 0
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [(t1 _ _ hv).1, ← hy, Category.assoc])
  rw [Fintype.linearIndependent_iff]
  rintro cf hc ⟨τ, k⟩
  have hb := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hy k1).1 (t1 _ _ hv)))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1
      ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ τ hv).2 (fun j hj => absurd rfl hj) b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have hcomb : ∀ d : Fin (Dw.mult τ) → ℂ, ∑ k, d k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ) d (v' ≫ Z.m.φ) := fun d hd =>
    (comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) d k1).2 ((comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) d k1).1
      ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _ _ (fun k => h3 ⟨τ, k⟩) d _).2 (hd ▸ hv)))
  have hτ : ∑ k, cf ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    have hz : ∀ ρ, (e j).1 ≠ ρ → (∑ k, cf ⟨ρ, k⟩ • W ⟨ρ, k⟩) j = 0 := fun ρ hρ => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Pi.smul_apply, by_contra fun h => hρ (hty ⟨ρ, k⟩ j h), smul_zero]
    by_cases h : (e j).1 = τ
    · have := congrFun hc j
      rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single τ (fun ρ _ hρ => hz ρ (h ▸ hρ.symm)) (by simp)] at this
      exact this
    · exact hz τ h
  exact congrFun (hb.unique (hcomb _ hτ) (hcomb 0 (by simp))) k

theorem per_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a
  haveI := Z.jQ_open
  refine ⟨?_, ?_⟩
  · rintro i j Q Q' ⟨P, W, y, hP, hy, hj, -⟩ ⟨P', W', y', hP', hy', hj', -⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    exact Fu.disj i j P P' hP hP' (hy.symm.trans hy')
  · rintro i Q Q' ⟨P, W, y, hP, hy, hj, hv, hQ⟩ ⟨P', W', y', hP', hy', hj', hv', hQ'⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    choose v₀ h1 h2 h3 using hv
    choose v₁ k1 k2 k3 using hv'
    obtain rfl : v₀ = v₁ := funext fun z =>
      Z.m.cart.1.hom_ext ((h2 z).trans (k2 z).symm) ((h1 z).trans (k1 z).symm)
    obtain ⟨gam, h, g1, g2, g3, g4⟩ := (Fu.fibre i P P' hP hP').1 (hy.symm.trans hy')
    have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
      LinearMap.toMatrix'_mulVec _ z
    obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ Fu i P P' gam
      (LinearMap.toMatrix' h.toLinearMap) hP hP' g1 g2 g3 (fun a => by rw [hm, g4])
    simp only [hm] at h5
    obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P' hP'
    have hW : ∀ z, h (W z) = W' z := fun z => (t3 _ (t1 _ _ (k3 z))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ Fu i P hP i P' h.toLinearMap hP' h5 _ _).1 (h3 z)) (k3 z)
    refine ⟨gam, g1, g2, fun v => funext fun z => ?_⟩
    refine Fintype.linearIndependent_iffₛ.1 (linearIndependent_dirs hP' hy' hj' k1 k2 k3) _ _ ?_ z
    rw [← hQ', g4, hQ, map_sum]
    simp only [map_smul, hW]

end GlobalTheory.ShFam.Hor.TwoMarkings
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open CategoryTheory.Limits

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (y₀ : FrPt Xo c (Formalism.L2.Pj.CAt σ)), cxPt Z y₀ ∈ ch.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ ch.e (cxPt Z y₀) ∈ B ∧ B ⊆ ch.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∀ y : FrPt Xo c (Formalism.L2.Pj.CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch y₀ hy₀
  have := Z.jQ_open
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm ch
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.e.target | ⊤ ≤ (ch.e.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  have hb₀ : ch.e (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.e.map_source hy₀, ?_⟩
    rw [ch.e.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.e.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.e.symm b).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift d (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (ch.e (cxPt Z y₀)))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb y hy => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h1 : w b = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y :=
      (cancel_mono Z.jQ).1 ((hw b hb1).trans (congrArg Subtype.val hy))
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    rw [h2, h1]
    exact GlobalTheory.ShFam.ptF_fst y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VanishingIdealComapOfIsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace

namespace GlobalTheory

open Scheme.IdealSheafData in

theorem vanishingIdeal_comap_of_isOpenImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (B : Closeds X) (B' : Closeds A), (∀ x : A, x ∈ B' ↔ g x ∈ B) → (Scheme.IdealSheafData.vanishingIdeal B).comap g = Scheme.IdealSheafData.vanishingIdeal B' := by
  intro A X g _ B B' h
  have hB : (vanishingIdeal B).support = B := by
    ext x
    simp
  have hr : (vanishingIdeal B).radical = vanishingIdeal B := by
    rw [← vanishingIdeal_support, hB]
  have hs : ((vanishingIdeal B).comap g).support = B' := by
    ext x
    simp [support_comap, h]
  rw [← hs, vanishingIdeal_support]
  ext U : 2
  rw [radical_ideal, ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical, ← radical_ideal, hr]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNegStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNegStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ, rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  first | exact @GlobalTheory.swap_odd_dvd | exact GlobalTheory.swap_odd_dvd | (intros; apply GlobalTheory.swap_odd_dvd <;> assumption)
end

