import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedOverring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamValTauAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.LamRigid GlobalTheory.LamBiext

namespace GlobalTheory.MumfordE8Bimultiplicative

theorem lamVal_law₁ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B]
    (M₀ : RigLB B₀) (M : RigLB B) (c₀ : CubicalStr B₀ M₀) (c : CubicalStr B M) (hB₀ : IsAbelianScheme B₀)
    (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b]
    (w : LB.Iso (abelian₂ B₀ M₀.L) ((abelian₂ B M.L).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left))
    (hw : w.IsGen)
    (hn : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι),
      Good M.L z J → Good M₀.L z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1)
    (T : Over S) (x x' y : T ⟶ B₀) (z : T.left) (J : (T.left ⟶ B.left) → M.L.ι) (J' : (T.left ⟶ B₀.left) → M₀.L.ι)
    (hJ : Good M.L z J) (hJ' : Good M₀.L z J') :
    GlobalTheory.PolDeg.lamVal w (lift (x * x') y).left z J J' * cubV c₀ z J' x x' y =
      cubV c z J (x ≫ a) (x' ≫ a) (y ≫ b) * GlobalTheory.PolDeg.lamVal w (lift x y).left z J J' *
        GlobalTheory.PolDeg.lamVal w (lift x' y).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B M.L).IsLB := DVR.linComb_isLB _ M.isLB _ _
  have hL' : (abelian₂ B₀ M₀.L).IsLB := DVR.linComb_isLB _ M₀.isLB _ _
  let β₂ : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  have Hlam : ∀ {T₀ : Over S} (p q : T₀ ⟶ B₀) {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift p q).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h ((p ≫ a) * (q ≫ b)).left * (h (p ≫ a).left)⁻¹ * (h (q ≫ b).left)⁻¹ *
          h (1 : T₀ ⟶ B).left := fun p q U _ h => by
    rw [GlobalTheory.MumRigidZero.lift_comp_left]; exact prod_lam (p ≫ a) (q ≫ b) h
  obtain ⟨l₁, l₂, hl₁, hl₂, cl₁, cl₂, vl⟩ := exists_laws M₀ c₀
  let φ3 := law1φ B₀ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2)
  let β₃ : (G3 B₀).left ⟶ (G3 B).left := (lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have e₁ := prod_cub (x3 B₀ 0 ≫ a) (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b) h
      have e₂ := prod_law₁ (x3 B₀ 0) (x3 B₀ 1) (x3 B₀ 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at e₂
      simp only [Over.id_left, Category.id_comp, Hlam, MonObj.mul_comp] at e₂
      rw [e₁, prod_flat, e₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  have ht₃ := nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃
  have Ft3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
      val (L := abelian₂ B M.L) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) (lift p (lift p' q)).left z₀ (ind B J₀) =
        cubV c z₀ J₀ (p ≫ a) (p' ≫ a) (q ≫ b) := by
    intro T₀ p p' q z₀ J₀ hJ₀
    show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
    rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
    simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
    rw [hv₃ _ _ z₀ J₀ hJ₀]
    refine (val_pull hJ₀ _ _ _).trans ?_
    refine congrArg (fun r => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t r z₀ J₀) ?_
    show (lift p (lift p' q) ≫ lift (x3 B₀ 0 ≫ a) (lift (x3 B₀ 1 ≫ a) (x3 B₀ 2 ≫ b))).left =
      (lift (p ≫ a) (lift (p' ≫ a) (q ≫ b))).left
    simp only [comp_lift, ← Category.assoc, cartesian_lift_three_comp_projection]
    rfl
  have Fa3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      Good M₀.L z₀ J₀' → val (L := abelian₂ B₀ M₀.L) l₁ (lift p (lift p' q)).left z₀ (ind B₀ J₀') = cubV c₀ z₀ J₀' p p' q := by
    intro T₀ p p' q z₀ J₀' hJ₀'
    show val (L := lamLB M₀) l₁ _ z₀ (ind B₀ J₀') = _
    rw [(vl z₀ (ind B₀ J₀') (good_ind hJ₀') J₀' hJ₀').1 p p' q, adj_ind M₀.isLB hJ₀', adj_ind M₀.isLB hJ₀',
      adj_ind M₀.isLB hJ₀']
    simp
  have Fp3 : ∀ {T₀ : Over S} (p p' q : T₀ ⟶ B₀) (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι)
      (J₀' : (T₀.left ⟶ B₀.left) → M₀.L.ι),
      pw w φ3 lawε (lift p (lift p' q)).left z₀ (fun k => ind B J₀ ((lift p (lift p' q)).left ≫ φ3 k ≫ β₂))
        (fun k => ind B₀ J₀' ((lift p (lift p' q)).left ≫ φ3 k)) =
        lamVal w (lift (p * p') q).left z₀ J₀ J₀' * (lamVal w (lift p q).left z₀ J₀ J₀')⁻¹ *
          (lamVal w (lift p' q).left z₀ J₀ J₀')⁻¹ := by
    intro T₀ p p' q z₀ J₀ J₀'
    rw [pw_eq]; exact prod_law₁ p p' q (fun χ => lamVal w χ z₀ J₀ J₀')
  have sj3 : Function.Surjective ((snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom).appTop.hom :=
    surj_comp (surj_snd hG hB₀ _) (surj_comp (surj_snd hG hB₀ _) (hG _ _ hB₀).2)
  have he3 : (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1)).left ≫ (snd B₀ (B₀ ⊗ B₀)).left ≫ (snd B₀ B₀).left ≫ B₀.hom =
      𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S) ⟶ B₀) (lift 1 1))
  have R3 := rigid_pw w hw hL hL' φ3 lawε hl₁ ht₃ _ _ he3 sj3 (fun y₀ => by
    obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt M.isLB y₀
    obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt M₀.isLB y₀
    refine ⟨ind B J₁, ind B₀ J₁', good_ind hJ₁, good_ind hJ₁', ?_⟩
    rw [Ft3 (T₀ := 𝟙_ (Over S)) 1 1 1 y₀ J₁ hJ₁, Fp3, Fa3 1 1 1 y₀ J₁' hJ₁', GlobalTheory.MumRigidZero.one_comp_hom a,
      _root_.mul_one, (isCub_cubV c hJ₁).face, (isCub_cubV c₀ hJ₁').face, hn (𝟙_ (Over S)) y₀ J₁ J₁' hJ₁ hJ₁']
    simp)
  have E3 := R3 T.left (lift x (lift x' y)).left z (ind B J) (ind B₀ J') (good_ind hJ) (good_ind hJ')
  rw [Ft3 x x' y z J hJ, Fp3, Fa3 x x' y z J' hJ'] at E3
  rw [E3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumfordE8Bimultiplicative

end

open GlobalTheory.Mum GlobalTheory.Mum.E8Ring

namespace GlobalTheory.MumfordE8Bimultiplicative

end GlobalTheory.MumfordE8Bimultiplicative
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat.UnifLat

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_tau {o B X : Type} [CommRing o] [CommRing B] [AddCommGroup X] (b : o →+* B) (ζ : oˣ) {L : ℕ}
    (hL : 0 < L) (hζ : ζ ^ L = 1) (c : X →+ ZMod L) :
    ∃ τ : Multiplicative X →* Bˣ,
      (∀ χ, τ χ = Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ∧ τ ^ L = 1 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hu : Units.map b.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
  refine ⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val
            map_one' := by simp
            map_mul' := fun χ χ' => by
              simp only [toAdd_mul, map_add, ZMod.val_add]
              rw [← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩
  refine MonoidHom.ext fun χ => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

end GlobalTheory.Poinc.FibLat.UnifLat

open GlobalTheory.Poinc.FibLat.UnifLat in

theorem GlobalTheory.Poinc.FibLat.latAt_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β'
    hβ hβ' hF' K _ _ _ iK hiK hKf c hc
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsSeparated Gu.hom := hGu.separated
  haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance
  obtain ⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V' :=
    ⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0 := fun x hx => by
    rw [zero_add, pow_one] at hx
    exact (hr _).2 (map_nonunit fV x hx)
  obtain ⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left),
      IsGrpPullback G₀ G' (spMap r) ψ := ⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩
  have h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β) := (hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl
  have hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β') := hψ.comp hβ'
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL
  refine ⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β',
    GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩
  · show ξ ((spMap r) (closedPoint (ResidueField V'))) = _
    rw [spMap, Spec_closedPoint]
  · rw [Category.assoc, hξ, spMap_comp_eq a r]
  refine ⟨fun e => ?_, fun t => ?_⟩
  · obtain ⟨F', hF1, hF2⟩ := hF' e
    have w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r := by
      rw [Category.assoc, Over.w F', hψ.1.w]
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left :=
      ⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
    have hE := hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀
      (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])
    have k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left =
        (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left := by
      rw [← Over.comp_left, hE]
    calc (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ (ψ ≫ β') ≫ (f e).left
        = (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ ≫ F'.left ≫ β' := by rw [hF2]; simp only [Category.assoc]
      _ = ((GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left) ≫ ψ ≫ β' := by
          rw [Category.assoc, reassoc_of% hF₀]
      _ = _ := by rw [k]
  · obtain ⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩ := hc t
    obtain ⟨τV, hτVv, hτV⟩ := exists_tau a ζ hL hζ (c t)
    obtain ⟨τκ, hτκv, hτκ⟩ := exists_tau (r.comp a) ζ hL hζ (c t)
    have hchar : ∀ χ, (τ χ : K) = iK (τV χ : V') := fun χ => by
      rw [hτVv]
      refine (hτ (Multiplicative.toAdd χ)).trans ?_
      simp
    have hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V') := fun χ => by
      rw [hτVv, hτκv]
      simp
    have hτL : τ ^ L = 1 := MonoidHom.ext fun χ => Units.ext (by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← MonoidHom.pow_apply, hτV]
      simp)
    have hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV :=
      (Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm
    obtain ⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _ :=
      ⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ hext
    obtain ⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _ :=
      ⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩
    have eσK : spMap iK ≫ σ = x' := hβ.1.hom_ext (by
        rw [Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx,
          hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])
      (by rw [Category.assoc, hσG, hx'1, Category.comp_id])
    have eσ'K : spMap iK ≫ σ' = x' := hβ'.1.hom_ext (by
        rw [Category.assoc, hσ'β]; exact ValAt.unique (hv.comp (spMap iK)) hx'3)
      (by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])
    haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩
    have eσ : σ = σ' := ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK)
      (eσK.trans eσ'K.symm)
    let φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ :=
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X,
        ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ)) :=
      ⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by
        show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _
        rw [MulEquiv.apply_symm_apply]; rfl⟩
    have hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom =
        (Over.mk (spMap (RingHom.id (ResidueField V')))).hom := by
      rw [Over.w z]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))
      rw [CommRingCat.ofHom_id, Spec.map_id]
    let z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X :=
      Over.homMk z.left hz1w
    have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := fun χ =>
      (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)
    have e3 := hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ
      z₁ (RingHom.id_comp _).symm hz₁
    have e2 := hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ
    have ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ := hβ.1.hom_ext
      (by
        rw [Category.assoc, Category.assoc, hσβ, ← e2, e3]
        rfl)
      (by
        rw [Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc,
          Over.w (z ≫ _)]
        exact Category.id_comp _)
    refine ⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩
    rw [← Category.assoc, ez, eσ, Category.assoc, hσ'β]
    exact hv.comp (spMap r)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureDescends
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelDescend

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}

theorem push_injective (h : X₀.IsPullBy X b i) {T : Over S₀} {z z' : T ⟶ X₀.A}
    (e : pushPt h.grp.1.w z = pushPt h.grp.1.w z') : z = z' := by
  have e' : z.left ≫ i = z'.left ≫ i := congrArg (fun f => CommaMorphism.left f) e
  apply Over.OverMorphism.ext
  exact h.grp.1.hom_ext e' (by rw [Over.w z, Over.w z'])

theorem push_surjective (h : X₀.IsPullBy X b i) {T : Over S₀} (y : Over.mk (T.hom ≫ b) ⟶ X.A) :
    ∃ z : T ⟶ X₀.A, pushPt h.grp.1.w z = y := by
  have hy : y.left ≫ X.A.hom = T.hom ≫ b := by simpa using Over.w y
  refine ⟨Over.homMk (h.grp.1.lift y.left T.hom hy) (h.grp.1.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.grp.1.lift_fst _ _ _

theorem push_mul (h : X₀.IsPullBy X b i) {T : Over S₀} (z z' : T ⟶ X₀.A) :
    pushPt h.grp.1.w (z * z') = pushPt h.grp.1.w z * pushPt h.grp.1.w z' := by
  apply Over.OverMorphism.ext
  exact (h.grp.2 T z z' _ _ rfl rfl).symm

theorem push_one (h : X₀.IsPullBy X b i) (T : Over S₀) :
    pushPt h.grp.1.w (1 : T ⟶ X₀.A) = 1 := by
  have e := push_mul h (1 : T ⟶ X₀.A) 1
  rw [_root_.mul_one] at e
  exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)

theorem push_pow (h : X₀.IsPullBy X b i) {T : Over S₀} (z : T ⟶ X₀.A) (n : ℕ) :
    pushPt h.grp.1.w (z ^ n) = pushPt h.grp.1.w z ^ n := by
  induction n with
  | zero => rw [_root_.pow_zero, _root_.pow_zero, push_one h]
  | succ n ih => rw [_root_.pow_succ, _root_.pow_succ, push_mul h, ih]

theorem push_pt_act (h : X₀.IsPullBy X b i) {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A))
    (hpq : ∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) {W : Scheme.{0}} (t₀ : W ⟶ S₀) (k : Fin 2) (a : 𝓞 F) :
    pushPt h.grp.1.w (toUnit (Over.mk t₀) ≫ α₀.pt k ≫ X₀.rm.act a) =
      toUnit (Over.mk (t₀ ≫ b)) ≫ q k ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  simp only [pushPt, Over.homMk_left, Over.comp_left, Over.toUnit_left, Over.mk_hom, Category.assoc,
    h.act a]
  rw [reassoc_of% (hpq k)]

end GlobalTheory.RealMult.LevelDescend

namespace GlobalTheory.RealMult

open LevelDescend in

theorem level_descend : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S₀ : Scheme.{0}}
    {X : Obj F 𝔠 S} {X₀ : Obj F 𝔠 S₀} {b : S₀ ⟶ S} {i : X₀.A.left ⟶ X.A.left}, X₀.IsPullBy X b i →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), ∃ t₀ : Sp Ω ⟶ S₀, t₀ ≫ b = t) →
    ∀ {N : ℕ} (α₀ : X₀.Level N) (q : Fin 2 → (𝟙_ (Over S) ⟶ X.A)), (∀ k, q k ^ N = 1) →
    (∀ k, (α₀.pt k).left ≫ i = b ≫ (q k).left) → Nonempty (X.Level N) := by
  intro F _ _ 𝔠 S S₀ X X₀ b i h hfac N α₀ q hq hpq
  refine ⟨{ pt := q, tors := hq, inj := ?_, surj := ?_ }⟩
  · intro Ω _ _ t a c e
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    apply α₀.inj Ω t₀ a c
    apply push_injective h
    rw [push_mul h, push_one h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨t₀, rfl⟩ := hfac Ω t
    obtain ⟨z, rfl⟩ := push_surjective h (T := Over.mk t₀) y
    have hz : z ^ N = 1 := by
      apply push_injective h
      rw [push_pow h, push_one h]
      exact hy
    obtain ⟨a, c, hac⟩ := α₀.surj Ω t₀ z hz
    refine ⟨a, c, ?_⟩
    rw [hac, push_mul h, push_pt_act h α₀ q hpq, push_pt_act h α₀ q hpq]

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelUnitThetaConstantNeZeroDividesAll
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem unit_ne_zero_dvd (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) :
    X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧
      ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
        algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraPeriodCoordinatesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_period_coordinates : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∃ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) ∧
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) ∧
      ∀ ω : X₀.Lie →ₗ[R] R, ∃ lam : Fin (Module.finrank ℚ (FR E)) → ℂ, ∀ v, ((ω v : R) : ℂ) = ∑ j, lam j * cd v j := by
  first | exact @GlobalTheory.LieCoord.exists_lieCoord_unif | exact GlobalTheory.LieCoord.exists_lieCoord_unif | (intros; apply GlobalTheory.LieCoord.exists_lieCoord_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCorrespondenceDifferentials
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem exists_detGen_coeff_algebraic : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  intro E _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hpb hv
  haveI := Obj.invertible_detOmega X₀
  obtain ⟨d, -, hd⟩ := finrank_eq_one_iff'.1 (Module.Invertible.finrank_eq_one Qb X₀.DetOmega)
  let δ₀ : X₀.DetGen := ⟨d, eq_top_iff.2 fun w _ ↦ Submodule.mem_span_singleton.2 (hd w)⟩
  obtain ⟨δ, hδ, -⟩ := hpb.existsUnique_detGen (algebraMap Qb ℂ) δ₀
  obtain ⟨δ₁, hδ₁⟩ := Obj.exists_detGen_holUnif (FR E) 𝔠 X _ U.u 1 one_ne_zero
  have hmem : δ.1 ∈ Submodule.span ℂ {δ₁.1} := by rw [δ₁.2]; exact Submodule.mem_top
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.1 hmem
  have hdet : U.IsDet δ.1 C := fun w W hW ↦ by
    rw [← hC, AlternatingMap.smul_apply, hδ₁ w W hW, smul_eq_mul, _root_.one_mul]
  refine ⟨δ₀, δ, C, hδ, hdet, ?_⟩
  have hW : ∀ j, U.u.IsDiff ((Matrix.diagonal fun j ↦ a (U.e j)) j) (v (U.e j)).hom := fun j ↦ by
    have h := (hv (U.e j)).2
    rw [Equiv.symm_apply_apply] at h
    convert h using 1
    ext k
    simp [Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  have h1 := hdet (fun j ↦ v (U.e j)) _ hW
  have h2 := hδ (fun j ↦ v₀ (U.e j)) (fun j ↦ v (U.e j)) fun j ↦ (hv (U.e j)).1
  rw [Matrix.det_diagonal, Equiv.prod_comp U.e a] at h1
  rw [← h1, h2]
  exact (mem_algebraicClosure_iff.1 (δ₀.1 fun j ↦ v₀ (U.e j)).2)

end GlobalTheory.LatJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibilityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), TiesB R F → TiesG T R κ v₀ O → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) ∧ Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false ∧ (R.toCx3 F).MLat false := by
  first | exact @GlobalTheory.PrimIn.liftTests_and_mLat_of_ties | exact GlobalTheory.PrimIn.liftTests_and_mLat_of_ties | (intros; apply GlobalTheory.PrimIn.liftTests_and_mLat_of_ties <;> assumption)
end

