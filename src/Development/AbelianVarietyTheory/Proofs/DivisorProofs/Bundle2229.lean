import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0117
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifTrait

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 1000000 in

theorem exists_intFr_frBor (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt) (hzs : z ≫ pullback.snd _ _ = spMap io) :
    letI := io.toAlgebra
    ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1 := by
  let _ := io.toAlgebra
  intro y₀ hy0
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T io O β Y yt z hz hzs _ m
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨x₀, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ := y₀
  change x₀ = z ≫ pullback.fst _ _ at hy0
  subst hy0
  obtain ⟨ub, u, hub, htan, heig, hbas, htri⟩ := lieFree Xo c T io _ t' _ m1 m2 hx u₀ htan₀ heig₀ hbas₀
  obtain ⟨θ, s, hθ, hmatch, hgen, a, ha⟩ :=
    GlobalTheory.DepthSum.thetaFrame_trait Xo c T io O β Y yt z hz hzs _ m t' m1 m2 s₀ hgen₀
  let y : FrPt Xo c T.Fr := ⟨z ≫ pullback.fst _ _, hx, u, htan, heig, hbas, s, hgen⟩
  choose cf hcf using htri
  let tt : Ix Dw → T.Frˣ := fun o => match o with
    | none => a
    | some p => (hcf p.1 p.2).1.unit
  have hFB : FrBor tt ⟨z ≫ pullback.fst _ _, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ y := by
    refine ⟨rfl, fun τ i => ⟨cf τ i, (hcf τ i).1.unit_spec.symm, (hcf τ i).2.1, (hcf τ i).2.2⟩, 𝟙 _,
      Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    change (Scheme.Hom.appLE (𝟙 (Gx (z ≫ pullback.fst _ _))) _ _ h).hom
      (scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i) = s.f i
    rw [ha i, Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp, show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨⟨y, GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T.Fr y, _, t', m1, m2, ⟨ub, hub⟩, θ, hθ, hmatch⟩, tt, hFB⟩

end Frames

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

section Split

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem charZero_residue_of_map {K : Type} [Field K] [CharZero K] (V : Type) [CommRing V] [IsLocalRing V]
    (f : Sp V ⟶ Sp K) : CharZero (ResidueField V) :=
  charZero_of_injective_ringHom ((residue V).comp (Spec.preimage f).hom).injective

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, Sx, ⟨d⟩⟩ := GlobalTheory.UnifAfterExt.exists_finite_split _ h₀
  have : Algebra.IsSeparable (ResidueField W) k' := inferInstance
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, -, -, e, he⟩ := GlobalTheory.unramExt W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) Sx _ d)⟩

end Split

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

open IsLocalRing

set_option maxHeartbeats 1000000 in

theorem exists_ext_intFr_unif : Hypotheses2 → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  intro _ E _ _ _ H Dw l Xo c TF T io
  letI := io.toAlgebra
  intro P w hw
  have hz : FlagMod.frX P ≫ TF.Y.j = spMap (algebraMap T.V T.Fr) ≫ w := by
    rw [hw, (TF.X.lies_ptY P).1]
  have hzs : FlagMod.frX P ≫ pullback.snd _ _ = spMap io := FlagMod.frX_snd P
  obtain ⟨y₀, tt, hB⟩ := exists_intFr_frBor T io c.F (RingHom.id c.F) TF.Y w (FlagMod.frX P) hz hzs P
    (FlagMod.frX_fst P).symm
  obtain ⟨G₀, ⟨m₀⟩⟩ : ∃ G₀ : SAB H (Sp T.V), Nonempty (SABMap G₀ TF.Y.t w) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull w TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₀, m1₀, m2₀, -⟩ := genFibre Xo c Out.CubePf.cubePull T io c.F (RingHom.id c.F) TF.Y w _ hz hzs G₀ m₀
  have : CharZero (ResidueField T.V) := charZero_residue_of_map T.V (w ≫ TF.Y.s)
  obtain ⟨W, _, _, _, _, _, hf, hi, hS⟩ := exists_split_baseChange T.V G₀.G G₀.semi
  have : CharZero W := charZero_of_injective_ringHom hi
  let T' : CDVR := { V := W }
  let j : T.V →+* T'.V := algebraMap T.V W
  have hfin : j.Finite := RingHom.finite_algebraMap.2 hf
  obtain ⟨i, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' j hi hfin
  letI := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
    T.Fr T'.Fr ψ y₀.1
  let y' : IntFr Xo c T' (i.comp io) := ⟨z', GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T'.Fr z',
    GlobalTheory.IntegralExt.integral_baseChange T T' io (i.comp io) j hi ψ hφ y₀.1 z' hz' y₀.2.2⟩
  obtain ⟨G, ⟨mG⟩⟩ : ∃ G : SAB H (Sp T'.V), Nonempty (SABMap G TF.Y.t (spMap j ≫ w)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap j ≫ w) TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  have hι : i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j := RingHom.ext hφ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap j = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hι]
  have hz2 : (spMap i ≫ FlagMod.frX P) ≫ TF.Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap j ≫ w := by
    rw [Category.assoc, hz, ← Category.assoc, ← hio, Category.assoc]
  have hzs2 : (spMap i ≫ FlagMod.frX P) ≫ pullback.snd _ _ = spMap (i.comp io) := by
    rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T' (i.comp io) c.F (RingHom.id c.F) TF.Y
    (spMap j ≫ w) _ hz2 hzs2 G mG
  have hx' : y'.1.x = (spMap i ≫ FlagMod.frX P) ≫ pullback.fst _ _ := by
    rw [Category.assoc, FlagMod.frX_fst, ← hB.1]
    exact hz'.1
  obtain ⟨Pu, -⟩ := GlobalTheory.IntegralExt.exists_unif_of_split T T' j i hφ m1₀ m2₀ (Category.assoc _ _ _) m1 m2 hS
  have hloc : IsLocalHom j := hfin.to_isIntegral.isLocalHom hi
  refine ⟨T', i, j, r, y', G, mG, Pu, t', (by rw [hx']; exact m1), m2, hr0, hv, hι, fun a ha => map_nonunit j a ha,
    ?_⟩
  rw [TF.X.ptY_frBor hB, ← TF.X.ptY_frMap hz']

end GlobalTheory.UnifTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow.TwoFibres

open GlobalTheory.ZM

theorem unitS_spMap_eq {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitS_spMap_comp {o R R' : Type} [CommRing o] [CommRing R] [CommRing R'] (β : o →+* R) (i : R →+* R')
    (u : oˣ) : unitS (spMap i ≫ spMap β) u = unitOn (Units.map (i.comp β).toMonoidHom u) := by
  rw [SpreadLevel.unitS_comp, unitS_spMap_eq β]
  exact (unitS_spMap_eq i _).trans (congrArg unitOn (Units.ext rfl))

def ofLevel {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) : TObj g k PEmpty b s where
  A := P.A
  ab := P.isAb
  dim := hg ▸ P.smoothDim
  L := P.L
  isLB := P.isLB
  rigid := P.rigid
  sym := P.sym
  ample := P.ample
  ktriv := P.ktriv
  pt := levelBasis l hg
  torsion := fun i => l.torsion _
  bij := by
    intro K' _ _ x y hy
    subst hg
    haveI : NeZero k := ⟨hk.ne'⟩
    obtain ⟨c, hc⟩ := l.span K' x y hy
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
    · simp only [levelBasis_rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (c _).2]
      exact hc
    · have e := l.indep K' x (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
      funext i
      have := congrArg (fun d => ((d i : ℕ) : ZMod k)) e
      simpa using this
  pairing := by
    intro i j
    subst hg hze
    exact l.pairing i j
  act := fun e => e.elim
  hom := fun e => e.elim

theorem ofLevel_lab {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) (a : Ix g k) : (ofLevel hk b s P hg l hze).lab a = levelPoint l hg a := by
  subst hg
  rfl

theorem ofLevel_hasTh {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k ^ 2) (b : TBase o (k ^ 2)) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ}
    (l : Level P (k ^ 2) ze) (hze : ze = unitS s b.ζ) (w : Ix g (k ^ 2) → K)
    (h : IsThetaPt P k (levelPoint l hg) fun a => Ex.fnOf (w a)) :
    (ofLevel hk b s P hg l hze).HasTh (𝟙 _) w := by
  have hx : (fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫
      (ofLevel hk b s P hg l hze).lab a) = levelPoint l hg := by
    funext a
    have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; rfl
    rw [e, Category.id_comp, ofLevel_lab]
  subst hg
  exact (congrArg (fun x => IsThetaPt P k x (fun a => Ex.fnOf (w a))) hx).mpr h

theorem linComb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {m : ℕ} (x' : Fin m → (Out.baseOver S' ⟶ G'))
    (x : Fin m → (Out.baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = f ≫ (x i).left) (c : Fin m → ℕ) :
    (Out.linComb x' c).left ≫ φ = f ≫ (Out.linComb x c).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e : ∀ i, pushHom h (Out.baseOver S') (x' i) = preHom U (x i) := fun i =>
    Over.OverMorphism.ext (hx i)
  have := congrArg (fun z => z.left) ((SpreadLevel.map_linComb (pushHom h (Out.baseOver S')) x' c).trans
    ((congrArg (fun z => Out.linComb z c) (funext e)).trans (SpreadLevel.map_linComb (preHom U) x c).symm))
  exact this

end GlobalTheory.MBLow.TwoFibres

namespace GlobalTheory.MBLow

open GlobalTheory.ZM GlobalTheory.MBLow.TwoFibres

theorem exists_family_of_two_fibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  intro g n hn hodd
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨j₀, H⟩ := exists_tObj_of_veryDense hL hL2 g PEmpty (fun e => e.elim) 0 n hn hodd
  refine ⟨j₀, fun j hj o _ _ ζ W _ _ _ _ β v K₀ K₁ _ _ _ _ i₀ i₁ hW P₀ P₁ h₀ h₁ l₀ l₁ hT₀ hT₁ => ?_⟩
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hζ : IsPrimitiveRoot ζ ((n ^ j) ^ 2) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (Units.map (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv.hom.toMonoidHom).comp
      (Units.map (i₀.comp β).toMonoidHom)) l₀.prim ?_
    exact (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv).1).comp
      (Units.map_injective (i₀.comp β).injective)
  let b : TBase o ((n ^ j) ^ 2) :=
    { ζ := ζ
      unit := (Nat.cast_ne_zero.2 hk.ne').isUnit
      prim := fun K _ β' => (IsPrimitiveRoot.coe_units_iff.2 hζ).map_of_injective β'.injective }
  let t₀ := ofLevel hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm
  let t₁ := ofLevel hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm
  have hS₀ : t₀.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hS₁ : t₁.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hh₀ : t₀.HasTh (𝟙 _) (fun a => i₀ (v a)) :=
    ofLevel_hasTh hk b _ P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm _ hT₀
  have hh₁ : t₁.HasTh (𝟙 _) (fun a => i₁ (v a)) :=
    ofLevel_hasTh hk b _ P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm _ hT₁
  have hvd : VeryDense (objPrimes b (fun e : PEmpty => e.elim) 0 β v) := by
    intro q f hq hf
    rcases hW q hq with rfl | rfl
    · exact ⟨_, ⟨K₀, inferInstance, inferInstance, i₀, t₀, rfl, hS₀, hh₀⟩, hq, le_rfl, hf⟩
    · exact ⟨_, ⟨K₁, inferInstance, inferInstance, i₁, t₁, rfl, hS₁, hh₁⟩, hq, le_rfl, hf⟩
  obtain ⟨t, -, ht⟩ := H j hj o b W β v hvd
  obtain ⟨φ₀, hp₀, hL₀, hpt₀, -⟩ := ht K₀ i₀ t₀ hS₀ hh₀
  obtain ⟨φ₁, hp₁, hL₁, hpt₁, -⟩ := ht K₁ i₁ t₁ hS₁ hh₁
  haveI := t.ab.comm
  refine ⟨t.pol, t.lab, φ₀, φ₁, rfl, fun a => DenseBasis.linComb_pow_eq_one t.pt t.torsion _, hp₀, hp₁, hL₀, hL₁,
    fun a => ?_, fun a => ?_⟩
  · rw [← ofLevel_lab hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm a]
    exact linComb_push hp₀ t₀.pt t.pt hpt₀ _
  · rw [← ofLevel_lab hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm a]
    exact linComb_push hp₁ t₁.pt t.pt hpt₁ _

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.CdvrLiftCp

theorem mem_int_iff' {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem norm_p_lt_one' {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem mem_range_of_norm_le {p : ℕ} [Fact p.Prime] {W L : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (kL : L →+* ℂ_[p])
    (hW : ∀ w, ‖kL (algebraMap W L w)‖ ≤ 1) (x : L) (hx : ‖kL x‖ ≤ 1) : x ∈ Set.range (algebraMap W L) := by
  by_contra hxr
  have hx0 : x ≠ 0 := by rintro rfl; exact hxr ⟨0, map_zero _⟩
  have hunit : ∀ u : Wˣ, ‖kL (algebraMap W L u)‖ = 1 := by
    intro u
    have h1 : kL (algebraMap W L u) * kL (algebraMap W L ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a1 := hW u
    have a2 := hW ↑u⁻¹
    nlinarith [norm_nonneg (kL (algebraMap W L u)), norm_nonneg (kL (algebraMap W L ↑u⁻¹))]
  obtain ⟨y, hy⟩ : IsLocalization.IsInteger W x⁻¹ :=
    (ValuationRing.isInteger_or_isInteger W x).resolve_left (fun ⟨a, ha⟩ => hxr ⟨a, ha⟩)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx0 (inv_eq_zero.1 hy.symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hxr
    refine ⟨↑u⁻¹, ?_⟩
    rw [hyu, pow_zero, mul_one] at hy
    rw [map_units_inv, hy, inv_inv]
  have hy1 : ‖kL (algebraMap W L y)‖ = 1 := by
    have h1 : kL x * kL (algebraMap W L y) = 1 := by rw [← map_mul, hy, mul_inv_cancel₀ hx0, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a2 := hW y
    nlinarith [norm_nonneg (kL x), norm_nonneg (kL (algebraMap W L y))]
  have hϖ1 : ‖kL (algebraMap W L ϖ)‖ = 1 := by
    rw [hyu, map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hy1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 hy1
  have hall : ∀ w : W, w ≠ 0 → ‖kL (algebraMap W L w)‖ = 1 := by
    intro w hw
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    rw [map_mul, map_mul, norm_mul, hunit, map_pow, map_pow, norm_pow, hϖ1, one_pow, one_mul]
  have hp : kL (algebraMap W L (p : W)) = (p : ℂ_[p]) := by simp
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpW : (p : W) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hp
    exact hp0 hp.symm
  have := hall _ hpW
  rw [hp] at this
  exact absurd this (ne_of_lt norm_p_lt_one')

end GlobalTheory.CdvrLiftCp

namespace GlobalTheory.CdvrLiftCp

theorem exists_cdvr_lift : ∀ (p : ℕ) [Fact p.Prime] (T : CDVR), T.FinRes → ∀ (kO : T.V →+* 𝓞_ℂ_[p]) (k : T.Fr →+* ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L] (kL : L →+* ℂ_[p]), (∀ a, kL (algebraMap T.Fr L a) = k a) → ∃ (T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr) (ψ : L ≃+* T'.Fr) (kO' : T'.V →+* 𝓞_ℂ_[p]), T'.FinRes ∧ Function.Injective kO' ∧ (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iF a) ∧ (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap T'.V T'.Fr a))) ∧ ∀ (A : Type) [CommRing A] (f : A →+* L), (∀ a, ‖kL (f a)‖ ≤ 1) → ∃ fO : A →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (fO a) = ψ (f a) := by
  intro p _ T hT kO k hk L _ _ _ kL hkL
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iF : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := by
    intro w
    change (FractionRing.algEquiv W L).symm (algebraMap W L w) = _
    exact AlgEquiv.commutes _ w
  have hψs : ∀ w : W, ψ.symm (algebraMap W (FractionRing W) w) = algebraMap W L w := by
    intro w
    rw [← hψ, RingEquiv.symm_apply_apply]
  have hφ : ∀ a, iF (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change ψ (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, hψ]
  haveI : Algebra.IsIntegral T.V W := Algebra.IsIntegral.of_finite T.V W
  have hint : ∀ w : W, kL (algebraMap W L w) ∈ 𝓞_ℂ_[p] := by
    intro w
    have hw : IsIntegral T.V w := Algebra.IsIntegral.isIntegral w
    have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = (kL.comp (algebraMap W L)).comp (algebraMap T.V W) := by
      ext a
      change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kL (algebraMap W L (algebraMap T.V W a))
      rw [hk, ← hkL, ← RingHom.comp_apply (algebraMap W L), ← RingHom.comp_apply (algebraMap T.Fr L), hc]
    have h1 : IsIntegral 𝓞_ℂ_[p] (kL (algebraMap W L w)) := IsIntegral.map_of_comp_eq kO _ hcomp hw
    exact (PadicComplexInt.integers p).mem_of_integral h1
  have hW : ∀ w : W, ‖kL (algebraMap W L w)‖ ≤ 1 := fun w => (mem_int_iff' _).1 (hint w)
  let kO' : W →+* 𝓞_ℂ_[p] := (kL.comp (algebraMap W L)).codRestrict 𝓞_ℂ_[p] hint
  have hkO' : ∀ w, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' w) = kL (algebraMap W L w) := fun w => rfl
  refine ⟨T', algebraMap T.V W, iF, ψ, kO', ?_, ?_, fun a => (hφ a).symm, fun a => rfl, ?_, ?_⟩
  · haveI : Finite (IsLocalRing.ResidueField T.V) := hT
    exact Module.finite_of_finite (IsLocalRing.ResidueField T.V) (M := IsLocalRing.ResidueField W)
  · intro a b hab
    have h1 := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hab
    rw [hkO', hkO'] at h1
    exact IsFractionRing.injective W L (kL.injective h1)
  · intro a
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap W (FractionRing W) a))
    rw [hkO', hψs]
  · intro A _ f hf
    have hmem : ∀ a, f a ∈ (algebraMap W L).range := fun a => mem_range_of_norm_le kL hW (f a) (hf a)
    let e : W ≃+* (algebraMap W L).range :=
      RingEquiv.ofBijective (algebraMap W L).rangeRestrict
        ⟨fun a b h => IsFractionRing.injective W L (congrArg Subtype.val h), (algebraMap W L).rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (f.codRestrict _ hmem), fun a => ?_⟩
    change algebraMap W (FractionRing W) (e.symm (f.codRestrict _ hmem a)) = ψ (f a)
    have h2 : algebraMap W L (e.symm (f.codRestrict _ hmem a)) = f a := by
      have h3 : e (e.symm (f.codRestrict _ hmem a)) = f.codRestrict _ hmem a := e.apply_symm_apply _
      exact congrArg Subtype.val h3
    rw [← hψ, h2]

end GlobalTheory.CdvrLiftCp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem exists_frPt_of_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  intro E _ _ _ H Dw l Xo c Y X K _ z hO
  obtain ⟨a, h⟩ := GlobalTheory.CompHS.exists_chartFr z hO
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨Q, hQ⟩ := h k hz
  refine ⟨algebraMap c.F K, ?_⟩
  have e : (algebraMap c.F K).toAlgebra = a := Algebra.algebra_ext _ _ fun _ => rfl
  rw [e]
  exact ⟨Q, (FlagCover.eq_ptY hQ.lies).symm⟩

end GlobalTheory.CompHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHarmonicCongrColumnPolynomialStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_harmonic_congr_column_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  first | exact @GlobalTheory.RefGlob.exists_harmA_congr_polyT | exact GlobalTheory.RefGlob.exists_harmA_congr_polyT | (intros; apply GlobalTheory.RefGlob.exists_harmA_congr_polyT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedFieldStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_cover_over_sized_field : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j → 5 ≤ D.host.splitBound → Nat.Coprime 15 (D.host.g 0 * D.host.g 1) → ∀ e : ℕ, ∃ Y : Deep T j, Y.Good e (fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) + Real.log D.host.d + 1)) := by
  first | exact @GlobalTheory.CovTop.SizedCover.exists_good_sized | exact GlobalTheory.CovTop.SizedCover.exists_good_sized | (intros; apply GlobalTheory.CovTop.SizedCover.exists_good_sized <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimatesStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_bound_of_all_estimates : Size → LowDef → DeepEx → DeepGood → Ring → Maps → Rk → Gmin → Flat → ULow → Low := by
  first | exact @GlobalTheory.CovTop.LowCover.low | exact GlobalTheory.CovTop.LowCover.low | (intros; apply GlobalTheory.CovTop.LowCover.low <;> assumption)
end

