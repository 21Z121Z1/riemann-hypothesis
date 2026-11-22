import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePullbackExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.LevelPull

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem toUnit_left {S : Scheme.{0}} {T : Over S} (u : T ⟶ 𝟙_ (Over S)) : u.left = T.hom := by
  simpa using Over.w u

theorem push_inj {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'} {x y : T ⟶ X'.A}
    (e : pushPt hg.1.w x = pushPt hg.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hg.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

def liftPt {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    𝟙_ (Over S') ⟶ X'.A :=
  Over.homMk (hg.1.lift (b ≫ p.left) (𝟙_ (Over S')).hom (by
    rw [Category.assoc, Over.w p]; simp)) (hg.1.lift_snd _ _ _)

theorem liftPt_push {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) (p : 𝟙_ (Over S) ⟶ X.A) :
    (liftPt hg p).left ≫ φ = b ≫ p.left :=
  hg.1.lift_fst _ _ _

theorem push_liftPt_act {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) (p : 𝟙_ (Over S) ⟶ X.A) {T : Over S'}
    (u : T ⟶ 𝟙_ (Over S')) (a : 𝓞 F) :
    pushPt h.grp.1.w (u ≫ liftPt h.grp p ≫ X'.rm.act a) =
      toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a := by
  apply Over.OverMorphism.ext
  show (u ≫ liftPt h.grp p ≫ X'.rm.act a).left ≫ φ = (toUnit (Over.mk (T.hom ≫ b)) ≫ p ≫ X.rm.act a).left
  simp only [Over.comp_left, Category.assoc]
  rw [h.act a, ← Category.assoc (liftPt h.grp p).left, liftPt_push, toUnit_left, toUnit_left]
  simp

section
variable {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (hg : IsGrpPullback X'.A X.A b φ) {T : Over S'}

theorem push_mul (x y : T ⟶ X'.A) : pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
  map_mul (pushHom hg T) x y

theorem push_one : pushPt hg.1.w (1 : T ⟶ X'.A) = 1 := map_one (pushHom hg T)

theorem push_pow (x : T ⟶ X'.A) (n : ℕ) : pushPt hg.1.w (x ^ n) = pushPt hg.1.w x ^ n :=
  map_pow (pushHom hg T) x n
end

theorem exists_level_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  intro F _ _ 𝔠 S S' X X' b φ h N α
  refine ⟨⟨fun i => liftPt h.grp (α.pt i), ?_, ?_, ?_⟩, fun i => liftPt_push h.grp _⟩
  · intro i
    apply push_inj h.grp
    have e2 : pushPt h.grp.1.w (liftPt h.grp (α.pt i)) =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i := by
      apply Over.OverMorphism.ext
      show (liftPt h.grp (α.pt i)).left ≫ φ = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i).left
      rw [liftPt_push, Over.comp_left, toUnit_left]
      simp
    have e3 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i) ^ N =
        toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ α.pt i ^ N :=
      (map_pow (preHom (G := X.A) (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)))) (α.pt i) N).symm
    rw [push_pow h.grp, e2, e3, α.tors i, push_one h.grp]
    exact MonObj.comp_one _
  · intro Ω _ _ t a c hyp
    apply α.inj Ω (t ≫ b) a c
    have e := congrArg (pushPt h.grp.1.w) hyp
    rw [push_mul h.grp, push_one h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)] at e
    exact e
  · intro Ω _ _ t y hy
    obtain ⟨a, c, hac⟩ := α.surj Ω (t ≫ b) (pushPt h.grp.1.w y) (by
      rw [← push_pow h.grp, hy, push_one h.grp])
    refine ⟨a, c, push_inj h.grp ?_⟩
    rw [push_mul h.grp, push_liftPt_act h (α.pt 0), push_liftPt_act h (α.pt 1)]
    exact hac

end GlobalTheory.RealMult.LevelPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
section
namespace LeviFormCombination
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviComb

theorem levi_sum_add {e : ℕ} {ι : Type} (s : Finset ι) (a : ι → ℝ) (f : ι → (Fin e → ℂ) → ℝ)
    (g : (Fin e → ℂ) → ℝ) {y : Fin e → ℂ} (hf : ∀ i, ContDiffAt ℝ 2 (f i) y) (hg : ContDiffAt ℝ 2 g y)
    (w : Fin e → ℂ) :
    ContDiffAt ℝ 2 (fun z => ∑ i ∈ s, a i * f i z + g z) y ∧
      levi (fun z => ∑ i ∈ s, a i * f i z + g z) y w = ∑ i ∈ s, a i * levi (f i) y w + levi g y w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert b s hb ih =>
    have he : (fun z => ∑ i ∈ insert b s, a i * f i z + g z) =
        fun z => (∑ i ∈ s, a i * f i z + g z) + a b * f b z := by
      funext z
      rw [Finset.sum_insert hb]
      ring
    rw [he, Finset.sum_insert hb]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf b)), ?_⟩
    rw [levi_add_smul (a b) ih.1 (hf b) w, ih.2]
    ring

theorem leviAt_combPot (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ι : Type) [Fintype ι]
    (P : ι → LocPot X) (a : ι → ℝ) (u : X → ℝ) (hP : ∀ i, IsPotential A (P i)) (hu : A.Smooth u) :
    ∀ j, ∀ y ∈ (A.chart j).target, ∀ w,
      leviAt A (InhabCalc.combPot P a u) j y w = ∑ i, a i * leviAt A (P i) j y w + leviAt A (LocPot.ofFun u) j y w := by
  intro j y hy w
  have hU : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm isOpen_univ).mem_nhds ⟨hy, Set.mem_univ _⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hL := (levi_sum_add Finset.univ a
    (fun i => (P i).φ ((A.chart j).symm y) ∘ (A.chart j).symm) (u ∘ (A.chart j).symm)
    (y := y) (fun i => Deg.potential_chart_contDiffAt_two A (hP i) j hy) hU w).2
  exact hL

end GlobalTheory.CompanionTheory.LeviComb

end
end

end LeviFormCombination
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.leviAt_linear_combination_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ι : Type) [Fintype ι] (P : ι → LocPot X) (a : ι → ℝ) (u : X → ℝ), (∀ i, IsPotential A (P i)) → A.Smooth u → ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A (InhabCalc.combPot P a u) j y w = ∑ i, a i * leviAt A (P i) j y w + leviAt A (LocPot.ofFun u) j y w := by
  first | exact @LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot | exact LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot | (intros; apply LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNegStatement
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lgOf_single_neg_one_eq_neg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  first | exact @GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg | exact GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg | (intros; apply GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieProj

theorem lie_finite_projective_rank : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)),
    Module.Finite R X.Lie ∧ Module.Projective R X.Lie ∧ ∀ p, Module.rankAtStalk (R := R) X.Lie p = Module.finrank ℚ F := by
  intro F _ _ 𝔠 R _ X
  have hd := X.dim
  haveI : Smooth X.A.hom := hd.smooth
  refine finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie X.rm) (Module.finrank ℚ F) fun p => ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := exists_chart_lieBasis X.A _ hd p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm
    (isGrpPullback_pullback X.A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away X.A X.rm r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end GlobalTheory.LieProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDuals
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GtBasis

open GlobalTheory.TorusModel

section Tangent

variable {R : Type} [CommRing R]

def redO (R : Type) [CommRing R] : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) GlobalTheory.MBLow.GtVec.red_comp

theorem isTangent_iff {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) : IsTangent y ↔ redO R ≫ y = 1 := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    refine h.trans ?_
    simp [Hom.one_def]
  · intro h
    have := congrArg (·.left) h
    refine this.trans ?_
    simp [Hom.one_def]

theorem redO_scale (c : R) : redO R ≫ epsScale R c = redO R := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_mul {y y' : epsR R ⟶ G} (h : IsTangent y) (h' : IsTangent y') : IsTangent (y * y') := by
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, h, h', _root_.mul_one]

theorem isTangent_inv {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent y⁻¹ := by
  rw [isTangent_iff] at *
  rw [GrpObj.comp_inv, h, inv_one]

theorem isTangent_scale (c : R) {y : epsR R ⟶ G} (h : IsTangent y) : IsTangent (epsScale R c ≫ y) := by
  rw [isTangent_iff] at *
  rw [← Category.assoc, redO_scale, h]

theorem isTangent_tanComb {m : ℕ} (c : Fin m → R) {v : Fin m → (epsR R ⟶ G)} (h : ∀ i, IsTangent (v i)) :
    IsTangent (tanComb c v) := by
  unfold tanComb
  refine List.prod_induction (fun y => IsTangent y) (fun _ _ => isTangent_mul) ?_ ?_
  · exact (isTangent_iff _).2 (MonObj.comp_one _)
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact isTangent_scale _ (h i)

theorem eq_tanComb' {m : ℕ} {c : Fin m → R} {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  exact funext fun i => Over.OverMorphism.ext (hu i)

end Tangent

section Stalk

variable {R : Type} [CommRing R]

theorem gs_id_eq (z : Sp R) (a : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = toStkA z a := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ z ⊤ trivial]
  simp [toStkA]
  rfl

theorem dn_inj [IsLocalRing (DualNumber R)] {a a' : R}
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 (Sp (DualNumber R))) (cpt (DualNumber R)) ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a'))) : a = a' := by
  rw [gs_id_eq, gs_id_eq] at h
  exact TrivSqZeroExt.inr_injective (add_left_cancel (toStkA_injective h))

end Stalk

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ D.X) (x : Fin D.P.g ⊕ Fin r → (epsR R ⟶ H)), IsLieBasis vB → (∀ j, GtTan (Φ _ (x j))) → (∀ i, (Φ _ (x (Sum.inl i))).b = vB i) → (∀ l, (Φ _ (x (Sum.inr l))).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x (Sum.inr l))).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : R)))) → ∀ (n : ℕ) (σ : Fin n ≃ Fin D.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := by
  intro R _ _ _ D H _ _ Φ hΦ r vB bX x hvB htan hb htor n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using hΦ.2 T 1 1)
  have bpull : ∀ (T T' : Over (Sp R)) (k : T' ⟶ T) (y : T ⟶ H), (Φ T' (k ≫ y)).b = k ≫ (Φ T y).b :=
    fun T T' k y => ((isPull_iff _ _ _).1 (hΦ.1 T' T k y)).1
  have gtan : ∀ y : epsR R ⟶ H, GtTan (Φ _ y) ↔ IsTangent y := by
    intro y
    rw [isTangent_iff]
    exact ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hΦ.1 _ _ (redO R) y) h).trans
      (GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hΦ.1 _ _ (redO R) y⟩⟩
  let β : (epsR R ⟶ H) →* (epsR R ⟶ D.P.A) :=
    { toFun := fun y => (Φ _ y).b
      map_one' := (hz _).1
      map_mul' := fun y y' => ((TorusModel.isAdd_iff _ _ _).1 (hΦ.2 _ y y')).1 }
  have βapp : ∀ y, β y = (Φ _ y).b := fun _ => rfl
  have βcomb : ∀ {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ H)),
      β (tanComb c v) = tanComb c (fun i => β (v i)) := by
    intro m c v
    simp only [tanComb, map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun i => bpull _ _ _ _)
  have βtan : ∀ y, IsTangent y → IsTangent (β y) := fun y h => (isTangent_iff _).2 (by
    rw [βapp, ← bpull, (isTangent_iff y).1 h]
    exact (hz _).1)
  have xtan : ∀ j, IsTangent (x j) := fun j => (gtan _).1 (htan j)
  have tor := GlobalTheory.T.torusTangentCombination_characterValues R D H Φ hΦ r (fun l χ => ((bX.repr χ l : ℤ) : R)) (fun l => x (Sum.inr l)) htor
  have split : ∀ c : Fin n → R, tanComb c (fun k => x (σ k)) =
      tanComb (fun i => c (σ.symm (Sum.inl i))) (fun i => x (Sum.inl i)) *
        tanComb (fun l => c (σ.symm (Sum.inr l))) (fun l => x (Sum.inr l)) := by
    intro c
    simp only [tanComb, List.prod_ofFn]
    have e := Equiv.prod_comp σ (fun j => epsScale R (c (σ.symm j)) ≫ x j)
    simp only [Equiv.symm_apply_apply] at e
    rw [e, Fintype.prod_sum_type]
  have βA : ∀ a : Fin D.P.g → R, β (tanComb a (fun i => x (Sum.inl i))) = tanComb a vB := by
    intro a
    rw [βcomb]
    simp only [βapp, hb]
  have βB : ∀ d : Fin r → R, β (tanComb d (fun l => x (Sum.inr l))) = 1 := fun d => (tor d).1
  have : IsLocalRing (DualNumber R) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber R
  obtain ⟨J₀, hJ₀⟩ := TorusCoord.exists_good' D.P.isLB (cpt (DualNumber R))

  have uniq : ∀ c c' : Fin n → R, tanComb c (fun k => x (σ k)) = tanComb c' (fun k => x (σ k)) → c = c' := by
    intro c c' h
    rw [split, split] at h
    have hA := congrArg β h
    rw [map_mul, map_mul, βA, βA, βB, βB, _root_.mul_one, _root_.mul_one] at hA
    have ha : (fun i => c (σ.symm (Sum.inl i))) = (fun i => c' (σ.symm (Sum.inl i))) := by
      refine (hvB.2 _ (isTangent_tanComb _ hvB.1)).unique (isLieComb_tanComb _ _) ?_
      rw [hA]
      exact isLieComb_tanComb _ _
    rw [ha, mul_right_inj] at h
    have he : ∀ l, c (σ.symm (Sum.inr l)) = c' (σ.symm (Sum.inr l)) := by
      intro l
      have v1 := (tor (fun l => c (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      have v2 := (tor (fun l => c' (σ.symm (Sum.inr l)))).2 (bX l) _ (𝟙 _) _ J₀ hJ₀
      rw [h] at v1
      have := dn_inj (v1.symm.trans v2)
      simp only [Module.Basis.repr_self, Finsupp.single_apply] at this
      simpa using this
    funext k
    obtain ⟨j, rfl⟩ := σ.symm.surjective k
    rcases j with i | l
    · exact congrFun ha i
    · exact he l
  refine ⟨fun k => xtan (σ k), fun w hw => ?_⟩
  obtain ⟨c₁, hc₁, -⟩ := hvB.2 (β w) (βtan w hw)
  have hw₁ : β (tanComb c₁ (fun i => x (Sum.inl i))) = β w := by
    rw [βA]
    exact (eq_tanComb' hc₁).symm
  have tw' : IsTangent (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹) :=
    isTangent_mul hw (isTangent_inv (isTangent_tanComb _ fun i => xtan _))
  have bw' : (Φ _ (w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹)).b = DegPre.zeroT D (epsR R) := by
    rw [← βapp, map_mul, map_inv, hw₁, mul_inv_cancel]
    rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.torusExtensionTangent_characterValues_additive R D _ ((gtan _).2 tw') bw'
  have hl : ∀ χ, lam χ = ∑ l, lam (bX l) * ((bX.repr χ l : ℤ) : R) := by
    intro χ
    conv_lhs => rw [← bX.sum_repr χ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  obtain ⟨bd, vd⟩ := tor (fun l => lam (bX l))
  have e : w * (tanComb c₁ (fun i => x (Sum.inl i)))⁻¹ = tanComb (fun l => lam (bX l)) (fun l => x (Sum.inr l)) :=
    (Φ _).injective (pt_ext (bw'.trans bd.symm) fun χ y J hJ => Units.ext ((hlam χ _ _ y J hJ).trans
      ((congrArg _ (by rw [hl χ])).trans (vd χ _ _ y J hJ).symm)))
  have hw : w = tanComb (fun k => Sum.elim c₁ (fun l => lam (bX l)) (σ k)) (fun k => x (σ k)) := by
    rw [split]
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← e, mul_comm w, mul_inv_cancel_left]
  refine ⟨_, hw ▸ isLieComb_tanComb _ _, fun c hc => ?_⟩
  exact uniq _ _ ((eq_tanComb' hc).symm.trans hw)

end GlobalTheory.GtBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUniv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h
  have hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x) := by
    intro x
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]
  have hb : Function.Bijective (e.lTensor R') := by
    have := (TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective
    convert this using 1
    funext x
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r m => rfl
  have hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R')) := funext hsq
  constructor
  · intro hf
    have h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f))) := he'.comp hf
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ hb).mp h1
  · intro hg
    have h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))) := hg.comp hb
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff' he' _).mp h1

end GlobalTheory.BaseChangeIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinear
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_prod_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ f f' g hg hf hf'
  have key : ∀ y, liftSemi g y =
      (liftSemi f (TensorProduct.prodRight R R' R' M N y).1,
        liftSemi f' (TensorProduct.prodRight R R' R' M N y).2) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul x c => simp [liftSemi_tmul, hg]
    | add a b ha hb => rw [map_add, ha, hb, map_add]; ext <;> simp
  have e : ⇑(liftSemi g) = Prod.map (liftSemi f) (liftSemi f') ∘ (TensorProduct.prodRight R R' R' M N) :=
    funext key
  rw [e]
  exact (hf.prodMap hf').comp (TensorProduct.prodRight R R' R' M N).bijective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (J : Type) [Finite J] (M M' : J → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) (g : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i)), (∀ x i, g x i = f i (x i)) → (∀ i, Function.Bijective (liftSemi (f i))) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ J _ M M' _ _ _ _ f g hg hf
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ y : R' ⊗[R] (∀ i, M i),
      liftSemi g y = Pi.map (fun i => liftSemi (f i)) (TensorProduct.piRight R R' R' M y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext i; simp [Pi.map]
    | tmul x m =>
      funext i
      simp [liftSemi_tmul, hg, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]; funext i; simp
  have : (liftSemi g : R' ⊗[R] (∀ i, M i) → ∀ i, M' i)
      = Pi.map (fun i => liftSemi (f i)) ∘ (TensorProduct.piRight R R' R' M) := funext key
  rw [this]
  exact (Function.Bijective.piMap hf).comp (TensorProduct.piRight R R' R' M).bijective

end GlobalTheory
end

