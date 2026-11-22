import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleModel

open GlobalTheory.PrimNorm GlobalTheory.MulPull

section Charts

variable {Y Y' : Scheme.{0}}

def chartQuotOut (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm
          ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartQuotIn (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull (LB.div (M.pull f) (N.pull f)) ((LB.div M N).pull f) (𝟙 Y') :=
  have le : ∀ p : (PUnit → M.ι) × (PUnit → N.ι), (M.pull f).U p.1 ⊓ (N.pull f).U p.2 ≤
      ((LB.div M N).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M N)).2 ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => ((chartQuotOut M N f).g y _ _ (le p hp) (le q hq)).symm }

end Charts

section Cubical

theorem isPullCubical_of_lbIso (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') {f : S' ⟶ S} {α : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f α) {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (cubeMapOf gp).e (fun _ => (cubeMapOf gp).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := HeckePoint.exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
      fun I => (cubeMapOf gp).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (cubeMapOf gp).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (cubeMapOf gp).F3 =
        (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1)).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over S'))))
      have e₁ : e ≫ x3 G' i = 1 := by fin_cases i <;> simp [e, x3]
      have e₂ : lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1) ≫ x3 G i = 1 := by
        fin_cases i <;> simp [x3]
      rw [e₁, e₂]
      exact o
    have b₁ := (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S')) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S') ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

end Cubical

section Ample

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Ample

section Extend

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Sp R)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {φ : B.left ⟶ A.left} {L : LB A.left} {L' : LB B.left}

end Extend

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

abbrev fibre (T : Over S) (j : S' ⟶ S) : Over S' := Over.mk (pullback.snd T.hom j)

abbrev fibreProj (T : Over S) (j : S' ⟶ S) : Over.mk ((fibre T j).hom ≫ j) ⟶ T :=
  Over.homMk (pullback.fst T.hom j) pullback.condition

end Points

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (hLaws : Out.Laws) (t₀ : SAB H (Sp K)) {A : Over (Sp R)} [GrpObj A] {φ : t₀.G.left ⟶ A.left}
  (hA : IsAbelianScheme A) (gp : IsGrpPullback t₀.G A (spMap (algebraMap R K)) φ)
  {L : LB A.left} (hL : L.IsLB) (hr : Out.Rigidified A L) (i : LBIso t₀.PP.L (L.pull φ))

include hLaws hA gp hL hr i

end Triple

end GlobalTheory.TripleModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.LamF.ringAct_iff_oAct :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G],
      (∀ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, ∃ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, b.act = a.act) ∧
        ∀ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, a.act = b.act := by
  intro O _ S G _ _
  exact ⟨fun a => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ofRingAct a, rfl⟩, fun b => ⟨b.toRingAct, rfl⟩⟩

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.Faithful

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem act_zero (act : OAct O G) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := act.act 0) (by rw [← h, _root_.mul_one])

theorem act_natCast (act : OAct O G) (n : ℕ) : act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem act_mul_eq_one (act : OAct O G) {c : O} (hc : act.act c = 1) (d : O) : act.act (d * c) = 1 := by
  rw [act.mul, hc, MonObj.comp_one]

theorem pow_eq_one_of_act (act : OAct O G) {n : ℕ} (hn : act.act (n : O) = 1) {T : Over S} (x : T ⟶ G) :
    x ^ n = 1 := by
  have h : x ≫ (𝟙 G ^ n) = x ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← h, ← act_natCast act, hn, MonObj.comp_one]

end

theorem act_injective : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  intro hL E _ _ K _ _ P act hg a b hab
  by_contra hne
  have hc0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hc : act.act (a - b) = 1 := by
    have h := act.add (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_right_cancel (b := act.act b) (by rw [← h, _root_.one_mul])
  set n : ℕ := Ideal.absNorm (Ideal.span {a - b}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a - b}))
  have h1 : act.act (n : 𝓞 E) = 1 := by
    rw [hn, ← hd]; exact act_mul_eq_one act hc d
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp (𝓞 K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap K k).comp (algebraMap (𝓞 K) K)))
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap K k).injective
  have key : ∀ m : ℕ, 1 ≤ m → Nat.card (Over.mk t ⟶ P.A) = (n * m) ^ (2 * P.g) := by
    intro m hm
    have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn0 (by omega)
    obtain ⟨-, -, -, -, h⟩ := hL.mulN _ P (n * m) (Nat.one_le_iff_ne_zero.mpr hnm)
    rw [← h k t (Nat.cast_ne_zero.mpr hnm)]
    refine (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)).symm
    rw [pow_mul, pow_eq_one_of_act act h1, one_pow]
  have e := (key 1 le_rfl).symm.trans (key 2 (by norm_num))
  have := Nat.pow_left_injective (by omega : 2 * P.g ≠ 0) e
  omega

end GlobalTheory.LamF.Faithful
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.RosLam

theorem form_rosati {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f g : G ⟶ G)
    {V : Type} [CommGroup V] (k : ((G ⊗ G).left ⟶ G.left) → V) :
    (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G ≫ f, snd G G] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) /
      (∏ I : ULift.{0} (Finset (Fin 2)),
        k (psum G ![fst G G, snd G G ≫ g] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card))) =
      ∏ i, k (Out.rosatiφ G f g i) ^ Out.rosatiε i := by
  have p := prod_ros f g (fst G G) (snd G G) k
  rw [lift_fst_snd] at p
  simp only [Over.id_left, Category.id_comp] at p
  rw [p, GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem lbIso_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f g : G ⟶ G) (t : LB.Gen (LB.LinComb L (Out.rosatiφ G f g) Out.rosatiε)) (ht : t.IsGen) :
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) := by
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, -, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ := h₅ _ _ L hL _ (Out.rosatiφ G f g) Out.rosatiε
  obtain ⟨b, b'⟩ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB ∧ cl (cubeLB G ![fst G G ≫ f, snd G G] L) = _ :=
    h₅ _ _ L hL _ _ _
  obtain ⟨c, c'⟩ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB ∧ cl (cubeLB G ![fst G G, snd G G ≫ g] L) = _ :=
    h₅ _ _ L hL _ _ _
  refine (h₁ _ _ _ b c).1 ?_
  have e := ((h₂ _ _ a).2 ⟨t, ht⟩).symm.trans a'
  rw [b', c', ← div_eq_one, e]
  have key := form_rosati f g (V := Multiplicative (FreeAbelianGroup ((G ⊗ G).left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : (G ⊗ G).left ⟶ G.left => Additive.ofMul (pl ψ (cl L)))) key
  simpa only [map_div, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd,
    FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem rosatiAdj_iff_lamEq : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (f g : P.A ⟶ P.A), IsMonHom f → IsMonHom g → (Out.RosatiAdj P.A P.L f g ↔ LamEq P.L f (𝟙 P.A) P.L (𝟙 P.A) g) := by
  intro hG S P f g hf hg
  have := P.isAb.comm
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  constructor
  · intro h
    obtain ⟨u, hu, -⟩ := exists_ros hG P.isAb P.isLB f g h
    exact lbIso_of_gen P.isLB f g u hu
  · intro h s
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB f g h
    exact ⟨⊤, trivial, LB.pullGen P.L _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

end GlobalTheory.RosLam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SingleMemSpanIffOfSelfDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem single_mem_span_iff_of_selfDual : ∀ (O R K La I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K] [AddCommGroup La] [Module O La] [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : La → La → O) (ev dv : La → I → K) (n : ℕ) (x y : Fin n → La), (∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i) → (∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m)) → Submodule.span K (Set.range ev) = ⊤ → ∀ (i : I) (t : K), Pi.single i t ∈ Submodule.span R (Set.range ev) ↔ ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  intro O R K La I _ _ _ _ _ _ _ _ τ₀ h ev dv n x y hh hev hspan i t
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have : ∑ j, (r • u) j * dv b j = algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, _root_.mul_assoc]
      rw [this]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul,
          ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

theorem isTensor_induction {S : Scheme.{0}} {O : Type} [CommRing O] {G A T : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} {M : Type} [AddCommGroup M] [Module O M]
    (t : Serre.IsTensor A b G a M) {P : (T ⟶ A) → Prop} (y : T ⟶ A)
    (tmul : ∀ (m : M) (x : T ⟶ G), P (x ≫ t.tmul m)) (mul : ∀ y z, P y → P z → P (y * z)) : P y := by
  refine t.induction_on y ?_ tmul mul
  have h := tmul 0 1
  rwa [t.tmul_zero, MonObj.comp_one] at h

theorem lamEq_of_tmul : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (b' : OAct O A') (M' : Type) [AddCommGroup M'] [Module O M'] (t' : Serre.IsTensor A' b' G a M') (B B' : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : LB B.left) (L' : LB B'.left) (f₁ : A ⟶ B) (f₂ : A' ⟶ B) (g₁ : A ⟶ B') (g₂ : A' ⟶ B'), L.IsLB → L'.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → (∃ t : LB.Gen (Theta B' L'), t.IsGen) → IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
  (∀ m m', LamEq L (t.tmul m ≫ f₁) (t'.tmul m' ≫ f₂) L' (t.tmul m ≫ g₁) (t'.tmul m' ≫ g₂)) → LamEq L f₁ f₂ L' g₁ g₂ := by
  intro S O _ G A _ _ _ _ a b M _ _ t A' _ _ b' M' _ _ t' B B' _ _ _ _ L L' f₁ f₂ g₁ g₂ hL hL' hT hT' _ _ _ _ h
  have key : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ A'),
      LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L') := by
    intro T x y
    refine isTensor_induction t
      (P := fun x => LBIso (cubeLB B ![x ≫ f₁, y ≫ f₂] L) (cubeLB B' ![x ≫ g₁, y ≫ g₂] L')) x
      (fun m u => ?_) (fun x x' hx hx' => ?_)
    · refine isTensor_induction t'
        (P := fun y => LBIso (cubeLB B ![(u ≫ t.tmul m) ≫ f₁, y ≫ f₂] L)
          (cubeLB B' ![(u ≫ t.tmul m) ≫ g₁, y ≫ g₂] L')) y (fun m' v => ?_) (fun y y' hy hy' => ?_)
      · simp only [Category.assoc]
        exact lbIso_of_lamEq (h m m') u v
      · simp only [MonObj.mul_comp]
        exact lbIso_cubeLB_mul_right_of hL hL' hT hT' hy hy'
    · simp only [MonObj.mul_comp]
      exact lbIso_cubeLB_mul_left_of hL hL' hT hT' hx hx'
  exact key _ (fst A A') (snd A A')

end GlobalTheory.LamCalc
end
end

