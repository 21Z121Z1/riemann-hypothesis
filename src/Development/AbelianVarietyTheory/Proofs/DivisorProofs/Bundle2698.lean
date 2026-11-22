import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBalA

theorem bal_alg (O X U : Type) [CommRing O] [StarRing O] [AddCommGroup X] [Module O X] [Module.Projective O X]
    [CommGroup U] (δ : O → X → X → U)
    (hy : ∀ a y y' z, δ a (y + y') z = δ a y z * δ a y' z)
    (hz : ∀ a y z z', δ a y (z + z') = δ a y z * δ a y z')
    (ha : ∀ a b y z, δ (a + b) y z = δ a y z * δ b y z)
    (hm : ∀ a b y z, δ (a * b) y z = δ a (b • y) z * δ b y (star a • z)) :
    ∃ β : X → X → U, (∀ y y' z, β (y + y') z = β y z * β y' z) ∧ (∀ y z z', β y (z + z') = β y z * β y z') ∧
      ∀ b y z, β (b • y) z * δ b y z = β y (star b • z) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O X)
  have hs' : ∀ y, Finsupp.linearCombination O id (s y) = y := fun y => congrArg (fun q => q y) hs
  have h0 : ∀ y z, δ 0 y z = 1 := fun y z => by
    have := ha 0 0 y z
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hy0 : ∀ a z, δ a 0 z = 1 := fun a z => by
    have := hy a 0 0 z
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have key : ∀ (b : O) (z : X) (v : X →₀ O),
      δ b (Finsupp.linearCombination O id v) z = v.prod (fun x a => δ b (a • x) z) := by
    intro b z v
    induction v using Finsupp.induction with
    | zero => simp [hy0]
    | single_add x a f hxf ha0 ih =>
      rw [map_add, hy, ih, Finsupp.prod_add_index' (fun x => by simp [hy0]) (fun x a₁ a₂ => by rw [add_smul, hy]),
        Finsupp.prod_single_index (by simp [hy0])]
      simp
  refine ⟨fun y z => (s y).prod (fun x a => (δ a x z)⁻¹), fun y y' z => ?_, fun y z z' => ?_, fun b y z => ?_⟩
  · simp only [map_add]
    exact Finsupp.prod_add_index' (fun x => by simp [h0]) (fun x a₁ a₂ => by rw [ha, mul_inv])
  · simp only [hz, mul_inv]
    exact Finsupp.prod_mul
  · simp only [map_smul]
    rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul _ (fun i _ => by simp [h0])]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [← Finsupp.prod.eq_def (f := s y) (g := fun x a => (δ (b * a) x z)⁻¹)]
    simp only [hm, mul_inv]
    rw [Finsupp.prod_mul, Finsupp.prod_inv]
    rw [show δ b y z = δ b (Finsupp.linearCombination O id (s y)) z by rw [hs']]
    rw [key, mul_right_comm, inv_mul_cancel, _root_.one_mul]
end GlobalTheory.UBalA

namespace GlobalTheory.UBalA

theorem unit_of_empty {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (hF : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (z : Y) J, Good L z J → val t (𝟙 Y) z J = gm (𝟙 Y) z ⊤ w := by
  obtain ⟨t', -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by rw [hF U h]; simp) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun z J hJ => ?_⟩
  rw [← hv _ (𝟙 Y) z J hJ, val_of t' (𝟙 Y) z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res (𝟙 Y) z le trivial _).symm

theorem ros_uniq {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hG : GlobalFnsSt)
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u u' : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen) (hu' : u'.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    (h₀' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (zero2 A)) (LB.oneGen L))
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val u r z J = val u' r z J := by
  have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (hG _ _ hA).2
  have he : zero2 A ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[A] η[A])
  refine gen_unique hL _ (zero2 A) he sj hu hu' (fun y I hI => ?_) Z r z J hJ
  have a := val_corr hI h₀ (𝟙 _)
  have b := val_corr hI h₀' (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  rw [a, b]

end GlobalTheory.UBalA
namespace GlobalTheory.UBalA

theorem formal_zero {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (f g : B ⟶ B) (x z : T ⟶ B)
    (U : Type) [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ k, h (Sum.elim (GlobalTheory.PolDeg.lamPts (x ≫ f) z) (Sum.elim (fun i => (lift x z).left ≫ rosatiφ B f g i)
      (GlobalTheory.PolDeg.lamPts x (z ≫ g))) k) ^ (Sum.elim GlobalTheory.PolDeg.negε (Sum.elim rosatiε (fun k => - GlobalTheory.PolDeg.negε k))) k = 1 := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_ros f g x z h, Fin.prod_univ_four, Fin.prod_univ_four]
  simp only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε]
  simp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel
end GlobalTheory.UBalA

namespace GlobalTheory.UBalA

theorem exists_balTau : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Projective O X] [Module.Finite O X] [Module.Free ℤ X]
      (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') → (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) →
    ∃ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ := by
  intro R _ _ B _ _ hA M cub O _ _ act hros X _ _ _ _ _ c c_add c_lin
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  haveI : ∀ a : O, IsMonHom (act.act a) := act.hom
  obtain ⟨τ₀, hg, hsym, hadd⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c c_add
  have hadd2 : ∀ y z z' p J, Good M.L p J → val (τ₀ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ₀ y z) (𝟙 _) p J * val (τ₀ y z') (𝟙 _) p J := by
    intro y z z' p J hJ
    rw [hsym _ _ p J hJ, hsym y z p J hJ, hsym y z' p J hJ]
    exact hadd z z' y p J hJ
  choose u hug hu0 using fun a : O => exists_ros hG hA M.isLB (act.act a) (act.act (star a)) (hros a)
  have hδ : ∀ (a : O) (y z : X), ∃ w : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ, ∀ p J, Good M.L p J →
      val (τ₀ (a • y) z) (𝟙 _) p J * val₂ (u a) p J (c y) (c z) =
        gm (𝟙 _) p ⊤ w * val (τ₀ y (star a • z)) (𝟙 _) p J := by
    intro a y z
    refine (unit_of_empty M.isLB (fun U _ h => ?_)
      (LB.mulGen M.L _ _ _ _ (τ₀ (a • y) z) (LB.mulGen M.L _ _ _ _
        (LB.pullGen M.L _ _ (u a) (lift (c y) (c z)).left) (LB.invGen M.L _ _ (τ₀ y (star a • z)))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hg _ _) (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ (hug a) _) (DVR.invGen_isGen _ _ _ _ (hg _ _))))).elim
      fun w hw => ⟨w, fun p J hJ => ?_⟩
    · rw [c_lin, c_lin]
      exact formal_zero _ _ _ _ U h
    · have e := hw p J hJ
      rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp] at e
      rw [← e, val₂]
      group
  choose δ hδ using hδ
  have hy : ∀ a y y' z, δ a (y + y') z = δ a y z * δ a y' z := by
    intro a y y' z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ a (y + y') z p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ a y' z p J hJ
    have a1 := hadd (a • y) (a • y') z p J hJ
    have a2 := hadd y y' (star a • z) p J hJ
    have r := (ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c y) (c y') (c z)).1
    rw [← c_lin, ← c_lin, ← c_lin, ← c_add] at r
    rw [smul_add] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have hz : ∀ a y z z', δ a y (z + z') = δ a y z * δ a y z' := by
    intro a y z z'
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ a y (z + z') p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ a y z' p J hJ
    have a1 := hadd2 (a • y) z z' p J hJ
    have a2 := hadd2 y (star a • z) (star a • z') p J hJ
    have r := (ros_add cub hG hA (act.act a) (act.act (star a)) (u a) (hug a) (hu0 a) hJ (c z) (c z') (c y)).2
    rw [← c_lin, ← c_lin, ← c_lin, ← c_add] at r
    have C := isCub_cubV cub hJ
    rw [C.s01 (c y), C.s12 (c (star a • z)), C.s01 (c (a • y)), C.s12 (c z)] at r
    rw [smul_add] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have ha : ∀ a b y z, δ (a + b) y z = δ a y z * δ b y z := by
    intro a b y z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ (a + b) y z p J hJ
    have e2 := hδ a y z p J hJ
    have e3 := hδ b y z p J hJ
    have a1 := hadd (a • y) (b • y) z p J hJ
    have a2 := hadd2 y (star a • z) (star b • z) p J hJ
    have r := GlobalTheory.T.rosatiGenerator_value_add_endomorphisms_cubical cub hG hA (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a + b))
      (act.act (star (a + b))) (act.map_add a b) (by rw [star_add, act.map_add]) (u a) (u b) (u (a + b)) (hug a) (hug b)
      (hug (a + b)) (hu0 a) (hu0 b) (hu0 (a + b)) hJ (c y) (c z)
    rw [← c_lin, ← c_lin, ← c_lin, ← c_lin] at r
    rw [add_smul, show star (a + b) • z = star a • z + star b • z by rw [star_add, add_smul]] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g1 := congrArg Additive.ofMul a1
    have g2 := congrArg Additive.ofMul a2
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g1 g2 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g1 + g3 - g2
  have hm : ∀ a b y z, δ (a * b) y z = δ a (b • y) z * δ b y (star a • z) := by
    intro a b y z
    apply GlobalTheory.TauLocal.eq_of_gm M.isLB
    intro p J hJ
    rw [map_mul]
    have e1 := hδ (a * b) y z p J hJ
    have e2 := hδ a (b • y) z p J hJ
    have e3 := hδ b y (star a • z) p J hJ
    have r := GlobalTheory.T.rosatiGenerator_value_comp_endomorphisms hG hA M.isLB (act.act a) (act.act (star a)) (act.act b) (act.act (star b)) (act.act (a * b))
      (act.act (star (a * b))) (act.map_mul a b) (by rw [star_mul, act.map_mul]) (u a) (u b) (u (a * b)) (hug a) (hug b)
      (hug (a * b)) (hu0 a) (hu0 b) (hu0 (a * b)) hJ (c y) (c z)
    rw [← c_lin, ← c_lin] at r
    rw [mul_smul, show star (a * b) • z = star b • (star a • z) by rw [star_mul, mul_smul]] at e1
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul e1
    have f2 := congrArg Additive.ofMul e2
    have f3 := congrArg Additive.ofMul e3
    have g3 := congrArg Additive.ofMul r
    simp only [ofMul_mul] at f1 f2 f3 g3 ⊢
    linear_combination (norm := abel) -f1 + f2 + f3 + g3
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := bal_alg O X _ δ hy hz ha hm
  refine ⟨fun y z => DVR.scaleGen (β y z) (τ₀ y z), fun y z => DVR.scaleGen_isGen _ _ (hg y z),
    fun y y' z p J hJ => ?_, fun y z z' p J hJ => ?_, fun a u' hu' h0' y z p J hJ => ?_⟩
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ1, map_mul, _root_.mul_assoc, hadd y y' z p J hJ]
    ac_rfl
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, hβ2, map_mul, _root_.mul_assoc, hadd2 y z z' p J hJ]
    ac_rfl
  · rw [GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ, GlobalTheory.TauLocal.val_scaleGen' _ _ _ _ _ hJ,
      ros_uniq hG hA M.isLB _ _ u' (u a) hu' (hug a) h0' (hu0 a) _ p J hJ, _root_.mul_assoc]
    have e := hδ a y z p J hJ
    rw [val₂] at e
    rw [e, ← _root_.mul_assoc, ← map_mul, hβ3]

end GlobalTheory.UBalA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleExtensionTranslateOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.CechPic

theorem exists_ext_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP →
    ∀ (O : G.left.Opens) (N : LB O.toScheme), N.IsLB →
    LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) →
    ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, ∃ N' : LB ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).toScheme, N'.IsLB ∧
      LBIso (N'.pull (pullback.fst ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R))))
        (L.pull (pullback.snd ((𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O).ι (pullback.fst G.hom (jK R)))) := by
  intro R _ _ G _ _ L PP hL hExt O N hN hNL a
  have hPP : PP.IsLB := hExt.1
  let GK := (Over.pullback (jK R)).obj G
  let J := pullback.fst G.hom (jK R)
  let T := (𝟙 G * (toUnit G ≫ a)).left
  let V := T ⁻¹ᵁ O
  let σ := (lift (𝟙 G) (toUnit G ≫ a)).left
  obtain ⟨N', hN', hc⟩ := cls_surj (pull (T ∣_ O) (cls N hN) - pull (V.ι ≫ σ) (cls PP hPP))
  refine ⟨N', hN', ?_⟩
  let p₁ := pullback.fst V.ι J
  let p₂ := pullback.snd V.ι J
  rw [← cls_eq_iff (pull_isLB hN' _) (pull_isLB hL _), cls_pull hN', cls_pull hL, hc]

  have hNL' : pull (pullback.fst O.ι J) (cls N hN) = pull (pullback.snd O.ι J) (cls L hL) := by
    rw [← cls_pull hN, ← cls_pull hL]
    exact (cls_eq_iff (pull_isLB hN _) (pull_isLB hL _)).2 hNL

  obtain ⟨κ₂, hκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G GK J (isGrpPullback_pullback G (jK R))
  have hLamc : lam (cls L hL) (fst GK GK) (snd GK GK) = pull κ₂ (cls PP hPP) := by
    rw [← cls_cube_two hL (fst GK GK) (snd GK GK) (LB.isLB_linComb hL _ _), ← cls_pull hPP κ₂ (pull_isLB hPP _)]
    exact (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hPP _)).2 (hExt.2 κ₂ hκ)

  have hw : p₁ ≫ V.ι ≫ G.hom = p₂ ≫ GK.hom ≫ jK R := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (p₂ ≫ ·) pullback.condition
  let Ty : Over (Sp (FractionRing R)) := Over.mk (p₂ ≫ GK.hom)
  let y : Ty ⟶ GK := Over.homMk p₂ rfl
  have haw : a.left ≫ G.hom = 𝟙 _ := by simpa using Over.w a
  let aK : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK :=
    Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by rw [Category.assoc, haw]; simp)) (pullback.lift_snd _ _ _)
  let aY : Ty ⟶ GK := toUnit Ty ≫ aK
  have hzero : ∀ (z : 𝟙_ (Over (Sp (FractionRing R))) ⟶ GK) (c : Pic GK.left), pull (toUnit Ty ≫ z).left c = 0 := by
    intro z c
    rw [Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero (FractionRing R) (pull z.left c), map_zero]
  have haY : aY.left ≫ J = p₁ ≫ V.ι ≫ G.hom ≫ a.left := by
    have : aY.left = (p₂ ≫ GK.hom) ≫ aK.left := rfl
    rw [this, Category.assoc, show aK.left ≫ J = jK R ≫ a.left from pullback.lift_fst _ _ _, ← Category.assoc,
      ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc]
    rw [← Category.assoc p₁, ← Category.assoc (p₁ ≫ V.ι), Category.assoc p₁, hw]
    simp only [Category.assoc]

  have hsq : (lift y aY).left ≫ κ₂ = p₁ ≫ V.ι ≫ σ := by
    apply pullback.hom_ext
    · show ((lift y aY).left ≫ κ₂) ≫ (fst G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (fst G G).left
      rw [Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Category.assoc, σ, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
      exact pullback.condition.symm
    · show ((lift y aY).left ≫ κ₂) ≫ (snd G G).left = (p₁ ≫ V.ι ≫ σ) ≫ (snd G G).left
      rw [Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd, haY]
      show p₁ ≫ V.ι ≫ G.hom ≫ a.left = (p₁ ≫ V.ι ≫ (lift (𝟙 G) (toUnit G ≫ a)).left) ≫ (snd G G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Over.toUnit_left]
  have hlam : pull (p₁ ≫ V.ι ≫ σ) (cls PP hPP) = @id (Pic (pullback V.ι J)) (pull (y * aY).left (cls L hL)) - pull p₂ (cls L hL) := by
    have h := congrArg (pull (lift y aY).left) hLamc
    rw [pull_lam, lift_fst, lift_snd, ← pull_comp, hsq] at h
    rw [← h, lam, hzero, show (1 : Ty ⟶ GK) = toUnit Ty ≫ 1 from (MonObj.comp_one _).symm, hzero]
    simp only [sub_zero, add_zero]
    rfl

  let u : Over.mk (Ty.hom ≫ jK R) ⟶ G := Over.homMk (p₁ ≫ V.ι) (by simpa [Ty] using hw)
  have hmul : (y * aY).left ≫ J = p₁ ≫ V.ι ≫ T := by
    have e := (isGrpPullback_pullback G (jK R)).2 Ty y aY u (u ≫ toUnit G ≫ a) (pullback.condition (f := V.ι) (g := J))
      (by rw [haY, Over.comp_left, Over.comp_left, Over.toUnit_left]; show (p₁ ≫ V.ι) ≫ _ = _; simp only [Category.assoc])
    have e' : u * (u ≫ toUnit G ≫ a) = u ≫ (𝟙 G * (toUnit G ≫ a)) := by rw [MonObj.comp_mul, Category.comp_id]
    rw [← e, e', Over.comp_left]
    exact Category.assoc _ _ _
  have hq : (p₁ ≫ (T ∣_ O)) ≫ O.ι = (y * aY).left ≫ J := by
    rw [Category.assoc, morphismRestrict_ι, hmul]
  have hN2 := congrArg (pull (pullback.lift _ _ hq)) hNL'
  rw [← pull_comp, ← pull_comp, pullback.lift_fst, pullback.lift_snd] at hN2
  rw [map_sub, ← pull_comp, ← pull_comp, hN2, hlam]
  exact sub_sub_cancel _ _

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  first | exact @GlobalTheory.Mum.RigScale.exists_rig_rescale | exact GlobalTheory.Mum.RigScale.exists_rig_rescale | (intros; apply GlobalTheory.Mum.RigScale.exists_rig_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriesTransportUniformisingIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecTransport

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {β : Y ⟶ X}

lemma le_pull (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ (L.pull β).U (fun _ => j 0) ⊓ M.U i :=
  fun _ hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0, hy.2⟩

lemma le_one (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι) :
    Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c * ((res (le_pull j i) (ℓ.s (fun _ => j 0, i))) ^ k).val *
    (Y.presheaf.map (homOfLE (le_one j i)).op).hom (σ'.f (fun _ => i))

theorem gs_piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :
    gs r z _ (piece ℓ c k σ' j i) = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
      gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
  exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    (gs_res r z le_top hz c) ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans
      (congrArg (· ^ k) (gm_res r z (le_pull j i) hz _)))))))
    (gs_res r z (le_one j i) hz _))

theorem indep (hL : L.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : PGen ℓ) (k : ℕ) (σ' : H0 M k) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (j₀ : L.ι) (i i' : M.ι) (hj : β (r z) ∈ L.U j₀) (hi : r z ∈ M.U i) (hi' : r z ∈ M.U i') :
    (gw ℓ r z j₀ i ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) =
      (gw ℓ r z j₀ i' ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i')) (σ'.f (fun _ => i')) := by
  have e1 := hℓ Z r z j₀ j₀ i i' hj hj hi hi'
  rw [gm_self hL (r ≫ β) z hj, _root_.one_mul] at e1
  have hm : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hm' : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have e2 := sec_trans σ' r z hm hm'
  have e3 : trF (L := M) (fun _ : Fin 1 => 𝟙 Y) (fun _ => (k : ℤ)) r z (fun _ => i) (fun _ => i') =
      gm r z _ (M.g i i') ^ k := by
    simp only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast]
  rw [e2, e3, ← _root_.mul_assoc, ← Units.val_mul, e1, mul_pow, inv_pow,
    _root_.mul_comm ((gm r z _ (M.g i i') ^ k)⁻¹), _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

theorem exists_transport (hL : L.IsLB) (hM : M.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : ℓ.IsGen) (c : Γ(Y, ⊤))
    (k : ℕ) (σ' : H0 M k) : ∃ σ : SecK L β k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good M z J' →
      sval σ r z J = gs r z ⊤ c * (gw ℓ r z (J (r ≫ β)) (J' r) ^ k).val * sval σ' r z J' := by
  have hP := (isGen_iff ℓ).1 hℓ
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (i : M.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => β) j → r z ∈ M.U i →
      gs r z _ a = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
        gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
    intro j
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun i : M.ι => LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i)
      (LB.wchart L (fun _ : Fin 1 => β) j) (fun i => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨(exists_chart hM y).choose, hy, (exists_chart hM y).choose_spec⟩)
      (fun i => piece ℓ c k σ' j i) (fun i i' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [gs_piece ℓ c k σ' j i (𝟙 Y) y hy.1, gs_piece ℓ c k σ' j i' (𝟙 Y) y hy.2, _root_.mul_assoc, _root_.mul_assoc]
        exact congrArg _ (indep hL ℓ hP k σ' (𝟙 Y) y (j 0) i i' (Set.mem_iInter.1 hy.1.1 0) hy.1.2 hy.2.2))
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha i)).trans (gs_piece ℓ c k σ' j i r z hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    change gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j) (a j) =
      _ * gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j') (a j')
    rw [ha j _ (𝟙 Y) y i hy.1 hi, ha j' _ (𝟙 Y) y i hy.2 hi]
    have e1 := hP Y (𝟙 Y) y (j 0) (j' 0) i i (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0) hi hi
    rw [gm_self hM (𝟙 Y) y hi, inv_one, _root_.mul_one] at e1
    rw [e1]
    simp only [Fin.prod_univ_one, zpow_natCast, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  · rw [sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => β) r) (hJ' r)

end GlobalTheory.Mum.SecTransport

namespace GlobalTheory.Mum

theorem Trait.exists_carries : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W)
    (σ' : H0 T.U.LG.L k), ∃ σ'' : SecK C.P.L.L T.β k, T.Carries u σ' σ'' := by
  intro R _ _ _ D C W _ _ _ T k u σ'
  exact SecTransport.exists_transport C.P.L.isLB T.U.LG.isLB T.ℓ T.ℓ_gen (scal T.G.hom u) k σ'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaDescriptionAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalThetaDescription_abelianPart : ∀ κ : Rule, Rule4 κ → AllC fun {R} _ _ {D} _ {N} ν => 1 ≤ D.P.g → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  first | exact @GlobalTheory.MBLow.AbCl.exists_ab_keyOK | exact GlobalTheory.MBLow.AbCl.exists_ab_keyOK | (intros; apply GlobalTheory.MBLow.AbCl.exists_ab_keyOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernelStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubgroupScheme_poincare_left_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧ Triv (ev P (fst N B ≫ i) (snd N B)) ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  first | exact @GlobalTheory.DualKernel.exists_closed_subgroup_ker | exact GlobalTheory.DualKernel.exists_closed_subgroup_ker | (intros; apply GlobalTheory.DualKernel.exists_closed_subgroup_ker <;> assumption)
end

