import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrincSubring

section Transport

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {Z : Scheme.{0}} (f : Z ⟶ X')
    (z : Z) {k : L'.ι} (hk : f z ∈ L'.U k) : gm f z (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (f z))
  have e := hw Z f z j j k k hj hj hk hk
  rw [gm_self hL (f ≫ F) z hj, _root_.one_mul] at e
  exact inv_eq_one.1 (mul_eq_right.1 e.symm)

theorem trF_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {q : K → L'.ι} (hq : r z ∈ LB.wchart L' φ' q) :
    trF (L := L') φ' ε r z q q = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self_of_pGen hw hL (r ≫ φ' k) z (Set.mem_iInter.1 hq k), one_zpow]

theorem exists_down_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self_of_pGen hw hL _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

end Transport

theorem kerAlong_of_pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  intro S S' f A _ P A₁ _ P₁ φ φ₂ hP₁ h hs hw hK T a ha x hx
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨c, hc⟩ := hx
  let T' : Over S' := Over.mk a
  have hxw : x.left ≫ A₁.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : T' ⟶ A := Over.homMk (h.1.lift x.left a hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = x.left := h.1.lift_fst _ _ _
  have key : x' = 1 := hK T' x' <| by
    let b : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ T := Over.homMk (fst T' A).left (by
      show (fst T' A).left ≫ T.hom = (T' ⊗ A).hom ≫ f
      rw [← ha, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (fst T' A)))
    let c' : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ A₁ := pushPt h.1.w (snd T' A)
    have k₁ : (lift b c').left ≫ (fst T A₁).left = (fst T' A).left := congrArg (fun q => q.left) (lift_fst b c')
    have k₂ : (lift b c').left ≫ (snd T A₁).left = (snd T' A).left ≫ φ := congrArg (fun q => q.left) (lift_snd b c')
    have k₃ : (fst T' A ≫ x').left ≫ φ = (lift b c').left ≫ (fst T A₁ ≫ x).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc, k₁]
    have k₄ := GlobalTheory.SiegelDescent.lift_comp_square hs (T' := T' ⊗ A) (lift b c').left _ _ _ _ k₃ k₂.symm
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame P₁
      (fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left ≫ φ₂) _ _ (lift b c').left fun _ => k₄) c hc
    exact exists_down_of_pGen (φ' := fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left) (ε := fun _ => 1)
      ((isGen_iff w).1 hwg) hP₁ c₂ h₂
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) (by
    show 𝟙 T.left ≫ T.hom = a ≫ f
    rw [Category.id_comp, ha])
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext (by
    show 𝟙 T.left ≫ x.left = x'.left ≫ φ
    rw [Category.id_comp, hx'])
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A₁) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  have e₃ : 𝟙 T.left ≫ x.left = 𝟙 T.left ≫ (1 : T ⟶ A₁).left := congrArg (fun q => q.left) e₂
  exact Over.OverMorphism.ext (by simpa only [Category.id_comp] using e₃)

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral GlobalTheory.KTrivSpread

noncomputable section

namespace GlobalTheory.PrincSubring

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}
variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)
variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)

include hadd hsym hLW hmon huniv in

theorem trivAlong_of_kernelAlong {S' : Scheme.{0}} (g : S' ⟶ S) (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A,
      pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : TrivAlong G L g := by
  intro T a ha x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv T fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    (T.left.openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 :=
    (hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e

include hadd hsym hLW hmon huniv in

theorem kernelAlong_of_trivAlong {S' : Scheme.{0}} (g : S' ⟶ S) (u₀ : Fin n) (hK : TrivAlong G L g)
    (T : Over S) (a : T.left ⟶ S') (ha : a ≫ g = T.hom) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  obtain ⟨y, hy, -⟩ := huniv T fun u => if u = u₀ then x else 1
  have hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0 := fun Z b z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z b).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK T a ha y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have h := hy u₀
  rw [if_pos rfl, h1, MonObj.one_comp] at h
  exact h.symm

end Calc

theorem kerAlong_iff_trivAlong : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}}
    (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  intro S h A _ _ P hs hA S' g
  obtain ⟨hab, -, hP, hr₁, hr₂, hsw⟩ := hs
  have hadd : ∀ (T : Over S) (x x' y : T ⟶ A),
      pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A
      (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    unfold PrincipalIntegral.pair
    abel
  have hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x := fun T x y => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsw
    have k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    unfold PrincipalIntegral.pair
    rw [← k, pull_comp, ← e]
  obtain ⟨-, hdet⟩ := isE8_W8
  have hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u :=
    fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP _ _
  have hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A) := cls_linComb hP _ _ _
  have tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x) :=
    fun T x => by
      rw [PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)
  constructor
  · intro hk
    exact trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)
  · intro hK T a ha x hx
    exact kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)

end GlobalTheory.PrincSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelStable_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (exact GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (intros; apply GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelThetaSeriesSpanOverClassRepresentativesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_thetaSeries_span_over_class_representatives : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ), KernelSpanOverClasses R i U ψ ph v (ownAt D v) := by
  first | exact @GlobalTheory.OneKernelSpan.kernelSpanOverClasses_of | exact GlobalTheory.OneKernelSpan.kernelSpanOverClasses_of | (intros; apply GlobalTheory.OneKernelSpan.kernelSpanOverClasses_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_fibre_of_composable_baseChange : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)) (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  first | exact @GlobalTheory.KeyEven.keyPB_of_keyOn_comp | exact GlobalTheory.KeyEven.keyPB_of_keyOn_comp | (intros; apply GlobalTheory.KeyEven.keyPB_of_keyOn_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  first | exact @GlobalTheory.KeyEvenBC.keyOn_pullback | exact GlobalTheory.KeyEvenBC.keyOn_pullback | (intros; apply GlobalTheory.KeyEvenBC.keyOn_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  intro k K K' _ _ _ _ c c' e hce n x T φ S S' hx hS h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FieldPair.placeEquiv_ringEquiv c c' e hce
  have hmem : ∀ (P : Place c) (b : K'), b ∈ (Φ P).ring ↔ e.symm b ∈ P.ring := fun P b => by
    simpa using (hΦ P).1 (e.symm b)
  have hord : ∀ (P : Place c) (b : K'), (Φ P).ord b = P.ord (e.symm b) := fun P b => by
    simpa using (hΦ P).2.1 (e.symm b)
  have hdisc : ∀ P : Place c, (Φ P).disc (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) =
      P.disc (dForm c x) φ := fun P => by
    simp only [Place.disc]
    rw [(hΦ P).2.2.1 φ, (hΦ P).2.2.2 n x hx]
  have hΦS : Φ S = S' := Place.ext (ValuationSubring.ext _ _ fun b => by
    rw [hmem, ← hS (e.symm b), e.apply_symm_apply])
  have hk : Klt c n ⊤ (dForm c x) φ := ⟨h.1, h.2.1, fun P hP =>
    (P.ring_ne_top (eq_top_iff.2 fun f _ => hP f trivial)).elim⟩
  have hk' := ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x ⊤ φ hx).2.2.1).1 hk
  refine ⟨hk'.1, hk'.2.1, ?_⟩
  intro Q' hQ' t' u' E' hTQ hmax hdim hSQ hEQ ht hu hoth
  set Q : Subring K := Q'.map e.symm.toRingHom with hQdef
  have hQmem : ∀ a : K, a ∈ Q ↔ e a ∈ Q' := fun a => by
    exact Subring.mem_map_equiv (f := e.symm) (K := Q')
  have hQQ : Q.map e.toRingHom = Q' := by
    ext b
    exact (Subring.mem_map_equiv (f := e) (K := Q)).trans ((hQmem _).trans (by rw [e.apply_symm_apply]))
  have hQ : IsLocModel c Q :=
    ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x Q φ hx).2.1).2 (hQQ ▸ hQ')
  let ψ : Q' ≃+* Q := e.symm.subringMap
  have hψ : ∀ y, ((ψ y : Q) : K) = e.symm y := fun y => rfl
  have hprime : ∀ P : Place c, (Φ P).IsPrimeOf Q' ↔ P.IsPrimeOf Q := by
    intro P
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · have := h1 (e f) ((hQmem f).1 hf)
        rwa [hmem, e.symm_apply_apply] at this
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ :=
          h2 (e f) (by rw [hmem, e.symm_apply_apply]; exact hf)
        refine ⟨e.symm a, by rw [hQmem, e.apply_symm_apply]; exact ha,
          e.symm b, by rw [hQmem, e.apply_symm_apply]; exact hb,
          by simpa using hb0, by rw [← hord]; exact hbo, ?_⟩
        apply e.injective
        rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hfab]
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rw [hmem]
        exact h1 _ (by rw [hQmem, e.apply_symm_apply]; exact hf)
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ := h2 (e.symm f) ((hmem P f).1 hf)
        refine ⟨e a, (hQmem a).1 ha, e b, (hQmem b).1 hb, by simpa using hb0,
          by rw [hord, e.symm_apply_apply]; exact hbo, ?_⟩
        rw [← hfab, map_mul, e.apply_symm_apply]
  set E := Φ.symm E' with hEdef
  have hE : Φ E = E' := Φ.apply_symm_apply E'
  haveI := hQ'.isLocalRing
  haveI := hQ.isLocalRing
  have hTQ' : T ≤ Q := fun f hf => (hQmem f).2 (hTQ (Subring.mem_map.2 ⟨f, hf, rfl⟩))
  have hmax' : Ideal.span {ψ t', ψ u'} = IsLocalRing.maximalIdeal Q := by
    have h1 := congrArg (Ideal.map ψ) hmax
    rw [Ideal.map_span, Set.image_pair] at h1
    rw [h1]
    ext z
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      rwa [isUnit_map_iff]
    · intro hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
      rwa [isUnit_map_iff ψ.symm]
  have hdim' : ringKrullDim Q = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ψ]
    exact hdim
  have hSQ' : S.IsPrimeOf Q := (hprime S).1 (hΦS ▸ hSQ)
  have hEQ' : E.IsPrimeOf Q := (hprime E).1 (hE ▸ hEQ)
  have ht' : S.ord ((ψ t' : Q) : K) = 1 := by
    rw [hψ, ← hord, hΦS]
    exact ht
  have hu' : E.ord ((ψ u' : Q) : K) = 1 := by
    rw [hψ, ← hord, hE]
    exact hu
  have hoth' : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.disc (dForm c x) φ = 0 := by
    intro P hP hPS hPE
    rw [← hdisc]
    refine hoth (Φ P) ((hprime P).2 hP) (fun hr => hPS ?_) (fun hr => hPE ?_)
    · have h3 : Φ P = Φ S := Place.ext (hr.trans (congrArg Place.ring hΦS).symm)
      rw [Φ.injective h3]
    · have h3 : Φ P = Φ E := Place.ext (hr.trans (congrArg Place.ring hE).symm)
      rw [Φ.injective h3]
  have key := h.2.2 Q hQ (ψ t') (ψ u') E hTQ' hmax' hdim' hSQ' hEQ' ht' hu' hoth'
  rw [← hE, hdisc]
  exact key

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_change_of_tangent_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  first | exact @GlobalTheory.KSFrameChange.isKS_frame_change | exact GlobalTheory.KSFrameChange.isKS_frame_change | (intros; apply GlobalTheory.KSFrameChange.isKS_frame_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivialStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_zero_tangent_trivial : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  first | exact @GlobalTheory.FlagTan.eq_const_of_isKS_zero | exact GlobalTheory.FlagTan.eq_const_of_isKS_zero | (intros; apply GlobalTheory.FlagTan.eq_const_of_isKS_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kunneth_cup_tensor_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom), ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 → ∑ i, x i ⊗ₜ[K] y i = 0 := by
  first | exact @GlobalTheory.Kunneth.cup_tmul_injective | exact GlobalTheory.Kunneth.cup_tmul_injective | (intros; apply GlobalTheory.Kunneth.cup_tmul_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimagStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  first | exact @GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | exact GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | (intros; apply GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularityOfDensityStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularity_of_density : DensSt → ModSt := by
  first | exact @GlobalTheory.FlatModel.modSt_of_densSt | exact GlobalTheory.FlatModel.modSt_of_densSt | (intros; apply GlobalTheory.FlatModel.modSt_of_densSt <;> assumption)
end

