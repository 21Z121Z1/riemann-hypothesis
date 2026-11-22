import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortCentralMove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLifts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_comp_map {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (V : X.Opens) (hz : h (g z) ∈ V)
    (a : Γ(X, V)) : gs (g ≫ h) z V a = (g.stalkMap z).hom (gs h (g z) V a) := by
  rw [← gs_pull g h z V hz a, gs_eq_map_gs g z (h ⁻¹ᵁ V) hz, gs_pull (𝟙 Y) h (g z) V hz a, Category.id_comp]

theorem secCarriedOver_of_lift {X Z P : Scheme.{0}} (q : Z ⟶ X) (p₁ : Z ⟶ P) (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (d : ℕ) (B : Fin d → Γ(P, ⊤))
    (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k))
    (hdec : ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
      gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs p₁ z ⊤ (B l) * gs q z (O ⊓ L.U k) (s l k))
    (huniq : ∀ (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U →
      (∀ z : Z, q z = x → ∑ l, gs p₁ z ⊤ (B l) * gs q z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0)
    (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)) (f' : Z ⟶ Z) (hf'q : f' ≫ q = q ≫ φ) (hf'p : f' ≫ p₁ = p₁)
    (hcar : FrameCarriedAlong L q (q ⁻¹ᵁ W) τ φ w f') (l : Fin d) : SecCarriedOver L O (s l) φ w := by
  have hpt : ∀ z, q (f' z) = φ (q z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hf'q, Scheme.Hom.comp_apply]
  intro x j k hxO hφxO hxk hφxj
  let U' : X.Opens := O ⊓ L.U k ⊓ φ ⁻¹ᵁ (O ⊓ L.U j) ⊓ ((L.pull φ).U (fun _ => j) ⊓ L.U k)
  have h1 : U' ≤ φ ⁻¹ᵁ (O ⊓ L.U j) := fun _ h => h.1.2
  have h2 : U' ≤ (L.pull φ).U (fun _ => j) ⊓ L.U k := fun _ h => h.2
  have h3 : U' ≤ O ⊓ L.U k := fun _ h => h.1.1
  let a : Fin d → Γ(X, U') := fun l' =>
    (X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j)) -
      (X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val * (X.presheaf.map (homOfLE h3).op).hom (s l' k)
  have ha : ∀ {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (hy : g y ∈ U') (l' : Fin d),
      gs g y U' (a l') = gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) -
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val * gs g y (O ⊓ L.U k) (s l' k) := by
    intro Y g y hy l'
    have e1 : gs g y U' ((X.presheaf.map (homOfLE h1).op).hom ((φ.app (O ⊓ L.U j)).hom (s l' j))) =
        gs (g ≫ φ) y (O ⊓ L.U j) (s l' j) :=
      (gs_res g y h1 hy _).trans (gs_pull g φ y (O ⊓ L.U j) (h1 hy) _)
    have e2 : gs g y U' ((X.presheaf.map (homOfLE h2).op).hom (w.s (fun _ => j, k)).val) =
        (gm g y ((L.pull φ).U (fun _ => j) ⊓ L.U k) (w.s (fun _ => j, k))).val :=
      (gs_res g y h2 hy _).trans (gs_unit g y _ (h2 hy) _)
    have e3 : gs g y U' ((X.presheaf.map (homOfLE h3).op).hom (s l' k)) = gs g y (O ⊓ L.U k) (s l' k) :=
      gs_res g y h3 hy _
    rw [gs_sub' g y U' hy, gs_mul g y U' hy, e1, e2, e3]
  have hxU : x ∈ U' := ⟨⟨⟨hxO, hxk⟩, hφxO, hφxj⟩, mem_pull.2 hφxj, hxk⟩
  have key := huniq U' a x hxU (by
    intro z hz
    have hzU : q z ∈ U' := hz ▸ hxU
    have hzO : q z ∈ O := hz ▸ hxO
    have hzk : q z ∈ L.U k := hz ▸ hxk
    have hzW : z ∈ q ⁻¹ᵁ W := hOW hzO
    have hf'zO : q (f' z) ∈ O := by rw [hpt, hz]; exact hφxO
    have hf'zj : q (f' z) ∈ L.U j := by rw [hpt, hz]; exact hφxj
    have hmj : q (f' z) ∈ O ⊓ L.U j := ⟨hf'zO, hf'zj⟩
    have hmWj : f' z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j := ⟨hOW hf'zO, hf'zj⟩
    have hmWk : (𝟙 Z) z ∈ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := ⟨hzW, hzk⟩
    have hcz := hcar z j k hzW (hOW hf'zO) hzk hf'zj
    have S1 : ∑ l', gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) =
        (gm f' z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U j) (τ j)).val := by
      have e1 : ∀ l', gs p₁ z ⊤ (B l') = (f'.stalkMap z).hom (gs p₁ (f' z) ⊤ (B l')) := fun l' => by
        conv_lhs => rw [← hf'p]
        exact gs_comp_map f' p₁ z ⊤ trivial _
      have e2 : ∀ l', gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) = (f'.stalkMap z).hom (gs q (f' z) (O ⊓ L.U j) (s l' j)) :=
        fun l' => by rw [← hf'q]; exact gs_comp_map f' q z _ hmj _
      simp only [e1, e2, ← map_mul, ← map_sum]
      rw [← hdec (f' z) j hf'zO hf'zj, ← gs_eq_map_gs f' z _ hmWj, gs_unit f' z _ hmWj]
    have S3 := hdec z k hzO hzk
    rw [gs_unit (𝟙 Z) z _ hmWk] at S3
    have e4 : ∀ l', gs p₁ z ⊤ (B l') * gs q z U' (a l') =
        gs p₁ z ⊤ (B l') * gs (q ≫ φ) z (O ⊓ L.U j) (s l' j) -
          (gw w q z j k).val * (gs p₁ z ⊤ (B l') * gs q z (O ⊓ L.U k) (s l' k)) := fun l' => by
      rw [ha q z hzU l', gw]; ring
    rw [Finset.sum_congr rfl (fun l' _ => e4 l'), Finset.sum_sub_distrib, ← Finset.mul_sum, S1, ← S3, hcz,
      Units.val_mul, sub_self])
  have e := key l
  rw [ha (𝟙 X) x hxU l, Category.id_comp, sub_eq_zero] at e
  exact e

theorem secCarriedOver_of_frameCarriedAlong : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X) (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ (φ : X ⟶ X) (w : LB.Iso L (L.pull φ)), φ ≫ f = f → (∀ f' : (pullback f (spMap ρ₁)) ⟶ (pullback f (spMap ρ₁)), f' ≫ (pullback.fst f (spMap ρ₁)) = (pullback.fst f (spMap ρ₁)) ≫ φ → f' ≫ (pullback.snd f (spMap ρ₁)) = (pullback.snd f (spMap ρ₁)) → FrameCarriedAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ φ w f') → ∀ l, SecCarriedOver L O (s l) φ w := by
  intro R R₁ _ _ ρ₁ d b hb X f L W O hOW τ s hdec φ w hφ hcar l
  have hcond : (pullback.fst f (spMap ρ₁) ≫ φ) ≫ f = pullback.snd f (spMap ρ₁) ≫ spMap ρ₁ := by
    rw [Category.assoc, hφ, pullback.condition]
  have hf'q : pullback.lift _ _ hcond ≫ pullback.fst f (spMap ρ₁) = pullback.fst f (spMap ρ₁) ≫ φ :=
    pullback.lift_fst _ _ _
  have hf'p : pullback.lift _ _ hcond ≫ pullback.snd f (spMap ρ₁) = pullback.snd f (spMap ρ₁) :=
    pullback.lift_snd _ _ _
  exact secCarriedOver_of_lift (pullback.fst f (spMap ρ₁)) (pullback.snd f (spMap ρ₁)) L W O hOW τ d
    (fun l => (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) s hdec
    (fun U a x hx hz => GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange R R₁ ρ₁ d b hb X f U a x hx hz) φ w _ hf'q hf'p (hcar _ hf'q hf'p) l

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowPull

theorem tri_succ (n : ℤ) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  have : (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_neg (n : ℤ) : tri (-n) = tri n - n := by
  unfold tri
  have : n * n + n = -n * -n + -n + n * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

theorem eq_of_rec {M : Type*} [AddCommGroup M] (f : ℤ → M) (a l : M) (h0 : f 0 = 0)
    (hs : ∀ n, f (n + 1) = f n + a + n • l) (n : ℤ) : f n = n • a + tri (-n) • l := by
  have step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n := fun n => by
    rw [tri_neg, tri_neg, tri_succ]; ring
  induction n using Int.induction_on with
  | zero => simp [h0, tri]
  | succ n ih => rw [hs, ih, step]; module
  | pred n ih =>
    have h := hs (-(n : ℤ) - 1)
    have h' := step (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h h'
    rw [ih, h'] at h
    rw [eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]
    module

open GlobalTheory.CechPic in

theorem pull_zpow : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  intro K _ A _ hA L hL T z n
  have := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h1 : pull (1 : T ⟶ A).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]
  let φ : (T ⟶ A) →* Multiplicative (Pic T.left) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by
      rw [lam_mul_left hL hΘ, ofAdd_add]
  have hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z := fun m =>
    congrArg Multiplicative.toAdd (map_zpow φ z m)
  have key := eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z)
    (by rw [zpow_zero, h1]) (fun m => by
      rw [← hz, zpow_add_one, lam, h1]; abel)
  have k1 := key (-1)
  have t1 : tri (- -1) = 1 := by decide
  rw [zpow_neg_one, t1] at k1
  rw [key n, k1, tri_neg]
  module

end GlobalTheory.PowPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParameteStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  first | exact @GlobalTheory.pull_two_nsmul_eq_zero_of_triples | exact GlobalTheory.pull_two_nsmul_eq_zero_of_triples | (intros; apply GlobalTheory.pull_two_nsmul_eq_zero_of_triples <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultiple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.HeartFrame

theorem splitOffBad_of_mul {D : D7} (V : HSp D) (a b : ℕ) (h : GA D V) (hs : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := hs
  refine ⟨h1, e, P, h2, fun PP hPP ha => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ ha

set_option maxHeartbeats 2000000 in

theorem central_short_series_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨x', ε, hx', hε, hmv⟩ := GlobalTheory.CentralLevelMove.short_central_move D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h (splitOffBad_of_mul _ _ _ _ hSB) hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨h0L, m0, hm0, h0⟩ := GlobalTheory.AdTh.CoverRoot.covAt_base_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP c0 hcov
  obtain ⟨c0', h1L, ⟨m1, hm1, h1⟩, hcT⟩ := GlobalTheory.OnCmp.CoverRoot.cover_value_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hF0 hdel hRun χ hK.chr
  have hrat : c0' * c0⁻¹ ∈ D.what₂.embLL.range := by
    obtain ⟨a, ha⟩ := h1L
    obtain ⟨b, hb⟩ := h0L
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv₀, ha, hb]⟩
  have hroot : (c0' * c0⁻¹) ^ (m1 * m0) = 1 := by
    rw [mul_pow, inv_pow, pow_mul, h1, one_pow, mul_comm m1, pow_mul, h0]
    simp
  obtain ⟨y₀, c, hrk, hint, hmain⟩ := GlobalTheory.FrameShort.short_at_frame D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x' P y hUm hTb hTd hLev hx' hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hrat ⟨m1 * m0, Nat.mul_pos hm1 hm0, hroot⟩ hcT
  refine ⟨y₀, ε * c, hrk, fun lam hlam => ?_, fun φ' hφ' w hw F₀ hF₀ g => ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint lam hlam
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact hε.mul hsi
  obtain ⟨F₁, hF₁, he⟩ := hmv F₀ hF₀
  have e3 := hmain φ' hφ' w hw F₁ hF₁ g
  rw [he, map_mul]
  linear_combination (D.what₂.embLL ε) * e3

end GlobalTheory.HeartFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartTransitionMapsDescendOverlaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem chart_transition_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ (i j : J) (V : U.left.Opens), (∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j)) → ∃ τ : V.toScheme ⟶ U.left, ∀ (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ V.toScheme), a ≫ e i = b ≫ e j → v ≫ V.ι = a ≫ pullback.fst _ _ → v ≫ τ = b ≫ pullback.fst _ _ := by
  intro R _ _ _ _ S X π hπ hs hS U hU J e he hkey i j V hV
  have hpb0 : IsPullback (pullback.fst U.hom π ∣_ V) (pullback.fst U.hom π ⁻¹ᵁ V).ι V.ι
      (pullback.fst U.hom π) := isPullback_morphismRestrict _ _
  have hpb : IsPullback (pullback.fst U.hom π ∣_ V)
      ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ pullback.snd U.hom π) (V.ι ≫ U.hom) π :=
    hpb0.paste_vert (IsPullback.of_hasPullback U.hom π)
  have hflat : Flat (V.ι ≫ U.hom) := inferInstance
  have hrange : Set.range ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i).base ⊆ Set.range (e j).base := by
    rintro _ ⟨z, rfl⟩
    have hz : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ pullback.fst U.hom π ⁻¹ᵁ V := by
      have h0 : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ Set.range (pullback.fst U.hom π ⁻¹ᵁ V).ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at h0
    simpa using (hV _).1 hz
  let hZ := IsOpenImmersion.lift (e j) ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i) hrange
  have hZe : hZ ≫ e j = (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  let p' := pullback.fst U.hom π ∣_ V
  have heq : pullback.fst p' p' ≫ (hZ ≫ pullback.fst U.hom π) =
      pullback.snd p' p' ≫ (hZ ≫ pullback.fst U.hom π) := by
    obtain ⟨h₂, h₂e, h₂p⟩ := hkey i j (pullback p' p') (pullback.fst p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι)
      (pullback.snd p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι) (pullback.fst p' p' ≫ hZ)
      (by simp only [Category.assoc, ← morphismRestrict_ι]; rw [pullback.condition_assoc])
      (by simp only [Category.assoc, hZe])
    have : h₂ = pullback.snd p' p' ≫ hZ := by
      rw [← cancel_mono (e j), h₂e]; simp only [Category.assoc, hZe]
    subst this
    simpa only [Category.assoc] using h₂p.symm
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S V.toScheme (pullback.fst U.hom π ⁻¹ᵁ V).toScheme U.left π
    (V.ι ≫ U.hom) p' _ hπ hs hS hflat hpb _ heq
  refine ⟨τ, fun T a b v hab hv => ?_⟩
  let a' := hpb0.lift v a hv
  have ha'1 : a' ≫ p' = v := hpb0.lift_fst _ _ _
  have ha'2 : a' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι = a := hpb0.lift_snd _ _ _
  have ha'3 : a' ≫ hZ = b := by
    rw [← cancel_mono (e j), Category.assoc, hZe, ← Category.assoc, ha'2, hab]
  rw [← ha'1, Category.assoc, hτ, ← Category.assoc, ha'3]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubringStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_mem_dominating_valuationSubring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  first | exact @GlobalTheory.Mum.chartVal_mem_of_dominates | exact GlobalTheory.Mum.chartVal_mem_of_dominates | (intros; apply GlobalTheory.Mum.chartVal_mem_of_dominates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureLowerTriangularPositiveDiagonalStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  first | exact @GlobalTheory.ChernCalc.curv_lowerTriangular | exact GlobalTheory.ChernCalc.curv_lowerTriangular | (intros; apply GlobalTheory.ChernCalc.curv_lowerTriangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormNewtonIdentitiesCurvaturePowerSumsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_newton_identities_curvature_power_sums : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j = -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  first | exact @GlobalTheory.ChernCalc.chernAt_newton | exact GlobalTheory.ChernCalc.chernAt_newton | (intros; apply GlobalTheory.ChernCalc.chernAt_newton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphicStatement
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (φ : V n → V n) (v : V n), AnalyticAt ℂ φ v → MContDiffAt 2 H (φ v) → IsUnit (H (φ v)).det → ∀ j, (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt n) := by
  first | exact @GlobalTheory.CxForm.chernAt_comp | exact GlobalTheory.CxForm.chernAt_comp | (intros; apply GlobalTheory.CxForm.chernAt_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTopPowerPullbackSmallerDimEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernLowDim

open MeasureTheory Set GlobalTheory.ChartGlue GlobalTheory.Points

theorem det_mul_mul_eq_zero {m n : ℕ} (hmn : m < n) (P : Matrix (Fin n) (Fin m) ℂ)
    (K : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin m) (Fin n) ℂ) : (P * K * Q).det = 0 := by
  by_contra h
  have hu : IsUnit (P * K * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (P * K * Q).rank ≤ m :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
      ((Matrix.rank_le_card_width P).trans (by simp))
  simp only [Fintype.card_fin] at h1
  omega

theorem chernPart_pull_of_lt : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  intro k _ X Y _ _ p q e e' hX hY hlt g hg hgen N σ ε
  obtain ⟨T, hT, hTg, hc⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p e hX
  set Z : Set Y := (⇑g) ⁻¹' T with hZdef
  have hZ : IsClosed Z := hT.preimage g.continuous
  have hZg : genericPoint Y ∉ Z := by
    simp only [hZdef, mem_preimage, hgen]
    exact hTg
  set φ := (N.pull g hg).φ σ
  set A : Set (CxPts q σ) := {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} with hAdef
  have h0 : φ.chernPart e' ε A = 0 := GlobalTheory.ChernNull.chernPart_over_closed hY Z hZ hZg σ φ ε
  have hA : MeasurableSet A := by
    have : A = (ptsIn q σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [hAdef, mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl

  have hdens : ∀ (c : AlgChart q σ e') (y : CxPts q σ), y ∈ c.e.source → y ∉ A →
      c.chernDens φ y = 0 := by
    intro c y hys hyA
    have hy' : (PtsOver.map g hg (spMap σ) y).1 (IsLocalRing.closedPoint ℂ) ∉ T := by
      intro hT'
      exact hyA (show g (y.1 (IsLocalRing.closedPoint ℂ)) ∈ T from hT')
    obtain ⟨c', hc'⟩ := hc σ _ hy'
    obtain ⟨P, Q, hPQ⟩ := GlobalTheory.HessPull.hess_pull_factor k X Y p q g hg σ e' e c c' y hys hc'
    obtain ⟨K, hK⟩ := hPQ N (pick φ.isLB y) (mem_pick _ y)
    rw [AlgChart.chernDens, hK, det_mul_mul_eq_zero hlt, Complex.zero_re, mul_zero]
  have key : φ.chernPart e' ε ≤ (φ.chernPart e' ε).restrict A := iSup_le fun c => by
    have e0 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Aᶜ = 0 := by
      rw [chartMeas_apply _ _ hA.compl]
      have hm := measurableSet_image c.e (c.e.open_source.measurableSet.inter hA.compl)
        inter_subset_left
      rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, lintegral_zero]
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1, hdens c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := A) (mem_ae_iff.2 e0)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart q σ e' =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) c)
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ((key univ).trans_eq ?_) zero_le)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, h0]

end GlobalTheory.ChernLowDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_complement_dense_open_null_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  first | exact @GlobalTheory.ChernNullField.chernPart_compl_null | exact GlobalTheory.ChernNullField.chernPart_compl_null | (intros; apply GlobalTheory.ChernNullField.chernPart_compl_null <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordConstantOnProjectionFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_productCoord_constant_on_projectionFibres : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left) → ∀ z z' : O.toScheme, pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z) = pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z') → (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z)) = closedPoint R → h z = h z' := by
  first | exact @GlobalTheory.Mum.Near.closed_fibre_constant | exact GlobalTheory.Mum.Near.closed_fibre_constant | (intros; apply GlobalTheory.Mum.Near.closed_fibre_constant <;> assumption)
end

