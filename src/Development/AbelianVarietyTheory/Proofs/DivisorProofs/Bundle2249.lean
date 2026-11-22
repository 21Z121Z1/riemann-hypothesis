import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionNthPowerDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} (P : PolAV S)

def toProd : P.A.left ⟶ (baseOver S ⊗ P.A).left := (λ_ P.A).inv.left

theorem toProd_snd : toProd P ≫ (snd (baseOver S) P.A).left = 𝟙 _ := by
  have h := congrArg (fun f => f.left) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Over.id_left, leftUnitor_hom] at h
  exact h

variable {P}
theorem chart_le {n : ℕ} (j : PUnit → P.L.ι) :
    (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ()) := by
  intro y hy
  have hy' : y ∈ P.L.U (j ()) := Set.mem_iInter.1 hy ()
  refine Set.mem_iInter.2 fun _ => ?_
  show (toProd P ≫ (snd (baseOver S) P.A).left).base y ∈ P.L.U (j ())
  rw [toProd_snd]; exact hy'
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
theorem coe_res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    ((res h (pullU f U x) : Γ(Y, W)ˣ) : Γ(Y, W)) = (f.appLE U W h).hom x := by
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem appLE_res_pullU_pow {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h1 : V ≤ g ⁻¹ᵁ U) (h2 : W ≤ f ⁻¹ᵁ V) (h3 : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) (n : ℕ) :
    (f.appLE V W h2).hom ((res h1 (pullU g U x)).val ^ n) =
      (res h3 (pullU (f ≫ g) U x)).val ^ n := by
  rw [map_pow, coe_res_pullU, coe_res_pullU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem res_pullU_of_eq {X Y : Scheme.{0}} {f g : Y ⟶ X} (hfg : f = g) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : res h (pullU f U x) = res (hfg ▸ h) (pullU g U x) := by
  subst hfg; rfl

variable {S : Scheme.{0}} {P : PolAV S}
theorem g_eq {n : ℕ} (i j : PUnit → P.L.ι)
    (e : (lbPow P.L n).U i ⊓ (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ ((LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => i ()) ⊓
      (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ()))) :
    ((toProd P).appLE _ _ e).hom ((LPow P.A P.L (n : ℤ) (baseOver S)).g (fun _ => i ()) (fun _ => j ())).val =
      ((lbPow P.L n).g i j).val := by
  simp only [LPow, LB.LinComb, Units.coe_prod, Fin.prod_univ_one, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  simp only [lbPow, LB.LinComb, Units.coe_prod, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  refine (appLE_res_pullU_pow (toProd P) (snd (baseOver S) P.A).left (P.L.U (i ()) ⊓ P.L.U (j ()))
    ((P.L.wchart (fun _ : Fin 1 => (snd (baseOver S) P.A).left) fun _ => i ()) ⊓
      P.L.wchart (fun _ : Fin 1 => (snd (baseOver S) P.A).left) fun _ => j ())
    (P.L.wchart (fun _ : PUnit => 𝟙 P.A.left) i ⊓ P.L.wchart (fun _ : PUnit => 𝟙 P.A.left) j) _ e ?_ (P.L.g (i ()) (j ())) n).trans ?_
  · rw [toProd_snd]
    intro z hz
    exact ⟨Set.mem_iInter.1 hz.1 (), Set.mem_iInter.1 hz.2 ()⟩
  · rw [res_pullU_of_eq (toProd_snd P)]
    rfl
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} {P : PolAV S}

def descSec (n : ℕ) (t : LB.Sec (LPow P.A P.L (n : ℤ) (baseOver S))) : (lbPow P.L n).Sec where
  f j := ((toProd P).appLE _ _ (chart_le j)).hom (t.f (fun _ => j ()))
  compat i j := by
    have e : (lbPow P.L n).U i ⊓ (lbPow P.L n).U j ≤ toProd P ⁻¹ᵁ ((LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => i ()) ⊓
        (LPow P.A P.L (n : ℤ) (baseOver S)).U (fun _ => j ())) :=
      fun z hz => ⟨chart_le i hz.1, chart_le j hz.2⟩
    have ht := congrArg ((toProd P).appLE _ _ e).hom (t.compat (fun _ => i ()) (fun _ => j ()))
    rw [map_mul] at ht
    erw [g_eq i j e] at ht
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply] at ht
    rw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE] at ht
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    exact ht
end GlobalTheory.TrSecDesc

namespace GlobalTheory.TrSecDesc
variable {S : Scheme.{0}} {P : PolAV S}

end GlobalTheory.TrSecDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackGroupPointToModelGroupLinearCombination
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TanComb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {V : Type} [CommRing V]

def push (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) (q : epsOver V V ⟶ G.G) :
    overAt x (DualNumber V) ⟶ Y.t.G :=
  Over.homMk (q.left ≫ ψ.φ) (by
    have hw := ψ.cart.1.w
    simp only [Category.assoc, hw]
    rw [← Category.assoc, Over.w q]
    rfl)

theorem push_mul (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) (p q : epsOver V V ⟶ G.G) :
    push x ψ (p * q) = push x ψ p * push x ψ q := by
  apply Over.OverMorphism.ext
  exact (ψ.cart.2 (epsOver V V) p q (push x ψ p) (push x ψ q) rfl rfl).symm

theorem push_one (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) :
    push x ψ 1 = 1 := by
  have h : push x ψ 1 * push x ψ 1 = push x ψ 1 := by
    rw [← push_mul, _root_.mul_one]
  exact mul_eq_left.1 h

def pushHom (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) :
    (epsOver V V ⟶ G.G) →* (overAt x (DualNumber V) ⟶ Y.t.G) where
  toFun := push x ψ
  map_one' := push_one x ψ
  map_mul' := push_mul x ψ

end GlobalTheory.TanComb

open GlobalTheory.TanComb in

theorem GlobalTheory.TanComb.tanComb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G)) (ub' : Fin m → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G) (a : Fin m → V) (w : epsOver V V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) → (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → IsComb ub a w → ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ m ub ub' a w v hub hv hw
  obtain ⟨u, hu, rfl⟩ := hw
  apply GlobalTheory.FlagMod.tan_ext_left
  rw [hv, GlobalTheory.FlagMod.tv_sum']
  have key : ∏ i, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (a i • ub' i) = pushHom x ψ (List.ofFn u).prod := by
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    show (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (a i • ub' i)).left = (u i).left ≫ ψ.φ
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left, hub i, hu i, Category.assoc]
  rw [key]
  rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntGaugePull

theorem top_le_of_redE {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp (DualNumber A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (redE A ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro z _
  let w : Sp A := (Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A)))).base z
  have hw : (redE A).base w = z := by
    simp only [w, redE, spMap, Spec.map_base]
    refine PrimeSpectrum.ext (Ideal.ext fun t => ?_)
    simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      CommRingCat.hom_ofHom]
    have hn : TrivSqZeroExt.inr (TrivSqZeroExt.snd t) ∈ z.asIdeal := by
      apply z.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact z.asIdeal.zero_mem
    have ht : t = algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) +
        TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := by
      rw [TrivSqZeroExt.algebraMap_eq_inl]; exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq t).symm
    constructor
    · intro h1; rw [ht]; exact z.asIdeal.add_mem h1 hn
    · intro h1
      have e : algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) =
          t - TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := eq_sub_of_add_eq ht.symm
      change algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) ∈ z.asIdeal
      rw [e]; exact z.asIdeal.sub_mem h1 hn
  have := h (show w ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← hw]
  exact this

theorem sep_unique {C : Type} [Field C] (S : ValuationSubring C) {X Y : Scheme.{0}} (p : X ⟶ Y) [IsSeparated p]
    (x₁ x₂ : Sp S ⟶ X) (h₁ : x₁ ≫ p = x₂ ≫ p) (h : spMap S.subtype ≫ x₁ = spMap S.subtype ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness p := IsSeparated.valuativeCriterion p
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := Spec.map (CommRingCat.ofHom (algebraMap S C)) ≫ x₁, i₂ := x₁ ≫ p,
      commSq := ⟨by rw [Category.assoc]⟩ }
  have := (hU Q).elim ⟨x₁, rfl, rfl⟩ ⟨x₂, h.symm, h₁.symm⟩
  exact congrArg CommSq.LiftStruct.l this

theorem spMap_subtype_cancel {C : Type} [Field C] (S : ValuationSubring C) {A : Type} [CommRing A]
    (f g : Sp S ⟶ Sp A) (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  simp only [spMap, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  have := congrArg (fun u => u.hom a) h'
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem spMap_comp_spMap {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem redE_dual {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    redE B ≫ spMap (dualMap f) = spMap f ≫ redE A := by
  simp only [redE, spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap (dualMap f) ≫ spMap (dualMap g) = spMap (dualMap (f.comp g)) := by
  rw [spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem famφB_hom {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (β : D.X) (i : Fin 4) :
    D.famφB β i ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases i
  · exact Category.id_comp _
  all_goals exact Over.w _

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem sE_norm_le_one_of_pull : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  intro V _ _ _ D C _ _ hC N ν hI k β σ σF hS Q hQ r hr
  obtain ⟨S, hSmem, hInt⟩ := hI
  have hle : ∀ v : V, toF V C v ∈ S := fun v => (hSmem _).2 (hC.1 v)
  let toS : V →+* S := (toF V C).codRestrict S hle
  have htoS : S.subtype.comp toS = toF V C := by ext v; rfl
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have hpt : ∀ i : Fin 4, ⊤ ≤ (spMap (dualMap toS) ≫ Q ≫ D.toPre.famφB β i) ⁻¹ᵁ
      D.toPre.P.L.U (ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i)) := by
    intro i
    have hQi : (Q ≫ D.toPre.famφB β i) ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) := by
      rw [Category.assoc, famφB_hom, hQ]
    let xi : TF (R := V) C ⟶ D.toPre.P.A :=
      Over.homMk (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) (by
        simp only [Category.assoc]
        rw [famφB_hom, hQ, spMap_comp_spMap, redE, spMap_comp_spMap]
        simp only [TF, Over.mk_hom, jFK, jK]
        rw [← Spec.map_comp]
        congr 1
        ext v
        simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl)
    obtain ⟨x₀, hx₀, hU⟩ := hInt xi
    have hxy : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ (spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i) := by
      rw [hx₀]
      simp only [xi, Over.homMk_left]
      rw [← Category.assoc (spMap S.subtype), spMap_comp_spMap, htoS, ← Category.assoc, redE_dual, Category.assoc]
    have heq : x₀ = spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i :=
      sep_unique S D.toPre.P.A.hom _ _ (spMap_subtype_cancel S _ _ (by simp only [← Category.assoc] at hxy ⊢; rw [hxy])) hxy
    apply top_le_of_redE
    rw [← Category.assoc, redE_dual, Category.assoc, ← heq]
    exact hU

  have hj : ∀ i, ν.J (redE C ≫ r ≫ D.toPre.famφ C β i) =
      ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) := by
    intro i; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq, ← Category.assoc r, hr, Category.assoc]
  unfold sE
  set j : Fin 4 → D.toPre.P.L.ι := fun k => ν.J (redE C ≫ r ≫ D.toPre.famφ C β k) with hjdef
  have hQ' : ⊤ ≤ (spMap (dualMap toS) ≫ Q) ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
    intro z _
    show (spMap (dualMap toS) ≫ Q).base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    refine Set.mem_iInter.2 fun i => ?_
    have := hpt i (show z ∈ (⊤ : (Sp (DualNumber S)).Opens) from trivial)
    rw [← hj i] at this
    exact this
  obtain ⟨hrB0, hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (dualMap S.subtype) (spMap (dualMap toS) ≫ Q) _ hQ'
  have hrq : spMap (dualMap S.subtype) ≫ spMap (dualMap toS) ≫ Q = r ≫ (D.toPre.prB C).left := by
    rw [← Category.assoc, dualMap_comp, htoS, hr]
  rw [hrq] at hrB0 hval

  have hW2 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j :=
by
    intro z hz
    have h' : (r ≫ (D.toPre.prB C).left).base z ∈
        ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hrB0 hz
    show r.base z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
  have hWeq : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j =
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j :=
    congrArg (fun φ => LB.wchart D.toPre.P.L φ j) (funext (ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq D.toPre C β))
  have hW1 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ C β) j := hWeq ▸ hW2
  have hW : ⊤ ≤ r ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j) :=
    fun z hz => ⟨hW1 hz, hW2 hz⟩
  have hcoh : D.toPre.P.L.Coh (Sum.elim (D.toPre.famφ C β) fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k)
      (Sum.elim j j) := by
    have key : ∀ a, Sum.elim j j a = ν.J (redE C ≫ r ≫ (Sum.elim (D.toPre.famφ C β)
        (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) a)) := by
      rintro (a | a)
      · rfl
      · simp only [Sum.elim_inr, hjdef]; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq]
    intro a b hab; rw [key a, key b, hab]
  have E := hS j j hcoh
  simp only [map_one, _root_.one_mul] at E

  have hv : valR r (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j) (σF.f j) =
      dualMap S.subtype (valR (spMap (dualMap toS) ≫ Q) (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) (σ.f j)) := by
    refine Eq.trans ?_ (hval (σ.f j))
    have hrB1 : ⊤ ≤ r ⁻¹ᵁ (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j :=
      fun z hz => hrB0 hz
    refine Eq.trans ?_ (GlobalTheory.ZH.EvCrd.valR_comp r (D.toPre.prB C).left
      (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) hrB1 (σ.f j))
    have hle2 : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
        LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j ≤
        (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
      intro z hz
      have h' : z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hz.2
      show (D.toPre.prB C).left.base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
    refine Eq.trans (GlobalTheory.ZH.CrdCalc.valR_res r inf_le_left hW (σF.f j)).symm ?_
    refine Eq.trans ?_ (GlobalTheory.ZH.CrdCalc.valR_res r hle2 hW _)
    congr 1
    exact E.symm
  rw [hv]
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add]
  exact ⟨(hSmem _).1 (Subtype.prop _), (hSmem _).1 (Subtype.prop _)⟩

end GlobalTheory.IntGaugePull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotient
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem functionFieldMap_fnOf (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {x : X}
    (hx : x ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from hx)) s) =
      GlobalTheory.Cartier.fnOf (f ⁻¹ᵁ U) (GlobalTheory.Cartier.gen_mem hx) (f.app U s) := by
  rw [← GlobalTheory.Cartier.algebraMap_germ (show f x ∈ U from hx), functionFieldMap_algebraMap,
    ← GlobalTheory.Cartier.algebraMap_germ hx]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply f U x hx s

theorem fnOf_appLE (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    {x : X} (hx : x ∈ V) (s : Γ(Y, U)) :
    GlobalTheory.Cartier.fnOf V (GlobalTheory.Cartier.gen_mem hx) (f.appLE U V e s) =
      functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from e hx)) s) := by
  rw [functionFieldMap_fnOf f (e hx)]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact X.presheaf.germ_res_apply (homOfLE e) _ _ _

end GlobalTheory.FnPull

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {Γ : Type} [Group Γ]

theorem functionFieldMap_act (ρ : Γ →* Aut X) (q : X ⟶ Y) [IsDominant q]
    (hq : ∀ g, (ρ g).hom ≫ q = q) (hs : Function.Surjective q) (g : Γ) [IsDominant (ρ g).hom]
    (c : Y.functionField) :
    functionFieldMap (ρ g).hom (functionFieldMap q c) = functionFieldMap q c := by
  obtain ⟨U₀, hη, s, rfl⟩ := Y.presheaf.exists_germ_eq c
  obtain ⟨x, hx⟩ := hs (genericPoint Y)
  have hx' : x ∈ q ⁻¹ᵁ U₀ := show q x ∈ U₀ from hx ▸ hη
  change functionFieldMap (ρ g).hom (functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)) =
    functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)
  rw [functionFieldMap_fnOf q hx' s]
  obtain ⟨e, hinv⟩ := isInvariantSection_app ρ q hq U₀ s g
  rw [← fnOf_appLE (ρ g).hom e hx', hinv]

theorem isInvariantSection_of_fnOf [Finite Γ] {ρ : Γ →* Aut X} {q : X ⟶ Y} [IsDominant q]
    (h : IsAffineQuotient ρ q) {V : Y.Opens} {x : X} (hx : x ∈ q ⁻¹ᵁ V) (c : Γ(X, q ⁻¹ᵁ V))
    (b : Y.functionField) (hc : GlobalTheory.Cartier.fnOf _ (GlobalTheory.Cartier.gen_mem hx) c = functionFieldMap q b) :
    IsInvariantSection ρ _ c := fun g ↦ by
  haveI : IsIso (ρ g).hom := Iso.isIso_hom _
  refine ⟨h.preimage_le V g, GlobalTheory.Cartier.fnOf_injective _ (GlobalTheory.Cartier.gen_mem hx) ?_⟩
  rw [fnOf_appLE (ρ g).hom (h.preimage_le V g) hx, hc,
    functionFieldMap_act ρ q h.comp_eq h.surjective.surj g]

end GlobalTheory.FnPull

namespace GlobalTheory.OrbitSep

theorem unitAt_of_forall_unitAt_fibre : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  intro X W _ _ Γ _ _ ρ q _ h y b hb
  have hsurj : Function.Surjective q := h.surjective.surj
  haveI := h.isIntegralHom
  let O : Set X := {x | GlobalTheory.Cartier.UnitAt x (functionFieldMap q b)}
  have hOo : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hx
    exact ⟨U, fun z hz ↦ hU z hz, U.isOpen, hxU⟩
  have hV : IsOpen (q '' Oᶜ)ᶜ := (q.isClosedMap _ hOo.isClosed_compl).isOpen_compl
  let V : W.Opens := ⟨_, hV⟩
  obtain ⟨x₀, hx₀⟩ := hsurj y
  have hyV : y ∈ V := fun ⟨x, hx, e⟩ ↦ hx (hb x e)
  have hx₀V : x₀ ∈ q ⁻¹ᵁ V := show q x₀ ∈ V from hx₀ ▸ hyV
  have hUO : ∀ x ∈ q ⁻¹ᵁ V, GlobalTheory.Cartier.UnitAt x (functionFieldMap q b) := fun x hx ↦ by
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hUO
  have hgen := GlobalTheory.Cartier.gen_mem hx₀V
  have ha1 : GlobalTheory.Cartier.fnOf _ hgen (a : Γ(X, q ⁻¹ᵁ V)) = functionFieldMap q b := ha hgen
  have ha2 : GlobalTheory.Cartier.fnOf _ hgen ((a⁻¹ : Γ(X, q ⁻¹ᵁ V)ˣ) : Γ(X, q ⁻¹ᵁ V)) =
      functionFieldMap q b⁻¹ := by
    rw [map_units_inv, ha1, map_inv₀]
  obtain ⟨t, ht⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b ha1)
  obtain ⟨t', ht'⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b⁻¹ ha2)
  have htt : t * t' = 1 := h.app_injective V (by rw [map_mul, ht, ht', Units.mul_inv, map_one])
  let u : Γ(W, V)ˣ := ⟨t, t', htt, by rw [mul_comm]; exact htt⟩
  have hgenW := GlobalTheory.Cartier.gen_mem hyV
  have hbu : GlobalTheory.Cartier.fnOf V hgenW t = b := (functionFieldMap q).injective (by
    rw [GlobalTheory.FnPull.functionFieldMap_fnOf q hx₀V t, ht, ha1])
  rw [← hbu]
  exact GlobalTheory.Cartier.unitAt_fnOf hyV hgenW u

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

open MonObj

theorem IsTranslate.fst_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  intro E _ _ _ H X t R S _ _ φ x g₀ v w hg hv ⟨g', v', h₁, h₂, h₃⟩
  have e1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [dualMap]
  let r : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, e1, Category.id_comp])
  let q : Over.mk (g₀ ≫ t.G.hom) ⟶ Over.mk x := Over.homMk (spMap φ) hg.symm
  have hv1 : r ≫ v' = 1 := by
    rw [← MonObj.comp_one q]
    apply Over.OverMorphism.ext
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = spMap φ ≫ _
    rw [h₂, ← Category.assoc, e2, Category.assoc, hv.2]
  have h : (r ≫ (g' * v')).left = (r ≫ g').left := by
    rw [MonObj.comp_mul, hv1, _root_.mul_one]
  rw [← h₃]
  refine h.trans ?_
  show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ g'.left = g₀
  rw [h₁, ← Category.assoc, e1, Category.id_comp]

end GlobalTheory.LogKS
end

