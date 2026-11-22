import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddGeneric

theorem exists_additionFactor_generator_value {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {T : Over S}
    (x y : T ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![x.left, y.left, (x * y).left, (x * y⁻¹).left] ![2, 2, -1, -1]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P.L.L z J →
        val t ρ.left z J = kap0 P.c P.sym z J (ρ ≫ x) (ρ ≫ y) := by
  let r₀ := LB.pullGen P.L.L (fun _ : PUnit => eSec G) (fun _ => 1) P.L.rig T.hom
  have hr₀ : r₀.IsGen := DVR.pullGen_isGen _ _ _ _ P.L.rigGen _
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := ![x.left, y.left, (x * y).left, (x * y⁻¹).left])
    (ε' := ![2, 2, -1, -1]) (fun U _ h => by
      have o : ∏ _k : PUnit, h (T.hom ≫ eSec G) ^ (1 : ℤ) = h (1 : T ⟶ G).left := by
        rw [Fintype.prod_unique, zpow_one, one_left]
      refine (DVR.prod_sum₂ (U := U) (K := thK ⊕ Fin 2) (K' := PUnit ⊕ PUnit) _
        (DVR.prod_sum₂ (U := U) (K := thK) (K' := Fin 2) _ (prod_cub x y y⁻¹ h) (DVR.prod_neg _ _ (prod_sym y h)))
        (DVR.prod_sum₂ (U := U) (K := PUnit) (K' := PUnit) _ o o)).trans ?_
      rw [mul_inv_cancel_right, mul_inv_cancel]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen P.L.L _ _ _ _
      (LB.mulGen P.L.L _ _ _ _ (LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift x (lift y y⁻¹)).left)
        (LB.invGen P.L.L _ _ (LB.pullGen P.L.L _ _ P.sym y.left)))
      (LB.mulGen P.L.L _ _ _ _ r₀ r₀))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen _))) (DVR.mulGen_isGen _ _ _ _ _ _ _ hr₀ hr₀))
  refine ⟨t, ht, fun T' ρ z J hJ => ?_⟩
  have e₀ : val r₀ ρ.left z J =
      val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T'.hom z J :=
    (val_pull hJ _ _ _).trans (by rw [Over.w ρ])
  refine ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub P.c ρ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ e₀))))).trans ?_
  rw [kap0, sq, GrpObj.comp_inv, Over.comp_left]

theorem exists_additionFactor_generator_transported {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G)
    {A : Over S'} [GrpObj A] [IsCommMonObj A] {Φ : A.left ⟶ G.left} (hw : Φ ≫ G.hom = A.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A), toBase hw (x * y) = toBase hw x * toBase hw y)
    {L' : LB A.left} (hL' : L'.IsLB) (u : LB.Iso L' (P.L.L.pull Φ)) (hu : PGen u) {Y : Over S'} (p q s d : Y ⟶ A)
    (hs : s = p * q) (hd : d = p * q⁻¹) :
    ∃ a : LB.Gen (LB.LinComb L' (K := Fin 4) ![p.left, q.left, s.left, d.left] ![2, 2, -1, -1]), a.IsGen ∧
      ∀ (T : Over S') (ρ : T ⟶ Y) (z : T.left) (J J'), Good P.L.L z J → Good L' z J' →
        ∀ W : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw u x.left z (J (x.left ≫ Φ)) (J' x.left)) →
        @id (T.left.presheaf.stalk z)ˣ (kap0 P.c P.sym (T := Over.mk (T.hom ≫ f)) z J (toBase hw (ρ ≫ p)) (toBase hw (ρ ≫ q))) =
          W (ρ ≫ p) ^ 2 * W (ρ ≫ q) ^ 2 * (W ((ρ ≫ p) * (ρ ≫ q)))⁻¹ * (W ((ρ ≫ p) * (ρ ≫ q)⁻¹))⁻¹ *
            val a ρ.left z J' := by
  subst hs hd
  obtain ⟨t, ht, hv⟩ := exists_additionFactor_generator_value P (toBase hw p) (toBase hw q)
  have hψ : ∀ k : Fin 4, ![p.left, q.left, (p * q).left, (p * q⁻¹).left] k ≫ Φ = 𝟙 Y.left ≫
      ![(toBase hw p).left, (toBase hw q).left, (toBase hw p * toBase hw q).left,
        (toBase hw p * (toBase hw q)⁻¹).left] k := by
    intro k
    rw [Category.id_comp]
    have e : toBase hw (p * q⁻¹) = toBase hw p * (toBase hw q)⁻¹ :=
      (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul Y) q))
    rw [← e, ← mul]
    fin_cases k <;> rfl
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps hu P.L.isLB hL' (𝟙 Y.left) hψ t ht
  refine ⟨a, ha, fun T ρ z J J' hJ hJ' W hW => ?_⟩
  have e₁ := DegPull.pmaps_val hψ H ρ.left z hJ hJ'
  let ρ' : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := Over.homMk ρ.left (by
    show ρ.left ≫ Y.hom ≫ f = T.hom ≫ f
    rw [← Category.assoc, Over.w ρ])
  have e₂ := hv _ ρ' z J hJ
  have e₃ : ∀ x : Y ⟶ A, ρ' ≫ toBase hw x = toBase hw (ρ ≫ x) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [e₃, e₃] at e₂
  rw [Category.comp_id] at e₁
  refine e₂.symm.trans (e₁.trans (congrArg (· * val a ρ.left z J') ?_))
  rw [← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, ← zpow_neg_one (W _), ← zpow_neg_one (W _),
    ← zpow_natCast (W _), ← zpow_natCast (W _), hW, hW, hW, hW, Fin.prod_univ_four]
  rfl

theorem cancel_alg {B : Type} [CommRing B] {n : ℕ} (a b c d k k' : Bˣ) (r s s' : B) (t t' : Fin n → B)
    (hk : k = a ^ 2 * b ^ 2 * c⁻¹ * d⁻¹ * k')
    (h : ∑ i, (a.val ^ 2 * t i) * (b.val ^ 2 * t' i) = r * k.val * ((c.val ^ 1 * s) * (d.val ^ 1 * s'))) :
    ∑ i, t i * t' i = r * k'.val * (s * s') := by
  apply (a ^ 2 * b ^ 2).isUnit.mul_left_cancel
  rw [Finset.mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h.trans ?_)
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  · have hc := c.inv_mul
    have hd := d.inv_mul
    rw [hk]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s' * (d⁻¹).val * d.val) * hc +
      (r * a.val ^ 2 * b.val ^ 2 * k'.val * s * s') * hd

theorem isUnit_scal {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) {r : R} (hr : r ≠ 0) : IsUnit (scal (p ≫ jK R) r) := by
  have e : scal (jK R) r = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) :=
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  have h : IsUnit (algebraMap R (FractionRing R) r) :=
    IsUnit.mk0 _ fun h => hr ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
  have : IsUnit (scal (jK R) r) := e ▸ h.map _
  exact this.map p.appTop.hom

theorem addA_of_addG : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (θ : U.SecGT (𝟙_ _) 1) (r : R) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := R) F))), r ≠ 0 → U.AddG θ r σ σ' → U.PullG F (toUnit _) 1 θ th → (∀ i, U.PullG F (toUnit _) 2 (σ i) (t i) ∧ U.PullG F (toUnit _) 2 (σ' i) (t' i)) → AddA A (TFK (R := R) F) th t t' := by
  intro R _ _ D I A G _ _ U F _ _ θ r n σ σ' th t t' hr hadd hθ hσ
  have := U.gen_hom
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  obtain ⟨u, hu, huv⟩ := ThetaBaseChange.exists_unpull U.wA_gen U.gen.inv.left hi rfl
  have hw : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ G.hom = A.A.hom ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ jK R) (Over.w U.gen.inv)
  have tb : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), toBase hw x =
      toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R)) pullback.condition
        (x ≫ U.gen.inv) := fun T x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  have mul : ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x y : T ⟶ A.A),
      toBase hw (x * y) = toBase hw x * toBase hw y := fun T x y => by
    rw [tb, tb, tb, MonObj.mul_comp, toBase_mul_pullback]
  obtain ⟨a, ha, hv⟩ := exists_additionFactor_generator_transported U.P hw mul A.isLB u hu (Y := TFK (R := R) F ⊗ (A.A ⊗ A.A))
    (snd _ _ ≫ fst A.A A.A) (snd _ _ ≫ snd A.A A.A) (snd _ _ ≫ (fst A.A A.A * snd A.A A.A))
    (snd _ _ ≫ (fst A.A A.A * (snd A.A A.A)⁻¹)) (MonObj.comp_mul _ _ _)
    ((MonObj.comp_mul _ _ _).trans (by rw [GrpObj.comp_inv]))
  have hun := isUnit_scal (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom hr
  refine ⟨scaleGen hun.unit a, scaleGen_isGen _ ha, fun T ρ x y z J hJ => ?_⟩
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let W : (T ⟶ A.A) → (T.left.presheaf.stalk z)ˣ := fun p =>
    gw u p.left z (JG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (J p.left)
  have k₀ := hv T (lift ρ (lift x y)) z JG J hJG hJ W (fun _ => rfl)
  have ex : lift ρ (lift x y) ≫ snd _ _ ≫ fst A.A A.A = x := by simp
  have ey : lift ρ (lift x y) ≫ snd _ _ ≫ snd A.A A.A = y := by simp
  rw [ex, ey] at k₀
  have pull : ∀ (k : ℕ) (s : U.SecGT (𝟙_ _) k) (s' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      U.PullG F (toUnit _) k s s' → ∀ p : T ⟶ A.A,
      (W p).val ^ k * sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
        s' (lift ρ p).left z J =
      @id (T.left.presheaf.stalk z) (sval s (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left z JG) := by
    intro k s s' h p
    have e₁ : (p.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = p.left := by rw [Category.assoc, hi, Category.comp_id]
    have e := h T.left (lift ρ p).left (p.left ≫ U.gen.inv.left)
      (lift (toUnit (Over.mk (T.hom ≫ jK R))) (toBase hw p)).left
      ((congrArg (fun q => q.left) (lift_snd ρ p)).trans e₁.symm)
      ((congrArg (fun q => q.left) (lift_snd _ (toBase hw p))).trans (Category.assoc _ _ _).symm)
      (by
        rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
        show T.hom ≫ jK R = ρ.left ≫ jFK (R := R) F ≫ jK R
        rw [← Category.assoc]
        exact congrArg (· ≫ jK R) (Over.w ρ).symm) z J JG hJ hJG
    rw [e₁, Category.assoc] at e
    refine Eq.trans (congrArg (fun q : (T.left.presheaf.stalk z)ˣ => q.val ^ k * _) ?_) e
    exact huv _ p.left z _ _ (hJG (p.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hJ p.left)
  have add := hadd (Over.mk (T.hom ≫ jK R)) (toBase hw x) (toBase hw y) z JG hJG
  have e : toBase hw (x * y⁻¹) = toBase hw x * (toBase hw y)⁻¹ :=
    (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul T) y))
  rw [← e, ← mul] at add
  have key := cancel_alg (W x) (W y) (W (x * y)) (W (x * y⁻¹)) _ _ _ _ _ _ _ k₀
    ((Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (pull 2 _ _ (hσ i).1 x) (pull 2 _ _ (hσ i).2 y)).trans
      (add.trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (pull 1 _ _ hθ _).symm (pull 1 _ _ hθ _).symm))))
  refine key.trans (congrArg (· * _) ?_)
  rw [val_scaleGen _ _ _ hJ, Units.val_mul]
  refine congrArg (· * _) (Eq.trans ?_ (gs_unit _ z ⊤ trivial _))
  refine Eq.trans ?_ ((gs_pull (𝟙 _) (lift ρ (lift x y)).left z ⊤ trivial _).trans (by rw [Category.id_comp]))
  refine congrArg (gs (𝟙 T.left) z ⊤) ?_
  show scal (T.hom ≫ jK R) r = scal ((lift ρ (lift x y)).left ≫ (TFK (R := R) F ⊗ (A.A ⊗ A.A)).hom ≫ jK R) r
  rw [← Category.assoc, Over.w]

end GlobalTheory.AddGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletedPoint

theorem adicLevelMap_surjective {B : Type} [CommRing B] (J : Ideal B) (n : ℕ) :
    Function.Surjective (adicLevelMap J (Nat.succ_le_succ (Nat.zero_le n))) := by
  intro p
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.zero_le n)))) = _ :=
    range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)
  refine this.ge ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun a ha => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b ∈ J := by
    have h : Ideal.Quotient.mk (J ^ (0 + 1)) b = 0 := ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at h
  refine p.isPrime.mem_of_pow_mem (n + 1) ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hb _)]
  exact zero_mem _

theorem hom_ext_spec {B : Type} [CommRing B] (J : Ideal B) [IsHausdorff J B] {S : CommRingCat.{0}}
    {g g' : Spec (CommRingCat.of B) ⟶ Spec S}
    (h : ∀ n, adicLevelι J (n + 1) ≫ g = adicLevelι J (n + 1) ≫ g') : g = g' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
  congr 1
  ext1
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
  intro n a
  have h1 := h n
  rw [← Spec.map_comp, ← Spec.map_comp] at h1
  exact congr($(Spec.map_injective h1).hom a)

theorem exists_of_isAdicFamily {B : Type} [CommRing B] (J : Ideal B) [IsAdicComplete J B] {X : Scheme.{0}}
    {V : X.Opens} (hV : IsAffineOpen V) {f : ∀ n : ℕ, Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily J f) (h₀ : ∀ p, f 0 p ∈ V) :
    ∃ g : Spec (CommRingCat.of B) ⟶ X, (∀ p, g p ∈ V) ∧ ∀ n, adicLevelι J (n + 1) ≫ g = f n := by
  have hr : ∀ n, Set.range (f n) ⊆ Set.range hV.fromSpec := fun n => by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := adicLevelMap_surjective J n p
    rw [hV.range_fromSpec, ← Scheme.Hom.comp_apply, hf.of_le (Nat.zero_le n)]
    exact h₀ q
  have hφ : ∀ n, ∃ φ : Γ(X, V) ⟶ CommRingCat.of (B ⧸ J ^ (n + 1)), Spec.map φ ≫ hV.fromSpec = f n := fun n => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec (f n) (hr n))
    exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap J (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom J ha (fun n => (φ n).hom) hc)) ≫ hV.fromSpec, fun p => ?_,
    fun n => ?_⟩
  · exact hV.range_fromSpec.le ⟨_, rfl⟩
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha (fun n => (φ n).hom) hc (n := n)]
    exact hφ n

theorem exists_completion {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) :
    ∃ (B : Type) (_ : CommRing B) (ψ : A →+* B), IsAdicComplete (J.map ψ) B ∧ ψ.Flat ∧
      ∀ p : PrimeSpectrum A, J ≤ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap ψ) := by
  refine ⟨AdicCompletion J A, inferInstance, algebraMap _ _, ?_, ?_, fun p hp => ?_⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · have h : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ 1))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus,
        Ideal.mk_ker, pow_one]
      exact hp
    obtain ⟨q, rfl⟩ := h
    refine ⟨PrimeSpectrum.comap (AdicCompletion.evalₐ J 1).toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 2

open GlobalTheory.FormalPoint in

theorem exists_completed_point {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (G G' : Over (Spec (CommRingCat.of R))) [Flat G'.hom] [LocallyOfFiniteType G'.hom]
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G)
    (hj : ∀ e, thickMap R I e G' ≫ (j (e + 1)).left = (j e).left ≫ thickMap R I e G)
    (x : (thickObj R I 0 G').left) (W : G.left.Opens) (W' : G'.left.Opens)
    (hW : (fstG I 0 G).left ((j 0).left x) ∈ W) (hW' : (fstG I 0 G').left x ∈ W') :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left)
      (g : Spec (CommRingCat.of B) ⟶ G.left), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧
      Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧
      g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ W' ∧ ⊤ ≤ g ⁻¹ᵁ W ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).left ≫ (fstG I e G).left = ρ ≫ g := by
  have tf : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      thickMap R I e H ≫ (fstG I (e + 1) H).left = (fstG I e H).left := fun e H =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fh : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      (fstG I e H).left ≫ H.hom = (thickObj R I e H).hom ≫ thick R I e := fun e H => pullback.condition
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hci : IsClosedImmersion (thick R I 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hci' : IsClosedImmersion (fstG I 0 G').left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst G'.hom (thick R I 0)))
  obtain ⟨O, hO, hO'⟩ := (fstG I 0 G').left.isClosedEmbedding.isInducing.isOpen_iff.1
    (((j 0).left ≫ (fstG I 0 G).left) ⁻¹ᵁ V).isOpen
  have hxO : (fstG I 0 G').left x ∈ O := hO'.ge hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ := G'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show (fstG I 0 G').left x ∈ O ∩ W' from ⟨hxO, hW'⟩) (hO.inter W'.isOpen)
  replace hV' : IsAffineOpen V' := hV'
  have hln : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hN : IsNoetherianRing Γ(G'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV'.fromSpec ≫ G'.hom)
  have hφf : φ.hom.Flat := by
    have : Flat (Spec.map φ) := by rw [hφ]; exact Flat.comp _ _
    exact Flat.SpecMap_iff.1 this
  obtain ⟨B, _, ψ, hB, hψ, hs⟩ := exists_completion (I.map φ.hom)
  letI : Algebra R B := (ψ.comp φ.hom).toAlgebra
  have hBc : IsAdicComplete (I.map (algebraMap R B)) B := by
    rw [Ideal.map_map] at hB; exact hB
  let g' : Spec (CommRingCat.of B) ⟶ G'.left := Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec
  have hg' : g' ≫ G'.hom = spMap (algebraMap R B) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  have hg'V : ∀ p, g' p ∈ V' := fun p => hV'.range_fromSpec.le ⟨_, rfl⟩
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have hf : IsAdicFamily (I.map (algebraMap R B)) fun e => reduction I y e ≫ (j e).left ≫ (fstG I e G).left := by
    intro e
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, tf, hy, adicLevelMap_ι_assoc]
    show _ ≫ _ ≫ _ = _
    rw [reassoc_of% h₁, reassoc_of% (hj e), tf]
  obtain ⟨g, hgV, hg⟩ := exists_of_isAdicFamily _ hV hf fun p => by
    have h₁ : (fstG I 0 G').left (reduction I y 0 p) ∈ O := by
      have : (reduction I y 0 ≫ (fstG I 0 G').left) p ∈ V' := by rw [hy]; exact hg'V _
      exact (hVO this).1
    exact hO'.le h₁
  refine ⟨B, inferInstance, inferInstance, g', g, hBc, RingHom.Flat.comp hφf hψ, ?_, ?_, hg', ?_, fun p _ => (hVO (hg'V p)).2,
    fun p _ => hVW (hgV p), fun e Z ρ r h => ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom ψ)) := Flat.SpecMap_iff.2 hψ
    exact Flat.comp _ _
  · obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    obtain ⟨q, hq⟩ := hs p (by
      rw [Ideal.map_le_iff_le_comap]
      have h₁ : Spec.map φ p = thick R I 0 ((thickObj R I 0 G').hom x) := by
        rw [hφ, Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply, fh]; rfl
      have h₂ : p.asIdeal.comap φ.hom = _ := congrArg PrimeSpectrum.asIdeal h₁
      rw [h₂]
      intro a ha
      show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _)
    exact ⟨q, (congrArg hV'.fromSpec hq).trans hp⟩
  · refine hom_ext_spec (I.map (algebraMap R B)) fun e => ?_
    rw [reassoc_of% (hg e), fh, ← Category.assoc (j e).left, Over.w, ← Category.assoc, reduction_hom,
      levelMap_thick]
  · have w : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
      rw [← hg', ← Category.assoc, ← h, Category.assoc, fh, Category.assoc]
    obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w
    obtain rfl : r = l ≫ reduction I y e := by
      rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
      exact h.trans (Category.assoc _ _ _)
    rw [Category.assoc, Category.assoc, hg]

end GlobalTheory.CompletedPoint

theorem GlobalTheory.exists_completed_point_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ x : (thickObj R I 0 G').left, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧ Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧ g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g := by
  intro R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ hG' U U' hD j hj x
  have := hG'.smooth
  obtain ⟨jL, h⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', h'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, H⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G' (fun e => (j e).hom)
    (fun e => (hj e).2.1) x _ _ h h'
  exact ⟨B, _, _, g', g, jL, jL', H⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftUnitTensor
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

theorem exists_lift_unit_tensor {S Z : Scheme.{0}} (X : Over S) (q : Z ⟶ X.left) :
    ∃ r : Z ⟶ (𝟙_ (Over S) ⊗ X).left, r ≫ (snd _ X).left = q ∧ r ≫ (fst _ X).left = q ≫ X.hom := by
  refine ⟨q ≫ (λ_ X).inv.left, ?_, ?_⟩
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_snd, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_fst]
    rfl

theorem expandsAt_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → U.ExpT (𝟙_ _) k σ' f' → ∀ e, U'.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  dsimp only at hL hgt hw
  subst hL hgt
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hσ
  obtain ⟨S, hS⟩ := hE e
  refine DVR.expandsAt_of_val U' e k σ f S fun y J hJ => ?_
  obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (fstG I e G).left
  obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (U'.gt e).pG.left
  have hc : (U'.gt e).pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U'.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := hS _ (𝟙 _) rG rB (hG₁.trans (Category.id_comp _).symm) (hB₁.trans (Category.id_comp _).symm)
    (hB₂.trans (hc.trans hG₂.symm)) y
  have hf : ∀ α, sval (f' α) rB y J = sval (f α) (DVR.pGl U' e) y J := fun α => by
    rw [hB α _ rB y J hJ, hB₁]
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · choose JG hJG using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
    exact (hf α).symm.trans ((H JG J hJG hJ).1 α hα)
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U'.LG.L U'.LG.isLB y (fun _ : PUnit => (fstG I e G).left) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    have e₀ : JG (fstG I e G).left = jL := eJ PUnit.unit
    have H₂ := (H JG J hJG hJ).2
    have hs : sval σ' rG y JG = DVR.sv U' k σ (DVR.fGl I G e) y jL := by
      rw [hG _ rG y JG hJG, hG₁]
      exact sval_of σ _ y JG (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact e₀)
    simp only [Category.id_comp, e₀, hs, hf] at H₂
    rw [Units.val_pow_eq_pow_val]
    exact H₂

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def gtCoordSetPsi {e : ℕ} (g : GtCoord I D e G) (ψ) (h) : GtCoord I (setPsi D ψ h) e G where
  q := g.q
  q_hom := g.q_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  i := g.i
  i_hom := g.i_hom
  isKernel := g.isKernel
  t := g.t
  t_gen := g.t_gen
  t_mul := g.t_mul
  t_unit := g.t_unit
  t_weight := g.t_weight

def PreU.setPsi (U : PreU I D A G) (ψ) (h) : PreU I (setPsi D ψ h) A G where
  semi := U.semi
  gen := U.gen
  gen_hom := U.gen_hom
  P := U.P
  wA := U.wA
  wA_gen := U.wA_gen
  gt := fun e => gtCoordSetPsi (U.gt e) ψ h
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals := U.w_vals
  w_compat := U.w_compat
end

theorem exists_preU_setPsi : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) ψ h, ∃ (U' : PreU I (setPsi D ψ h) A G) (hP : U'.P = U.P), U'.gen = U.gen ∧ HEq U'.wA U.wA ∧ ∀ θ f, U.Theta θ f → ∃ θ', U'.Theta θ' f :=
  fun _ _ _ _ _ _ _ _ _ U ψ h => ⟨U.setPsi ψ h, rfl, rfl, HEq.rfl, fun θ _ hθ => ⟨θ, hθ⟩⟩
end GlobalTheory.UU
end
end

