import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BeTransSymmOfWitData
section
noncomputable section

namespace GlobalTheory.ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}} (f : A →+* F) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (z : Sp F) :
    ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
  let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
  refine ⟨Units.map g.toMonoidHom a, ?_⟩
  have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← toStk_valF _ U z hz]
  congr 1
  have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
  rw [valF, dif_pos ht]
  have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
  rw [e1]
  exact e3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k}

theorem psi_value_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.toPre.X) (hχ : e y = χ) (j : P.toPre.P.L.ι)
    (hj : (P.toPre.c χ).left (cpt (PowerSeries k)) ∈ P.toPre.P.L.U j) :
    ∃ u : (PowerSeries k)ˣ,
      (gm (Out.jFK (R := PowerSeries k) F) z
        (LB.wchart P.toPre.P.L (K := PUnit) (fun _ => Out.ptK (P.toPre.c χ)) (fun _ => j))
        ((P.toPre.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X)) ^ (a.be y y / 2) *
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ u.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let f : PowerSeries k →+* F :=
    (algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)
  let x : Sp (PowerSeries k) ⟶ P.toPre.P.A.left := (P.toPre.c (e y)).left
  have hx : Out.jFK (R := PowerSeries k) F ≫ Out.ptK (P.toPre.c (e y)) = spMap f ≫ x := by
    have : spMap f = Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k) := by
      simp only [f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt (PowerSeries k))))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.toPre.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := PowerSeries k) F ≫ Out.ptK (P.toPre.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.toPre.P.L.U j := by
    rw [hx]
    exact ht (show spMap f z ∈ (⊤ : (Sp (PowerSeries k)).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := exists_unit_gm_spMap f x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := k) F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing k))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := k) F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := exists_unit_gm_spMap (algebraMap (FractionRing k) F) (𝟙 _) _ ht₀ ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, hr⟩ := (FractionRing.algEquiv k k).symm.surjective u₀.val
  have hr' : algebraMap k (FractionRing k) r = u₀.val := by
    rw [← hr]; exact ((FractionRing.algEquiv k k).symm.commutes r).symm
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr', h0, map_zero])
  rw [← hr', hF, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * Units.map (PowerSeries.C (R := k)).toMonoidHom (Units.mk0 r hr0), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem be_self_nonneg (a : ArcIn D l β k b) (y : a.D₀.X) : 0 ≤ a.be y y := by
  by_cases hy : y = 0
  · subst hy; simp
  · exact (a.be_pos y hy).le

theorem be_self_eq_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let f : PowerSeries k →+* F :=
    (algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)
  have hf : Function.Injective f :=
    (algebraMap (FractionRing (PowerSeries k)) F).injective.comp (IsFractionRing.injective _ _)
  let g : k →+* F := f.comp (PowerSeries.C (R := k))
  let alg : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing k) F _ _ alg (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := fun x =>
    IsFractionRing.lift_algebraMap g.injective x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.toPre.P.isLB ((P.toPre.c (e₁ y)).left (cpt (PowerSeries k)))
  obtain ⟨u, hu⟩ := @psi_value_of_witData E _ _ _ H D l c O _ β k _ b a P _ oP φ₁ he₁ w₁ e₁ h₁ F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨u', hu'⟩ := @psi_value_of_witData E _ _ _ H D l c O _ β k _ b a P _ oP φ₂ he₂ w₂ e₂ h₂ F _ _ _ alg hF z y' _
    hy.symm j hj
  have e := (toStk z).injective (hu.symm.trans hu')
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (be_self_nonneg a y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (be_self_nonneg a y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  have e' : u.val * PowerSeries.X ^ m = u'.val * PowerSeries.X ^ n := by
    apply hf
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm, mul_comm (f u')]
    exact e
  have hmn : m = n := IsDiscreteValuationRing.unit_mul_pow_congr_pow PowerSeries.X_irreducible PowerSeries.X_irreducible
    u u' m n e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

theorem be_trans_symm_of_witData (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) (y z : a.D₀.X) :
    a.be (e₁.trans e₂.symm y) (e₁.trans e₂.symm z) = a.be y z := by
  have key : ∀ v, a.be v v = a.be (e₁.trans e₂.symm v) (e₁.trans e₂.symm v) := fun v =>
    be_self_eq_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ v _ (by simp)
  have k₁ := key y
  have k₂ := key z
  have k₃ := key (y + z)
  have s₁ := a.be_symm z y
  have s₂ := a.be_symm (e₁.trans e₂.symm z) (e₁.trans e₂.symm y)
  simp only [map_add, LinearMap.add_apply] at k₃
  omega

theorem be_isometry_of_witData
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
    (h₁ : WitData a P oP φ₁ he₁ w₁ e₁) (h₂ : WitData a P oP φ₂ he₂ w₂ e₂) :
    (∀ y y', e₁ y = e₂ y' → a.be y y = a.be y' y') ∧
      ∀ y z, a.be (e₁.trans e₂.symm y) (e₁.trans e₂.symm z) = a.be y z :=
  ⟨be_self_eq_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂,
    be_trans_symm_of_witData a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂⟩

end GlobalTheory.ThetaShiftProofs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

theorem finite_form_le {Y : Type} [AddCommGroup Y] [Module.Finite ℤ Y] (q : LinearMap.BilinForm ℤ Y)
    (hq : ∀ y, y ≠ 0 → 0 < q y y) (n : ℕ) : {y | q y y ≤ n}.Finite := by
  have h0 : ∀ y, 0 ≤ q y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hq y h).le
  have : AddGroup.FG Y := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Y (n := 4 * n + 1) (by omega)
  refine Set.Finite.of_finite_image (f := fun y => (QuotientAddGroup.mk y :
    Y ⧸ (nsmulAddMonoidHom (4 * n + 1) : Y →+ Y).range)) (Set.toFinite _) fun y hy y' hy' h => ?_
  obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 h
  obtain rfl : y' = y + (4 * n + 1) • v := by rw [show (4 * n + 1) • v = -y + y' from hv, add_neg_cancel_left]
  by_contra hne
  have hv0 : v ≠ 0 := fun e => hne (by rw [e, smul_zero, add_zero])
  have a₁ := hq v hv0
  have a₂ := h0 (y + (y + (4 * n + 1) • v))
  have a₃ : q y y ≤ n := hy
  have a₄ : q (y + (4 * n + 1) • v) (y + (4 * n + 1) • v) ≤ n := hy'
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at a₂ a₄
  push_cast at a₂ a₄
  have a₅ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [mul_nonneg (mul_nonneg a₅ a₅) a₁.le, mul_nonneg a₅ a₁.le, mul_nonneg a₅ (sub_nonneg.2 (Int.add_one_le_of_lt a₁))]

include hj in

theorem finite_expo_lt (α : a.D₀.X) (n : ℤ) : {mu | expo a j α mu < n}.Finite := by
  refine Set.Finite.subset ((finite_form_le a.be a.be_pos (2 * n + a.be α α).toNat).preimage
    (add_left_injective α).injOn) fun mu h => ?_
  have h₁ : expo a j α mu < n := h
  have h₂ := two_mul_expo a j α mu
  have h₃ := a.be_symm α mu
  have h₄ : 0 ≤ a.be mu mu := by
    by_cases h : mu = 0
    · simp [h]
    · exact (a.be_pos mu h).le
  have h₅ : a.be mu mu ≤ j * a.be mu mu := le_mul_of_one_le_left h₄ (by exact_mod_cast hj)
  show a.be (mu + α) (mu + α) ≤ _
  simp only [map_add, LinearMap.add_apply]
  omega

include hj in
theorem exists_expo_bound (α : a.D₀.X) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu := by
  obtain ⟨n, hn⟩ := ((finite_expo_lt hj α 0).image fun mu => expo a j α mu).bddBelow
  refine ⟨(-n).toNat, fun m hm mu => ?_⟩
  by_cases h : expo a j α mu < 0
  · have : n ≤ expo a j α mu := hn ⟨mu, h, rfl⟩
    omega
  · omega

theorem map_add_nsmul (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (α mu : a.D₀.X) : e (α + j • mu) = e α + j • e mu := by
  rw [map_add, map_nsmul]

theorem eq_or_off (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (j : ℕ) (α : a.D₀.X) (χ : P.toPre.X) :
    (∃ mu, e (α + j • mu) = χ) ∨ ∀ mu, e α + j • mu ≠ χ := by
  by_cases h : ∃ mu, e α + j • mu = χ
  · obtain ⟨mu, rfl⟩ := h
    exact .inl ⟨e.symm mu, by rw [map_add_nsmul, e.apply_symm_apply]⟩
  · exact .inr fun mu h' => h ⟨mu, h'⟩

include hj in
theorem exists_isIntegralForm (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) {m : ℕ}
    (hm : ∀ mu, 0 ≤ (m : ℤ) + expo a j α mu) : ∃ f, IsIntegralForm hW j α s₀ m f := by
  have ex : ∀ χ, ∃ t : SecBMod P.toPre j χ, (∀ mu, e (α + j • mu) = χ → HEq t
      ((PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀))) ∧ ((∀ mu, e α + j • mu ≠ χ) → t = 0) := fun χ => by
    rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | h
    · refine ⟨(PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
        pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀), fun mu' h => ?_, fun h => absurd (map_add_nsmul e α mu).symm (h _)⟩
      obtain rfl := FamFree.add_nsmul_inj hj α _ _ (e.injective h)
      rfl
    · exact ⟨0, fun mu h' => absurd ((map_add_nsmul e α mu).symm.trans h') (h _), fun _ => rfl⟩
  choose f h₁ h₂ using ex
  exact ⟨f, fun mu => ⟨hm mu, eq_of_heq (h₁ _ mu rfl)⟩, h₂⟩

variable {hW} in

theorem IsIntegralForm.resF_eq {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {m : ℕ} {f : ∀ χ, SecBMod P.toPre j χ}
    (h : IsIntegralForm hW j α s₀ m f) (χ : P.toPre.X) : resF P.toPre F j χ (f χ) =
      toF (R := PowerSeries k) F (PowerSeries.X ^ m) • famComp P.toPre F j χ (constFam hW F hG hj α s₀) := by
  rcases eq_or_off e j α χ with ⟨mu, rfl⟩ | hχ
  · rw [(h.1 mu).2, map_smulₛₗ, resF_pullB, constFam_add_nsmul, smul_smul, map_pow, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (h.1 mu).1, zpow_add₀ (toF_X_ne_zero F), zpow_natCast]
  · rw [h.2 χ hχ, map_zero, constFam_off hW F hG hj α s₀ χ hχ, smul_zero]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries k))))}
  {G : Over (Spec (CommRingCat.of (PowerSeries k)))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (Ideal.span {PowerSeries.X}) P A G)

include hG hj in

theorem exists_expandsAt (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
    ∃ (f : ∀ χ, SecBMod P.toPre j χ) (σ : H0 U.LG.L j), IsIntegralForm hW j α s₀ m f ∧
      ∀ n, U.toUnifPre.ExpandsAt n j σ f := by
  obtain ⟨s, ⟨r, hr, σ, f', -, hf', hE⟩, -⟩ := (U.expand j hj).2 (constFam hW _ hG hj α s₀)
  obtain ⟨n₀, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr PowerSeries.X_irreducible
  obtain ⟨m₁, hm₁⟩ := exists_expo_bound hj α
  refine ⟨max n₀ m₁, fun m hm => ?_⟩
  obtain ⟨f, hf⟩ := exists_isIntegralForm hW hj α s₀ (hm₁ m ((le_max_right _ _).trans hm))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((le_max_left _ _).trans hm)
  refine ⟨f, SecOps.secScale (scal G.hom (u⁻¹.val * PowerSeries.X ^ d)) σ, hf, fun n =>
    expandsAt_secIsMul _ _ _ _ _ U.toUnifPre n j (u⁻¹.val * PowerSeries.X ^ d) σ _ f' f (fun _ => rfl)
      (fun χ => ?_) (hE n)⟩
  have e₁ : f χ = (u⁻¹.val * PowerSeries.X ^ d : PowerSeries k) • (show SecBMod P.toPre j χ from f' χ) := by
    refine resF_injective P.toPre (FractionRing (PowerSeries k)) j χ ?_
    rw [hf.resF_eq _ hG hj, map_smulₛₗ, (secScal_iff_resF P.toPre _ (famComp _ _ j χ _) _ _).1 (hf' χ), smul_smul,
      ← map_mul, _root_.mul_mul_mul_comm, Units.inv_mul, _root_.one_mul, ← pow_add, add_comm]
  rw [e₁]
  exact fun _ => rfl

include hG hj in

theorem exists_pow_smul_mem_span {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) (m : (Σ x, Idx x) → ℕ)
    (f : (Σ x, Idx x) → ∀ χ, SecBMod P.toPre j χ)
    (σ : (Σ x, Idx x) → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (hf : ∀ i : Σ x, Idx x, IsIntegralForm hW j (rep i.1) (bas i.1 i.2) (m i) (f i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ n : ℕ, (PowerSeries.X : PowerSeries k) ^ n • s ∈ Submodule.span (PowerSeries k) (Set.range σ) := by
  obtain ⟨B, hB⟩ := exists_basis_constFam hW (FractionRing (PowerSeries k)) hG hj rep hrep bas
  obtain ⟨t, ht, h⟩ := exists_smul_mem_span_of_expandsAt U hj B B.span_eq (fun i => PowerSeries.X ^ m i)
    (fun i => pow_ne_zero _ PowerSeries.X_ne_zero) σ f (fun i χ => by
      rw [show B i = _ from hB i.1 i.2]; exact (hf i).resF_eq _ hG hj χ) hE s
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht PowerSeries.X_irreducible
  refine ⟨n, ?_⟩
  have := Submodule.smul_mem _ u⁻¹.val h
  rwa [smul_smul, Units.inv_mul_cancel_left] at this

end GlobalTheory.ConstFam

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

end GlobalTheory
end
end

