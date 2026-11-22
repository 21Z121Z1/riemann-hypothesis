import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpreadPt

theorem isOpen_compl_basicOpen_sub {X : Scheme.{0}} (a b : Γ(X, ⊤)) {k : ℕ} (hk0 : 0 < k) (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hk : IsUnit (k : Γ(X, ⊤))) : IsOpen ((X.basicOpen (a - b) : Set X)ᶜ) := by
  let bu : Γ(X, ⊤)ˣ := Units.ofPowEqOne b k hb hk0.ne'
  have hbu : (bu : Γ(X, ⊤)) = b := rfl
  set u : Γ(X, ⊤) := a * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) with hu_def
  have hab : a - b = b * (u - 1) := by
    have : b * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = 1 := by rw [← hbu]; exact bu.mul_inv
    rw [hu_def, mul_sub, _root_.mul_one, mul_left_comm, this, _root_.mul_one]
  have hu : u ^ k = 1 := by
    have : bu ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hbu, hb, Units.val_one])
    rw [hu_def, mul_pow, ha, _root_.one_mul, ← Units.val_pow_eq_pow_val, inv_pow, this, inv_one, Units.val_one]
  have hbo : X.basicOpen (a - b) = X.basicOpen (u - 1) := by
    rw [hab, Scheme.basicOpen_mul, ← hbu, Scheme.basicOpen_of_isUnit _ bu.isUnit, top_inf_eq]
  set g : Γ(X, ⊤) := ∑ i ∈ Finset.range k, u ^ i with hg
  have h1 : (u - 1) * g = 0 := by rw [hg, mul_comm, geom_sum_mul, hu, sub_self]
  obtain ⟨q, hq⟩ : (u - 1) ∣ g - k := by
    have : g - k = ∑ i ∈ Finset.range k, (u ^ i - 1) := by
      rw [hg, Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow u 1 i
  have hdis : X.basicOpen (u - 1) ⊓ X.basicOpen g = ⊥ := by
    rw [← Scheme.basicOpen_mul, h1, Scheme.basicOpen_zero]
  have e : (k : Γ(X, ⊤)) = g + (u - 1) * (-q) := by rw [mul_neg, ← hq]; ring
  have hcov : ⊤ ≤ X.basicOpen g ⊔ X.basicOpen (u - 1) := by
    calc (⊤ : X.Opens) = X.basicOpen (k : Γ(X, ⊤)) := (Scheme.basicOpen_of_isUnit _ hk).symm
      _ = X.basicOpen (g + (u - 1) * (-q)) := by rw [← e]
      _ ≤ X.basicOpen g ⊔ X.basicOpen ((u - 1) * (-q)) := Scheme.basicOpen_add_le _ _ _
      _ ≤ _ := sup_le_sup_left (by rw [Scheme.basicOpen_mul]; exact inf_le_left) _
  have hd : ∀ x, x ∈ X.basicOpen (u - 1) → x ∈ X.basicOpen g → False := fun x h h' => by
    have : x ∈ ((X.basicOpen (u - 1) ⊓ X.basicOpen g : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_inf]; exact ⟨h, h'⟩
    rw [hdis] at this; exact this
  have hc : ∀ x, x ∈ X.basicOpen g ∨ x ∈ X.basicOpen (u - 1) := fun x => by
    have : x ∈ ((X.basicOpen g ⊔ X.basicOpen (u - 1) : X.Opens) : Set X) := hcov trivial
    rwa [TopologicalSpace.Opens.coe_sup, Set.mem_union] at this
  have hs : ((X.basicOpen (u - 1) : Set X)ᶜ) = X.basicOpen g := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => (hc x).resolve_right h, fun h h' => hd x h' h⟩
  rw [hbo, hs]
  exact (X.basicOpen g).isOpen

end GlobalTheory.LevelSpreadPt

namespace GlobalTheory

open LevelSpread LevelSpreadPt TorsRootParam

theorem exists_levelIsometry_of_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (A : Type) [CommRing A] [IsDomain A] (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (z : A) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver (Sp A) ⟶ P.A)) (n m N : ℕ), 0 < n → 0 < N → Nonempty (ℚ →+* A) → z ^ N = 1 → (∀ i, pt i ^ N = 1) → (∀ a, IsMonHom (act a)) → (∃ (K : Type) (_ : Field K) (β : A →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : A →+* K), ∃ (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i := by
  intro E _ _ _ H D A _ _ P act z κ lam pt n m N hn hN hQ hz hpt hact hex K _ _ β
  obtain ⟨K₀, _, β₀, ζ₀, ev₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hex
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  obtain ⟨q₀⟩ := hQ
  have hnat : ∀ k : ℕ, 0 < k → IsUnit (k : Γ(Sp A, ⊤)) := fun k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp q₀)
    rwa [map_natCast] at h
  have hK : ∀ {L : Type} [Field L] (ρ : A →+* L) (k : ℕ), 0 < k → (k : L) ≠ 0 := fun ρ k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map (ρ.comp q₀)
    rw [map_natCast] at h
    exact h.ne_zero
  have hn' := hnat n hn
  refine GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp A) P act A (𝟙 _) z κ lam pt n m hn ?_ K (spMap β) β
    (hK β n hn) (Category.comp_id _)
  let gp : Sp A := (⊥ : PrimeSpectrum A)
  refine Dense.mono ((Set.singleton_subset_iff (a := gp)).2 ?_) ?_
  rotate_left
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun p => ?_)
    exact specializes_iff_mem_closure.1 ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum A) p).1 bot_le)

  obtain ⟨Z₀, e₀, -, hZet, hadd, hpow, hrep⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom (Sp A) P.A n D.La P.isAb hn'
  let s₀ : Z₀.left ⟶ Sp ℤ := specZIsTerminal.from _
  let p := pullback.fst s₀ (spMap (algebraMap ℤ (CycRing n)))
  let g := pullback.snd s₀ (spMap (algebraMap ℤ (CycRing n)))
  let Y : Over (Sp A) := Over.mk (p ≫ Z₀.hom)
  let π : Y ⟶ Z₀ := Over.homMk p rfl
  let et : D.La → (Y ⟶ P.A) := fun a => π ≫ e₀ a
  let c : Γ(Y.left, ⊤)ˣ := Units.map (LevCover.fnOn g).toMonoidHom (cycUnit hn)
  have hu : IsUnit (n : Γ(Y.left, ⊤)) := isUnit_natCast_of_hom Y.hom hn'
  have hadd' : ∀ a a', et (a + a') = et a * et a' := fun a a' => by
    simp only [et]; rw [hadd, MonObj.comp_mul]
  have hpow' : ∀ a, et a ^ n = 1 := fun a => by
    simp only [et]; rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  have hc : c ^ n = 1 := by rw [← map_pow, cycUnit_pow, map_one]
  have hflat : Flat Y.hom := by
    have : Module.Free ℤ (CycRing n) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic n ℤ)).basis
    have : Flat (spMap (algebraMap ℤ (CycRing n))) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    have : Flat Z₀.hom := inferInstance
    show Flat (p ≫ Z₀.hom)
    infer_instance

  have hq1 : ∀ {T : Over (Sp A)} (h : T ⟶ Y) (x y : Y ⟶ P.A), h ≫ (x * y⁻¹) = 1 ↔ h ≫ x = h ≫ y :=
    fun h x y => by rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hn' (et (b • a) * (et a ≫ act b)⁻¹) (by
      haveI := hact b
      rw [mul_pow, inv_pow, hpow', ← MonObj.pow_comp, hpow', MonObj.one_comp, inv_one, _root_.mul_one])
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL (Sp A) P n Y (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow' _) (hpow' _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let qY : Y ⟶ Out.baseOver (Sp A) := Over.homMk Y.hom (by simp)
  have hnN : IsUnit ((n * N : ℕ) : Γ(Sp A, ⊤)) := hnat _ (Nat.mul_pos hn hN)
  choose C4 hC4 HC4 using fun i : κ =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hnN (et (lam i) ^ m * (qY ≫ pt i)⁻¹) (by
      have e1 : (et (lam i) ^ m) ^ (n * N) = 1 := by
        rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, hpow', one_pow]
      have e2 : (qY ≫ pt i) ^ (n * N) = 1 := by
        rw [← MonObj.comp_pow, show n * N = N * n by ring, pow_mul, hpt, one_pow, MonObj.comp_one]
      rw [mul_pow, inv_pow, e1, e2, inv_one, _root_.mul_one])
  let w : Γ(Y.left, ⊤) := LevCover.fnOn Y.hom z
  let C3 : Set Y.left := (Y.left.basicOpen ((c : Γ(Y.left, ⊤)) ^ m - w) : Set Y.left)ᶜ
  have hC3 : IsOpen C3 := by
    refine isOpen_compl_basicOpen_sub _ _ (Nat.mul_pos hn hN) ?_ ?_ (isUnit_natCast_of_hom Y.hom hnN)
    · rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, ← Units.val_pow_eq_pow_val, hc, Units.val_one,
        one_pow]
    · simp only [w]
      rw [← map_pow, show n * N = N * n by ring, pow_mul, hz, one_pow, map_one]
  let C : Set Y.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Y.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hgen : ∀ {y y' : Y.left}, y ⤳ y' → y' ∈ C → y ∈ C := by
    intro y y' hyy hy'
    simp only [C, Set.mem_inter_iff, Set.mem_iInter] at hy' ⊢
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hy'
    exact ⟨⟨⟨fun b a => hyy.mem_open (hC1 b a).isOpen (k1 b a),
      fun a a' => hyy.mem_open (C2 a a').isOpen (k2 a a')⟩, hyy.mem_open hC3 k3⟩,
      fun i => hyy.mem_open (hC4 i).isOpen (k4 i)⟩
  have key : ∀ (F : Type) [Field F] (x : Sp F ⟶ Sp A) (ρ : A →+* F) (ζ : Fˣ) (h : Over.mk x ⟶ Y), x = spMap ρ →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : F) ^ m = ρ z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro F _ x ρ ζ h hx hζ
    have hw : h.left ≫ Y.hom = x := Over.w h
    have hq : h ≫ qY = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff Y.hom h.left ρ (by rw [hw, hx]) z c ζ m hζ
    have hzk : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a _ h, hq1, Category.assoc]
    · rw [← HC2 a a' _ h, hzk]
    · rw [← HC4 i _ h, hq1, ← hq, Category.assoc, MonObj.comp_pow]

  obtain ⟨ρ₀, hρ₀⟩ := exists_map_eq hn h₁
  obtain ⟨h₀, hh₀, -⟩ := hrep (Over.mk (spMap β₀)) ev₀ h₂ h₃
  let w₀ : Sp K₀ ⟶ Y.left := pullback.lift h₀.left (spMap ρ₀) (specZIsTerminal.hom_ext _ _)
  have hw₀ : w₀ ≫ p = h₀.left := pullback.lift_fst _ _ _
  have hw₀' : w₀ ≫ g = spMap ρ₀ := pullback.lift_snd _ _ _
  let y₀ : Over.mk (spMap β₀) ⟶ Y := Over.homMk w₀ (by
    show w₀ ≫ p ≫ Z₀.hom = spMap β₀
    rw [← Category.assoc, hw₀]
    exact Over.w h₀)
  have hy₀c : Units.map y₀.left.appTop.hom.toMonoidHom c = unitOn ζ₀ := by
    rw [← hρ₀]
    exact LevCover.map_fnOn g w₀ ρ₀ hw₀' (cycUnit hn)
  obtain rfl : (fun a => y₀ ≫ et a) = ev₀ := funext fun a => by
    apply Over.OverMorphism.ext
    show w₀ ≫ p ≫ (e₀ a).left = (ev₀ a).left
    rw [← Category.assoc, hw₀]
    exact congrArg (fun t => t.left) (hh₀ a)
  have hC₀ := (key K₀ (spMap β₀) β₀ ζ₀ y₀ rfl hy₀c).1 ⟨h₄, h₅, h₆, h₇⟩
  obtain ⟨v₀⟩ : Nonempty (Sp K₀) := inferInstance

  have hs : (⊥ : PrimeSpectrum A) ⤳ Y.hom (w₀ v₀) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨y, hy, ey⟩ := Flat.generalizingMap Y.hom hs
  have hyC : y ∈ C := hgen hy (hC₀ ⟨v₀, rfl⟩)
  let k := AlgebraicClosure (Y.left.residueField y)
  let u : Sp k ⟶ Y.left := spMap (algebraMap (Y.left.residueField y) k) ≫ Y.left.fromSpecResidueField y
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have huy : ∀ v', u v' = y := fun v' => by
    have : u v' ∈ Set.range (Y.left.fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨ρ, hρ⟩ := LevCover.exists_spMap (A := k) (u ≫ Y.hom)
  let yk : Over.mk (u ≫ Y.hom) ⟶ Y := Over.homMk u rfl
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := k) (Units.map yk.left.appTop.hom.toMonoidHom c)
  have hprim : IsPrimitiveRoot ζ n := by
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (A := k) (u ≫ g)
    have e1 := (LevCover.map_fnOn g u β' hβ' (cycUnit hn)).symm.trans hζ
    rw [← unitOn_inj e1]
    exact isPrimitiveRoot_map hn (hK ρ n hn) β'
  refine ⟨k, inferInstance, u ≫ Y.hom, ρ, ζ, fun a => yk ≫ et a, hK ρ n hn, ⟨v, ?_⟩, by rw [Category.comp_id, hρ],
    hprim, fun a a' => by beta_reduce; rw [hadd', MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow', MonObj.comp_one],
    (key k (u ≫ Y.hom) ρ ζ yk hρ hζ).2 ?_⟩
  · show Y.hom (u v) = _
    rw [huy v, ey]
  · rintro _ ⟨v', rfl⟩
    show u v' ∈ C
    rw [huy v']
    exact hyC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrMod
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_cell_section : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  intro E _ _ _ H D X _ _ _ y n N hn hN Z Z' h hker hsurj
  haveI := D.proj
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hN
    omega
  let mulN : X →ₗ[𝓞 E] X := N • LinearMap.id
  have hinj : Function.Injective mulN := by
    intro u v huv
    have h1 : N • u = N • v := by simpa [mulN] using huv
    have h2 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hN0
    · exact sub_eq_zero.1 h3
  let q : D.La →ₗ[𝓞 E] D.La := LinearMap.id - Z'.subtype ∘ₗ h.proj
  have hqa : ∀ a, q a = a - (h.proj a : D.La) := fun a => rfl
  have hq : ∀ a, q a ∈ perp D Z := fun a => by rw [hqa]; exact h.sub_proj_mem a
  have hrange : ∀ a, (y ∘ₗ q) a ∈ LinearMap.range mulN := fun a => by
    obtain ⟨e, he⟩ := (hker (q a)).2 ⟨q a, hq a, 0, by simp⟩
    exact ⟨e, by simp [mulN, he]⟩
  let ε : D.La →ₗ[𝓞 E] X :=
    (LinearEquiv.ofInjective mulN hinj).symm.toLinearMap ∘ₗ (y ∘ₗ q).codRestrict _ hrange
  have hε : ∀ a, N • ε a = y (q a) := by
    intro a
    have h2 := congrArg Subtype.val ((LinearEquiv.ofInjective mulN hinj).apply_symm_apply ⟨(y ∘ₗ q) a, hrange a⟩)
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let muln : X →ₗ[𝓞 E] X := n • LinearMap.id
  let S : Submodule (𝓞 E) X := LinearMap.range muln
  let g : Z' →ₗ[𝓞 E] X ⧸ S := S.mkQ ∘ₗ y ∘ₗ Z'.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, hb, e, he⟩ := hsurj x
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply, he]
    rw [Submodule.Quotient.eq]
    exact ⟨e, by simp [mulN, muln]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (S.mkQ ∘ₗ ε) hg
  have hs' : ∀ a, ∃ e, y (s a) = ε a + n • e := by
    intro a
    have h1 := LinearMap.congr_fun hs a
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨e, ?_⟩
    have he' : n • e = y (s a) - ε a := by simpa [muln] using he
    rw [he']
    abel
  refine ⟨Z'.subtype ∘ₗ h.proj + N • (Z'.subtype ∘ₗ s ∘ₗ q), fun a => ?_, fun b hb => ?_, fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact add_mem (h.proj a).2 (Z'.nsmul_mem (s (q a)).2 N)
  · have hqb : q b = 0 := by rw [hqa, h.proj_of_mem hb, sub_self]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, hqb,
      map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    exact h.proj_of_mem hb
  · obtain ⟨e, he⟩ := hs' (q a)
    refine ⟨N • e, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add,
      map_nsmul]
    have hy : y (q a) = y a - y (h.proj a) := by rw [hqa, map_sub]
    have hqq : q (q a) = q a := by rw [hqa (q a), h.proj_of_perp (hq a), sub_zero]
    rw [he, smul_add, hε, hqq, hy, smul_comm N n e]
    abel
  · refine ⟨(h.proj a : D.La) - a, ?_, s (q a), ?_⟩
    · have := neg_mem (h.sub_proj_mem a)
      rwa [neg_sub] at this
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      abel

end GlobalTheory.LowFilt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalPull

set_option maxHeartbeats 3200000 in

theorem exists_pelUnif_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  intro E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have aV := hV.1
  have hI : (maximalIdeal R).map θ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap θ) t
  let t' : SAB H (Sp V) := ⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap θ) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ) := hm₁
  let W : (Sp R).Opens := PrimeSpectrum.basicOpen f
  have hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R)) := hψ
  have hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    show f ∉ Ideal.comap θ ⊥
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  let x : Sp (FractionRing V) ⟶ Sp R := jK V ≫ specOf θ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK V).base z = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
    show (specOf θ).base ((jK V).base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW
  obtain ⟨PK, cubK, symK, adjK, primK, mK, hmK⟩ := sabPull CubePf.cubePull x t
  let tK : SAB H (Sp (FractionRing V)) := ⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩
  have hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x)) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    rw [P.bundle, ← hmK]
    exact ⟨wK, gK⟩
  have hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB := pull_isLB P.U.LG.isLB _
  have hp : IsProper tK.G.hom := GlobalTheory.ZH.isProper_hom_of_relAmple hamp
  haveI := hp
  have hA : RelAmple tK.G tK.PP.L :=
    GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB
      (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp
  have hK : KTriv tK.G tK.PP.L := GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt

  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have dA : d = P.A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hpbG := isGrpPullback_pullback t.G x
  have hdB : SmoothOfRelativeDimension P.A.g tK.G.hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing V)) := GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK
  let oA' : A'.OAct (𝓞 E) := ⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  have hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ)) :=
    ((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback t'.G (jK V)).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))),
      wA.IsGen := by
    rw [← heA]
    exact LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩

  have hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm
  have hψn := GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW
  have extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom =
      eA.hom ≫ (OAct.pullback x t.G t.act).act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpbG.1.hom_ext
    · have a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) =
          pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) =
          pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
          pullback.fst t.G.hom x ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have i₀ : (Iso.refl t'.G).hom.left = 𝟙 _ := rfl
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA,
        i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen
    t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL
  have extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a := by
    intro a
    rw [hgenU]
    exact extA₀ a
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      mod := mod'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := hLG
      lin := lin'
      w0 := w0' H.w0 P.w0 }
  exact ⟨t', P', hD, ⟨m₀⟩, xl, el⟩

end GlobalTheory.LocalPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogoStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_perp | exact GlobalTheory.LowFilt.exists_improves_of_perp | (intros; apply GlobalTheory.LowFilt.exists_improves_of_perp <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_quadraticForm_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ, (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (exact GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (intros; apply GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_ratio_of_exp_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  intro R _ _ _ hB D C k hk G S Ψ hΨ W₀ _ _ _ T₀ a₀ b₀ ha hb hS
  obtain ⟨u₀, hu₀⟩ := hΨ W₀ T₀
  have hp := GlobalTheory.T.traitExpansions_same_family_proportional R hB D C W₀ T₀ k hk G S Ψ a₀ b₀ 1 (u₀ : W₀) hS hu₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.secK_ratio_trait_descends_to_fractionField R hB D C W₀ T₀ k S Ψ ((u₀ : W₀) * a₀) (b₀ * 1)
    (mul_ne_zero u₀.ne_zero ha) (by rw [_root_.mul_one]; exact hb) hp
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨u, hu⟩ := hΨ W T
  exact ⟨u, GlobalTheory.T.expansion_transfer_of_relation_genericFibre R D C W T k G S Ψ r t (u : W) hrt hu⟩

end GlobalTheory.Mum
end

