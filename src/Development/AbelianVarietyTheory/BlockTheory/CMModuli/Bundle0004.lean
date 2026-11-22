import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.CyclotomicRootsOfUnity
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels

def LiesOver (W : ValuationSubring ℂ) (p : ℕ) : Prop := (p : ℂ) ∈ W.nonunits

example (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, LiesOver W p := by
  have hI : Ideal.span {((p : ℕ) : (⊥ : Subring ℂ))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    obtain ⟨⟨x, hx⟩, h1⟩ := h.exists_right_inv
    obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hx
    have h2 : ((p : ℤ) : ℂ) * (m : ℂ) = 1 := by simpa using congrArg Subtype.val h1
    have h3 : (p : ℤ) * m = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨m, h3.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast h4))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨W, hW ⟨_, Ideal.subset_span rfl, by simp⟩⟩

abbrev locRing (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : ValuationSubring F :=
  W.comap F.val.toRingHom

abbrev locIncl (W : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) : locRing W F →+* F :=
  (locRing W F).subtype

def locMap (W : ValuationSubring ℂ) {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    locRing W F →+* locRing W F' :=
  ((IntermediateField.inclusion h).toRingHom.comp (locIncl W F)).codRestrict (locRing W F') fun x => x.2

theorem inv_natCast_mem {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {d : ℕ}
    (hd : ¬ p ∣ d) : (d : ℂ)⁻¹ ∈ W := by
  by_contra h
  have hdn : (d : ℂ) ∈ W.nonunits := (W.mem_nonunits_iff_or).mpr (Or.inr h)
  have hc : IsCoprime (p : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : ℂ) * p + (b : ℂ) * d = 1 := by exact_mod_cast hab
  have hv : ∀ (m : ℤ) (x : ℂ), W.valuation x < 1 → W.valuation ((m : ℂ) * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).mpr (intCast_mem W m))) hx
  have := Valuation.map_add_lt W.valuation (hv a _ (W.mem_nonunits_iff.mp hW)) (hv b _ (W.mem_nonunits_iff.mp hdn))
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem zeta_mem_valuationSubring (W : ValuationSubring ℂ) {M : ℕ} (hM : M ≠ 0) : zeta M ∈ W := by
  have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
  rw [← W.valuation_le_one_iff]
  have h2 : W.valuation (zeta M) ^ M = 1 := by rw [← map_pow, h1, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' hM).mp h2).le

theorem cycloLocal_le {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {M : ℕ} (hM : M ≠ 0)
    {F : IntermediateField ℚ ℂ} (hF : zeta M ∈ F) : cycloLocal p M ≤ W.toSubring ⊓ F.toSubfield.toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨q, hq, rfl⟩ | hx)
  · refine ⟨?_, SubfieldClass.ratCast_mem F q⟩
    change (q : ℂ) ∈ W
    rw [Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem W _) (inv_natCast_mem hp hW hq)
  · obtain rfl : x = zeta M := hx
    exact ⟨zeta_mem_valuationSubring W hM, hF⟩

def cycloMap {W : ValuationSubring ℂ} {p : ℕ} (hp : p.Prime) (hW : LiesOver W p) {M : ℕ} (hM : M ≠ 0)
    {F : IntermediateField ℚ ℂ} (hF : zeta M ∈ F) : cycloLocal p M →+* locRing W F :=
  ((cycloLocal p M).subtype.codRestrict F fun x => (cycloLocal_le hp hW hM hF x.2).2).codRestrict
    (locRing W F) fun x => (cycloLocal_le hp hW hM hF x.2).1

theorem zeta_mem_of_dvd {F : IntermediateField ℚ ℂ} {a N : ℕ} (hN : N ≠ 0) (h : a ∣ N) (hF : zeta N ∈ F) :
    zeta a ∈ F := by
  obtain ⟨k, rfl⟩ := h
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hN)
  have : zeta a = zeta (a * k) ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hF k

theorem zeta_lcm_mem {F : IntermediateField ℚ ℂ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h₁ : zeta a ∈ F)
    (h₂ : zeta b ∈ F) : zeta (Nat.lcm a b) ∈ F := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hl : ((Nat.lcm a b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero ha hb)
  have e1 : ((Nat.gcd a b : ℕ) : ℂ) * (Nat.lcm a b : ℕ) = a * b := by exact_mod_cast Nat.gcd_mul_lcm a b
  have e2 : ((Nat.gcd a b : ℕ) : ℂ) = a * (Nat.gcdA a b : ℂ) + b * (Nat.gcdB a b : ℂ) := by
    exact_mod_cast Nat.gcd_eq_gcd_ab a b
  have : zeta (Nat.lcm a b) = zeta a ^ Nat.gcdB a b * zeta b ^ Nat.gcdA a b := by
    rw [zeta, zeta, zeta, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    field_simp
    linear_combination (-1 : ℂ) * e1 + (Nat.lcm a b : ℂ) * e2
  rw [this]
  exact mul_mem (zpow_mem h₁ _) (zpow_mem h₂ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Idx (H : Host E) (p : ℕ) : Type := Σ l : {l : Level H // l.GoodAt p}, Coeff l.1

abbrev Idx.l {p : ℕ} (i : Idx H p) : Level H := i.1.1

abbrev Idx.F {p : ℕ} (i : Idx H p) : IntermediateField ℚ ℂ := i.2.F

def Idx.Le {p : ℕ} (i j : Idx H p) : Prop := i.l.Dvd j.l ∧ i.F ≤ j.F

theorem Idx.Le.refl {p : ℕ} (i : Idx H p) : i.Le i := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩

theorem Idx.Le.trans {p : ℕ} {i j k : Idx H p} (h : i.Le j) (h' : j.Le k) : i.Le k :=
  ⟨⟨h.1.1.trans h'.1.1, h'.1.2.1.trans h.1.2.1, h.1.2.2.trans h'.1.2.2⟩, h.2.trans h'.2⟩

def addLevel (l : Level H) {N : ℕ} (hN : N ≠ 0) : Level H :=
  { l with A := Nat.lcm l.A N, A_pos := Nat.lcm_pos l.A_pos (Nat.pos_of_ne_zero hN) }

theorem zeta_mem_sup (F : IntermediateField ℚ ℂ) (N : ℕ) :
    zeta N ∈ F ⊔ IntermediateField.adjoin ℚ {zeta N} :=
  (le_sup_right : _ ≤ F ⊔ _) (IntermediateField.subset_adjoin _ _ rfl)

def addCoeff {l : Level H} (c : Coeff l) {N : ℕ} (hN : N ≠ 0) : Coeff (addLevel l hN) :=
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hz : zeta (addLevel l hN).M' ∈ c.F ⊔ IntermediateField.adjoin ℚ {zeta N} := by
    have : (addLevel l hN).M' = Nat.lcm l.M' N := (Nat.lcm_assoc _ _ _).symm
    rw [this]
    exact zeta_lcm_mem hM' hN ((le_sup_left : c.F ≤ _) c.zeta_mem) (zeta_mem_sup _ _)
  { F := c.F ⊔ IntermediateField.adjoin ℚ {zeta N}
    fin := by
      have := c.fin
      have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta N}) :=
        IntermediateField.adjoin.finiteDimensional
          (((Complex.isPrimitiveRoot_exp N hN).isIntegral (Nat.pos_of_ne_zero hN)).tower_top)
      infer_instance
    conj := fun τ a => (le_sup_left : c.F ≤ _) (c.conj τ a)
    zeta_mem := hz
    le := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x (rfl | hx)
      · exact (le_sup_left : c.F ≤ _) (c.le (IntermediateField.subset_adjoin _ _ (by simp)))
      · obtain rfl : x = _ := hx
        exact zeta_mem_of_dvd
          (Nat.lcm_ne_zero (by have := l.three_le; change l.M ≠ 0; omega) (addLevel l hN).A_pos.ne')
          (Nat.dvd_lcm_right _ _) hz }

def Idx.add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : Idx H p :=
  ⟨⟨addLevel i.l hN, i.1.2⟩, addCoeff i.2 hN⟩

theorem Idx.le_add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : i.Le (i.add hN) :=
  ⟨⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩, le_sup_left⟩

theorem Idx.zeta_mem_add {p : ℕ} (i : Idx H p) {N : ℕ} (hN : N ≠ 0) : zeta N ∈ (i.add hN).F :=
  zeta_mem_sup _ _

def abOpen {S : Scheme.{0}} (G : Over S) : S.Opens := ⟨interior (abLocus G), isOpen_interior⟩

def IsBirational {X Z : Scheme.{0}} (h : X ⟶ Z) : Prop :=
  ∃ V : Z.Opens, Dense (V : Set Z) ∧ Dense ((h ⁻¹ᵁ V : X.Opens) : Set X) ∧ IsIso (h ∣_ V)

example (X : Scheme.{0}) : IsBirational (𝟙 X) :=
  ⟨⊤, dense_univ, dense_univ, inferInstance⟩

def IsSymplecticFrame (D : Datum H) {g N : ℕ} (ρ : D.La →+ Std g N) : Prop :=
  Function.Surjective ρ ∧ (∀ a, ρ a = 0 ↔ ∃ b, a = N • b) ∧
    ∀ a b, stdForm (ρ a) (ρ b) = (D.EF a b : ZMod N)

def genus (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * (D.p + D.q)

section Compare

variable {D : Datum H} {l l₁ : Level H} {Xo : Moduli D l} {Xo₁ : Moduli D l₁} {c : Coeff l} {c₁ : Coeff l₁}
  {O O₁ : Type} [CommRing O] [CommRing O₁] {β : O →+* c.F} {β₁ : O₁ →+* c₁.F}

def IsEtaleCoverOnAb (Y : Model Xo c β) (Y₁ : Model Xo₁ c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) : Prop :=
  ∃ q : (abOpen Y₁.t.G).toScheme ⟶ pullback ((abOpen Y.t.G).ι ≫ Y.s) (spMap b),
    q ≫ pullback.fst _ _ ≫ (abOpen Y.t.G).ι = (abOpen Y₁.t.G).ι ≫ π ∧
    q ≫ pullback.snd _ _ = (abOpen Y₁.t.G).ι ≫ Y₁.s ∧
    IsFinite q ∧ Etale q ∧ Surjective q

def IsClassified (Y₁ : Model Xo₁ c₁ β₁) {g N : ℕ} (ρ : D.La →+ Std g N) {R : Type} [CommRing R] (κ : R →+* O₁)
    {𝒜 : Scheme.{0}} (s : 𝒜 ⟶ Sp R) (A : Over 𝒜) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std g N → (𝟙_ (Over 𝒜) ⟶ A)) (good : Prop) : Prop :=
  ∃ (t : SAB H (abOpen Y₁.t.G).toScheme) (m : SABMap t Y₁.t (abOpen Y₁.t.G).ι)
    (j : Xo₁.XF c₁ ⟶ (abOpen Y₁.t.G).toScheme) (ψ : Y₁.oF.t.G.left ⟶ t.G.left)
    (lv₁ : Std g N → (𝟙_ (Over (abOpen Y₁.t.G).toScheme) ⟶ t.G))
    (f : (abOpen Y₁.t.G).toScheme ⟶ pullback s (spMap κ)),

    j ≫ (abOpen Y₁.t.G).ι = Y₁.j ∧ ψ ≫ m.φ = Y₁.m.φ ∧

    (∀ a, j ≫ (lv₁ (ρ a)).left = (Y₁.oF.etaA a ^ (l₁.A / N)).left ≫ ψ) ∧

    f ≫ pullback.snd _ _ = (abOpen Y₁.t.G).ι ≫ Y₁.s ∧ IsFinite f ∧
    IsPullbackTriple t.G (abelian₂ t.G t.PP.L) lv₁ A P lv (f ≫ pullback.fst _ _) ∧

    (good → ∃ (Z : Scheme.{0}) (h : (abOpen Y₁.t.G).toScheme ⟶ Z) (w : Z ⟶ pullback s (spMap κ))
      (tZ : SAB H Z) (mZ : SABMap t tZ h) (eZ eA : D.La → (𝟙_ (Over Z) ⟶ tZ.G))
      (lvZ : Std g N → (𝟙_ (Over Z) ⟶ tZ.G)),
      h ≫ w = f ∧ IsFinite h ∧ IsBirational h ∧ Surjective h ∧
      IsReduced Z ∧ Flat (w ≫ pullback.snd _ _) ∧ IsFinite w ∧ FormallyUnramified w ∧
      (∀ a, j ≫ h ≫ (eZ a).left = (Y₁.oF.eta a).left ≫ ψ ≫ mZ.φ) ∧
      (∀ a, j ≫ h ≫ (eA a).left = (Y₁.oF.etaA a).left ≫ ψ ≫ mZ.φ) ∧
      (∀ a, lvZ (ρ a) = eA a ^ (l₁.A / N)) ∧
      IsPullbackTriple tZ.G (abelian₂ tZ.G tZ.PP.L) lvZ A P lv (w ≫ pullback.fst _ _))

end Compare

abbrev Models {D : Datum H} (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) : Type 1 :=
  ∀ i : Idx H p, Model (Xo i.l) i.2 (locIncl W i.F)

abbrev Transitions {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ}
    (Y : Models Xo p W) : Type :=
  ∀ i j : Idx H p, i.Le j → ((Y j).X ⟶ (Y i).X)

def SiegelComparison {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : LiesOver W p) (Y : Models Xo p W) (π : Transitions Y) : Prop :=
  ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p ∧ (∀ i : Idx H p, n.Coprime i.l.M) ∧
    ∃ (M₁ : ℕ) (hM : M₁ ≠ 0), 3 ≤ M₁ ∧ (∃ e : ℕ, M₁ = n ^ e) ∧
      ∃ (𝒜 : Scheme.{0}) (s : 𝒜 ⟶ Sp (cycloLocal p M₁)) (A : Over 𝒜) (_ : GrpObj A) (P : LB (A ⊗ A).left)
        (lv : Std (genus D) M₁ → (𝟙_ (Over 𝒜) ⟶ A)) (ρ : D.La →+ Std (genus D) M₁),
        IsSiegelFamily (genus D) p hM 𝒜 s A P lv ∧ IsSymplecticFrame D ρ ∧
        ∀ i : Idx H p,
          IsEtaleCoverOnAb (Y i) (Y (i.add hM)) (locMap W (i.le_add hM).2) (π i (i.add hM) (i.le_add hM)) ∧
          IsClassified (Y (i.add hM)) ρ (cycloMap hp hW hM (i.zeta_mem_add hM)) s A P lv (¬ p ∣ i.l.M')

def IsLocalSystem {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} (hp : p.Prime)
    {W : ValuationSubring ℂ} (hW : LiesOver W p) (Y : Models Xo p W) (π : Transitions Y) : Prop :=

  (∀ (i j : Idx H p) (h : i.Le j), IsTransition (Y i) (Y j) (locMap W h.2) (π i j h)) ∧

  (∀ i : Idx H p, π i i (Idx.Le.refl i) = 𝟙 _) ∧
  (∀ (i j k : Idx H p) (h : i.Le j) (h' : j.Le k), π j k h' ≫ π i j h = π i k (h.trans h')) ∧

  (∀ i : Idx H p, OneModel p (Y i)) ∧

  SiegelComparison hp hW Y π

def LocalSystemExists (H : Host E) : Prop :=
  ∀ (D : Datum H), 1 ≤ D.p + D.q → ∀ (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : LiesOver W p), ∃ (Y : Models Xo p W) (π : Transitions Y), IsLocalSystem hp hW Y π

end GlobalTheory.IndefiniteRowSideFullHecke.CyclotomicRootsOfUnity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.LevelActionTransitions
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Group

variable (D : Datum H)

def nLa (n : ℕ) : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))

theorem mem_nLa {n : ℕ} {x : D.La} : x ∈ nLa D n ↔ ∃ y, x = n • y := by
  simp only [nLa, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, eq_comm]

abbrev LaMod (n : ℕ+) : Type := D.La ⧸ nLa D n

abbrev cls (n : ℕ+) (a : D.La) : LaMod D n := Submodule.Quotient.mk a

theorem cls_eq {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ ∃ y, a = b + (n : ℕ) • y := by
  rw [Submodule.Quotient.eq, mem_nLa]
  exact exists_congr fun y => by rw [sub_eq_iff_eq_add']

def KMax : Subgroup (∀ n : ℕ+, LaMod D n ≃ₗ[𝓞 E] LaMod D n) where
  carrier := {g | (∀ (n m : ℕ+) (a b : D.La), g (n * m) (cls D _ a) = cls D _ b → g n (cls D n a) = cls D n b) ∧
    ∀ (n : ℕ+) (a b a' b' : D.La), g n (cls D n a) = cls D n a' → g n (cls D n b) = cls D n b' →
      D.EF a' b' ≡ D.EF a b [ZMOD (n : ℕ)]}
  one_mem' := by
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨y, hy⟩ := (cls_eq D).mp h
      exact (cls_eq D).mpr ⟨(m : ℕ) • y, by rw [hy, PNat.mul_coe, mul_smul]⟩
    · obtain ⟨y, rfl⟩ := (cls_eq D).mp ha
      obtain ⟨z, rfl⟩ := (cls_eq D).mp hb
      refine Int.modEq_iff_dvd.mpr ⟨D.EF a' z + D.EF y b' + (n : ℕ) * D.EF y z, ?_⟩
      simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      ring
  mul_mem' := by
    rintro g g' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' (n * m) (cls D _ a))
      change g (n * m) (g' (n * m) (cls D _ a)) = _ at h
      change g n (g' n (cls D _ a)) = _
      rw [h1' n m a c hc.symm]
      exact h1 n m c b (by rw [← h, ← hc])
    · obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ a))
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (g' n (cls D _ b))
      change g n (g' n (cls D _ a)) = _ at ha
      change g n (g' n (cls D _ b)) = _ at hb
      exact (h2 n c d a' b' (by rw [← ha, ← hc]) (by rw [← hb, ← hd])).trans (h2' n a b c d hc.symm hd.symm)
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    refine ⟨fun n m a b h => ?_, fun n a b a' b' ha hb => ?_⟩
    · change (g (n * m)).symm (cls D _ a) = _ at h
      change (g n).symm (cls D _ a) = _
      rw [LinearEquiv.symm_apply_eq] at h ⊢
      exact (h1 n m b a h.symm).symm
    · change (g n).symm (cls D _ a) = _ at ha
      change (g n).symm (cls D _ b) = _ at hb
      rw [LinearEquiv.symm_apply_eq] at ha hb
      exact (h2 n a' b' a b ha.symm hb.symm).symm

theorem neg_mem_KMax : (fun n => LinearEquiv.neg (𝓞 E)) ∈ KMax D := by
  have h1 := (KMax D).one_mem
  refine ⟨fun n m a b h => h1.1 n m (-a) b h, fun n a b a' b' ha hb => ?_⟩
  simpa using h1.2 n (-a) (-b) a' b' ha hb

variable {D}

def modulus (l : Level H) : ℕ+ := ⟨l.M', Nat.lcm_pos (by have := l.three_le; omega) l.A_pos⟩

def Sends (l : Level H) (g : KMax D) (a b : D.La) : Prop :=
  g.1 (modulus l) (cls D _ a) = cls D _ b

def FixesLevel (l : Level H) (g : KMax D) : Prop :=
  ∀ a b, Sends l g a b → a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ∧ a - b ∈ nLa D l.A

theorem exists_sends (l : Level H) (g : KMax D) (a : D.La) : ∃ b, Sends l g a b := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (g.1 (modulus l) (cls D _ a))
  exact ⟨b, hb.symm⟩

end Group

def IsNormalisation {U Z Y : Scheme.{0}} (i : U ⟶ Z) (p : Z ⟶ Y) : Prop :=
  ∃ (_ : QuasiCompact (i ≫ p)) (_ : QuasiSeparated (i ≫ p)) (e : Z ≅ (i ≫ p).normalization),
    i ≫ e.hom = (i ≫ p).toNormalization ∧ e.hom ≫ (i ≫ p).fromNormalization = p

theorem isNormalisation_normalization {U Y : Scheme.{0}} (f : U ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsNormalisation f.toNormalization f.fromNormalization := by
  have key : ∀ g : U ⟶ Y, g = f → ∃ (_ : QuasiCompact g) (_ : QuasiSeparated g) (e : f.normalization ≅ g.normalization),
      f.toNormalization ≫ e.hom = g.toNormalization ∧ e.hom ≫ g.fromNormalization = f.fromNormalization := by
    rintro g rfl
    exact ⟨inferInstance, inferInstance, Iso.refl _, by simp, by simp⟩
  exact key _ f.toNormalization_fromNormalization

theorem IsNormalisation.isIntegralHom {U Z Y : Scheme.{0}} {i : U ⟶ Z} {p : Z ⟶ Y} (h : IsNormalisation i p) :
    IsIntegralHom p := by
  obtain ⟨_, _, e, -, he⟩ := h
  rw [← he]; infer_instance

section OneLevel

variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀}

def etaMap (m : Model univ h φ) (a : D.La) : baseChange str h ⟶ m.t.G.left := m.secMap (toUnit _ ≫ univ.eta a)

def etaAMap (m : Model univ h φ) (a : D.La) : baseChange str h ⟶ m.t.G.left := m.secMap (toUnit _ ≫ univ.etaA a)

def Descends (m : Model univ h φ) : Prop :=
  ∃ (Y : Scheme.{0}) (sY : Y ⟶ Sp (KA l)) (i : X₀ ⟶ Y) (p : pullback m.s (spMap φ) ⟶ Y)
    (tY : SAB H Y) (tQ : SAB H (pullback m.s (spMap φ)))
    (u : SABMap univ.t tY i) (qX : SABMap tQ m.t (pullback.fst m.s (spMap φ))) (qY : SABMap tQ tY p),
    IsOpenImmersion i ∧ i ≫ sY = str ∧
    IsPullback p (pullback.snd m.s (spMap φ)) sY (spMap h.incl) ∧
    m.j ≫ p = baseChangeFst str h ≫ i ∧
    qX.cart.1.lift m.toModel.φ (m.t₀.G.hom ≫ m.j) (by rw [Category.assoc]; exact m.toModel.cart.1.w) ≫ qY.φ =
      m.toUniv.φ ≫ u.φ

structure IsLevelAction (m : Model univ h φ) (act : KMax D → (m.X ⟶ m.X)) (lift : ∀ g, SABMap m.t m.t (act g))
    (act₀ : KMax D → (baseChange str h ⟶ baseChange str h)) : Prop where
  act_over : ∀ g, act g ≫ m.s = m.s
  act_one : act 1 = 𝟙 _
  act_mul : ∀ g g', act (g * g') = act g ≫ act g'
  lift_one : (lift 1).φ = 𝟙 _
  lift_mul : ∀ g g', (lift (g * g')).φ = (lift g).φ ≫ (lift g').φ
  act_fix : ∀ g, FixesLevel l g → act g = 𝟙 _
  lift_fix : ∀ g, FixesLevel l g → (lift g).φ = 𝟙 _
  act₀_over : ∀ g, act₀ g ≫ baseChangeStr str h = baseChangeStr str h
  act₀_incl : ∀ g, act₀ g ≫ m.incl = m.incl ≫ act g
  eta : ∀ g a b, Sends l g a b → etaMap m b ≫ (lift g).φ = act₀ g ≫ etaMap m a
  etaA : ∀ g a b, Sends l g a b → etaAMap m b ≫ (lift g).φ = act₀ g ≫ etaAMap m a

def LevelActs (m : Model univ h φ) : Prop := ∃ act lift act₀, IsLevelAction m act lift act₀

theorem IsLevelAction.isIso {m : Model univ h φ} {act lift act₀} (ρ : IsLevelAction m act lift act₀) (g : KMax D) :
    IsIso (act g) :=
  ⟨act g⁻¹, by rw [← ρ.act_mul, mul_inv_cancel, ρ.act_one], by rw [← ρ.act_mul, inv_mul_cancel, ρ.act_one]⟩

variable {O' : Type} [CommRing O'] {φ' : O' →+* F₀}

def inclBase (m' : Model univ h φ') (ψ : O' →+* O) (hψ : φ.comp ψ = φ') :
    baseChange str h ⟶ pullback m'.s (spMap ψ) :=
  pullback.lift m'.incl (baseChangeStr str h ≫ spMap φ) (by
    rw [m'.incl_over, Category.assoc, ← Spec.map_comp, ← hψ]; rfl)

def compare (m' : Model univ h φ') (m : Model univ h φ) : m'.t₀.G.left ⟶ m.t₀.G.left :=
  m.toUniv.cart.1.lift m'.toUniv.φ m'.t₀.G.hom m'.toUniv.cart.1.w

def Dominates (m' : Model univ h φ') (m : Model univ h φ) (ψ : O' →+* O) (hψ : φ.comp ψ = φ') : Prop :=
  ∃ (δ : pullback m'.s (spMap ψ) ⟶ m.X) (t : SAB H (pullback m'.s (spMap ψ)))
    (q' : SABMap t m'.t (pullback.fst m'.s (spMap ψ))) (q : SABMap t m.t δ),
    δ ≫ m.s = pullback.snd m'.s (spMap ψ) ∧
    inclBase m' ψ hψ ≫ δ = m.incl ∧
    q'.cart.1.lift m'.toModel.φ (m'.t₀.G.hom ≫ inclBase m' ψ hψ)
        (by rw [Category.assoc, inclBase, pullback.lift_fst]; exact m'.toModel.cart.1.w) ≫ q.φ =
      compare m' m ≫ m.toModel.φ

end OneLevel

section TwoLevels

variable {D : Datum H} {l l₂ : Level H} {X₀ X₂ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)} {str₂ : X₂ ⟶ Sp (KA l₂)}
  {univ : Obj D l (baseKA l) str} {univ₂ : Obj D l₂ (baseKA l₂) str₂} {F₀ F₂ : IntermediateField ℚ ℂ}
  {h : IsCoeffField l F₀} {h₂ : IsCoeffField l₂ F₂}
  {O O₂ : Type} [CommRing O] [CommRing O₂] {φ : O →+* F₀} {φ₂ : O₂ →+* F₂}

structure IsTransition (m₂ : Model univ₂ h₂ φ₂) (m : Model univ h φ) (hl : l.Dvd l₂) (hF : F₀ ≤ F₂) (ψ : O →+* O₂)
    (hψ : φ₂.comp ψ = (IntermediateField.inclusion hF).toRingHom.comp φ) (π : m₂.X ⟶ m.X) : Prop where
  map_over : π ≫ m.s = m₂.s ≫ spMap ψ
  normalisation : IsNormalisation m₂.incl (pullback.lift π m₂.s map_over : m₂.X ⟶ pullback m.s (spMap ψ))
  compat : ∃ (π₀ : baseChange str₂ h₂ ⟶ baseChange str h) (q : SABMap m₂.t m.t π),
    π₀ ≫ baseChangeStr str h = baseChangeStr str₂ h₂ ≫ spMap (IntermediateField.inclusion hF).toRingHom ∧
    π₀ ≫ m.incl = m₂.incl ≫ π ∧
    (∀ a, etaMap m₂ ((l₂.M / l.M) • a) ≫ q.φ = π₀ ≫ etaMap m a) ∧
    (∀ a, etaAMap m₂ ((l₂.A / l.A) • a) ≫ q.φ = π₀ ≫ etaAMap m a)

end TwoLevels

end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
end
end

