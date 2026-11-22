import Mathlib
import ReciprocityTheory.DualLattices.Bundle0029
import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNsmulRight
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory

namespace SignChar

variable {R₀ : Type} [CommRing R₀]

section Pairing

variable (B : BX R₀) {R : LAlg R₀}

lemma pairing_zero_left (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz

lemma pairing_zero_right (N : ℕ) (x : B.G R) (hx : N • x = 0) : B.IsPairing N x 0 1 := by
  have h := B.pairing_sw N 0 x 1 (pairing_zero_left B N x hx)
  rwa [inv_one] at h

lemma pairing_nsmul_left (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h

lemma pairing_nsmul_right (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_right B N x h.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_right N _ _ _ _ _ ih h

lemma pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (z : ι → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_left B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ _ _ _ (h a) ih

lemma pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_right B N x hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_right N _ _ _ _ _ (h a) ih

end Pairing

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := by
  have h := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
  exact ⟨h.1, h.2.1⟩

lemma toZMod_eq_of_q (a : ℤ_[p]) (k : ℕ)
    (h : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) a) = k) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : ¬ IsUnit (a - k) := by
    intro hu
    have h2 := (hu.map (algebraMap ℤ_[p] (Tw.O : Type))).map (Tw.q 0).1
    rw [map_sub, map_sub, h, map_natCast, map_natCast, sub_self] at h2
    exact not_isUnit_zero h2
  have h3 : a - k ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod]
    exact h1
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h3
  exact h3

lemma pairing_ptOf (D : Dat p g B Tw Dt Oe σ cp) (s t : TT p g) :
    ∃ n : ℕ, (n : ZMod p) = PadicInt.toZMod (pair p g D.H.E s t) ∧
      B.IsPairing p (ptOf B D.L.τ (red p g s)) (ptOf B D.L.τ (red p g t)) (Tw.ζ 0 ^ n) := by
  choose k hk hpair using fun i j => D.L.E_spec i j 0
  simp only [zero_add, pow_one] at hpair
  refine ⟨∑ i, (∑ j, k i j * (red p g t j).val) * (red p g s i).val, ?_, ?_⟩
  · simp only [pair, dotProduct, mulVec, map_sum, map_mul, Nat.cast_sum, Nat.cast_mul,
      ZMod.natCast_zmod_val, red]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toZMod_eq_of_q _ _ (hk i j)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_left B _ p _ _ _ (D.pt_p _) fun i => ?_
    rw [pow_mul]
    refine pairing_nsmul_left B p _ _ _ ?_ _
    rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_right B _ p _ _ _ (hpair i i).1 fun j => ?_
    rw [pow_mul]
    exact pairing_nsmul_right B p _ _ _ (hpair i j) _

end SignChar

theorem signChar_mem_evImg :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvenTwoEvaluationSign D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ _ _ hp s
  have hex : ∀ i, ∃ z, B.IsPairing p (B.map (D.fin.sO i) (ptOf B D.L.τ (red p g s)))
      (D.fin.y i) z := fun i =>
    B.pairing_exists p _ _ (by rw [← map_nsmul, D.pt_p, map_zero]) (D.fin.y_p i)
  choose e he using hex
  refine ⟨D.evAll C fun i => (e i : (D.fin.AAx i : Type)), Submodule.subset_span ⟨_, rfl⟩,
    fun t => ?_⟩
  obtain ⟨h1, h2⟩ := SignChar.ptMap_spec D (red p g t)
  have h3 := B.pairing_map (D.ptMap (red p g t)) p _ _ _ (he (D.ptIdx (red p g t)))
  rw [← B.map_comp, h1, B.map_id, h2] at h3
  obtain ⟨n, hn, h4⟩ := SignChar.pairing_ptOf D s t
  have h5 := congrArg Units.val (B.pairing_unique p _ _ _ _ h3 h4)
  rw [Units.val_pow_eq_pow_val, D.zeta0 hp, Units.coe_map] at h5
  have h6 : (D.ptMap (red p g t)).1 (e (D.ptIdx (red p g t)) : (D.fin.AAx _ : Type)) =
      (-1) ^ n := h5
  have h7 : (PadicInt.toZMod (pair p g D.H.E s t)).val % 2 = n % 2 := by
    rw [← hn, ZMod.val_natCast, ← hp, Nat.mod_mod]
  unfold Dat.evAll
  rw [h6, map_pow, map_neg, map_one, neg_one_pow_eq_pow_mod_two n, ← h7,
    ← neg_one_pow_eq_pow_mod_two]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsFibreProduct
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem bxFibre_exists_chart {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] [IsLocalRing P] (x : Spec (CommRingCat.of P) ⟶ Y)
    (h : x (closedPoint P) ∈ U) :
    ∃ φ : Γ(Y, U) →+* P, x = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen h
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
    (isAffineOpen_top (Spec (CommRingCat.of P))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem bxFibre_closed {Y : Scheme.{0}} {P Q : Type} [CommRing P] [IsLocalRing P] [CommRing Q]
    [IsLocalRing Q] (f : P →+* Q) [IsLocalHom f] (x : Spec (CommRingCat.of P) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ x) (closedPoint Q) = x (closedPoint P) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => x y) ?_)
  exact IsLocalRing.comap_closedPoint f

theorem bxFibre_comp {Y : Scheme.{0}} {A P Q : Type} [CommRing A] [CommRing P] [CommRing Q]
    (φ : A →+* P) (f : P →+* Q) (g : Spec (CommRingCat.of A) ⟶ Y) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom φ) ≫ g =
      Spec.map (CommRingCat.ofHom (f.comp φ)) ≫ g := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem bxFibre_inj {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem bxFibre_affine {Y : Scheme.{0}} (y : Y) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  exact ⟨U, hU, hmem⟩

theorem bxFibre_unique {Y : Scheme.{0}} {F P Q : Type} [CommRing F] [IsLocalRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] (p : F →+* P) [IsLocalHom p] (q : F →+* Q)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) (c c' : Spec (CommRingCat.of F) ⟶ Y)
    (hp : Spec.map (CommRingCat.ofHom p) ≫ c = Spec.map (CommRingCat.ofHom p) ≫ c')
    (hq : Spec.map (CommRingCat.ofHom q) ≫ c = Spec.map (CommRingCat.ofHom q) ≫ c') :
    c = c' := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (c (closedPoint F))
  have hmem' : c' (closedPoint F) ∈ U := by
    rw [← bxFibre_closed p c', ← hp, bxFibre_closed p c]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU c hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU c' hmem'
  rw [hφ, hψ] at hp hq ⊢
  have h1 : p.comp φ = p.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ p hU.fromSpec).symm.trans (hp.trans (bxFibre_comp ψ p hU.fromSpec)))
  have h2 : q.comp φ = q.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ q hU.fromSpec).symm.trans (hq.trans (bxFibre_comp ψ q hU.fromSpec)))
  have : φ = ψ := RingHom.ext fun s =>
    hinj _ _ (RingHom.congr_fun h1 s) (RingHom.congr_fun h2 s)
  rw [this]

theorem bxFibre_exists {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (a (closedPoint P))
  have hmem' : b (closedPoint Q) ∈ U := by
    rw [← bxFibre_closed g b, ← h, bxFibre_closed f a]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU a hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU b hmem'
  rw [hφ, hψ] at h ⊢
  erw [bxFibre_comp, bxFibre_comp] at h
  have h1 := bxFibre_inj hU h
  have h2 : ∀ s, ∃ c, p c = φ s ∧ q c = ψ s := fun s =>
    (hex _ _ (RingHom.congr_fun h1 s)).exists
  choose k hk hk' using h2
  let χ : Γ(Y, U) →+* F :=
    { toFun := k
      map_one' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_mul' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk'])
      map_zero' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_add' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk']) }
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, ?_, ?_⟩
  · erw [bxFibre_comp]
    have : p.comp χ = φ := RingHom.ext hk
    rw [this]
  · erw [bxFibre_comp]
    have : q.comp χ = ψ := RingHom.ext hk'
    rw [this]

theorem points_fibre_product :
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) := by
  intro R₀ _ X F R₁ R₂ R p₁ p₂ f₁ f₂ hsq a b hab
  obtain ⟨hc, -, -, hex⟩ := hsq
  haveI : IsLocalHom p₁.1.toRingHom := p₁.2
  haveI : IsLocalHom f₁.1.toRingHom := f₁.2
  haveI : IsLocalHom f₂.1.toRingHom := f₂.2
  have hinj : ∀ s t, p₁.1.toRingHom s = p₁.1.toRingHom t → p₂.1.toRingHom s = p₂.1.toRingHom t →
      s = t := fun s t h1 h2 =>
    (hex (p₁.1 t) (p₂.1 t) (AlgHom.congr_fun hc t)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  obtain ⟨c, h1, h2⟩ := bxFibre_exists (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom
    f₁.1.toRingHom f₂.1.toRingHom hex hinj a.left b.left (congrArg (·.left) hab)
  have hw : c ≫ X.hom = (sp (R₀ := R₀) (F : Type)).hom := by
    refine bxFibre_unique p₁.1.toRingHom p₂.1.toRingHom hinj _ _ ?_ ?_
    · rw [← Category.assoc, h1]
      exact (Over.w a).trans (Over.w (spMap p₁.1)).symm
    · rw [← Category.assoc, h2]
      exact (Over.w b).trans (Over.w (spMap p₂.1)).symm
  refine ⟨Over.homMk c hw, ⟨Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩, ?_⟩
  rintro c' ⟨k1, k2⟩
  apply Over.OverMorphism.ext
  exact bxFibre_unique (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom hinj _ _
    ((congrArg (·.left) k1).trans h1.symm) ((congrArg (·.left) k2).trans h2.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisGram
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma gram_zero (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h
  have e : z * z = z := B.pairing_unique N 0 y _ _ h hz
  have e1 : z = 1 := by simpa using e
  rwa [e1] at hz

private lemma gram_nsmul (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (m : ℕ) : B.IsPairing N (m • x) y (z ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact gram_zero B N y h.2.1
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ y _ _ ih h

private lemma gram_sum {κ : Type} (s : Finset κ) (N : ℕ) (x : κ → B.G R) (y : B.G R)
    (z : κ → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact gram_zero B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ y _ _ (h a) ih

end SlopeTestRemainingChoices

private lemma gram_limit {p : ℕ} [Fact p.Prime] (k : ℕ → ℕ)
    (hk : ∀ n, k n ≡ k (n + 1) [MOD p ^ (n + 1)]) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow (n + 1) a = (k n : ZMod (p ^ (n + 1))) := by
  have hi : ∀ i : ℕ, (p : ℤ) ^ i ∣ (fun i : ℕ => (k (i - 1) : ℤ)) (i + 1) -
      (fun i : ℕ => (k (i - 1) : ℤ)) i := by
    intro i
    cases i with
    | zero => simp
    | succ n =>
      have h := (Nat.modEq_iff_dvd.1 (hk n))
      simpa using h
  have key := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i : ℕ => (k (i - 1) : ℤ)) p hi
  refine ⟨_, fun n => (key (n + 1)).trans ?_⟩
  simp only [Nat.add_sub_cancel, Int.cast_natCast]

private lemma gram_ext {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, h,
    PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) b]

private lemma gram_toZMod {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (k : ℕ)
    (h : PadicInt.toZModPow (0 + 1) a = (k : ZMod (p ^ (0 + 1)))) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : a - (k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (0 + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, h, sub_self]
  rw [PadicInt.ker_toZModPow, zero_add, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h1
  exact h1

theorem tateBasis_gram :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by
  intro R₀ _ p hp g B Tw _ _ _ hζ hζp τ htors hcomp hbasis hnd
  have hex : ∀ i j n, ∃ k : ℕ, k < p ^ (n + 1) ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := by
    intro i j n
    obtain ⟨z, hz⟩ := B.pairing_exists _ _ _ (htors i n) (htors j n)
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    obtain ⟨k, hk, e⟩ := (hζ n).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ z).2 (B.pairing_pow _ _ _ _ hz))
    exact ⟨k, hk, e ▸ hz⟩
  choose k hklt hk using hex
  have hcompat : ∀ i j n, k i j n ≡ k i j (n + 1) [MOD p ^ (n + 1)] := by
    intro i j n
    have h1 := gram_nsmul B _ _ _ _ (hk i j (n + 1)) p
    rw [← hcomp, pow_succ p (n + 1)] at h1
    have h2 := B.pairing_mul _ p _ _ _ (htors i n)
      (by rw [← pow_succ]; exact htors j (n + 1)) h1
    rw [← hcomp, ← pow_mul, mul_comm, pow_mul, hζp] at h2
    have h3 := B.pairing_unique _ _ _ _ _ (hk i j n) h2
    rwa [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf] at h3
  choose E hE using fun i j => gram_limit (k i j) (hcompat i j)
  have hanti : ∀ i j, E j i = -E i j := by
    intro i j
    refine gram_ext _ _ fun n => ?_
    have h1 := B.pairing_unique _ _ _ _ _ (hk j i n) (B.pairing_sw _ _ _ _ (hk i j n))
    rw [eq_inv_iff_mul_eq_one, ← pow_add, (hζ n).pow_eq_one_iff_dvd,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_add] at h1
    rw [map_neg, hE, hE]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Matrix.of E, ⟨?_, fun i => ?_⟩, ?_, fun i j n => ?_⟩
  · ext i j
    exact hanti i j
  · exact self_eq_neg.1 (hanti i i)
  · by_contra hu
    have hd : (Matrix.of E).det ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      exact hu
    rw [RingHom.mem_ker, RingHom.map_det] at hd
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have ht0 : ∀ i, p • τ i 0 = 0 := fun i => by simpa using htors i 0
    have hpt : ∀ t : Ix g → ZMod p, p • ptOf B τ t = 0 := fun t => by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by rw [ht0, smul_zero]
    have hrow : ∀ j, B.IsPairing p (ptOf B τ s) (τ j 0) 1 := by
      intro j
      have h1 := gram_sum B Finset.univ (p ^ (0 + 1)) (fun i => (s i).val • τ i 0) (τ j 0)
        (fun i => (Tw.ζ 0 ^ k i j 0) ^ (s i).val) (htors j 0)
        (fun i => gram_nsmul B _ _ _ _ (hk i j 0) _)
      have h2 : ∏ i, (Tw.ζ 0 ^ k i j 0) ^ (s i).val = 1 := by
        simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum, (hζ 0).pow_eq_one_iff_dvd, zero_add, pow_one,
          ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (congrFun hs j)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm, ← gram_toZMod _ _ (hE i j 0)]
        rfl
      rw [h2, zero_add, pow_one] at h1
      exact h1
    have hx : ptOf B τ s = 0 := by
      refine hnd _ (hpt s) fun y hy => ?_
      obtain ⟨t, rfl, -⟩ := hbasis y hy
      have h1 := gram_sum B Finset.univ p (fun j => (t j).val • τ j 0) (ptOf B τ s)
        (fun j => (1⁻¹) ^ (t j).val) (hpt s)
        (fun j => gram_nsmul B _ _ _ _ (B.pairing_sw _ _ _ _ (hrow j)) _)
      have h2 := B.pairing_sw _ _ _ _ h1
      simp only [inv_one, one_pow, Finset.prod_const_one] at h2
      exact h2
    have h0 : (0 : B.G Tw.O) = ptOf B τ (0 : Ix g → ZMod p) := by simp [ptOf]
    exact hs0 ((hbasis 0 (smul_zero p)).unique hx.symm h0)
  · rw [Matrix.of_apply, hE, ZMod.val_cast_of_lt (hklt i j n)]
    exact hk i j n

end GlobalTheory
end

