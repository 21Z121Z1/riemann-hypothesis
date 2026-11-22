import Development.EtaleCohomology.EtaleSheaves.CechSqPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0036
import Development.EtaleCohomology.EtaleSheaves.ConeExcision.ExcisionOfCokernel

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntegralSurjectiveRingCechAugmentationEtaleEqv
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf LateralTheory.E.CechSqPf

namespace LateralTheory.E.CechSqPf

def lev0Iso {C D : CommRingCat.{0}} (g : C ⟶ D) : D ≅ widePushout C (fun _ : Fin 1 => D) (fun _ => g) where
  hom := WidePushout.ι (fun _ => g) 0
  inv := WidePushout.desc g (fun _ => 𝟙 D) (fun _ => by simp)
  hom_inv_id := by apply WidePushout.ι_desc
  inv_hom_id := by
    apply WidePushout.hom_ext
    · intro j
      rw [Subsingleton.elim j 0, ← Category.assoc, WidePushout.ι_desc, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, WidePushout.head_desc, Category.comp_id]
      convert WidePushout.arrow_ι (fun _ : Fin 1 => g) (0 : Fin 1) using 1

theorem Level0_of (h : LevelPush) : Level0 := by
  intro q i A Y C D Y' φ c w φ' g hpo
  have hp := h φ c w φ' g hpo (SimplexCategory.mk 0)
  refine ⟨_, w ≫ (coAug (pushout.inr g φ')).app (SimplexCategory.mk 0),
    (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0), ?_, fun m hm => ?_⟩
  · refine hp.of_iso (Iso.refl _) (Iso.refl _) (lev0Iso g).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Iso.symm_hom, Category.assoc]
      change c ≫ WidePushout.head _ ≫ (lev0Iso g).inv = c ≫ g
      rw [← WidePushout.arrow_ι (fun _ : Fin 1 => g) 0]
      change c ≫ (g ≫ (lev0Iso g).hom) ≫ (lev0Iso g).inv = c ≫ g
      simp
    · simp
    · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc (lev0Iso g) _).symm
  · have key : sch.map (Spec.map ((lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) ≫
        sch.map (Spec.map (lev0Iso g).inv) =
        𝟙 _ ≫ sch.map (Spec.map ((Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0))) := by
      have hring : (lev0Iso g).inv ≫ (lev0Iso g).hom ≫ (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) =
          (Arrow.mapCechConerve (sqHom g φ')).app (SimplexCategory.mk 0) := Iso.inv_hom_id_assoc _ _
      rw [← sch.map_comp, ← Spec.map_comp, Category.id_comp]
      exact congrArg (fun f => sch.map (Spec.map f)) hring
    exact RelZS.of_iso (ZMod q) (tw q i) _ _ (Iso.refl _) (sch.mapIso (asIso (Spec.map (lev0Iso g).inv))) key m hm

theorem arrowι {C D : CommRingCat.{0}} (g : C ⟶ D) (n : SimplexCategory) (j : Fin (n.len + 1)) :
    g ≫ (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) = (coAug g).app n :=
  @WidePushout.arrow_ι _ _ _ C (fun _ => D) (fun _ => g) _ j

theorem basePush {C D Y' : CommRingCat.{0}} (g : C ⟶ D) (φ' : C ⟶ Y') (n : SimplexCategory) :
    IsPushout φ' ((coAug g).app n) ((coAug (pushout.inr g φ')).app n)
      ((Arrow.mapCechConerve (sqHom g φ')).app n) := by
  have hw : φ' ≫ (coAug (pushout.inr g φ')).app n =
      (coAug g).app n ≫ (Arrow.mapCechConerve (sqHom g φ')).app n := by
    simp [coAug, sqHom]
    symm; apply WidePushout.head_desc
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc s.inl
      (fun j => pushout.desc ((WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫ s.inr) s.inl (by
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s.inr) (arrowι g n j)).trans s.condition.symm)))
      (fun j => pushout.inr_desc _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.head_desc
  · intro s
    apply WidePushout.hom_ext
    · intro j
      have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
          (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
          (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
            _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
        apply WidePushout.ι_desc
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) key).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.ι_desc]
      exact pushout.inl_desc _ _ _
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) hw.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      erw [WidePushout.head_desc]
      exact s.condition
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      apply pushout.hom_ext
      · erw [WidePushout.ι_desc, pushout.inl_desc]
        rw [← h2]
        have key : (WidePushout.ι (fun _ : Fin (n.len + 1) => g) j : D ⟶ (Arrow.mk g).cechConerve.obj n) ≫
            (Arrow.mapCechConerve (sqHom g φ')).app n = pushout.inl g φ' ≫
            (WidePushout.ι (fun _ : Fin (n.len + 1) => pushout.inr g φ') j :
              _ ⟶ (Arrow.mk (pushout.inr g φ')).cechConerve.obj n) := by
          apply WidePushout.ι_desc
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m) key.symm).trans (Category.assoc _ _ _))
      · erw [WidePushout.ι_desc, pushout.inr_desc]
        rw [← h1]
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) (arrowι (pushout.inr g φ') n j))
    · erw [WidePushout.head_desc]
      rw [← h1]
      rfl

theorem LevelPush_of : LevelPush := by
  intro A Y C D Y' φ c w φ' g hpo n
  exact hpo.paste_vert (basePush g φ' n)

theorem integral_surjective_ring_cech_augmentation_etale_eqv : IntegralSurjectiveRingCechAugmentationEtaleEqv := by
  intro hB4 q i C D g hgi hgs hq
  haveI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  haveI : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hq' : IsUnit (q : Γ(Spec C, ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso C).inv.hom
  exact hB4 q (Spec.map g) hq' i

theorem BaseChange_of : BaseChange := by
  intro C D Y' g φ' hgi hgs
  have hp := (isPullback_SpecMap_pushout g φ')
  have hI : IsIntegralHom (Spec.map g) := IsIntegralHom.SpecMap_iff.mpr hgi
  have hS : Surjective (Spec.map g) := ⟨fun x => by
    obtain ⟨Q, hQ, hQc⟩ := hgs x.asIdeal x.isPrime
    refine ⟨⟨Q, hQ⟩, ?_⟩
    rw [Spec.map_base]
    exact PrimeSpectrum.ext hQc⟩
  have hI' : IsIntegralHom (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hp hI
  have hS' : Surjective (Spec.map (pushout.inr g φ')) := MorphismProperty.of_isPullback (P := @Surjective) hp hS
  refine ⟨IsIntegralHom.SpecMap_iff.mp hI', fun r hr => ?_⟩
  obtain ⟨y, hy⟩ := hS'.surj ⟨r, hr⟩
  refine ⟨y.asIdeal, y.isPrime, ?_⟩
  have := congrArg PrimeSpectrum.asIdeal hy
  rw [Spec.map_base] at this
  exact this

section helpers
variable {C D : CommRingCat.{0}} (g : C ⟶ D) {J : Type} [HasWidePushout C (fun _ : J => D) (fun _ => g)]

theorem ιd (j : J) {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w = fs j :=
  WidePushout.ι_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w) j

theorem hd {X : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w = f :=
  WidePushout.head_desc (arrows := fun _ => g) (f := f) (fs := fs) (w := w)

theorem ar (j : J) : g ≫ WidePushout.ι (fun _ : J => g) j = WidePushout.head (fun _ : J => g) :=
  WidePushout.arrow_ι (arrows := fun _ : J => g) j

theorem ιd_assoc (j : J) {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.ι (fun _ : J => g) j ≫ WidePushout.desc f fs w ≫ h = fs j ≫ h := by
  rw [← Category.assoc, ιd]

theorem hd_assoc {X Y : CommRingCat.{0}} (f : C ⟶ X) (fs : J → (D ⟶ X)) (w : ∀ j, g ≫ fs j = f) (h : X ⟶ Y) :
    WidePushout.head (fun _ : J => g) ≫ WidePushout.desc f fs w ≫ h = f ≫ h := by
  rw [← Category.assoc, hd]

end helpers

abbrev up {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    widePushout C (fun _ : Fin (k + 1) => D) (fun _ => g) ⟶ widePushout C (fun _ : Fin (k + 2) => D) (fun _ => g) :=
  WidePushout.desc (WidePushout.head _) (fun i => WidePushout.ι (fun _ : Fin (k + 2) => g) i.castSucc)
    (fun i => ar g i.castSucc)

theorem wp {C D : CommRingCat.{0}} (g : C ⟶ D) (k : ℕ) :
    IsPushout (WidePushout.head (fun _ : Fin (k + 1) => g)) g (up g k)
      (WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _)) := by
  have hw : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k =
      g ≫ WidePushout.ι (fun _ : Fin (k + 2) => g) (Fin.last _) := by
    simp [up, hd, ar]
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => WidePushout.desc (g ≫ s.inr)
      (fun i => Fin.lastCases s.inr (fun i => WidePushout.ι (fun _ : Fin (k + 1) => g) i ≫ s.inl) i)
      (fun i => by
        induction i using Fin.lastCases with
        | last => simp
        | cast i =>
          simp only [Fin.lastCases_castSucc]
          rw [← Category.assoc, ar]
          exact s.condition)) ?_ ?_ ?_)
  · intro s
    apply WidePushout.hom_ext
    · intro j
      simp [up, ιd, ιd_assoc, hd, hd_assoc]
    · simp [up, ιd, ιd_assoc, hd, hd_assoc]
      exact s.condition.symm
  · intro s
    simp [ιd]
  · intro s m h1 h2
    apply WidePushout.hom_ext
    · intro j
      induction j using Fin.lastCases with
      | last => simpa [ιd] using h2
      | cast i =>
        simp only [WidePushout.ι_desc, Fin.lastCases_castSucc]
        rw [← h1]
        simp [up, ιd, ιd_assoc]
    · simp only [WidePushout.head_desc]
      rw [← h2, ← Category.assoc]
      exact congrArg (· ≫ m) (WidePushout.arrow_ι (fun _ : Fin (k + 2) => g) (Fin.last _)).symm

theorem cechConerve_levelwise : LevelP := by
  intro A P hP C D c g hCc hDc
  have Q : ∀ k : ℕ, P _ (c ≫ WidePushout.head (fun _ : Fin (k + 1) => g)) := by
    intro k
    induction k with
    | zero =>
      have hsq : IsPushout g (𝟙 C) (WidePushout.ι (fun _ : Fin 1 => g) 0) (WidePushout.head (fun _ : Fin 1 => g)) := by
        have : IsIso (WidePushout.ι (fun _ : Fin 1 => g) 0) := (lev0Iso g).isIso_hom
        exact IsPushout.of_vert_isIso ⟨(WidePushout.arrow_ι (fun _ : Fin 1 => g) 0).trans (Category.id_comp _).symm⟩
      have := hP c g (𝟙 C) _ _ hsq hCc hDc (by simpa using hCc)
      rw [WidePushout.arrow_ι (fun _ : Fin 1 => g) 0] at this
      exact this
    | succ k ih =>
      have := hP c _ g _ _ (wp g k) hCc ih hDc
      have e : WidePushout.head (fun _ : Fin (k + 1) => g) ≫ up g k = WidePushout.head (fun _ : Fin (k + 2) => g) :=
        hd g _ _ _
      rw [e] at this
      exact this
  intro n
  exact Q n.len

theorem CechSq_full : CechSq :=
  CechSq_of integral_surjective_ring_cech_augmentation_etale_eqv BaseChange_of LevelPush_of cechConerve_levelwise (Level0_of LevelPush_of)

end LateralTheory.E.CechSqPf

theorem LateralTheory.E.CechSqPf2.CechSq_of : LateralTheory.E.DescIntPf.CechSq := LateralTheory.E.CechSqPf.CechSq_full
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_prim_locPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

def AlgRoot : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ : Prim q A) (x : A), x ^ q = 1 →
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ a n : ℕ, f ^ n * (x - ζ.1 ^ a) = 0

def EtRoot : Prop := ∀ (U : Scheme.{0}) (p : Polynomial Γ(U, ⊤)), p.Monic → (Nontrivial Γ(U, ⊤) → 0 < p.natDegree) → p.Separable →
  Loc U fun V g => ∃ t : Γ(V, ⊤), (p.map g.appTop.hom).IsRoot t

section Alg
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (Polynomial.aeval ζ.1) hr
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h2
  exact sub_eq_zero.1 h2

theorem prim_isPrim {B : Type} [CommRing B] [IsDomain B] (φ : A →+* B) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hq : IsUnit (q : B) := by simpa using ζ.2.1.map φ
  haveI : NeZero (q : B) := ⟨hq.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := (Prim.map φ ζ).2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact h

theorem unit_sub (ζ : Prim q A) {j : ℕ} (hj0 : 0 < j) (hjq : j < q) : IsUnit (ζ.1 ^ j - 1) := by
  by_contra h
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
  have hp := prim_isPrim (Ideal.Quotient.mk m) ζ
  have h0 : Ideal.Quotient.mk m (ζ.1 ^ j - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  exact hp.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.1 hj0) hjq h0

end Alg

section Idem
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (x : A)

def yy (a : ℕ) : A := x * ζ.1 ^ (a * (q - 1))
def ee (a : ℕ) : A := (ζ.2.1.unit⁻¹ : Aˣ) * ∑ j ∈ Finset.range q, (yy ζ x a) ^ j

theorem zeta_mul_yy (a : ℕ) : ζ.1 ^ a * yy ζ x a = x := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  unfold yy
  rw [show q - 1 = k by omega]
  calc ζ.1 ^ a * (x * ζ.1 ^ (a * k)) = x * ζ.1 ^ (a + a * k) := by rw [pow_add]; ring
    _ = x * (ζ.1 ^ (k + 1)) ^ a := by rw [← pow_mul]; ring_nf
    _ = x := by rw [hz, one_pow, mul_one]

theorem ee_kill (hx : x ^ q = 1) (a : ℕ) : ee ζ x a * (x - ζ.1 ^ a) = 0 := by
  have h1 : x - ζ.1 ^ a = ζ.1 ^ a * (yy ζ x a - 1) := by
    rw [mul_sub, zeta_mul_yy, mul_one]
  have hy : (yy ζ x a) ^ q = 1 := by
    unfold yy
    rw [mul_pow, hx, ← pow_mul, mul_comm (a * (q - 1)) q, pow_mul, prim_pow_q, one_pow, one_mul]
  unfold ee
  rw [h1]
  calc _ = ((ζ.2.1.unit⁻¹ : Aˣ) : A) * ζ.1 ^ a * ((∑ j ∈ Finset.range q, (yy ζ x a) ^ j) * (yy ζ x a - 1)) := by ring
    _ = 0 := by rw [geom_sum_mul, hy, sub_self, mul_zero]

theorem inner_sum {j : ℕ} (hj0 : 0 < j) (hjq : j < q) :
    ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  have hik : i < k := by omega
  have e1 : (q - 1) * (i + 1) = (k + 1) * i + (k - i) := by
    rw [show q - 1 = k by omega]; zify [hik.le]; ring
  have hw : ζ.1 ^ ((q - 1) * (i + 1)) = ζ.1 ^ (k - i) := by
    rw [e1, pow_add, pow_mul, hz, one_pow, one_mul]
  have hu : IsUnit (ζ.1 ^ (k - i) - 1) := unit_sub ζ (by omega) (by omega)
  have hwq : (ζ.1 ^ (k - i)) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, prim_pow_q, one_pow]
  rw [hw]
  have h2 := geom_sum_mul (ζ.1 ^ (k - i)) q
  rw [hwq, sub_self] at h2
  exact (hu.mul_left_eq_zero).1 h2

theorem ee_sum : ∑ a ∈ Finset.range q, ee ζ x a = 1 := by
  unfold ee yy
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range q, ∑ a ∈ Finset.range q, (x * ζ.1 ^ (a * (q - 1))) ^ j =
      x ^ j * ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [inner_sum ζ (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne q))) h

end Idem

theorem ee_nil {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : ℕ) (ha : ¬ a.Coprime q) :
    IsNilpotent (ee ζ ξ.1 a) := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  intro p hp
  haveI : Ideal.IsPrime p := hp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  by_contra hne
  have hk := congrArg (Ideal.Quotient.mk p) (ee_kill ζ ξ.1 (prim_pow_q ξ) a)
  rw [map_mul, map_zero, map_sub, map_pow] at hk
  have he : Ideal.Quotient.mk p ξ.1 = (Ideal.Quotient.mk p ζ.1) ^ a :=
    sub_eq_zero.1 ((mul_eq_zero.1 hk).resolve_left hne)
  have hξ := prim_isPrim (Ideal.Quotient.mk p) ξ
  have hζ := prim_isPrim (Ideal.Quotient.mk p) ζ
  rw [he] at hξ
  exact ha ((hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 hξ)

theorem algPow : AlgPow := by
  intro q _ A _ ζ ξ
  refine ⟨Set.range fun a : Fin q => ee ζ ξ.1 a, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← ee_sum ζ ξ.1, Finset.sum_range]
    exact Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨a, rfl⟩
  · rintro f ⟨a, rfl⟩
    by_cases hc : (a : ℕ).Coprime q
    · refine ⟨ZMod.unitOfCoprime a hc, 1, ?_⟩
      have hv : ((ZMod.unitOfCoprime (a : ℕ) hc : (ZMod q)ˣ) : ZMod q).val = a := by
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt a.2]
      rw [hv, pow_one]
      exact ee_kill ζ ξ.1 (prim_pow_q ξ) a
    · obtain ⟨n, hn⟩ := ee_nil ζ ξ a hc
      exact ⟨1, n, by rw [hn, zero_mul]⟩

theorem loc_of_span {U : Scheme.{0}} (s : Set Γ(U, ⊤)) (hs : Ideal.span s = ⊤) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ f ∈ s, ∀ (V : Scheme.{0}) (g : V ⟶ U), IsUnit (g.appTop.hom f) → P V g) : Loc U P := by
  let O : s → U.Opens := fun f => U.basicOpen f.1
  have hO : TopologicalSpace.IsOpenCover O := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, U.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := U.openCoverOfIsOpenCover O hO
  let S : Sieve U := {
    arrows := fun V g => ∃ f ∈ s, IsUnit (g.appTop.hom f)
    downward_closed := by
      rintro V W g ⟨f, hf, hu⟩ k
      exact ⟨f, hf, (show IsUnit (k.appTop.hom (g.appTop.hom f)) from hu.map _)⟩ }
  have hgen : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ≤ S := by
    rintro W g ⟨Y, k, _, ⟨i⟩, rfl⟩
    refine (S.downward_closed ?_ k)
    refine ⟨i.1, i.2, ?_⟩
    have hle : (O i).ι ''ᵁ ⊤ ≤ U.basicOpen i.1 := by simp [O]
    have := (U.toRingedSpace.isUnit_res_basicOpen i.1).map (U.presheaf.map (homOfLE hle).op).hom
    have e : U.presheaf.map (homOfLE (x := (O i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        U.presheaf.map (homOfLE (U.basicOpen_le i.1)).op ≫ U.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    show IsUnit ((O i).ι.appTop.hom i.1)
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  refine ⟨S, Scheme.etaleTopology.superset_covering hgen
    (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)), ?_⟩
  rintro V g ⟨f, hf, hu⟩
  exact h f hf V g hu

theorem eq_of_unit_kill {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {f x y : A} {n : ℕ}
    (hn : f ^ n * (x - y) = 0) (hu : IsUnit (φ f)) : φ x = φ y := by
  have h0 : φ (f ^ n * (x - y)) = 0 := by rw [hn, map_zero]
  rw [map_mul, map_pow, map_sub] at h0
  exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem c1 (hE : EtRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) :
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤)) := by
  have hsep : (Polynomial.cyclotomic q Γ(U, ⊤)).Separable := by
    have h1 := Polynomial.separable_X_pow_sub_C_unit (1 : (Γ(U, ⊤))ˣ) hq
    rw [Units.val_one, map_one] at h1
    exact h1.of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : Nontrivial Γ(U, ⊤) → 0 < (Polynomial.cyclotomic q Γ(U, ⊤)).natDegree := by
    intro _; rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  refine loc_mono' (hE U _ (Polynomial.cyclotomic.monic q _) hdeg hsep) fun V g ⟨t, ht⟩ => ?_
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  refine ⟨⟨t, hqV, ?_⟩⟩
  rw [Polynomial.map_cyclotomic] at ht
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ht

theorem c4 (hE : EtRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  have hq0 : q ≠ 0 := NeZero.ne q
  refine loc_mono' (hE U _ (Polynomial.monic_X_pow_sub_C _ hq0) (fun _ => by rw [Polynomial.natDegree_X_pow_sub_C]; omega)
    (Polynomial.separable_X_pow_sub_C_unit u hq)) fun V g ⟨t, ht⟩ => ?_
  have ht' : t ^ q = g.appTop.hom u := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using ht
  have htu : IsUnit t := (isUnit_pow_iff hq0).1 (by rw [ht']; exact (u.isUnit.map _))
  refine ⟨htu.unit, Units.ext ?_⟩
  simp [ht']

theorem c2 (hA : AlgPow) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨s, hs, hf⟩ := hA q Γ(U, ⊤) ζ ξ
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

theorem c3 (hR : AlgRoot) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)) (hx : x ^ q = 1) :
    Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  obtain ⟨s, hs, hf⟩ := hR q Γ(U, ⊤) ζ x hx
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

end LateralTheory.E.L_prim_locPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCokIsoPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.LeafCokIsoPf

theorem isIso_cokernel_map_of_isPushout {C : Type*} [Category C] [HasZeroMorphisms C]
    {K' L' K L : C} (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L)
    [HasCokernel a] [HasCokernel b] (w : a ≫ v = u ≫ b) (h : IsPushout a u v b) :
    IsIso (cokernel.map a b u v w) := by
  let φ : L ⟶ cokernel a := h.desc (cokernel.π a) 0 (by simp)
  have hφ : b ≫ φ = 0 := h.inr_desc _ _ _
  refine ⟨⟨cokernel.desc b φ hφ, ?_, ?_⟩⟩
  · ext
    simp [φ]
  · ext
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply h.hom_ext
    · simp [φ]
    · simp [reassoc_of% hφ]

theorem isIso_cokernel_map_complex {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K' L' K L : HomologicalComplex C c}
    (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L) (w : a ≫ v = u ≫ b)
    (hpo : ∀ n, IsPushout (a.f n) (u.f n) (v.f n) (b.f n)) :
    IsIso (cokernel.map a b u v w) := by
  suffices hc : ∀ n, IsIso ((cokernel.map a b u v w).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  let G : HomologicalComplex C c ⥤ C := HomologicalComplex.eval C c n
  have w' : G.map a ≫ G.map v = G.map u ≫ G.map b := by
    rw [← G.map_comp, w, G.map_comp]
  have h1 : IsIso (cokernel.map (G.map a) (G.map b) (G.map u) (G.map v) w') :=
    isIso_cokernel_map_of_isPushout (G.map a) (G.map u) (G.map v) (G.map b) w' (hpo n)
  have e : cokernelComparison a G ≫ G.map (cokernel.map a b u v w) =
      cokernel.map (G.map a) (G.map b) (G.map u) (G.map v) w' ≫ cokernelComparison b G := by
    rw [← cancel_epi (cokernel.π (G.map a))]
    rw [π_comp_cokernelComparison_assoc, ← G.map_comp, cokernel.π_desc, G.map_comp,
      cokernel.π_desc_assoc, Category.assoc, π_comp_cokernelComparison]
  have : IsIso (cokernelComparison a G ≫ G.map (cokernel.map a b u v w)) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_left (cokernelComparison a G) (G.map (cokernel.map a b u v w))

open GlobalTheory.EtC in
theorem LeafCokIso_of : LateralTheory.E.LeafExcPf.LeafCokIso := by
  intro R _ K' L' K L a u v b w hpo
  exact isIso_cokernel_map_complex a u v b w hpo

end LateralTheory.E.LeafCokIsoPf
end
end

