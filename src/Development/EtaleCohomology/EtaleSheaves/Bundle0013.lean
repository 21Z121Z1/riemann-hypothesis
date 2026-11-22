import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.Bundle0004

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRoofPf
section
noncomputable section
open LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafRoofPf

theorem qiso_of {B W D : Type} [CommRing B] [CommRing W] [CommRing D] (α : B →+* W) (I : Ideal B) (h : W →+* D)
    (hI : ∀ x, h (α x) = 0 ↔ x ∈ I) (hs : ∀ w, ∃ x, h w = h (α x)) (hk : ∀ w, h w = 0 → w ∈ I.map α) :
    QIso α I := by
  have hle : I.map α ≤ RingHom.ker h := Ideal.map_le_iff_le_comap.mpr fun x hx => by
    simpa [RingHom.mem_ker] using (hI x).mpr hx
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.quotientMap_mk] at hxy
    rw [Ideal.Quotient.eq] at hxy ⊢
    apply (hI _).mp
    have := hle (by simpa [map_sub] using hxy)
    simpa [RingHom.mem_ker, map_sub] using this
  · intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hs w
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    simp only [Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq]
    exact hk _ (by simp [map_sub, hx])

def LeafRoofEt : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (P : Type) (_ : CommRing P) (a : B →+* P) (b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* P)
    (m : P →+* B ⧸ varIdeal φ) (g : P), a.Etale ∧ b.Etale ∧ (∀ j, a (φ (MvPolynomial.X j)) = b (MvPolynomial.X j)) ∧
    m.comp a = Ideal.Quotient.mk _ ∧ m.comp b = MvPolynomial.constantCoeff ∧ m g = 1 ∧
    ∀ x, m x = 0 → ∃ n : ℕ, g ^ n * x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j))

def LeafKerC : Prop := ∀ (d : ℕ) (D : Type) [CommRing D] (p : MvPolynomial (Fin d) D),
  MvPolynomial.constantCoeff p = 0 → p ∈ varIdeal (RingHom.id (MvPolynomial (Fin d) D))

theorem kerC_of : LeafKerC := by
  intro d D _ p hp
  have : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin d))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    by_contra hne
    push_neg at hne
    have h0 : mo = 0 := by ext i; simpa using hne i (Set.mem_univ i)
    subst h0
    exact (MvPolynomial.mem_support_iff.mp hmo) (by simpa [MvPolynomial.constantCoeff_eq] using hp)
  simpa [varIdeal, Set.image_univ] using this

theorem map_varIdeal {d : ℕ} {C B W : Type} [CommRing C] [CommRing B] [CommRing W]
    (φ : MvPolynomial (Fin d) C →+* B) (α : B →+* W) :
    (varIdeal φ).map α = Ideal.span (Set.range fun j => α (φ (MvPolynomial.X j))) := by
  unfold varIdeal; rw [Ideal.map_span, ← Set.range_comp]; rfl

theorem LeafRoof_of (h1 : LeafRoofEt) : LeafRoof := by
  intro d C B _ _ φ hφ
  obtain ⟨P, _, a, b, m, g, ha, hb, hab, hma, hmb, hg, hk⟩ := h1 d φ hφ
  have hu : IsUnit (m g) := by rw [hg]; exact isUnit_one
  let h : Localization.Away g →+* (B ⧸ varIdeal φ) := IsLocalization.Away.lift g hu
  have hh : ∀ x, h (algebraMap P (Localization.Away g) x) = m x := fun x =>
    IsLocalization.Away.lift_eq g hu x
  have hJ : ∀ w : Localization.Away g, h w = 0 →
      w ∈ (Ideal.span (Set.range fun j => b (MvPolynomial.X j))).map (algebraMap P (Localization.Away g)) := by
    intro w hw
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) w
    have hy : m y = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Submonoid.powers g) (S := Localization.Away g) _ y 0 s).mp hw
      simpa using this
    obtain ⟨n, hn⟩ := hk y hy
    have hm := Ideal.mem_map_of_mem (algebraMap P (Localization.Away g)) hn
    have hunit : IsUnit (algebraMap P (Localization.Away g) (g ^ n * s)) := by
      rw [map_mul]
      exact (IsLocalization.map_units _ (⟨g ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers g) n⟩ : Submonoid.powers g)).mul (IsLocalization.map_units _ s)
    rw [← Ideal.mul_unit_mem_iff_mem _ hunit]
    have e : IsLocalization.mk' (Localization.Away g) y s * algebraMap P _ (g ^ n * s) =
        algebraMap P _ (g ^ n * y) := by
      rw [map_mul, map_mul, mul_comm (algebraMap P _ (g ^ n)), ← mul_assoc, IsLocalization.mk'_spec, mul_comm]
    rw [e]; exact hm
  have hloc : (algebraMap P (Localization.Away g)).Etale := by
    rw [RingHom.etale_algebraMap]; exact Algebra.Etale.of_isLocalizationAway g
  refine ⟨B ⧸ varIdeal φ, Localization.Away g, inferInstance, inferInstance, Ideal.Quotient.mk _,
    (algebraMap P _).comp a, (algebraMap P _).comp b,
    RingHom.Etale.stableUnderComposition _ _ ha hloc, RingHom.Etale.stableUnderComposition _ _ hb hloc,
    fun j => by simp [hab], ?_, ?_⟩
  · apply qiso_of _ _ h
    · intro x
      rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hma, Ideal.Quotient.eq_zero_iff_mem]
    · intro w
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (h w)
      exact ⟨x, by rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hma, hx]⟩
    · intro w hw
      have := hJ w hw
      convert this using 1
      rw [map_varIdeal, Ideal.map_span, ← Set.range_comp]
      congr 1; ext j; simp [hab]
  · apply qiso_of _ _ h
    · intro p
      rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hmb]
      refine ⟨kerC_of d _ p, fun hp => ?_⟩
      have hle : varIdeal (RingHom.id (MvPolynomial (Fin d) (B ⧸ varIdeal φ))) ≤
          RingHom.ker (MvPolynomial.constantCoeff (R := B ⧸ varIdeal φ) (σ := Fin d)) := by
        exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; simp)
      exact hle hp
    · intro w
      exact ⟨MvPolynomial.C (h w), by rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hmb]; simp⟩
    · intro w hw
      have := hJ w hw
      convert this using 1
      rw [map_varIdeal, Ideal.map_span, ← Set.range_comp]
      rfl

end LateralTheory.E.LeafRoofPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.WhitneyPf

theorem alg {A : Type*} [CommRing A] (C D : ℕ → A) (x : A) (a b : ℕ) (hC : ∀ i, a < i → C i = 0)
    (hD : ∀ j, b < j → D j = 0) :
    ∑ k ∈ Finset.range (a + b + 1), (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      (∑ i ∈ Finset.range (a + 1), C i * x ^ (a - i)) * (∑ j ∈ Finset.range (b + 1), D j * x ^ (b - j)) := by
  set f : ℕ → ℕ → A := fun i j => C i * D j * x ^ (a + b - (i + j)) with hf
  have h1 : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
    intro k
    rw [Finset.sum_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ f k]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hf, hp]
  simp_rw [h1]
  rw [Finset.sum_range_diag_flip (a + b + 1) f, Finset.sum_mul_sum]
  have h2 : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i * x ^ (a - i) * (D j * x ^ (b - j)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hi hj
    simp only [hf]
    rw [show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]; ring
  rw [h2]
  symm
  calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset ?_ ?_
        · simp only [Finset.mem_range] at hi
          intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ hnj
          simp only [Finset.mem_range] at hnj
          simp only [hf]; rw [hD j (by omega)]; ring
    _ = ∑ i ∈ Finset.range (a + b + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_subset ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ hni
          simp only [Finset.mem_range] at hni
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [hf]; rw [hC i (by omega)]; ring

variable {q : ℕ}

def ccup {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j) (hk : i + j = k) : Ht q E (2 * k) k :=
  (cup q a b).cast (by subst hk; push_cast; ring) (by subst hk; push_cast; ring)

theorem ι_ccup (P : Collected q) {E : Spc} (h : Inv q E) {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j)
    (hk : i + j = k) : P.ι h k (ccup a b hk) = P.ι h i a * P.ι h j b := by
  subst hk; exact P.ι_mul h i j a b

theorem cast_zero {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem ccup_zero_left {E : Spc} {i j k : ℕ} (b : Ht q E (2 * j) j) (hk : i + j = k) :
    ccup (0 : Ht q E (2 * i) i) b hk = 0 := by
  unfold ccup; rw [map_zero, AddMonoidHom.zero_apply, cast_zero]

theorem ccup_zero_right {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (hk : i + j = k) :
    ccup a (0 : Ht q E (2 * j) j) hk = 0 := by
  unfold ccup; rw [map_zero, cast_zero]

section
variable [NeZero q]

theorem pull_ccup (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') {i j k : ℕ} (a : Ht q E' (2 * i) i)
    (b : Ht q E' (2 * j) j) (hk : i + j = k) : pull _ f _ _ (ccup a b hk) = ccup (pull _ f _ _ a) (pull _ f _ _ b) hk := by
  subst hk; unfold ccup; rw [pull_cast, (hA q).1]

theorem pull_cpow (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hA q).1, ih]

def yExpr {E E' : Spc} (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    Ht q E' (2 * a) a :=
  ∑ j : Fin (a + 1), ccup (pull _ g _ _ (c j)) (cpow q (c1 q L) (a - j)) (by have := j.isLt; omega)

theorem ι_yExpr (P : Collected q) {E E' : Spc} (hE : Inv q E) (hE' : Inv q E') (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    P.ι hE' a (yExpr g L c a) = ∑ j ∈ Finset.range (a + 1), P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j) := by
  unfold yExpr
  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun j => P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_ccup, P.map_ι, P.ι_cpow]

theorem pull_yExpr (hA : DivisorNaturality) {E E' E'' : Spc} (f : E'' ⟶ E') (hE' : Inv q E') (g : E' ⟶ E)
    (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    pull _ f _ _ (yExpr g L c a) = yExpr (f ≫ g) (f ≫ L) c a := by
  unfold yExpr
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_ccup hA, pull_cpow hA f hE', (hA q).2.2.1 f L hE', pull_comp]

theorem yExpr_eq_zero (P : Collected q) {E : Spc} (h : Inv q E) {a : ℕ} (V : E ⟶ ofCat (glCat a))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (hc : IsChern P h V c) : yExpr (PB.pr V) (PB.line V) c a = 0 := by
  have := ι_yExpr P h (inv_of (PB.pr V) h) (PB.pr V) (PB.line V) c a
  rw [hc.2.2] at this
  rw [← P.π_ι (inv_of (PB.pr V) h) a (yExpr (PB.pr V) (PB.line V) c a), this, map_zero]

end

def eExpr {E : Spc} (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) : Ht q E (2 * k) k :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).attach,
    ccup (c p.1.1) (d p.1.2) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)

theorem ι_eExpr (P : Collected q) {E : Spc} (h : Inv q E) (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) :
    P.ι h k (eExpr c d k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2) := by
  unfold eExpr
  rw [map_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
    (fun p => P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2))]
  exact Finset.sum_congr rfl fun p _ => ι_ccup P h _ _ _

end LateralTheory.E.D2.WhitneyPf

namespace LateralTheory.E.D2
open WhitneyPf

theorem LeafWhitney_of (hG : LeafGeom) (hC2 : LeafCover2) (hS : LeafA6supp) (hA : LeafA6nat) : LeafWhitney := by
  intro q _ P E h a b V W c d hc hd
  classical
  have he := ι_eExpr P h c d
  refine ⟨eExpr c d, ⟨?_, ?_, ?_⟩, he⟩
  · rw [he]; simp [hc.1, hd.1]
  · intro j hj
    unfold eExpr
    refine Finset.sum_eq_zero fun p _ => ?_
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    by_cases ha : a < p.1.1
    · rw [hc.2.1 _ ha, ccup_zero_left]
    · rw [hd.2.1 _ (by omega), ccup_zero_right]
  · have hX := inv_of (PB.pr (bsumOf V W)) h
    obtain ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, lc, e1, e2, e3, e4⟩ := hG V W
    have hcov := hC2 (ZMod q) f₁ f₂ m₁ m₂ lc
    have hy : pull _ f₁ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a) = 0 := by
      rw [pull_yExpr hA f₁ hX, ← e1, ← e2, ← pull_yExpr hA p₁ (inv_of (PB.pr V) h), yExpr_eq_zero P h V c hc,
        map_zero]
    have hz : pull _ f₂ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) = 0 := by
      rw [pull_yExpr hA f₂ hX, ← e3, ← e4, ← pull_yExpr hA p₂ (inv_of (PB.pr W) h), yExpr_eq_zero P h W d hd,
        map_zero]
    have h0 := hS q f₁ f₂ hcov _ _ hy hz
    have key : P.ι hX (a + b) (ccup (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a)
        (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) rfl) = 0 := by
      unfold ccup; rw [h0, cast_zero, map_zero]
    rw [ι_ccup, ι_yExpr P h hX, ι_yExpr P h hX,
      ← alg (fun i => P.map (PB.pr (bsumOf V W)) hX h (P.ι h i (c i)))
        (fun j => P.map (PB.pr (bsumOf V W)) hX h (P.ι h j (d j))) _ a b
        (fun i hi => by simp only [hc.2.1 i hi, map_zero])
        (fun j hj => by simp only [hd.2.1 j hj, map_zero])] at key
    refine Eq.trans ?_ key
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, map_sum]
    simp only [map_mul]

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineHighPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LineHighPf

open LateralTheory.E.t_E2Cut

def QAIC (q : ℕ) (W : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (I : Ideal B), AIC B ∧ IsUnit (q : B) ∧
    Nonempty (W ≅ Spec (CommRingCat.of (B ⧸ I)))

def Cover2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem acyc_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : Acyc q (sch.obj W')) : Acyc q (sch.obj W) := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have hs : ∀ z : Ht q (sch.obj W) n i,
      pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← hs x, ← hs y, Subsingleton.elim (pull _ (sch.map e.inv) (tw q i) n x) (pull _ (sch.map e.inv) (tw q i) n y)]

theorem acyc_of_QAIC (H : Hyp) (hQ : QuotAcyc) {q : ℕ} {W : Scheme.{0}} (h : QAIC q W) : Acyc q (sch.obj W) := by
  obtain ⟨B, _, _, I, hB, hq, ⟨e⟩⟩ := h
  exact acyc_of_iso e (hQ H q B I hB hq)

theorem high_of_cover (H : Hyp) (hM : MV) {q : ℕ} {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (hc : Set.range f ∪ Set.range g = Set.univ) (hU : Acyc q (sch.obj U)) (hV : Acyc q (sch.obj V))
    (hW : Acyc q (sch.obj (pullback f g))) (i n : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨δ, hδ, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have key : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 := by
    intro x
    have h3 := ((hδ f g hc m).2.2 x).1
    have := hU (m + 1) i (by omega)
    have := hV (m + 1) i (by omega)
    have := hW m i (by omega)
    obtain ⟨w, hw⟩ := h3 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem LineHigh_of (hQ : QuotAcyc) (hM : MV) (hC : Cover2) : LineHigh := by
  intro H q i A _ _ hq Z p hp hZ n hn
  obtain ⟨U, V, f, g, hf, hg, hc, hU, hV, hW⟩ := hC q A hq p hp hZ
  exact high_of_cover H hM f g hc (acyc_of_QAIC H hQ hU) (acyc_of_QAIC H hQ hV) (acyc_of_QAIC H hQ hW) i n hn

theorem fibre_affine (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] :
    Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (cpt A) ≅
      Spec (CommRingCat.of (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  refine ⟨pullbackSpecIso A B (IsLocalRing.ResidueField A) ≪≫ ?_⟩
  exact Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv).op

def Good {A : Type} [CommRing A] {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) : Prop :=
  IsEmpty W ∨ ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B), AIC B ∧
    ∃ e : W ≅ Spec (CommRingCat.of B), e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = w

def ZCov : Prop := ∀ (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ Z) (g : V ⟶ Z), IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    Good (f ≫ p) ∧ Good (g ≫ p) ∧ Good (pullback.fst f g ≫ f ≫ p)

def FibCov : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ {U V : Scheme.{0}} (f : U ⟶ Z) (g : V ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g],
  Set.range f ∪ Set.range g = Set.univ → Good (f ≫ p) → Good (g ≫ p) → Good (pullback.fst f g ≫ f ≫ p) →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem Cover2_of (hZ : ZCov) (hF : FibCov) : Cover2 := by
  intro q A _ _ hq Z p hp hZA
  obtain ⟨U, V, f, g, hf, hg, hc, h1, h2, h3⟩ := hZ A p hp hZA
  exact hF q A hq p hZA f g hc h1 h2 h3

end LateralTheory.E.LineHighPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineZeroCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineZeroCut

def LZNonempty : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)),
  UniversallyClosed p → Nonempty X → Nonempty ↑(pullback p (cpt A))

def LZDescend : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)),
  IsIntegralHom u → IsProper l → ¬ PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) →
  ∃ (Y : Scheme.{0}) (v : Z ⟶ Y) (r : Y ⟶ Spec (CommRingCat.of A)),
    IsProper r ∧ Surjective v ∧ v ≫ r = u ≫ l ∧ ¬ PreconnectedSpace ↑(pullback r (cpt A))

def LZProper : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r → ConnectedSpace X → PreconnectedSpace ↑(pullback r (cpt A))

theorem lzNonempty : LZNonempty := by
  intro A _ _ X p hp hX
  obtain ⟨x⟩ := hX
  have hc : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have h1 : IsLocalRing.closedPoint A ∈ Set.range p.base := by
    have : IsLocalRing.closedPoint A ∈ closure {p.base x} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).1 (IsLocalRing.le_maximalIdeal (p.base x).isPrime.ne_top)
    exact closure_minimal (by simp) hc this
  obtain ⟨z, hz⟩ := h1
  have h2 : (cpt A) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
    Spec_closedPoint
  obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := cpt A) z
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) (by rw [hz, h2])
  exact ⟨w⟩

theorem goal_of (h2 : LZDescend) (h3 : LZProper) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have := hl.1
  have := hZ.1
  have hne : Nonempty ↑(pullback (u ≫ l) (cpt A)) := lzNonempty A (u ≫ l) inferInstance inferInstance
  have hpre : PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) := by
    by_contra hn
    obtain ⟨Y, v, r, hr, hv, -, hY⟩ := h2 A u l hu hl.1 hn
    have hZc : ConnectedSpace Z := inferInstance
    have hYc : ConnectedSpace Y := hv.surj.connectedSpace v.continuous
    exact hY (h3 A r hr hYc)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.LineZeroCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocallyConstantH0
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LocallyConstantH0

def gam {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
  ζ.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

def IsLCMap (q : ℕ) [NeZero q] (i : ℤ)
    (m : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) →+ Sec (tw q i) (Spec (CommRingCat.of B)))) :
    Prop :=
  (∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      Sec.res (Spec.map (CommRingCat.ofHom f)) (m B ζ φ) = m C (ζ.map f) (lcMap f φ)) ∧
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (c : ZMod q), m B ζ (LocallyConstant.const _ c) = c.val • twGen i (gam ζ)

def LCMap : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ m, IsLCMap q i m

def LCBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Bijective (m B ζ)

theorem localConstant_H0 (hM : LCMap) (hB : LCBij) : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := by
  intro hA9 q _ i
  obtain ⟨m, hm⟩ := hM q i
  obtain ⟨-, e0, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨fun B _ ζ => (AddEquiv.ofBijective (m B ζ) (hB q i m hm B ζ)).trans (e0 (Spec (CommRingCat.of B))), ?_⟩
  intro B C _ _ f ζ φ
  simp only [AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  rw [hnat, hm.1]

end LateralTheory.E.LocallyConstantH0
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
end
end

