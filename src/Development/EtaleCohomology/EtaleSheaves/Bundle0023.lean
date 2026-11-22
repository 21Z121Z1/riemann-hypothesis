import Development.EtaleCohomology.EtaleSheaves.Bundle0009
import Development.EtaleCohomology.EtaleSheaves.Bundle0010
import Development.EtaleCohomology.EtaleSheaves.LeafExcRingPf
import Development.EtaleCohomology.EtaleSheaves.LeafSSCut
import Development.EtaleCohomology.EtaleSheaves.Bundle0011

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPf
section
noncomputable section

namespace LateralTheory.E.LeafCoordsPf

open LateralTheory.E.LeafChartRingPf
open scoped Pointwise

theorem linIndep_of_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B) (g : B) {ι : Type} [Fintype ι]
    (v : ι → Ω[Localization.Away g⁄A]) (hcard : Fintype.card ι = n)
    (hsp : Submodule.span (Localization.Away g) (Set.range v) = ⊤) :
    LinearIndependent (Localization.Away g) v := by
  cases subsingleton_or_nontrivial (Localization.Away g) with
  | inl h => exact linearIndependent_of_subsingleton
  | inr h =>
    have h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 B (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
    have h1 : Algebra.IsStandardSmoothOfRelativeDimension (0 + n) A (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans n 0 A B (Localization.Away g)
    rw [zero_add] at h1
    have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := A) (S := Localization.Away g) n
    have : Module.Free (Localization.Away g) Ω[Localization.Away g⁄A] := by
      have := h1.isStandardSmooth
      infer_instance
    have hf : Module.finrank (Localization.Away g) Ω[Localization.Away g⁄A] = n :=
      Module.finrank_eq_of_rank_eq hr
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hsp.ge (hcard.trans hf.symm)

theorem conormal_retraction {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) :
    ∃ l, l ∘ₗ (KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)) = LinearMap.id := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  exact (Algebra.FormallySmooth.iff_split_injection (R := A) (P := B) (A := B ⧸ I)
    Ideal.Quotient.mk_surjective).mp inferInstance

def dyt {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (y : Fin e → B) (t : Fin d → B) :
    Fin e ⊕ Fin d → Ω[B⁄A] :=
  Sum.elim (fun k => KaehlerDifferential.D A B (y k)) (fun j => KaehlerDifferential.D A B (t j))

theorem ideal_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) : I.FG := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I)
  simpa using h

theorem spread (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B)
    (P : Ideal B) (t : Fin d → B) (y : Fin e → B) (h : B) (hh : h ∉ P)
    (ht : ∀ j, t j ∈ I) (hI : h • I ≤ Ideal.span (Set.range t))
    (hΩ : h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t))) :
    ∃ g ∉ P,
    I.map (algebraMap B (Localization.Away g)) = Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) ∧
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤ := by
  have hu : IsUnit (algebraMap B (Localization.Away h) h) := IsLocalization.Away.algebraMap_isUnit h
  refine ⟨h, hh, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h * x ∈ Ideal.span (Set.range t) := hI (Submodule.smul_mem_pointwise_smul x h I hx)
      have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away h)) h1
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (ht j)
  · set T := Localization.Away h
    set S := Submodule.span T (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A T (algebraMap B T (y k)))
      (fun j => KaehlerDifferential.D A T (algebraMap B T (t j)))))
    let f := KaehlerDifferential.map A A B T
    have hspan : Submodule.span B (Set.range (dyt (A := A) y t)) ≤ (S.restrictScalars B).comap f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with k | j
      · exact Submodule.subset_span ⟨Sum.inl k, by simp [dyt, f, KaehlerDifferential.map_D]⟩
      · exact Submodule.subset_span ⟨Sum.inr j, by simp [dyt, f, KaehlerDifferential.map_D]⟩
    rw [eq_top_iff]
    intro ω _
    obtain ⟨⟨m, u⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers h) f ω
    have huu : IsUnit (algebraMap B T (u : B)) := IsLocalization.map_units T u
    have hm : f (h • m) ∈ S := hspan (hΩ (Submodule.smul_mem_pointwise_smul m h ⊤ trivial))
    have key : (algebraMap B T h * algebraMap B T (u : B)) • IsLocalizedModule.mk' f m u = f (h • m) := by
      rw [mul_smul, algebraMap_smul, algebraMap_smul, LinearMap.map_smul]
      congr 1
      exact IsLocalizedModule.mk'_cancel' f m u
    rw [← key] at hm
    exact (Submodule.smul_mem_iff_of_isUnit S (hu.mul huu)).mp hm

def LeafNakH : Prop := ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B), P.IsPrime →
  ∀ (N N' : Submodule B M), N'.FG → ∀ h ∉ P, h • N' ≤ N ⊔ P • N' → ∃ u ∉ P, u • N' ≤ N

def LeafCoordsPoint : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ h ∉ P, ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ h • I ≤ Ideal.span (Set.range t) ⊔ P • I ∧
    h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤

theorem LeafCoords_of (hPt : LeafCoordsPoint) (hN : LeafNakH) : LeafCoords := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨h, hh, t, y, ht, hI, hΩ⟩ := hPt d e A B I hB hBI P hP hIP
  obtain ⟨u1, hu1, h1⟩ := hN B B P hP _ I (ideal_fg I _ _ hB hBI) h hh hI
  have := hB.isStandardSmooth
  obtain ⟨u2, hu2, h2⟩ := hN B Ω[B⁄A] P hP _ ⊤ Module.Finite.fg_top h hh hΩ
  have hu : u1 * u2 ∉ P := fun H => (hP.mem_or_mem H).elim hu1 hu2
  obtain ⟨g, hg, hIg, hsp⟩ := spread d e A B I P t y (u1 * u2) hu ht
    (by
      rintro _ ⟨x, hx, rfl⟩
      have : u1 * x ∈ Ideal.span (Set.range t) := h1 (Submodule.smul_mem_pointwise_smul x u1 I hx)
      have := Ideal.mul_mem_left _ u2 this
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this)
    (by
      rintro _ ⟨x, -, rfl⟩
      have : u2 • x ∈ Submodule.span B (Set.range (dyt (A := A) y t)) :=
        h2 (Submodule.smul_mem_pointwise_smul x u2 ⊤ trivial)
      show (u1 * u2) • x ∈ _
      rw [mul_smul]
      exact Submodule.smul_mem _ u1 this)
  exact ⟨g, hg, t, y, hIg, linIndep_of_span (e + d) hB g _ (by simp) hsp, hsp⟩

end LateralTheory.E.LeafCoordsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDiscPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC HomologicalComplex CochainComplex.HomComplex
namespace LateralTheory.E.LeafDiscPf
variable (R : Type) [CommRing R]

theorem pullK_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp, Cochain.ofHom_comp]

theorem pullK_id {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp]

abbrev Ch (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev S0 (P : PSh) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P)

def e0 (P : PSh) : (Ch R P).X 0 ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

theorem chainsMap_degreeZero {E E' : Spc} (h : E ⟶ E') : ((chains R).map h).f 0 =
    (chainsXIso R E 0).hom ≫ (free R).map (h.app (op (SimplexCategory.mk 0))) ≫ (chainsXIso R E' 0).inv := by
  exact HomologicalComplex.extendMap_f ((chainsN R).map h) ComplexShape.embeddingDownNat (i := 0) rfl

def ι (P : PSh) : S0 R P ⟶ Ch R P :=
  mkHomFromSingle (e0 R P).inv (by
    rintro k rfl
    apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
      change -(i:ℤ) ≠ 1; omega))

theorem d_zero (P : PSh) : (Ch R P).d (-1) 0 = 0 := by
  have h1 : (ComplexShape.embeddingDownNat).f 1 = (-1 : ℤ) := rfl
  have h0 : (ComplexShape.embeddingDownNat).f 0 = (0 : ℤ) := rfl
  change (((chainsN R).obj (disc.obj P)).extend _).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq _ _ h1 h0]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj _).d (0+1) 0 = 0
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.isValue, pow_zero, pow_one, one_smul, neg_smul, one_zsmul, neg_one_zsmul]
    exact add_neg_cancel _
  rw [this]; simp

def π (P : PSh) : Ch R P ⟶ S0 R P :=
  mkHomToSingle (e0 R P).hom (by
    intro i hi
    obtain rfl : i = -1 := by simp at hi; omega
    rw [d_zero]; simp)

theorem retr (P : PSh) : ι R P ≫ π R P = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  simp [ι, π, mkHomFromSingle_f, mkHomToSingle_f]

theorem natι {P Q : PSh} (g : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g) ≫ ι R Q =
      ι R P ≫ (chains R).map (disc.map g) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [ι, e0, mkHomFromSingle_f, chainsMap_degreeZero, single_map_f_self]

theorem natπ {P Q : PSh} (g : P ⟶ Q) :
    (chains R).map (disc.map g) ≫ π R Q =
      π R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map g) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [π, e0, mkHomToSingle_f, chainsMap_degreeZero, single_map_f_self]

end LateralTheory.E.LeafDiscPf
open LateralTheory.E.LeafDiscPf in
theorem LateralTheory.E.LeafDiscPf.LeafDisc_of : LateralTheory.E.LeafLevelPf.LeafDisc := by
  intro R _ F P Q g n hs
  let a := mappingCone.map _ _ (ι R P) (ι R Q) (natι R g)
  let b := mappingCone.map _ _ (π R P) (π R Q) (natπ R g)
  have hab : a ≫ b = 𝟙 _ := by
    simp only [a, b, ← mappingCone.map_comp, retr, mappingCone.map_id]
  refine ⟨fun x y => ?_⟩
  have hx := pullK_comp R a b F n x
  have hy := pullK_comp R a b F n y
  rw [hab, pullK_id] at hx hy
  rw [hx, hy, Subsingleton.elim (HK.pull R b F n x) (HK.pull R b F n y)]
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExcRingOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
namespace LateralTheory.E.LeafExcRingPf2
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem schPb {X Y : Scheme.{0}} (g : Y ⟶ X) (U : X.Opens) :
    IsPullback (sch.map (g ∣_ U)) (sch.map (g ⁻¹ᵁ U).ι) (sch.map U.ι) (sch.map g) := by
  haveI : PreservesLimit (cospan U.ι g) (yoneda ⋙ SimplicialObject.const PSh) := inferInstance
  exact (isPullback_morphismRestrict g U).map (yoneda ⋙ SimplicialObject.const PSh)

theorem conn_iso (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {P Q E : Spc} (e : P ≅ Q) (p : P ⟶ E) (q : Q ⟶ E)
    (h : e.hom ≫ q = p) : Conn R F c p ↔ Conn R F c q := by
  have hb : ∀ n, Function.Bijective (pull R e.hom F n) := fun n => by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hp : ∀ n x, pull R p F n x = pull R e.hom F n (pull R q F n x) := fun n x => by rw [← h, pull_comp]
  unfold Conn ConnK
  refine forall_congr' fun n => and_congr (imp_congr_right fun _ => ?_) (imp_congr_right fun _ => ?_)
  · change Function.Bijective (pull R p F n) ↔ Function.Bijective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Bijective.of_comp_iff' (hb n) _).1 hh, fun hh => (hb n).comp hh⟩
  · change Function.Injective (pull R p F n) ↔ Function.Injective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Injective.of_comp_iff (hb n).1 _).1 hh, fun hh => (hb n).1.comp hh⟩

theorem leafPb : LeafPb := by
  intro R _ F c X Y g U
  exact (conn_iso R F c (schPb g U).isoPullback _ _ (schPb g U).isoPullback_hom_snd).symm

theorem LeafExcRing_of' (hE : LeafExc) (hC1 : LeafCov1) (hC2 : LeafCov2) : LeafExcRing :=
  LeafExcRing_of hE hC1 hC2 leafPb
end LateralTheory.E.LeafExcRingPf2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafFiltPf

abbrev Sg {R : Type} [CommRing R] (X : Shv R) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj X

variable {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ)

theorem coe_sub' {K L : Cx R} {m : ℤ} (a b : Cocycle K L m) :
    ((a - b : Cocycle K L m) : Cochain K L m) = (a : Cochain K L m) - (b : Cochain K L m) := rfl

theorem coe_zero' {K L : Cx R} {m : ℤ} : ((0 : Cocycle K L m) : Cochain K L m) = 0 := rfl

theorem res_zero (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

def V (s : ℤ) (z : Cocycle K (res R F) n) : Prop := ∀ p q (h : p + n = q), s < p → z.1.v p q h = 0

def S (s : ℤ) : Set (HK R K F n) := {x | ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z}

theorem memS {s : ℤ} {x : HK R K F n} (h : x ∈ S K F n s) :
    ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z := h

theorem cocyc (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    z.1.v s d hd ≫ (res R F).d d (d + 1) = 0 := by
  have h0 := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) s (d + 1) (by omega)
  rw [δ_v n (n + 1) rfl _ s (d + 1) _ d (s + 1) (by omega) rfl, hz (s + 1) (d + 1) (by omega) (by omega)] at h0
  simpa using h0

def clsC (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    Cocycle (Sg (K.X s)) (res R F) d :=
  Cocycle.fromSingleMk (z.1.v s d hd) (zero_add d) (d + 1) rfl (cocyc K F n s d hd z hz)

theorem clsC_v (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    (clsC K F n s d hd z hz).1.v 0 d (zero_add d) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd :=
  Cochain.fromSingleMk_v _ _

theorem CB (X : Shv R) (d : ℤ) (c : Cocycle (Sg X) (res R F) d) (hc : CohomologyClass.mk c = 0) (e : ℤ)
    (he : e + 1 = d) : ∃ β : Cochain (Sg X) (res R F) e,
      β.v 0 e (zero_add e) ≫ (res R F).d e d = c.1.v 0 d (zero_add d) := by
  obtain ⟨m, hm, β, hβ⟩ := (CohomologyClass.mk_eq_zero_iff c).1 hc
  obtain rfl : e = m := by omega
  refine ⟨β, ?_⟩
  have := Cochain.congr_v hβ 0 d (zero_add d)
  rw [δ_v e d hm β 0 d _ e 1 (by omega) rfl] at this
  have hz1 : IsZero ((Sg X).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
  rw [hz1.eq_of_tgt ((Sg X).d 0 1) 0] at this
  simpa using this

theorem KL (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) (e : ℤ) (he : e + 1 = d)
    (β : Cochain (Sg (K.X s)) (res R F) e)
    (hβ : β.v 0 e (zero_add e) ≫ (res R F).d e d =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd) :
    ∃ w : Cocycle K (res R F) n, CohomologyClass.mk w = CohomologyClass.mk z ∧ V K F n (s - 1) w := by
  let g : K.X s ⟶ (res R F).X e :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).inv ≫ β.v 0 e (zero_add e)
  let hh : Cochain K (res R F) (n - 1) := Cochain.single g (n - 1)
  let D : Cocycle K (res R F) n := Cocycle.mk (δ (n - 1) n hh) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - D, ?_, ?_⟩
  · have hD : CohomologyClass.mk D = 0 := (CohomologyClass.mk_eq_zero_iff D).2 ⟨n - 1, by omega, hh, rfl⟩
    rw [CohomologyClass.mk_sub, hD, sub_zero]
  · intro p q hpq hp
    have hDv : D.1.v p q hpq = (δ (n - 1) n hh).v p q hpq := rfl
    simp only [coe_sub', Cochain.sub_v, hDv]
    rw [δ_v (n - 1) n (by omega) hh p q hpq (q - 1) (p + 1) rfl rfl]
    rcases lt_or_eq_of_le (show s ≤ p by omega) with h | h
    · rw [hz p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = d := by omega
      obtain rfl : e = q - 1 := by omega
      rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp only [g, Category.assoc, hβ, Iso.inv_hom_id_assoc, comp_zero, smul_zero, add_zero, sub_self]

theorem step (s d : ℤ) (hd : s + n = d) [Finite (HK R (Sg (K.X s)) F d)] (hS : (S K F n (s - 1)).Finite) :
    (S K F n s).Finite := by
  classical
  let φ : HK R K F n → HK R (Sg (K.X s)) F d := fun x =>
    if h : x ∈ S K F n s then CohomologyClass.mk (clsC K F n s d hd (memS K F n h).choose (memS K F n h).choose_spec.2) else 0
  have key : ∀ x ∈ S K F n s, ∀ x' ∈ S K F n s, φ x = φ x' → x - x' ∈ S K F n (s - 1) := by
    intro x hx x' hx' he
    simp only [φ, dif_pos hx, dif_pos hx'] at he
    have hz := (memS K F n hx).choose_spec
    have hz' := (memS K F n hx').choose_spec
    have h0 : CohomologyClass.mk (clsC K F n s d hd (memS K F n hx).choose hz.2 -
        clsC K F n s d hd (memS K F n hx').choose hz'.2) = 0 := by
      rw [CohomologyClass.mk_sub, he, sub_self]
    obtain ⟨β, hβ⟩ := CB F (K.X s) d _ h0 (d - 1) (by omega)
    have hV : V K F n s ((memS K F n hx).choose - (memS K F n hx').choose) := by
      intro p q h hp
      simp [Cochain.sub_v, hz.2 p q h hp, hz'.2 p q h hp]
    obtain ⟨w, hw, hwV⟩ := KL K F n s d hd _ hV (d - 1) (by omega) β (by
      rw [hβ]
      simp only [coe_sub', Cochain.sub_v, clsC_v, Preadditive.comp_sub])
    exact ⟨w, by rw [hw, CohomologyClass.mk_sub, hz.1, hz'.1], hwV⟩
  let g : HK R (Sg (K.X s)) F d → HK R K F n := fun t =>
    if h : ∃ x ∈ S K F n s, φ x = t then h.choose else 0
  refine ((Set.finite_univ.prod hS).image (fun p => g p.1 + p.2)).subset ?_
  intro x hx
  have h : ∃ y ∈ S K F n s, φ y = φ x := ⟨x, hx, rfl⟩
  refine ⟨(φ x, x - g (φ x)), ⟨trivial, ?_⟩, ?_⟩
  · have hg : g (φ x) = h.choose := by simp only [g, dif_pos h]
    rw [hg]
    exact key x hx _ h.choose_spec.1 h.choose_spec.2.symm
  · simp

theorem base (s : ℤ) (hs : s + n < 0) : S K F n s ⊆ {0} := by
  rintro x ⟨z, rfl, hz⟩
  have : z = 0 := by
    refine Cocycle.ext (Cochain.ext _ _ (fun p q hpq => ?_))
    rw [coe_zero', Cochain.zero_v]
    rcases lt_or_ge s p with h | h
    · exact hz p q hpq h
    · exact (res_zero F q (by omega)).eq_of_tgt (z.1.v p q hpq) 0
  simp [this]

theorem LeafFilt_of : LateralTheory.E.LeafSSCut.LeafFilt := by
  intro _ R _ K _ F n hfin
  have ind : ∀ k : ℕ, ∀ r : ℕ, 1 ≤ r → n < r + k → (S K F n (-(r : ℤ))).Finite := by
    intro k
    induction k with
    | zero => intro r _ hr; exact (Set.finite_singleton 0).subset (base K F n _ (by push_cast at hr; omega))
    | succ k ih =>
      intro r hr1 hr
      by_cases hk : n < r + k
      · exact ih r hr1 hk
      · have : Finite (HK R (Sg (K.X (-(r : ℤ)))) F (n - r)) := hfin r (by omega) (by push_cast at hr; omega)
        have h2 := ih (r + 1) (by omega) (by push_cast at hr ⊢; omega)
        have e : (-((r + 1 : ℕ) : ℤ)) = -(r : ℤ) - 1 := by push_cast; ring
        rw [e] at h2
        exact step K F n (-(r : ℤ)) (n - r) (by omega) h2
  have hS := ind n.toNat 1 le_rfl (by omega)
  have e : (-((1 : ℕ) : ℤ)) = (0 : ℤ) - 1 := by norm_num
  rw [e] at hS
  have hsub : ((HK.pull R (LateralTheory.E.LeafSSCut.incl0 K) F n).ker : Set (HK R K F n)) ⊆ S K F n (0 - 1) := by
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hz : V K F n 0 z := fun p q hpq hp =>
      (CochainComplex.isZero_of_isStrictlyLE K 0 p hp).eq_of_src _ _
    have hc : CohomologyClass.mk (zcomp (Cocycle.ofHom (LateralTheory.E.LeafSSCut.incl0 K)) z (zero_add n)) = 0 := hx
    obtain ⟨β, hβ⟩ := CB F (K.X 0) n _ hc (n - 1) (by omega)
    obtain ⟨w, hw, hwV⟩ := KL K F n 0 n (zero_add n) z hz (n - 1) (by omega) β (by
      rw [hβ]
      change ((Cochain.ofHom (LateralTheory.E.LeafSSCut.incl0 K)).comp z.1 (zero_add n)).v 0 n (zero_add n) = _
      rw [Cochain.comp_v _ _ (zero_add n) 0 0 n (by omega) (by omega), Cochain.ofHom_v]
      simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f])
    exact ⟨w, hw, hwV⟩
  exact (hS.subset hsub).to_subtype

end LateralTheory.E.LeafFiltPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoVCut

def FamilyVe {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

def LeafCurveV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    genericPoint X ∈ Set.range e ∧ ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X

def LeafSpreadV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

theorem surj_of_generic {Y X : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [IsProper f]
    (hη : genericPoint X ∈ Set.range f) : Surjective f := by
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have h1 : closure ({genericPoint X} : Set X) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hc
  rw [(genericPoint_spec X).def] at h1
  exact ⟨fun x => h1 (Set.mem_univ x)⟩

theorem goal_of (hC : LeafCurveV) (hS : LeafSpreadV) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

end LateralTheory.E.LeafGeoVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumDeltaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumDeltaPf

open LateralTheory.E.E4

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ (δ : H ℤ (sch.obj C) Gm 1 →+ Ht q (sch.obj C) 2 1) (ι : Ht q (sch.obj C) 2 1 →+ H ℤ (sch.obj C) Gm 2),
    (∀ y, δ y = 0 ↔ ∃ z, y = q • z) ∧ ∀ x, ι x = 0 ↔ ∃ y, δ y = x

def LeafBrCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ w : H ℤ (sch.obj C) Gm 2, q • w = 0 → w = 0

end LateralTheory.E.LeafKumDeltaPf

end
end

