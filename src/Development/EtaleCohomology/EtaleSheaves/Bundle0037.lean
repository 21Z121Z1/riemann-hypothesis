import Development.EtaleCohomology.EtaleSheaves.Bundle0025
import Development.EtaleCohomology.EtaleSheaves.Bundle0024
import Development.EtaleCohomology.EtaleSheaves.Bundle0023
import Development.EtaleCohomology.EtaleSheaves.Bundle0026

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafPrimCoverPf

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = 1 := by
  obtain ⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1 := cyclotomic.dvd_X_pow_sub_one q A
  have hd := congrArg derivative hh
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  refine ⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩
  have hq0 : 0 < q := Nat.pos_of_neZero q
  have e1 : (X : A[X]) ^ q = X ^ (q - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel hq0]
  have hc : (C (q : A) : A[X]) = (q : A[X]) := map_natCast C q
  have hcu : C u * C (q : A) = 1 := by rw [← C_mul, hu, C_1]
  rw [e1] at hh
  linear_combination (-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu

def cycPair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq
    exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem etale_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  let P := cycPair A q hq
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]; exact isUnit_one
  let e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

theorem ff_adjoin (A : Type) [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Module.FaithfullyFlat A (AdjoinRoot (cyclotomic q A)) := by
  let b := AdjoinRoot.powerBasisAux' (cyclotomic.monic q A)
  have hpos : 0 < (cyclotomic q A).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_neZero q)
  have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hpos⟩⟩
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

example (U : Scheme.{0}) : U ⟶ Spec Γ(U, ⊤) := U.toSpecΓ

theorem prim_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Nonempty (Prim q (AdjoinRoot (cyclotomic q A))) := by
  refine ⟨⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), ?_⟩⟩
  have h0 : aeval (AdjoinRoot.root (cyclotomic q A)) (cyclotomic q A) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← aeval_map_algebraMap A, map_cyclotomic]
  exact h0

theorem spec_surj (A B : CommRingCat.{0}) (φ : A ⟶ B) (hA : Subsingleton A) : Surjective (Spec.map φ) := by
  constructor
  intro x
  exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

theorem leafPrimCover_pf : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := by
  intro q _ U hq
  let A : Type := Γ(U, ⊤)
  let B : Type := AdjoinRoot (cyclotomic q A)
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hEt : Etale (Spec.map φ) := by
    have := etale_adjoin A q hq
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)
  have hSu : Surjective (Spec.map φ) := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact spec_surj _ _ φ h
    · have := ff_adjoin A q
      exact ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2
  let f := pullback.fst U.toSpecΓ (Spec.map φ)
  refine ⟨Sieve.generate (Presieve.singleton f), ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) f).2 ⟨Surjective.surj, inferInstance⟩
  · rintro V g ⟨W, h, k, hk, rfl⟩
    cases hk
    obtain ⟨ζ⟩ := prim_adjoin A q hq
    exact ⟨Prim.map (h.appTop.hom.comp ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) ζ⟩

theorem LeafPrimCover_of : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := leafPrimCover_pf

end LateralTheory.E.LeafPrimCoverPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPPf
section
noncomputable section
open LateralTheory.E.t_E6Cut TensorProduct

namespace LateralTheory.E.LeafRoofEtPPf

theorem diag {C D : Type} [CommRing C] [CommRing D] [Algebra C D] [Algebra.Etale C D] :
    ∃ e : D ⊗[C] D, IsIdempotentElem e ∧ Algebra.TensorProduct.lmul' C e = 0 ∧
      ∀ x, Algebra.TensorProduct.lmul' C x = 0 → x ∈ Ideal.span {e} := by
  obtain ⟨e, he, hsp⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg C D)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[D⁄C]
  refine ⟨e, he, ?_, fun x hx => ?_⟩
  · have : e ∈ KaehlerDifferential.ideal C D := hsp ▸ Submodule.mem_span_singleton_self e
    simpa [RingHom.mem_ker] using this
  · have : x ∈ KaehlerDifferential.ideal C D := by simpa [RingHom.mem_ker] using hx
    rw [hsp] at this
    exact this

def LeafQuotEt : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ((Ideal.Quotient.mk (varIdeal φ)).comp (φ.comp MvPolynomial.C)).Etale

def LeafPolyEt : Prop := ∀ (d : ℕ) {C B D : Type} [CommRing C] [CommRing B] [CommRing D] [Algebra C D]
  (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  letI := (φ.comp MvPolynomial.C).toAlgebra
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : D →ₐ[C] B ⊗[C] D).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1:D))).Etale

theorem roofEtale_of_quotientEtale_polynomialEtale (h1 : LeafQuotEt) (h2 : LeafPolyEt) : LateralTheory.E.LeafRoofEtPf.LeafRoofEtP := by
  intro d C B _ _ φ hφ
  letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra
  haveI hD : Algebra.Etale C (B ⧸ varIdeal φ) := by
    rw [← RingHom.etale_algebraMap]; exact h1 d φ hφ
  let q : B ⊗[C] (B ⧸ varIdeal φ) →ₐ[C] (B ⧸ varIdeal φ) ⊗[C] (B ⧸ varIdeal φ) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (varIdeal φ)) (AlgHom.id C _)
  let m : B ⊗[C] (B ⧸ varIdeal φ) →+* B ⧸ varIdeal φ := ((Algebra.TensorProduct.lmul' C).comp q).toRingHom
  let b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* B ⊗[C] (B ⧸ varIdeal φ) :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : (B ⧸ varIdeal φ) →ₐ[C] B ⊗[C] _).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ))
  obtain ⟨e0, hi, he0, hk0⟩ := diag (C := C) (D := B ⧸ varIdeal φ)
  have hq : Function.Surjective q :=
    Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective C _) (fun x => ⟨x, rfl⟩)
  obtain ⟨e, rfl⟩ := hq e0
  have hbX : ∀ j, b (MvPolynomial.X j) = φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ) := fun j => by
    simp [b]
  have hker : RingHom.ker q = Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
    have hk : RingHom.ker (Ideal.Quotient.mkₐ C (varIdeal φ)) =
        Ideal.span (Set.range fun j => φ (MvPolynomial.X j)) := by
      ext x; exact Ideal.Quotient.eq_zero_iff_mem
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective C _), hk, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [hbX]
  have hmem : ∀ x, x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ↔ q x = 0 := fun x => by
    rw [← hker, RingHom.mem_ker]
  refine ⟨B ⊗[C] (B ⧸ varIdeal φ), inferInstance, algebraMap B _, b, m, e,
    RingHom.etale_algebraMap.mpr inferInstance, h2 d φ hφ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hbX]; rfl
  · ext x; simp [m, q]
  · apply MvPolynomial.ringHom_ext
    · intro r; simp [m, q, b]
    · intro j
      simp only [RingHom.comp_apply, hbX, MvPolynomial.constantCoeff_X]
      simp only [m, q, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  · exact he0
  · rw [hmem, map_sub, map_mul, hi.eq, sub_self]
  · intro x hx
    obtain ⟨r0, hr0⟩ := Ideal.mem_span_singleton'.mp (hk0 (q x) hx)
    obtain ⟨r, rfl⟩ := hq r0
    have : x - r * e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
      rw [hmem, map_sub, map_mul, hr0, sub_self]
    have h3 : x = (x - r * e) + r * e := by ring
    rw [h3]
    exact Ideal.add_mem _ (Ideal.mem_sup_left this)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

end LateralTheory.E.LeafRoofEtPPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSpreadVCut

def LeafDescendV : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type) [Field Ω]
    [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      IrreducibleSpace D0 ∧ topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafCloseB : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ topologicalKrullDim B ≤ ringKrullDim A

def LeafExtendY : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (A : Type) [CommRing A]
    [Algebra k A] (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b] (ι : Sp A ⟶ B) [IsOpenImmersion ι],
    ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) →
    ∀ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp A) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X),
    IsProper q → SmoothOfRelativeDimension 1 q → IsProper (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsProper (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) → IrreducibleSpace D0 →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X)
      (w0 : D0 ⟶ Y0) (w1 : D1 ⟶ Y1) (w2 : D2 ⟶ Y2),
      SmP π ι.opensRange ∧ SmP (g1 ≫ π) ι.opensRange ∧ SmP (g2 ≫ g1 ≫ π) ι.opensRange ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback w0 q π ι ∧ IsPullback w1 (d1 ≫ q) (g1 ≫ π) ι ∧ IsPullback w2 (d2 ≫ d1 ≫ q) (g2 ≫ g1 ≫ π) ι ∧
      d1 ≫ w0 = w1 ≫ g1 ∧ d2 ≫ w1 = w2 ≫ g2 ∧ w0 ≫ h = f

lemma succ_le_of_lt {a x : WithBot ℕ∞} (h : a < x) : a + 1 ≤ x ∧ a + 1 < ⊤ := by
  induction a with
  | bot => exact ⟨by simp, by simp⟩
  | coe n =>
    induction x with
    | bot => exact absurd h (not_lt_bot)
    | coe m =>
      have h' : n < m := WithBot.coe_lt_coe.mp h
      have hn : n ≠ ⊤ := ne_top_of_lt h'
      refine ⟨?_, ?_⟩
      · rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt h'
      · rw [← WithBot.coe_one, ← WithBot.coe_add]
        exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (by
          lift n to ℕ using hn
          exact ENat.natCast_ne_top (n + 1)))

theorem goal_of (hD : LeafDescendV) (hB : LeafCloseB) (hE : LeafExtendY) : LateralTheory.E.LeafGeoVCut.LeafSpreadV := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2 _ _
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, pq, sq, pq1, sq1, pq2, sq2, hf, irr, dD, P0, P1, P2,
    c1, c2, ve⟩ := hD k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, w0, w1, w2, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, we⟩ :=
    hE k p R B b ι hι D0 D1 D2 q d1 d2 f pq sq pq1 sq1 pq2 sq2 hf irr
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, ι.opensRange, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    v0 ≫ w0, v1 ≫ w1, v2 ≫ w2, iB, pb, ?_, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨(v0 ≫ w0) x, ?_⟩, P0.paste_horiz Q0, P1.paste_horiz Q1, P2.paste_horiz Q2, ?_, ?_,
    by rw [Category.assoc, we, ve]⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · show π ((v0 ≫ w0) x) ∈ Set.range ι
    rw [← Scheme.Hom.comp_apply, Category.assoc, Q0.w, ← Category.assoc, P0.w]
    exact ⟨_, rfl⟩
  · rw [← Category.assoc, c1, Category.assoc, Category.assoc, e1]
  · rw [← Category.assoc, c2, Category.assoc, Category.assoc, e2]

end LateralTheory.E.LeafSpreadVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTruncPf
section
noncomputable section
open CategoryTheory Limits Pretriangulated Triangulated

namespace LateralTheory.E.LeafTruncPf

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma mono_H_ι (Y : DerivedCategory C) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y
  have := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2
    (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)
  exact this

lemma epi_H_π (X : DerivedCategory C) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished n X
  have := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2
    (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)
  exact this

lemma lift_LT {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : φ ≫ (DerivedCategory.TStructure.t.truncGEπ n).app Y = 0) :
    ∃ ψ : X ⟶ (DerivedCategory.TStructure.t.truncLT n).obj Y,
      φ = ψ ≫ (DerivedCategory.TStructure.t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h

lemma desc_GE {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ φ = 0) :
    ∃ ψ : (DerivedCategory.TStructure.t.truncGE n).obj X ⟶ Y,
      φ = (DerivedCategory.TStructure.t.truncGEπ n).app X ≫ ψ :=
  Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h

lemma heart_zero {X Y : DerivedCategory C} (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (χ : X ⟶ Y) (hχ : (DerivedCategory.homologyFunctor C n).map χ = 0) : χ = 0 := by
  obtain ⟨A, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨B, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)
  have ha0 : a = 0 := by
    have eq := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a
    dsimp at eq
    rw [← eq, ha]
    simp [hχ]
  have : χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv := by simp
  rw [this, ← ha, ha0, Functor.map_zero]
  simp

lemma zero_of_H {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (φ : X ⟶ Y)
    (hφ : (DerivedCategory.homologyFunctor C n).map φ = 0) : φ = 0 := by
  have h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  obtain ⟨ψ, hψ⟩ := lift_LT (n + 1) φ h1
  have h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n
  obtain ⟨χ, hχ⟩ := desc_GE n ψ h2
  have hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0 := by
    have := mono_H_ι Y n
    have := epi_H_π X n
    rw [hψ, hχ, Functor.map_comp, Functor.map_comp] at hφ
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]
    simpa using hφ
  have : χ = 0 := heart_zero n χ hHχ
  rw [hψ, hχ, this]
  simp

end LateralTheory.E.LeafTruncPf

open LateralTheory.E.LeafTruncPf in
theorem LateralTheory.E.LeafGhostRelCut.LeafTrunc_of : LateralTheory.E.LeafGhostRelCut.LeafTrunc := by
  intro A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  have : K0.IsLE 2 := (DerivedCategory.isLE_iff K0 2).2 hK0
  have : K2.IsGE 0 := (DerivedCategory.isGE_iff K2 0).2 hK2
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have hP : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0 :=
    zero_of_H 2 _ (by simp [Functor.map_comp, hf])
  obtain ⟨f', hf'⟩ := lift_LT 2 f e1
  have e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫
      (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    zero_of_H 1 _ (by simp [Functor.map_comp, hg])
  obtain ⟨w, hw⟩ := lift_LT 1 _ e2
  have e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    DerivedCategory.TStructure.t.zero _ 0 1
  obtain ⟨ℓ', hℓ'⟩ := lift_LT 1 ℓ e3
  have hiso : IsIso ℓ' := by
    rw [DerivedCategory.isIso_iff]
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hm0 := mono_H_ι K2 0
      rw [zero_add] at hm0
      have hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫
          (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := by
        rw [← Functor.map_comp, ← hℓ']; exact hℓ
      have : Epi ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) :=
        epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _
      have : IsIso ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := isIso_of_mono_of_epi _
      exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app K2))
    · have hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj K2)) := by
        rcases lt_or_gt_of_ne hm with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 m h
        · exact DerivedCategory.isZero_of_isLE _ 0 m h
      exact ⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine ⟨f' ≫ w ≫ inv ℓ', ?_⟩
  rw [hf', hℓ']
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, hw]

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwAdjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.E8.TwSec

theorem twAdj_comap_surj (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyclotomic q A)))) := by
  have hm := cyclotomic.monic q A
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have : Module.Finite A (AdjoinRoot (cyclotomic q A)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  intro p
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
    · exact h
  have : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
    have hd : 0 < (cyclotomic q A).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q)
    have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hd⟩⟩
    exact (AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial
  exact Algebra.IsIntegral.comap_surjective A _ p

theorem twAdj_etale (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  have hsep : (cyclotomic q A).Separable :=
    (separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair A := ⟨cyclotomic q A, cyclotomic.monic q A, 1,
    ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) := P.equivAwayAdjoinRoot
  let e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)]
      Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) :=
    IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)
  have := Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))
  infer_instance

theorem LeafTwAdj_of : LeafTwAdj := by
  intro q _ U u hq
  obtain ⟨R, f, hf, ⟨x, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)
  have hqR : IsUnit ((q : ℕ) : R) := by
    simpa using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom
  have := twAdj_etale R q hqR
  let φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R)) :=
    CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  refine ⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := twAdj_comap_surj R q x
    refine ⟨y, ?_⟩
    subst hy
    rfl
  · let ψ := (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom
    refine ⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩
    · simpa using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ
    · have h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0 := by
        rw [← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)
      rw [h0, map_zero] at this
      exact this

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfC
section
namespace LateralTheory.E.E4

def LeafNoetherDim : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] B),
  Function.Injective g → g.Finite → s = 1

theorem LeafNoetherCurve_of (hD : LeafNoetherDim) : LeafNoetherCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨s, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k B
  obtain rfl := hD k B hB s g hg hf
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
  refine ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem LeafUnitsFG_of_dim (hD : LeafNoetherDim) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_leaves (LeafNoetherCurve_of hD) hV

end LateralTheory.E.E4
end

