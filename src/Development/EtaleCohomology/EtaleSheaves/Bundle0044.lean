import Development.EtaleCohomology.EtaleSheaves.Bundle0037
import Development.EtaleCohomology.EtaleSheaves.Bundle0034
import Development.EtaleCohomology.EtaleSheaves.Bundle0032
import Development.EtaleCohomology.EtaleSheaves.Bundle0033
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import Development.EtaleCohomology.EtaleSheaves.Bundle0021
import Development.EtaleCohomology.EtaleSheaves.Bundle0035

-- bundled from Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace LateralTheory.E.LeafGeoVV2Cut

def CurveThroughGenericPointSpreadsToSmoothProperFamily : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

def LeafDescendQF : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
      (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
      IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
      IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      IsIntegral D0 ∧ IsIntegral D1 ∧ IsIntegral D2 ∧
      LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
      topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafExtendZMT : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p]
  (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b]
  (ι : Sp R ⟶ B) [IsOpenImmersion ι], ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
  ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
  ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    IsSeparated q → QuasiCompact q → SmoothOfRelativeDimension 1 q →
    IsSeparated (d1 ≫ q) → QuasiCompact (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsSeparated (d2 ≫ d1 ≫ q) → QuasiCompact (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    IsIntegral D0 → IsIntegral D1 → IsIntegral D2 →
    LocallyQuasiFinite (pullback.lift q f hf.symm) → LocallyQuasiFinite d1 → LocallyQuasiFinite d2 →
    IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    γ1 ≫ v0 = v1 ≫ d1 → γ2 ≫ v1 = v2 ≫ d2 → v0 ≫ f = e →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X) (V : B.Opens)
      (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ V ∧
      SmP π V ∧ SmP (g1 ≫ π) V ∧ SmP (g2 ≫ g1 ≫ π) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback u0 c0 π (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u1 (γ1 ≫ c0) (g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

theorem spread_of (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB) (hE : LeafExtendZMT) :
    CurveThroughGenericPointSpreadsToSmoothProperFamily := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2,
    qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩ := hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩ :=
    hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2
      qf0 qf1 qf2 P0 P1 P2 c1 c2 ve
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩
  show π (u0 x) ∈ (V : Set B)
  rw [← Scheme.Hom.comp_apply, Q0.w]
  exact hs ⟨c0 x, rfl⟩

theorem geoV_of (hC : LeafCurveV) (hS : CurveThroughGenericPointSpreadsToSmoothProperFamily) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
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

theorem goal_of (hC : LeafCurveV) (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB)
    (hE : LeafExtendZMT) : LateralTheory.E.LeafGeoCut.LeafGeoV :=
  geoV_of hC (spread_of hD hB hE)

end LateralTheory.E.LeafGeoVV2Cut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmptyH2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def AffClosed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
  [LocallyOfFiniteType p] (V : X.Opens), IsAffineOpen V →
    ∃ (n : ℕ) (e : V.toScheme ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))), IsClosedImmersion e ∧
      e ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = V.ι ≫ p

def Chart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ), ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of (MvPolynomial (Fin n) A)) ⟶ P), IterLine q ∧ IsOpenImmersion j ∧
    j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))

theorem affClosed : AffClosed := by
  intro A _ X p _ V hV
  haveI : IsAffine V.toScheme := hV
  have hfT : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  have happ := HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT
  let g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop
  have hg : g.hom.FiniteType := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.FiniteType.comp happ h1
  letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra
  have hft : Algebra.FiniteType A Γ(V.toScheme, ⊤) := hg
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  refine ⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have hs := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    have hi : IsClosedImmersion V.toScheme.toSpecΓ := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hi hs
  · have hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g := by
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact φ.commutes a
    have h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
        Spec.map g := by rw [← Spec.map_comp, hcomp]
    have h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p := by
      have hn := Scheme.toSpecΓ_naturality (V.ι ≫ p)
      have h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
        Spec.map_comp _ _
      rw [h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    refine Eq.trans ?_ h3
    rw [Category.assoc]
    exact congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2

theorem Embed_of (hA : AffClosed) (hC : Chart) : LateralTheory.E.ChowGraphCut.Embed := by
  intro A _ X p _ V hV
  obtain ⟨n, e, he, hep⟩ := hA A p V hV
  obtain ⟨P, q, j, hq, hj, hjq⟩ := hC A n
  haveI := hj
  haveI := he
  refine ⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]

end LateralTheory.E.EmbedPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibreEqvPf

theorem eqv_snd_snd {q : ℕ} {i : ℤ} {Z S K L : Scheme.{0}} (c : Z ⟶ S) (t : L ⟶ S) (k : K ⟶ L) :
    Eqv _ (sch.map (pullback.snd (pullback.snd c t) k)) (tw q i) ↔ Eqv _ (sch.map (pullback.snd c (k ≫ t))) (tw q i) := by
  have e := pullbackLeftPullbackSndIso_hom_snd c t k
  rw [← e, Functor.map_comp]
  exact ⟨fun h => eqv_right h (eqv_iso (pullbackLeftPullbackSndIso c t k) q i), fun h => eqv_comp (eqv_iso _ q i) h⟩

theorem eqv_snd_iso {q : ℕ} {i : ℤ} {Z S K K' : Scheme.{0}} (c : Z ⟶ S) (T : K ⟶ S) (ρ : K' ⟶ K) [IsIso ρ]
    (h : Eqv _ (sch.map (pullback.snd c T)) (tw q i)) : Eqv _ (sch.map (pullback.snd c (ρ ≫ T))) (tw q i) := by
  rw [← eqv_snd_snd]
  have w : sch.map (pullback.snd (pullback.snd c T) ρ) ≫ sch.map ρ = sch.map (pullback.fst (pullback.snd c T) ρ) ≫ sch.map (pullback.snd c T) := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  refine eqv_left (g := sch.map ρ) ?_ (eqv_iso (asIso ρ) q i)
  rw [w]
  exact eqv_comp (eqv_iso (asIso (pullback.fst (pullback.snd c T) ρ)) q i) h

def StalkFib : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S → ∀ x : S, IsUnit (q : S.presheaf.stalk x) →
  Eqv _ (sch.map (pullback.snd c (S.fromSpecStalk x))) (tw q i)

theorem residue_bij {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨(IsLocalRing.ResidueField.map f).injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue f x⟩

theorem geom (H : Hyp) (h0 : HZero) (hA : AICAcyc) (hS : StalkSHS) (hF : StalkFib) (q : ℕ) (i : ℤ) {Z S : Scheme.{0}}
    (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c] (hZs : AICSch Z) (hSs : AICSch S)
    (hB : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t))
    (x : S) (hu : IsUnit (q : S.presheaf.stalk x)) :
    Eqv _ (sch.map (pullback.snd c (cpt (S.presheaf.stalk x) ≫ S.fromSpecStalk x))) (tw q i) := by
  have hsh := hS S hSs x
  obtain ⟨_, _⟩ := id hsh
  have hx := hF H h0 hA q i c hZs hSs x hu
  have hpb : Eqv _ (sch.map (pullback.fst (pullback.snd c (S.fromSpecStalk x)) (cpt (S.presheaf.stalk x)))) (tw q i) :=
    hB _ hsh hu (S.fromSpecStalk x)
  have hE1 : Eqv _ (sch.map (cpt (S.presheaf.stalk x))) (tw q i) := H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  rw [← eqv_snd_snd]
  refine eqv_left (g := sch.map (cpt (S.presheaf.stalk x))) ?_ hE1
  rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp]
  exact eqv_comp hpb hx

theorem FibreEqv_of (hS : StalkSHS) (hF : StalkFib) : FibreEqv := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  set j := pullback.fst p (cpt A)
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks j := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  have hsurj : Function.Surjective (j.stalkMap s).hom := j.stalkMap_surjective s
  have hu0 : IsUnit (q : Γ(S, ⊤)) := unit_of hq p
  have hu : IsUnit (q : S.presheaf.stalk (j s)) := by
    simpa using hu0.map (S.presheaf.germ ⊤ (j s) trivial).hom
  have hbij := residue_bij (j.stalkMap s).hom hsurj
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField ((pullback p (cpt A)).presheaf.stalk s))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk (j s)))) :=
    Spec.map (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom
  have sq : cpt ((pullback p (cpt A)).presheaf.stalk s) ≫ (pullback p (cpt A)).fromSpecStalk s ≫ j =
      ρ ≫ cpt (S.presheaf.stalk (j s)) ≫ S.fromSpecStalk (j s) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk j, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ρ, cpt, ← Spec.map_comp]
    congr 1
  rw [eqv_snd_snd, sq]
  exact eqv_snd_iso c _ ρ (geom H h0 hA hS hF q i c hZs hSs hB (j s) hu)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def BaseAIC : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, AICSch (pullback c (S.fromSpecStalk x))

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AICSch (Spec (S.presheaf.stalk x))

theorem StalkFib_of (hZB : BaseAIC) (hSA : StalkAIC) : StalkFib := by
  intro H h0 hA q i Z S c _ _ _ hZs hSs x hu
  have hB := hZB c hZs hSs x
  have hK := hSA S hSs x
  have : IsIntegral (pullback c (S.fromSpecStalk x) : Scheme.{0}) := hB.1
  have : ConnectedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) := inferInstance
  have : CompactSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c (S.fromSpecStalk x))
  have : QuasiSeparatedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd c (S.fromSpecStalk x))
  have hu1 : IsUnit (q : Γ(Spec (S.presheaf.stalk x), ⊤)) := unit_of (A := S.presheaf.stalk x) hu (𝟙 _)
  have hu2 : IsUnit (q : Γ(pullback c (S.fromSpecStalk x), ⊤)) :=
    unit_of (A := S.presheaf.stalk x) hu (pullback.snd c (S.fromSpecStalk x))
  exact eqv_of H.a9 _ (h0 H q (pullback.snd c (S.fromSpecStalk x)) hK inferInstance hu1 i) (fun n hn => hA H q _ hB hu2 n i hn)
    (fun n hn => hA H q _ hK hu1 n i hn)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def StalkAICRing : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

def SpecAIC : Prop := ∀ (B : CommRingCat.{0}), IsDomain B → AIC B → AICSch (Spec B)

theorem StalkAIC_of (h1 : StalkAICRing) (h2 : SpecAIC) : StalkAIC := by
  intro S hS x
  have : IsIntegral S := hS.1
  exact h2 _ inferInstance (h1 S hS x)

end LateralTheory.E.FibreEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibreIdem
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.StdChartsProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def Restr (B : Subalgebra A K) (t : K) (Q : PrimeSpectrum (AdjoinInv B t)) (S : Subalgebra A K) (x : PrimeSpectrum S) :
    Prop := ∀ s : S, s ∈ x.asIdeal ↔ ∃ d ∈ Q.asIdeal, (d : K) = (s : K)

structure Cover {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K) : Prop where
  ex : ∃ (jU : Spec (CommRingCat.of B) ⟶ Z) (jV : Spec (CommRingCat.of C) ⟶ Z),
    IsOpenImmersion jU ∧ IsOpenImmersion jV ∧ Set.range jU.base ∪ Set.range jV.base = Set.univ ∧
    jU ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧ jV ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C)) ∧
    ∀ (x : PrimeSpectrum B) (y : PrimeSpectrum C), jU.base x = jV.base y ↔
      ∃ Q : PrimeSpectrum (AdjoinInv B t), Restr B t Q B x ∧ Restr B t Q C y

def ChartsGeom : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ Cover p B C t

def FibreIdem : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K] {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (B C : Subalgebra A K) (t : K), Charts B C t → Cover p B C t →
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

theorem StdCharts_of (hG : ChartsGeom) (hF : FibreIdem) : LateralTheory.E.StandardEtaleChartsIdempotentGluing.StdCharts := by
  intro A _ _ Z p hIL hZ
  obtain ⟨K, hK, hA, B, C, t, hc, hint, hcov⟩ := hG A p hIL hZ
  exact ⟨K, hK, hA, B, C, t, hc, hint, fun W hW => hF A K p B C t hc hcov W hW⟩

end LateralTheory.E.StdChartsProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IterCompPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KillKerPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.KerLocPf

namespace LateralTheory.E.KillKerPf

def KillAt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n, pull _ (sch.map (Spec.map φ')) (tw q i) n x = 0 →
  ∀ r : Ideal D, r.IsPrime → ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
    (∃ Q : Ideal E, Q.IsPrime ∧ Q.comap e.hom = r) ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

def EtGlue : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (D : CommRingCat.{0})
  (x : H (ZMod q) (sch.obj (Spec D)) (tw q i) n),
  (∀ r : Ideal D, r.IsPrime → ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
    (∃ Q : Ideal E, Q.IsPrime ∧ Q.comap e.hom = r) ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧ SpS e ∧ pull _ (sch.map (Spec.map e)) (tw q i) n x = 0

end LateralTheory.E.KillKerPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCSurjPf

def LocForm : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
  Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)

def Descent : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
    (Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)) →
    ∃ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q),
      Loc (Spec (CommRingCat.of B)) fun _ g => Sec.res g y = Sec.res g (m B ζ ψ)

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  exact (LateralTheory.E.L_sec_gluePf.typeSheaf F S hS).isSeparatedFor.ext fun V g hg => hab V g hg

theorem LCSurj_of (hL : LocForm) (hD : Descent) : LateralTheory.E.LCBijPf.LCSurj := by
  intro q _ i m hm B _ ζ y
  obtain ⟨ψ, hψ⟩ := hD q i m hm B ζ y (hL q i B ζ y)
  exact ⟨ψ, (sec_sep _ _ _ _ hψ).symm⟩

end LateralTheory.E.LCSurjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LChartPf
section
noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I HenselianRing.jac (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCloseBCut
section
noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafCloseBCut

def LeafProjModel : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A))

def LeafDimOpen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (b : X ⟶ Sp k) [LocallyOfFiniteType b],
    IsIntegral X → ∀ U : Set X, IsOpen U → U.Nonempty → topologicalKrullDim X ≤ topologicalKrullDim U

theorem goal_of (h1 : LeafProjModel) (h2 : LeafDimOpen) : LateralTheory.E.LeafSpreadVCut.LeafCloseB := by
  intro k _ A _ _ _ _
  obtain ⟨B, b, ι, hB, hb, hι, hc⟩ := h1 k A
  refine ⟨B, b, ι, hB, hb, hι, hc, ?_⟩
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum A) := inferInstance
  have hemb := ι.isOpenEmbedding
  calc topologicalKrullDim B ≤ topologicalKrullDim (Set.range ι) :=
        h2 k b hB _ hemb.isOpen_range ⟨ι x, x, rfl⟩
    _ = topologicalKrullDim (Sp A) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (hemb.isEmbedding.toHomeomorph).isHomeomorph).symm
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end LateralTheory.E.LeafCloseBCut

end
end

