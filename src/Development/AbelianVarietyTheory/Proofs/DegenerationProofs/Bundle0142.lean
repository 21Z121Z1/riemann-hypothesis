import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.ProjFinite

theorem exists_relAmple_of_isProjBy {R : Type} [CommRing R] {A : Over (Sp R)} (h : GlobalTheory.AbLaw.IsProjBy A.hom) :
    ∃ H : LB A.left, H.IsLB ∧ Out.RelAmple A H := by
  obtain ⟨H, hH, m, s, hs⟩ := h
  have e : GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ) = H := by
    cases H
    simp [GlobalTheory.AbLaw.pw]
  have k : ∀ s : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy A.hom (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)) s → Out.RelAmple A H :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hH le_rfl s hs
  rw [e] at k
  exact ⟨H, hH, k s hs⟩

theorem isProjBy_of_fieldExtension {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)}
    {A : Over (Sp K)} [IsProper A₀.hom] {φ : A.left ⟶ A₀.left} (h : IsPullback φ A.hom A₀.hom (spMap i))
    {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB) (hw : LBIso L (L₀.pull φ))
    (hA : Out.RelAmple A L) : GlobalTheory.AbLaw.IsProjBy A₀.hom := by
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  have h₀ : Out.RelAmple A₀ L₀ :=
    (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull i h hL₀
      ((isAmpleLB_of_relAmple_of_isAffine A hL hA).of_lbIso (LB.isLB_pull hL₀ φ) hw.symm))
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K₀ A₀ L₀ hL₀).1 h₀
  exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL₀ d, n, s, hs⟩

theorem exists_isPullback {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
    {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S} (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, φ ≫ π₁ = π₂ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, h₁.lift_fst _ _ _, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_finite_isProjBy : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  let Ω := AlgebraicClosure K
  let a : K →+* Ω := algebraMap K Ω
  let B : Over (Sp Ω) := (Over.pullback (spMap a)).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap a)) B.hom A.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨H, hH, hamp⟩ := exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme Ω B hB)
  let K₀ : Subfield Ω := a.fieldRange
  let j : K →+* K₀ := a.rangeRestrictField
  have sq₀ := IsPullback.of_hasPullback A.hom (spMap j)
  obtain ⟨φ, hφ, sq⟩ := exists_isPullback sq₀ sqB (spMap K₀.subtype) (spMap_comp _ _)
  obtain ⟨s, hs⟩ := GlobalTheory.LBDescent.exists_lb_subfield Ω K₀ _ _ _ _ φ H hH sq
  let L : IntermediateField K Ω := IntermediateField.adjoin K (s : Set Ω)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have h : K₀ ≤ L.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  refine ⟨L, inferInstance, inferInstance, hfin, ?_⟩
  let C : Over (Sp L) := (Over.pullback (spMap (algebraMap K L))).obj A
  have sqC : IsPullback (pullback.fst A.hom (spMap (algebraMap K L))) C.hom A.hom (spMap (algebraMap K L)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨φ₁, hφ₁, sq₁⟩ := exists_isPullback sq₀ sqC (spMap (Subfield.inclusion h)) (spMap_comp _ _)
  obtain ⟨ψ, hψ, sq₂⟩ := exists_isPullback sqC sqB (spMap L.toSubfield.subtype) (spMap_comp _ _)
  obtain ⟨L₁, hL₁, hw⟩ := hs L.toSubfield h (IntermediateField.subset_adjoin K _) C.left C.hom φ₁ ψ sq₁
    (sq₀.hom_ext (by rw [Category.assoc, hφ₁, hψ, hφ]) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc, sq.w]
      exact congrArg _ (spMap_comp _ _))) sq₂.w
  have : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) sqC hA.proper
  exact isProjBy_of_fieldExtension L.toSubfield.subtype sq₂ hL₁ hH hw hamp

end GlobalTheory.ProjFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSums
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ArcSeries

section Comp
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def homComp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x)) :
    NumD.Hom k N N'' :=
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  { φ := I'.φ.comp I.φ
    h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
    h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
    θ_eq x y u := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.θ_eq x y u)
      have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    σ_eq x := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.σ_eq x)
      have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
      apply Additive.ofMul.injective
      simp only [e, map_mul, map_inv, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    lam := I'.lam * Units.map g.toMonoidHom I.lam
    th_eq x := by
      rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq, hk]
      simp only [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      ring
    e := I.e.trans I'.e
    c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
    ψ_eq χ := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.ψ_eq χ)
      have b := congrArg Additive.ofMul (I'.ψ_eq (I.e χ))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq] at a b ⊢
      linear_combination (norm := abel) a + b }

theorem homComp_rel (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x))
    {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b) (h' : I'.Rel b c) : (homComp I I' k hk).Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  have p := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (h.2 χ)
  have q := congrArg Additive.ofMul (h'.2 (I.e χ))
  apply Additive.ofMul.injective
  simp only [homComp, e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq, h.1] at p q ⊢
  linear_combination (norm := abel) p + q
end Comp

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]; exact Iff.rfl⟩

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  have : IsIntegral S x := hx.map_of_comp_eq ((algebraMap R K).codRestrict S h) (RingHom.id K) rfl
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

theorem exists_map {O O₁ K : Type} [CommRing O] [CommRing O₁] [Field K] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (io : O₁ →+* K)
    (hio : ∀ a, io (algebraMap O O₁ a) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {k : ℕ} (hk : 0 < k) {t : K}
    (ht : t ^ k = algebraMap (PowerSeries O) K PowerSeries.X) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (Φ : PowerSeries O₁ →+* K), Module.Finite (PowerSeries O) R₁ ∧
      (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ R₁ := by
  obtain ⟨Φ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free O O₁ K (algebraMap _ K) io hio
  obtain ⟨Φ, h4, h5, h6⟩ := GlobalTheory.T.exists_ringHom_powerSeries_root' O₁ K Φ₁ k t hk (ht.trans h2.symm)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := O₁)
  refine ⟨Algebra.adjoin _ (io '' s ∪ {t}), Φ, Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image _).union (Set.finite_singleton _)) ?_, fun a => (h4 a).trans (h1 a), h5, fun f => ?_⟩
  · rintro x (⟨a, -, rfl⟩ | rfl)
    · exact (Algebra.IsIntegral.isIntegral (R := O) a).map_of_comp_eq PowerSeries.C io (RingHom.ext fun a => (hio a).symm)
    · exact IsIntegral.of_pow hk (ht ▸ isIntegral_algebraMap)
  · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h6 f)
    rintro x (⟨g, rfl⟩ | rfl)
    · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h3 g)
      rintro x (⟨g, rfl⟩ | ⟨a, rfl⟩)
      · exact Subalgebra.algebraMap_mem _ g
      · have ha : a ∈ Submodule.span O (s : Set O₁) := hs ▸ Submodule.mem_top
        change io a ∈ Algebra.adjoin (PowerSeries O) (io '' s ∪ {t})
        induction ha using Submodule.span_induction with
        | mem x hx => exact Algebra.subset_adjoin (.inl ⟨x, hx, rfl⟩)
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ a b => rw [map_add]; exact add_mem a b
        | smul c x _ a => rw [Algebra.smul_def, map_mul, hio]; exact mul_mem (Subalgebra.algebraMap_mem _ _) a
    · exact Algebra.subset_adjoin (.inr rfl)

def Sums {R K F : Type} [CommRing R] [Field K] [Field F] [Algebra R K] (X : R) (io : F →+* K) (N : NumD F)
    (be : LinearMap.BilinForm ℤ N.X) (m j : ℕ) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j) (t : Kˣ)
    (v w : La → K) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
    (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) → ‖gam (algebraMap R K X)‖ < 1 →
    ∀ (N' : NumD C) (I : NumD.Hom (gam.comp io) N N') (k : ℕ) (β : N'.Form k), I.lam = 1 →
    (∀ y z, β.be (I.e y) (I.e z) = be y z) → ∀ u rm rj : Cˣ, (u : C) = gam (algebraMap R K X) →
    (rm : C) = gam (t ^ j : Kˣ) → (rj : C) = gam (t ^ m ^ 2 : Kˣ) →
    ∀ (q' : La → N'.QT (m ^ 2)) (p : La → (N'.twist β u).QT (m ^ 2)),
    (∀ x, (q' x).1.1.toAdd = I.e (q x).1.1.toAdd ∧ I.Rel (q x).1.2 (q' x).1.2) → (∀ x, TwRel β u rm (q' x) (p x)) →
    (∀ x, gam (v x) = (N'.twist β u).tx m (p x)) ∧
    ∀ (qz' : N'.QT j) (pz : (N'.twist β u).QT j), qz'.1.1.toAdd = I.e qz.1.1.toAdd → I.Rel qz.1.2 qz'.1.2 →
      TwRel β u rj qz' pz → ∃ s : Cˣ, ∀ x, gam (w x) = s * (N'.twist β u).ev m (p x) pz.1.2

theorem exists_sums {O O₁ K F : Type} [CommRing O] [CommRing O₁] [Field K] [Field F] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (f : O₁ →+* F) (io : F →+* K)
    (hio : ∀ a, io (f (algebraMap O O₁ a)) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {N : NumD F}
    (be : LinearMap.BilinForm ℤ N.X) {m j : ℕ} (hm : Odd m) (hj : 0 < j) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j)
    (t : Kˣ) (ht : (t : K) ^ (m ^ 2 * j) = algebraMap (PowerSeries O) K PowerSeries.X) {N₀ : NumD O₁}
    (I₀ : NumD.Hom f N₀ N) (hl : I₀.lam = 1)
    (hq : ∀ x, ∃ p₀ : N₀.QT (m ^ 2), (q x).1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 (q x).1.2)
    (hz : ∃ p₀ : N₀.QT j, qz.1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 qz.1.2) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (v w : La → K), Module.Finite (PowerSeries O) R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O) io N be m j q qz t v w := by
  have hk : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  obtain ⟨R₁, Φ, hR, h1, h2, h3⟩ := exists_map (io.comp f) hio hk ht
  choose p₀ hp hp' using hq
  obtain ⟨q₀, hz, hz'⟩ := hz
  let be₀ : LinearMap.BilinForm ℤ N₀.X := be.comp I₀.e.toAddMonoidHom.toIntLinearMap I₀.e.toAddMonoidHom.toIntLinearMap
  let s : ℕ := ((m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd)).toNat
  refine ⟨R₁, fun x => Φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x)),
    fun x => Φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x) q₀ s), hR, fun x => h3 _, ?_⟩
  intro C _ _ _ gam g1 g2 N' I k β hI hβ u rm rj hu hrm hrj q' p hq' hp''
  obtain ⟨S, hS⟩ := exists_ball C
  have n1 : ∀ g, ‖(gam.comp Φ) g‖ ≤ 1 := fun g => (hS _).1 (mem_of_isIntegral (S.comap gam)
    (fun r => (hS _).2 (g1 r)) ((Algebra.IsIntegral.isIntegral (⟨_, h3 g⟩ : R₁)).map R₁.val))
  have n2 : ‖(gam.comp Φ) PowerSeries.X‖ < 1 := by
    rw [← ht, map_pow, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hk.ne'] at g2
    rwa [RingHom.comp_apply, h2]
  let t' : Cˣ := Units.map gam.toMonoidHom t
  let J := homComp I₀ I ((gam.comp Φ).comp PowerSeries.C) fun x => congrArg gam (h1 x)
  have hJ : J.lam = 1 := by
    change I.lam * Units.map _ I₀.lam = 1
    rw [hI, hl, map_one, mul_one]
  have e1 : t' ^ j = rm := Units.ext (by rw [hrm, ← map_pow]; rfl)
  have key := fun x => GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt O₁ C (gam.comp Φ) n1 n2 t' u rm rj m j hm hj (congrArg gam h2.symm) e1
    (Units.ext (by rw [hrj, ← map_pow]; rfl))
    (Units.ext (by rw [hu, ← e1, ← pow_mul, mul_comm j, ← ht, ← map_pow, map_pow gam]; simp [t']))
    N₀ N' J k be₀ β (fun y z => hβ _ _) (p₀ x) (q' x) (p x) ((hq' x).1.trans (congrArg I.e (hp x)))
    (homComp_rel _ _ _ _ (hp' x) (hq' x).2) (hp'' x)
  refine ⟨fun x => ?_, fun qz' pz a b c => ⟨(J.lam * J.h q₀.1.2.b ^ (m ^ 2))⁻¹ * t' ^ s, fun x => ?_⟩⟩
  · rw [(key x).1, hJ, Units.val_one, one_mul]; rfl
  · have := (key x).2 q₀ qz' pz (a.trans (congrArg I.e hz)) (homComp_rel _ _ _ _ hz' b) c s (Int.self_le_toNat _)
    rw [Units.val_mul, mul_assoc, Units.val_pow_eq_pow_val, this, Units.inv_mul_cancel_left]; rfl

end GlobalTheory.ArcSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymPmaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibSym
open GlobalTheory.FrameValue GlobalTheory.TorusExt GlobalTheory.DegPull

theorem vF_down {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ} {u : HolUnif A L' g} (hL' : L'.IsLB)
    {X Y Y' : Scheme.{0}} {L : LB X} {Φ : A.left ⟶ X} {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)}
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {y : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' y z) :
    vF t (y ≫ h) J = genVal u hL' a y z * ∏ k, (fr (z k) : ℂ) ^ ε k := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : ∀ q : Sp ℂ, Good L q J := fun q ψ => hJ ψ trivial
  have gJ' : ∀ q : Sp ℂ, Good L' q (chartAt hL') := fun q ψ => le_chartAt hL' ψ trivial
  have key : ∀ {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ), ⊤ ≤ x ⁻¹ᵁ U →
      (gm x p U f).val = stalkConst p (valAt' x U f.val) := fun x U f hU =>
    (gs_unit x p U (hU trivial) f).symm.trans (gs_eq_stalkConst x p hU _)
  have e := congrArg Units.val (pmaps_val hψ H y p (gJ p) (gJ' p))
  have e₁ : (val t (y ≫ h) p J).val = stalkConst p (vF t (y ≫ h) J) :=
    key _ _ _ (fun q _ => (gJ q).mem φ (y ≫ h))
  have e₂ : (val a y p (chartAt hL')).val = stalkConst p (genVal u hL' a y z *
      frameProd u ε z fun k => chartAt hL' (y ≫ φ' k)) :=
    (key _ _ _ (le_wchart_chartAt hL' φ' y)).trans (congrArg _ (valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' y)))
  have hm : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ ((L.pull Φ).U (fun _ => J (x ≫ Φ)) ⊓ L'.U (chartAt hL' x)) :=
    fun x q _ => ⟨mem_pull.2 (gJ q (x ≫ Φ)), gJ' q x⟩
  have e₃ : ∀ x : Sp ℂ ⟶ A.left, Geo.Tor.gw w x p (J (x ≫ Φ)) (chartAt hL' x) = stalkUnits p
      (Units.mk0 (valAt' x _ (w.s (fun _ => J (x ≫ Φ), chartAt hL' x)).val)
        (CubeValues.val_unit_ne_zero x SymmetricSemicharacter.valueRules (hm x) _)) := fun x =>
    Units.ext (key x _ _ (hm x))
  rw [Units.val_mul, e₁, e₂] at e
  simp only [e₃, ← map_zpow, ← map_prod] at e
  rw [stalkUnits_val, ← map_mul] at e
  rw [(stalkConst p).injective e, mul_left_comm, frameProd, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, hfr (z k) _ (le_chartAt hL' _)]
  rfl

theorem exists_sym_pmaps {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') ∧
      (∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k) ∧ PMaps w _ _ _ s' s F := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_, hψ, H⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

theorem fibSymSt : Laws → FibSymSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, -, -, -, hex, hfr⟩ := hF
  obtain ⟨s, hs, hr, hψ, H⟩ := exists_sym_pmaps gp D.P.isLB P'.isLB ((isGen_iff w).1 hw) D.sym D.sym_gen D.sym_rig
  obtain ⟨h₁, h₂⟩ := genVal_sym P'.isLB hAH s hs hr
  refine ⟨fun x => ?_, h₂⟩
  have e := vF_down P'.isLB hψ hs H hJ (fr := fr) (fun z i hi => hex z ▸ hfr z i hi) (isLift_sym u x)
  rw [h₁, Fin.prod_univ_two] at e
  rw [hex x]
  refine (congrArg (· * (fr x : ℂ)) e).trans ?_
  simp

end GlobalTheory.Ex.Arch.FibSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis.AllExt

open GlobalTheory.FramePull GlobalTheory.ConstFam

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

theorem exists_cmp_inv (hF : IsPullback F G.hom G₀.hom π) {T : Over Z} {T₀ : Over S} {u : T.left ⟶ T₀.left}
    {v : T₀.left ⟶ T.left} (huv : u ≫ v = 𝟙 _) (hvu : v ≫ u = 𝟙 _) (hu : u ≫ T₀.hom = T.hom ≫ π)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left ∧
        Ψ ≫ Φ = 𝟙 _ ∧ Φ ≫ Ψ = 𝟙 _ := by
  have w₀ : (snd T₀ G₀).left ≫ G₀.hom = (((fst T₀ G₀).left ≫ v) ≫ T.hom) ≫ π := by
    rw [Category.assoc, Category.assoc, ← hu, reassoc_of% hvu, Over.w, Over.w]
  obtain ⟨Ψ, c₁, c₂⟩ : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left = hF.lift _ _ w₀ :=
    ⟨pullback.lift ((fst T₀ G₀).left ≫ v) (hF.lift _ _ w₀) (hF.lift_snd _ _ w₀).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have c₃ : Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left := by
    rw [reassoc_of% c₂, hF.lift_fst]
  refine ⟨Ψ, c₁, c₃, FramePull.prod_ext ?_ ?_, FramePull.prod_ext ?_ ?_⟩
  · rw [Category.assoc, a₁, reassoc_of% c₁, hvu, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, a₂, c₃, Category.id_comp]
  · rw [Category.assoc, c₁, reassoc_of% a₁, huv, Category.id_comp, Category.comp_id]
  · rw [Category.id_comp]
    apply hF.hom_ext
    · rw [Category.assoc, Category.assoc, c₃, a₂]
    · rw [Category.assoc, Category.assoc, reassoc_of% c₂, hF.lift_snd, reassoc_of% a₁,
        reassoc_of% huv, Over.w, Over.w]

theorem basis_up (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}}
    {χ : V ⟶ Z} {χ₀ : V ⟶ S} (hχ : χ₀ = χ ≫ π) {T : Over Z} {T₀ : Over S} {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀}
    {u : T.left ⟶ T₀.left} (e : h₀.left = h.left ≫ u)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)}
    (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) (H : BasisAlong G L N h b) : BasisAlong G₀ L₀ N h₀ b₀ := by
  have hu : 𝟙 V ≫ (Over.mk χ₀).hom = (Over.mk χ).hom ≫ π := (Category.id_comp _).trans hχ
  obtain ⟨Φ', b₁, b₂⟩ := exists_cmp hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (𝟙 V) hu
  obtain ⟨Ψ, c₁, c₃, i₁, i₂⟩ := exists_cmp_inv hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (u := 𝟙 V) (v := 𝟙 V)
    (Category.id_comp _) (Category.id_comp _) hu b₁ b₂
  have hc := cmp_comm (h := h) (h₀ := h₀) a₁ a₂ b₁ b₂ ((Category.id_comp _).trans e)
  replace b₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left := b₁.trans (Category.comp_id _)
  replace c₁ : Ψ ≫ (fst (Over.mk χ) G).left = (fst (Over.mk χ₀) G₀).left := c₁.trans (Category.comp_id _)
  intro s₀
  obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL b₂ s₀
  refine (existsUnique_congr fun c => ?_).2 (H s)
  rw [FramePull.lin_iff, FramePull.lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ') z J₀ hJ₀
    rw [Category.assoc r Φ' (fst (Over.mk χ₀) G₀).left, b₁] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ Ψ) z hJ₀ hJ _).2 (H W (r ≫ Ψ) z J hJ)
    rw [Category.assoc r Ψ Φ', i₁, Category.comp_id, Category.assoc r Ψ, c₁] at this
    exact this

theorem exists_allBasis : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  intro hL _ Z G₀ _ L₀ hL₀ K _ x A φ w gp hw k hk
  obtain ⟨U, hU, b, hb⟩ := PolFrames.exists_local_basisAlong k hL.secBaseChange A hk (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have huv : (⊤ : (Sp K).Opens).ι ≫ (Sp K).topIso.inv = 𝟙 _ := (Sp K).topIso.hom_inv_id
  have hvu : (Sp K).topIso.inv ≫ (⊤ : (Sp K).Opens).ι = 𝟙 _ := (Sp K).topIso.inv_hom_id
  obtain ⟨Φ, a₁, a₂⟩ := exists_cmp gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    (⊤ : (Sp K).Opens).ι rfl
  obtain ⟨Ψ, -, c₃, -, i₂⟩ := exists_cmp_inv gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    huv hvu rfl a₁ a₂
  choose τ hτ using fun i => exists_thr_up hw hL₀ A.isLB c₃ i₂ (b i)
  refine ⟨_, τ, fun K' _ ga x' h => ?_⟩
  have e : spMap ga = (spMap ga ≫ (Sp K).topIso.inv) ≫ (⊤ : (Sp K).Opens).ι := by
    rw [Category.assoc, hvu, Category.comp_id]
  exact basis_up gp.1 hw hL₀ A.isLB (h.symm.trans (congrArg (· ≫ x) e)) e a₁ a₂ hτ
    (hb K' (spMap ga ≫ (Sp K).topIso.inv))

end GlobalTheory.OneBasis.AllExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibLieOfLaws
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

open GlobalTheory.PointUnif GlobalTheory.EigenSplit in

theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
end

