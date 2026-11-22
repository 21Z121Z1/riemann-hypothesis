import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsSplitField

open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem exists_poly_split_torsion {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] (xK : Sp K ⟶ X) (q : ℕ) (hq : q ≠ 0) :
    ∃ f : Polynomial K, f ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra K L], (f.map (algebraMap K L)).Splits →
      ∀ (Ω : Type) [Field Ω] (j : L →+* Ω) (b : Sp Ω ⟶ X), b = spMap (j.comp (algebraMap K L)) ≫ xK →
        ∀ w : Over.mk b ⟶ t.G, w ^ q = 1 → ∃ w₀ : Sp L ⟶ t.G.left, spMap j ≫ w₀ = w.left := by
  classical
  have hsemi := t.semi
  have := hsemi.quasiCompact
  have := hsemi.separated
  have hLQF : LocallyQuasiFinite (torsion t.G q).hom := (GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq).2
  have hcl : IsClosedImmersion η[t.G].left := by
    have : IsClosedImmersion (η[t.G].left ≫ t.G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ t.G.hom
  have : IsClosedImmersion (torsion.ι t.G q).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GlobalTheory.GrpTangent.isPullback_torsion t.G q).flip hcl
  have hQC : QuasiCompact (torsion t.G q).hom := by
    rw [← Over.w (torsion.ι t.G q)]; infer_instance
  obtain ⟨⟨x0, ψ⟩, hxK⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective xK
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hxK
  have hfib : ((torsion t.G q).hom ⁻¹' {x0}).Finite := (torsion t.G q).hom.finite_preimage_singleton x0
  have hgen : ∀ z : (torsion t.G q).left, letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra;
      ∃ s : Finset ((torsion t.G q).left.residueField z),
        Submodule.span (X.residueField ((torsion t.G q).hom z)) (s : Set ((torsion t.G q).left.residueField z)) = ⊤ := by
    intro z
    letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
    have : Module.Finite (X.residueField ((torsion t.G q).hom z)) ((torsion t.G q).left.residueField z) :=
      GlobalTheory.T.residueFieldMap_finite_of_quasiFinite _ z
    exact Module.Finite.fg_top
  choose s hs using hgen
  have hint : ∀ (z : (torsion t.G q).left) (c : (torsion t.G q).left.residueField z),
      letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra;
      IsIntegral (X.residueField ((torsion t.G q).hom z)) c := by
    intro z c
    letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
    have : Module.Finite (X.residueField ((torsion t.G q).hom z)) ((torsion t.G q).left.residueField z) :=
      GlobalTheory.T.residueFieldMap_finite_of_quasiFinite _ z
    exact Algebra.IsIntegral.isIntegral c
  let P : ∀ z : (torsion t.G q).left, (torsion t.G q).left.residueField z → Polynomial K := fun z c =>
    if h : (torsion t.G q).hom z = x0 then
      letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
      (minpoly (X.residueField ((torsion t.G q).hom z)) c).map ((X.residueFieldCongr h).hom ≫ ψ).hom
    else 1
  obtain ⟨f, hfdef⟩ : ∃ f : Polynomial K, f = ∏ z ∈ hfib.toFinset, ∏ c ∈ s z, P z c := ⟨_, rfl⟩
  have hf0 : f ≠ 0 := by
    rw [hfdef, Finset.prod_ne_zero_iff]; intro z _; rw [Finset.prod_ne_zero_iff]; intro c _
    simp only [P]; split_ifs with h
    · letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
      exact ((minpoly.monic (hint z c)).map _).ne_zero
    · exact one_ne_zero
  refine ⟨f, hf0, ?_⟩
  intro L _ _ hspl Ω _ j b hb w hw
  obtain ⟨v, hv⟩ : ∃ v : Over.mk b ⟶ torsion t.G q, v ≫ torsion.ι t.G q = w :=
    ⟨pullback.lift w (toUnit _) (by rw [GlobalTheory.GrpTangent.comp_mulN, hw, Hom.one_def]), pullback.lift_fst _ _ _⟩
  obtain ⟨⟨z, φ⟩, hvz⟩ := (Scheme.SpecToEquivOfField Ω (torsion t.G q).left).symm.surjective v.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hvz
  have hb' : Spec.map ((torsion t.G q).hom.residueFieldMap z ≫ φ) ≫ X.fromSpecResidueField ((torsion t.G q).hom z) =
      Spec.map (ψ ≫ CommRingCat.ofHom (j.comp (algebraMap K L))) ≫ X.fromSpecResidueField x0 := by
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, hvz]
    have h1 := Over.w v
    simp only [Over.mk_hom] at h1
    rw [h1, hb, Spec.map_comp, Category.assoc, hxK]
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ hb'
  have hzf : z ∈ hfib.toFinset := by simpa using e
  letI := ((torsion t.G q).hom.residueFieldMap z).hom.toAlgebra
  have hcomp : (j.comp (algebraMap K L)).comp ((X.residueFieldCongr e).hom ≫ ψ).hom =
      φ.hom.comp ((torsion t.G q).hom.residueFieldMap z).hom := by
    have := congrArg CommRingCat.Hom.hom he
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
    rw [this]; rfl
  have hroot : ∀ c ∈ s z, φ.hom c ∈ j.fieldRange := by
    intro c hc
    have hP : ((P z c).map (j.comp (algebraMap K L))).IsRoot (φ.hom c) := by
      simp only [P, dif_pos e, Polynomial.map_map]
      rw [hcomp, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← RingHom.algebraMap_toAlgebra
        ((torsion t.G q).hom.residueFieldMap z).hom, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hdvd : P z c ∣ f := by
      rw [hfdef]
      exact (Finset.dvd_prod_of_mem _ hc).trans (Finset.dvd_prod_of_mem (fun z => ∏ c ∈ s z, P z c) hzf)
    have hF : ((f.map (algebraMap K L)).map j).IsRoot (φ.hom c) := by
      rw [Polynomial.map_map]
      exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hP
    exact RingHom.mem_fieldRange.2 (RingHom.mem_range.1 (hspl.mem_range_of_isRoot (Polynomial.map_ne_zero hf0) hF))
  have hall : ∀ c, φ.hom c ∈ j.fieldRange := by
    intro c
    have hc : c ∈ Submodule.span (X.residueField ((torsion t.G q).hom z)) (s z : Set _) := by rw [hs z]; trivial
    induction hc using Submodule.span_induction with
    | mem x hx => exact hroot x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine mul_mem ?_ hx
      have h2 := congrArg (fun h => h a) hcomp
      simp only [RingHom.comp_apply] at h2
      rw [RingHom.algebraMap_toAlgebra, ← h2]
      exact ⟨_, rfl⟩
  let e' := j.rangeRestrictFieldEquiv
  let g' : (torsion t.G q).left.residueField z →+* L := e'.symm.toRingHom.comp (φ.hom.codRestrict j.fieldRange hall)
  have hg' : CommRingCat.ofHom g' ≫ CommRingCat.ofHom j = φ := by
    ext c
    exact congrArg Subtype.val (e'.apply_symm_apply ⟨φ.hom c, hall c⟩)
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ (torsion t.G q).left.fromSpecResidueField z ≫ (torsion.ι t.G q).left, ?_⟩
  rw [← hv, Over.comp_left, ← hvz, spMap, ← Category.assoc, ← Spec.map_comp, hg', Category.assoc]

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem splitTors_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x : Sp A ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ SplitTors t (spMap (algebraMap A A') ≫ x) q := by
  intro E _ _ _ H X _ t A _ _ _ _ _ x q hq
  obtain ⟨f, hf0, hf⟩ := exists_poly_split_torsion t (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ x) q hq
  obtain ⟨A', i1, i2, i3, σ, hfin, hinj, hic, hζ, hspl, hcomm⟩ := GlobalTheory.T.exists_cyclotomic_splitting_extension A f hf0 q hq
  refine ⟨A', i1, i2, i3, hfin, hinj, hic, hζ, ?_⟩
  intro Ω _ io w hw
  letI : Algebra (FractionRing A) (FractionRing A') := σ.toAlgebra
  refine hf (FractionRing A') (by simpa [RingHom.algebraMap_toAlgebra] using hspl) Ω io _ ?_ w hw
  rw [RingHom.algebraMap_toAlgebra, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', RingHom.comp_assoc,
    RingHom.comp_assoc, hcomm]

end GlobalTheory.TorsSplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreExact

theorem locK_mem_of_values : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : IntermediateField ℚ ℂ), GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ), ((χ.locK P k : ℂˣ) : ℂ) ∈ M :=
  fun _ _ _ χ _ hv hi P _ => GlobalTheory.HeckeValField.mem_unitsIn.1 (GlobalTheory.HeckeValField.loc_mem χ hv hi P _)

theorem char_mem_of_values : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ M : IntermediateField ℚ ℂ, GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : D.host.Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ M := by
  intro D c χ hc M hv hi x hx
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => locK_mem_of_values D.host.E χ M hv hi P (k P)

theorem KsC_eq (X : Stages) : X.B.KsC = FO X.toD7 := by
  ext z
  rw [Base.mem_KsC, mem_FO_assembled_iff]

theorem exists_core_exact : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  intro X f hch hv _
  obtain ⟨J, hJ, hC, hCan, hp, hpq, -⟩ := GlobalTheory.FinalJoin2.exists_coreJ_of_chiOK_noVol X.toD7 (hermitianCodeWordStages_ringOfIntegers_full X)
    (hermitianCodeWordStages_has_rootOfUnity X) f.P.pb f.P.pb_over _ (GlobalTheory.FinalJoin.chiOK_one X.toD7)
  have hP : J.Q.PinField := hJ.pins.2.2.1
  letI := Formalism.IndefR.FWT.algTop J hP
  have ha : Formalism.IndefR.FWT.AlgTie J := Formalism.IndefR.FWT.algTie_algTop J hP

  have hemb : ∀ y : J.Q.c.F, X.toD7.what₂.embLL (algebraMap J.Q.c.F X.toD7.what₂.LL y) = (y : ℂ) := by
    have h : X.toD7.what₂.embLL.comp (algebraMap J.Q.c.F X.toD7.what₂.LL) = J.Q.c.F.val.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 J.Q.c.F)) (RingHom.ext fun x =>
        (congrArg X.toD7.what₂.embLL (ha x)).trans (hP x))
    exact fun y => RingHom.congr_fun h y

  have hle : ∀ y : J.Q.c.F, (y : ℂ) ∈ FO X.toD7 := by
    intro y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 J.Q.c.F) y
    have hi : ∀ a : 𝓞 J.Q.c.F, ((a : J.Q.c.F) : ℂ) ∈ FO X.toD7 := fun a => by
      rw [← hP a]
      exact phiO_mem_FO _ _
    rw [IntermediateField.coe_div]
    exact div_mem (hi a) (hi b)
  have hge : ∀ z ∈ FO X.toD7, ∃ y : J.Q.c.F, (y : ℂ) = z := by
    intro z hz
    have hle' : FO X.toD7 ≤ J.Q.c.F := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := J.Q.eO.surjective w
      have h : X.toD7.what₂.phiO (J.Q.eO x) = ((x : J.Q.c.F) : ℂ) := hP x
      rw [h]
      exact (x : J.Q.c.F).2
    exact ⟨⟨z, hle' hz⟩, rfl⟩

  have hback : ∀ z : X.toD7.what₂.LL, X.toD7.what₂.embLL z ∈ FO X.toD7 →
      ∃ y : J.Q.c.F, algebraMap J.Q.c.F X.toD7.what₂.LL y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hge _ hz
    exact ⟨y, X.toD7.what₂.embLL.injective ((hemb y).trans hy)⟩
  refine ⟨J, inferInstance, ⟨hC, hCan, hpq, hp⟩, hemb, fun y => ?_, fun x hx => hback x ?_, fun x => hback _ ?_,
    hJ, ha, hv.toLL, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (mem_FO_assembled_iff X _).1 (hle y)
    have : algebraMap J.Q.c.F X.toD7.what₂.LL y = x := X.toD7.what₂.embLL.injective (((hemb y).trans hx'.symm))
    rw [this]
    exact X.B.Ks_le hx
  · exact (mem_FO_assembled_iff X _).2 ⟨x, hx, rfl⟩
  · rw [show X.toD7.what₂.embLL (X.toD7.embE x) = X.toD7.host.φ₀ x from RingHom.congr_fun X.toD7.embE_φ₀ x]
    exact phi0_mem_coeff_field _ x
  · intro T' L μ hL hLC i x hx
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO X.toD7 := by
      refine char_mem_of_values X.toD7 _ _ (hL.mu0 i) (FO X.toD7) ?_ ?_ x hx
      · rw [hLC, ← KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => (X.toD7.hc (X.toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (conj_mem_FO _ _ _) (conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨y, hy⟩ := hge _ hmem
    exact ⟨y, by rw [hemb, hy]⟩

end GlobalTheory.CoreExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem frMat_self {V U : X.Opens} {n : ℕ} {m : Fin n → Γ(F, V)} (hm : VB.IsFrame m) (h : U ≤ V) :
    frMat hm hm h h = 1 := by
  rw [frMat, Module.Basis.toMatrix_self, Matrix.transpose_one]

theorem frMat_mul {V V' V'' U : X.Opens} {n n' n'' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')}
    {m'' : Fin n'' → Γ(F, V'')} (hm : VB.IsFrame m) (hm' : VB.IsFrame m') (hm'' : VB.IsFrame m'') (h : U ≤ V) (h' : U ≤ V')
    (h'' : U ≤ V'') : frMat hm hm' h h' * frMat hm' hm'' h' h'' = frMat hm hm'' h h'' := by
  rw [frMat, frMat, frMat, ← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix]

theorem resG_frMat {V V' U U' : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (e : U' ≤ U) (l : Fin n) (l' : Fin n') :
    resG X e (frMat hm hm' h h' l l') = frMat hm hm' (e.trans h) (e.trans h') l l' := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, VB.IsFrame.basis_apply]
  rw [← hm'.repr_resM h' e, resM_resM]

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

theorem map_ev_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (g : Z ⟶ X) {B : Z.Opens} (e : B ≤ g ⁻¹ᵁ (V ⊓ V')) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ B) (hU : ⊤ ≤ (z ≫ g) ⁻¹ᵁ U) :
    ((frMat hm hm' inf_le_left inf_le_right).map (g.appLE _ B e).hom).map (ev z B hz) =
      (frMat hm hm' h h').map (ev (z ≫ g) U hU) := by
  ext l l'
  refine (ev_appLE z g e hz (le_preimage_map g e hz) _).trans ?_
  rw [← ev_res (z ≫ g) (le_inf h h') hU, resG_frMat]
  rfl

def frameCoc (g : Z ⟶ X) {A : Type} (B : A → Z.Opens) (aff : ∀ α, IsAffineOpen (B α)) (cover : ∀ x : Z, ∃ α, x ∈ B α)
    {V : A → X.Opens} {n : A → ℕ} {m : ∀ α, Fin (n α) → Γ(F, V α)} (hm : ∀ α, VB.IsFrame (m α))
    (le : ∀ α, B α ≤ g ⁻¹ᵁ V α) : Coc Z where
  A := A
  B := B
  aff := aff
  cover := cover
  n := n
  T α β := (frMat (hm α) (hm β) inf_le_left inf_le_right).map
    (g.appLE _ _ (show B α ⊓ B β ≤ g ⁻¹ᵁ (V α ⊓ V β) from inf_le_inf (le α) (le β))).hom
  refl α S _ z h := by
    rw [map_ev_frMat (hm α) (hm α) le_rfl le_rfl g _ z _ (le_preimage_map g (le α) h), frMat_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  coc α β γ S _ z h₁ h₂ h₃ := by
    have hU : ⊤ ≤ (z ≫ g) ⁻¹ᵁ (V α ⊓ V β ⊓ V γ) := le_preimage_inf (le_preimage_inf (le_preimage_map g (le α) h₁)
      (le_preimage_map g (le β) h₂)) (le_preimage_map g (le γ) h₃)
    have a : V α ⊓ V β ⊓ V γ ≤ V α := inf_le_left.trans inf_le_left
    have b : V α ⊓ V β ⊓ V γ ≤ V β := inf_le_left.trans inf_le_right
    have c : V α ⊓ V β ⊓ V γ ≤ V γ := inf_le_right
    rw [map_ev_frMat (hm α) (hm β) a b g _ z _ hU, map_ev_frMat (hm β) (hm γ) b c g _ z _ hU,
      map_ev_frMat (hm α) (hm γ) a c g _ z _ hU, ← Matrix.map_mul, frMat_mul]

theorem isFrame_incl (N : VB.Sub F) {V U O : X.Opens} {n : ℕ} {m : Fin n → Γ(N.toMod, V)} (hm : VB.IsFrame m)
    (hO : ∀ U : X.Opens, U ≤ O → N.sec U = ⊤) (h : U ≤ V) (h' : U ≤ O) :
    VB.IsFrame fun l => resM F h (N.incl.app V (m l)) :=
  (hm.res h).map_of_linearEquiv
    (fun U' e => LinearEquiv.ofBijective (QCoh.appLinear N.incl U') ⟨N.incl_app_injective U', fun s =>
      N.mem_sec_iff.1 (by rw [hO U' (e.trans h')]; trivial)⟩)
    fun _ e l => (app_resM N.incl e _).trans (congrArg _ (app_resM N.incl h _))

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanLin_tanOf (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V))
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (l : Fin n) :
    tanLin t h s (tanOf hv) l = tanEv t hv h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

theorem tanLin_tr {F : X.Modules} (θ : F ⟶ GlobalTheory.LieVB.omega t.G) {V' : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)}
    {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m) (hm' : VB.IsFrame m') (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ V')
    (v : TanM x t.G) :
    ((frMat hm hm' inf_le_left inf_le_right).map (ev x _ (le_preimage_inf h h'))).mulVec
      (tanLin t h' (fun l => θ.app V' (m' l)) v) = tanLin t h (fun l => θ.app V (m l)) v := by
  funext l
  rw [tanLin_apply, ← tanEv_resM t _ (le_preimage_inf h h') inf_le_left, ← app_resM,
    sum_frMat hm hm' inf_le_left inf_le_right, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, app_resM]
  rw [tanEv_sum_smul]
  simp only [tanEv_resM]
  rfl

theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  exact funext fun l => GlobalTheory.LocM.tanEv_baseChange E H X t S x V h _ (isTan_tv v) S' φ _ h' (s l)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun l => tanEv_resM t _ hU e _⟩)

end Lin

section Phi

variable {X X' X₀ Z : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₀ : SAB H X₀} {τ : X ⟶ X₀} {τ' : X' ⟶ X₀}
  (mu : SABMap t t₀ τ) (mu' : SABMap t' t₀ τ') {π : Z ⟶ X} {g : Z ⟶ X'} (e : g ≫ τ' = π ≫ τ)
  {S : Type} [CommRing S]

def tanTrans (z : Sp S ⟶ Z) : TanM (z ≫ π) t.G ≃ₗ[S] TanM (z ≫ g) t'.G :=
  (pushE mu (z ≫ π) rfl).trans
    (pushE mu' (z ≫ g) (by rw [Category.assoc, Category.assoc, e] : (z ≫ g) ≫ τ' = (z ≫ π) ≫ τ)).symm

theorem left_tanTrans (z : Sp S ⟶ Z) (v : TanM (z ≫ π) t.G) :
    (tv (tanTrans mu mu' e z v)).left ≫ mu'.φ = (tv v).left ≫ mu.φ :=
  congrArg (fun w => (tv w).left) ((pushE mu' (z ≫ g) _).apply_symm_apply (pushE mu (z ≫ π) rfl v))

theorem tanTrans_eq (z : Sp S ⟶ Z) (v : TanM (z ≫ π) t.G) (w : TanM (z ≫ g) t'.G)
    (h : (tv w).left ≫ mu'.φ = (tv v).left ≫ mu.φ) : tanTrans mu mu' e z v = w :=
  (pushE mu' (z ≫ g) rfl).injective (tan_ext ((left_tanTrans mu mu' e z v).trans h.symm))

theorem tanTrans_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ Z) (z' : Sp S' ⟶ Z)
    (e₁ : spMap φ ≫ z ≫ π = z' ≫ π) (e₂ : spMap φ ≫ z ≫ g = z' ≫ g) (v : TanM (z ≫ π) t.G) :
    tanTrans mu mu' e z' (tanPull φ e₁ v) = tanPull φ e₂ (tanTrans mu mu' e z v) :=
  tanTrans_eq mu mu' e z' _ _ (by
    rw [FlagMod.tanPull_left, FlagMod.tanPull_left, Category.assoc, Category.assoc, left_tanTrans])

end Phi

theorem tv_comp_eq_of_isTrans {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}
    {Y : LocalSystem Xo p W} {i₀ i : Idx H p} {Z : Mdl Y i₀} (hc : i.c.F ≤ Z.i.c.F) {τ τ₀ : (Y Z.i).X ⟶ (Y i).X}
    {mu : SABMap (Y Z.i).t (Y i).t τ} {mu₀ : SABMap (Y Z.i).t (Y i).t τ₀} (tr : LocM.IsTrans i Z.i τ mu)
    (tr₀ : LocM.IsTrans i Z.i τ₀ mu₀) {K : Type} [Field K] (z : Sp K ⟶ Z.X) (hz : Set.range z ⊆ Z.opn)
    (v : TanM (z ≫ Z.π) (Y Z.i).t.G) : (tv v).left ≫ mu.φ = (tv v).left ≫ mu₀.φ := by
  obtain ⟨c, φ, hφ⟩ := Z.exists_chart z hz
  obtain ⟨y, hy, -⟩ := CommonMod.exists_lift_chart Z hφ
  exact (TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ₀ mu mu₀ hc tr tr₀).2 K y _ _ (tv v).left
    (by rw [hy]; exact (isTan_tv v).1)

theorem exists_lCrd_isLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X), IsMap Z t.B g → ∃ D : LCrd (Y Z.i) Z.π, IsLat t Z g D := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW t Z g hg
  cases isEmpty_or_nonempty Z.X with
  | inl hZ =>
    let C : Coc Z.X := ⟨Empty, fun a => a.elim, fun a => a.elim, fun x => hZ.elim x, fun a => a.elim, fun a => a.elim,
      fun a => a.elim, fun a => a.elim⟩
    exact ⟨⟨C, 0, ⟨fun a => a.elim, fun a => a.elim, fun a => a.elim⟩, fun a => a.elim, fun a => a.elim, fun a => a.elim,
      fun a => a.elim⟩, fun a => a.elim⟩
  | inr hZ =>
    obtain ⟨x₀, hx₀⟩ := Z.dense.nonempty
    obtain ⟨τ₀, mu₀, -, tr₀, -⟩ := hg.2 (Z.X.residueField x₀) (Z.X.fromSpecResidueField x₀) (by
      rintro _ ⟨a, rfl⟩
      exact (Scheme.fromSpecResidueField_apply x₀ a).symm ▸ hx₀)
    have e := CommonMod.comp_π_eq hg tr₀
    choose V n m hV hm using fun x : Z.X => t.L.free (g x)
    choose B aff hB le using fun x : Z.X => QCoh.exists_affine_mem_le (U := g ⁻¹ᵁ V x) x (hV x)
    have := isDiscreteValuationRing_V Z.i.c W hp hW
    let C₀ := frameCoc g B aff (fun x => ⟨x, hB x⟩) hm le
    obtain ⟨Γ', a, D, aff', cover, le', N, ⟨Em⟩⟩ := Coc.exists_refine_emb _ Z.X _ (geoOf Z).proj C₀
    have lt : ∀ γ, D γ ≤ g ⁻¹ᵁ V (a γ) := fun γ => (le' γ).trans (le _)
    refine ⟨{ C := C₀.refine a D aff' cover le'
              N := N
              Em := Em
              crd := fun γ S _ z h => (tanLin t.B.t (le_preimage_map g (lt γ) h)
                fun l => t.L.N.incl.app _ (m (a γ) l)).comp (tanTrans mu₀ t.B.tMap e z).toLinearMap
              tr := fun γ δ S _ z hγ hδ v => ?_
              bc := fun γ S S' _ _ φ z z' ez h h' e' v => ?_
              inj := fun γ K _ z h hz => ?_ }, fun γ => ⟨V (a γ), m (a γ), lt γ, hm _, ?_⟩⟩
    · rw [C₀.refine_tr a D aff' cover le' γ δ z hγ hδ]
      refine Eq.trans (congrArg (Matrix.mulVec · _) (map_ev_frMat (hm _) (hm _) inf_le_left inf_le_right g _ z _
        (le_preimage_inf (le_preimage_map g (lt γ) hγ) (le_preimage_map g (lt δ) hδ)))) ?_
      exact tanLin_tr t.B.t t.L.N.incl (hm _) (hm _) _ _ _
    · have e₂ : spMap φ ≫ z ≫ g = z' ≫ g := by rw [← Category.assoc, ez]
      exact (congrArg _ (tanTrans_tanPull mu₀ t.B.tMap e φ z z' e' e₂ v)).trans (tanLin_tanPull t.B.t φ e₂ _ _ _ _)
    · have hO : ⊤ ≤ (z ≫ g) ⁻¹ᵁ t.B.genO := le_preimage_map g (CommonMod.preimage_genO g).ge
        fun y _ => CommonMod.mem_genO_of_mem_opn hp.ne_zero Z (hz ⟨y, rfl⟩)
      exact (tanLin_injective t.B.t _ _ inf_le_left (le_preimage_inf (le_preimage_map g (lt γ) h) hO)
        (isFrame_incl t.L.N (hm _) t.L.gen inf_le_left inf_le_right)).comp (tanTrans mu₀ t.B.tMap e z).injective
    · intro τ mu tr K _ z h hz v v' hv' h' hv l
      have u := tv_comp_eq_of_isTrans hg.1.2.1 tr tr₀ z hz v
      have := tanTrans_eq mu₀ t.B.tMap e z v (tanOf hv') (hv.trans u)
      exact (congrFun (congrArg (tanLin t.B.t (le_preimage_map g (lt γ) h)
        fun l => t.L.N.incl.app _ (m (a γ) l)) this) l).trans (tanLin_tanOf t.B.t _ _ hv' l)

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_equation_complex_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∃ (W : C.Y.X → C.Y.X.Opens) (δ : C.Y.X → C.Y.Fnˣ) (a : C.Y.X → CxPts C.Y.str (σ.comp e.toRingHom) → CxFr Z σ), (∀ y, y ∈ W y) ∧ (∀ y, ∀ y' ∈ W y, (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))).IsEqn y' (δ y)) ∧ (∀ y, ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y), (a y p).1.1 = p.1 ≫ C.π) ∧ (∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts C.Y.str (σ.comp e.toRingHom)), IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B (CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y)) → HolFam B (fun b => a y (x b))) ∧ ∀ y y' (U : C.Y.X.Opens) (hU : genericPoint C.Y.X ∈ U) (r : Γ(C.Y.X, U)), fnOf U hU r = (δ y : C.Y.Fn) / (δ y' : C.Y.Fn) → ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y ⊓ W y' ⊓ U), ∃ M N, Chg (a y' p) (a y p) τ M ∧ Chg (a y' p) (a y p) (conjEmb τ) N ∧ M.det ≠ 0 ∧ M.det * CxPts.ev C.Y.str (σ.comp e.toRingHom) U r p = N.det := by
  first | exact @GlobalTheory.ShFam.HolFrames.exists_holFrames | exact GlobalTheory.ShFam.HolFrames.exists_holFrames | (intros; apply GlobalTheory.ShFam.HolFrames.exists_holFrames <;> assumption)
end

