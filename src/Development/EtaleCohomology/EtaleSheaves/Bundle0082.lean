import Development.EtaleCohomology.EtaleSheaves.Bundle0079
import Development.EtaleCohomology.EtaleSheaves.Bundle0081
import Development.EtaleCohomology.EtaleSheaves.Bundle0080

-- bundled from Development.EtaleCohomology.EtaleSheaves.FMrangePfQc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GeoProof
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.GeoProof
open LateralTheory.E.E4 LateralTheory.E.Bridge_yfiPf

theorem affNbhd {B : Scheme.{0}} (U : B.Etale) (u : U.left) :
    ∃ (U' : B.Etale) (a : U' ⟶ U) (R : CommRingCat.{0}) (_ : U'.left ≅ Spec R) (u' : U'.left), a.left u' = u := by
  let f := U.left.affineCover.f (U.left.affineCover.idx u)
  have : IsOpenImmersion f := U.left.affineCover.map_prop _
  refine ⟨Scheme.Etale.mk (f ≫ U.hom), MorphismProperty.Over.homMk f rfl trivial, _, Iso.refl _, ?_⟩
  exact U.left.affineCover.covers u

def AffGeo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (R : CommRingCat.{0}) (_ : U.left ≅ Spec R) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Shrink : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale)
  (a : U' ⟶ U) (m : ℤ) (u' : U'.left), Sys q i p ι U' m u' → Nonempty (Sys q i p ι U m (a.left u'))

theorem Geo_of (hA : AffGeo) (hS : Shrink) : Geo := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m u
  obtain ⟨U', a, R, e, u', rfl⟩ := affNbhd U u
  obtain ⟨S⟩ := hA hH q k hq i toK ι p hp U' R e m u'
  exact hS q i p ι U U' a m u' S

end LateralTheory.E.GeoProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GluedCurveChartOverlapIsPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemLiftOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.IdempotentLifting

abbrev Aq : Type := AdjoinRoot (X ^ 2 - X : ℤ[X])

lemma monic_q : (X ^ 2 - X : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_sub
  rw [degree_X]; decide

lemma integral_q : (algebraMap ℤ Aq).IsIntegral := by
  have := monic_q.finite_adjoinRoot
  exact fun x => Algebra.IsIntegral.isIntegral x

def toW {W : Type} [CommRing W] (e : W) (he : IsIdempotentElem e) : Aq →+* W :=
  AdjoinRoot.lift (Int.castRingHom W) e (by simp [sq, he.eq])

theorem IdemLift_of : IdemLift := by
  intro P _ _ W _ w _ e he
  let Z : Scheme.{0} := Spec (CommRingCat.of Aq)
  let t : Z ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Aq))
  have : IsIntegralHom t := IsIntegralHom.SpecMap_iff.2 integral_q
  let g : Spec (CommRingCat.of W) ⟶ Z := Spec.map (CommRingCat.ofHom (toW e he))
  let f₁ : Spec (CommRingCat.of W) ⟶ pullback (specZIsTerminal.from P) t :=
    pullback.lift w g (specZIsTerminal.hom_ext _ _)
  have H : w = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  let d := w.normalizationDesc f₁ (pullback.fst _ _) H
  let r : Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Aq)).inv (AdjoinRoot.root _)
  refine ⟨d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r), ?_⟩
  have key : w.toNormalization ≫ d ≫ pullback.snd (specZIsTerminal.from P) t = g := by
    rw [← Category.assoc, w.toNormalization_normalizationDesc, pullback.lift_snd]
  have h1 : w.toNormalization.appTop (d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r)) =
      g.appTop r := by
    rw [← key]; simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom (g.appTop r) = e := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp [r, toW, AdjoinRoot.lift_root]
  unfold phi
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg _ h1).trans h2

end LateralTheory.E.IdempotentLifting
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfDelta
section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (P : Ideal B) [P.IsPrime]

def delta0 (hIP : I ≤ P) : I →ₗ[B] P.ResidueField ⊗[B] Ω[B⁄A] where
  toFun x := (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)
  map_add' x y := by simp [TensorProduct.tmul_add]
  map_smul' b x := by
    simp only [SetLike.val_smul, smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, RingHom.id_apply]
    have : (1 : P.ResidueField) ⊗ₜ[B] ((x : B) • KaehlerDifferential.D A B b) = 0 := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP x.2), TensorProduct.zero_tmul]
    rw [this, add_zero, TensorProduct.tmul_smul]

def delta (hIP : I ≤ P) : P.ResidueField ⊗[B] I →ₗ[P.ResidueField] P.ResidueField ⊗[B] Ω[B⁄A] :=
  LinearMap.liftBaseChange P.ResidueField (delta0 (A := A) I P hIP)

theorem delta_tmul (hIP : I ≤ P) (k : P.ResidueField) (x : I) :
    delta (A := A) I P hIP (k ⊗ₜ x) = k • ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  simp [delta, delta0]

def cot (hIP : I ≤ P) : (RingHom.ker (algebraMap B (B ⧸ I))).Cotangent →ₗ[B] P.ResidueField ⊗[B] I :=
  Submodule.liftQ _ ((TensorProduct.mk B P.ResidueField I 1) ∘ₗ
    Submodule.inclusion (p := RingHom.ker (algebraMap B (B ⧸ I))) (p' := I)
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx))) (by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.map_smul_of_tower]
      rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr (hIP (Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp ha))),
        TensorProduct.zero_tmul]
    · intro x y hx hy; exact add_mem hx hy)

theorem delta_injective (n m : ℕ) (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) (hIP : I ≤ P) :
    Function.Injective (delta (A := A) I P hIP) := by
  obtain ⟨l, hl⟩ := conormal_retraction I n m hB hBI
  let ρ0 : Ω[B⁄A] →ₗ[B] P.ResidueField ⊗[B] I :=
    cot I P hIP ∘ₗ (l.restrictScalars B) ∘ₗ TensorProduct.mk B (B ⧸ I) Ω[B⁄A] 1
  let ρ := LinearMap.liftBaseChange P.ResidueField ρ0
  have h1 : ∀ x : I, ρ ((1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) =
      (1 : P.ResidueField) ⊗ₜ[B] x := by
    intro x
    have hx : (x : B) ∈ RingHom.ker (algebraMap B (B ⧸ I)) :=
      RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr x.2)
    have e1 : (1 : B ⧸ I) ⊗ₜ[B] KaehlerDifferential.D A B (x : B) =
        KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)
          ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩) :=
      (KaehlerDifferential.kerCotangentToTensor_toCotangent A B (B ⧸ I) ⟨x, hx⟩).symm
    have e2 := LinearMap.congr_fun hl ((RingHom.ker (algebraMap B (B ⧸ I))).toCotangent ⟨x, hx⟩)
    simp only [ρ, ρ0, LinearMap.liftBaseChange_tmul, one_smul, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.coe_restrictScalars]
    rw [e1]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at e2
    rw [e2]
    rfl
  have key : ∀ z, ρ (delta (A := A) I P hIP z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k x =>
      rw [delta_tmul, LinearMap.map_smul, h1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective key

theorem range_delta (hIP : I ≤ P) : LinearMap.range (delta (A := A) I P hIP) =
    Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B)) := by
  rw [LinearMap.range_eq_map, ← span_one_tmul (M := I) P, Submodule.map_span, ← Set.range_comp]
  congr 1; ext; simp [delta_tmul]

def LeafResSpanD : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P →
    FiniteDimensional P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ∧
    Module.finrank P.ResidueField (Submodule.span P.ResidueField (Set.range fun x : I =>
      (1 : P.ResidueField) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))) ≤ d

theorem LeafResDimI_of (hS : LeafResSpanD) : LeafResDimI := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨hfin, hle⟩ := hS d e A B I hB hBI P hIP
  have hinj := delta_injective (A := A) I P _ _ hB hBI hIP
  have e := LinearEquiv.ofInjective _ hinj
  rw [range_delta] at e
  have : FiniteDimensional P.ResidueField (P.ResidueField ⊗[B] I) := LinearEquiv.finiteDimensional e.symm
  rw [e.finrank_eq]; exact hle

theorem LeafCoordsPointRes_of'' (hS : LeafResSpanD) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of' (LeafResDimI_of hS) hY

end LateralTheory.E.LeafCoordsPointResPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfFP
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafGlueTwoPf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPfFP

def LeafPushoutQS : Prop := ∀ {DW DU DV : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV], CompactSpace DW → QuasiSeparatedSpace DW → QuasiSeparatedSpace DU →
    QuasiSeparatedSpace DV → QuasiSeparatedSpace (pushout φU φV : Scheme.{0})

set_option backward.isDefEq.respectTransparency false in
theorem pushout_finitePresentation_of_quasiSeparated (hQ : LeafPushoutQS) : LeafPushoutFP := by
  intro DW DU DV S φU φV _ _ qU qV h hS ⟨l1, c1, s1⟩ ⟨l2, c2, s2⟩ ⟨l3, c3, s3⟩
  have : CompactSpace DU := QuasiCompact.compactSpace_of_compactSpace qU
  have : CompactSpace DV := QuasiCompact.compactSpace_of_compactSpace qV
  have : CompactSpace DW := QuasiCompact.compactSpace_of_compactSpace (φU ≫ qU)
  have : QuasiSeparatedSpace DU := quasiSeparatedSpace_of_quasiSeparated qU
  have : QuasiSeparatedSpace DV := quasiSeparatedSpace_of_quasiSeparated qV
  have : QuasiSeparatedSpace DW := quasiSeparatedSpace_of_quasiSeparated (φU ≫ qU)
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  let T : Bool → Scheme.{0} := fun i => Bool.rec DU DV i
  let t : ∀ i, T i ⟶ pushout φU φV := fun i => Bool.rec (motive := fun i => T i ⟶ pushout φU φV)
    (pushout.inl φU φV) (pushout.inr φU φV) i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : (pushout φU φV).OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases pushout_cover φU φV x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have hL : LocallyOfFinitePresentation (pushout.desc qU qV h) := by
    refine IsZariskiLocalAtSource.of_openCover 𝒰 ?_
    rintro (_ | _)
    · change LocallyOfFinitePresentation (pushout.inl φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inl_desc]; exact l1
    · change LocallyOfFinitePresentation (pushout.inr φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inr_desc]; exact l2
  have hC : CompactSpace (pushout φU φV : Scheme.{0}) := by
    refine ⟨?_⟩
    have hu : (Set.univ : Set (pushout φU φV : Scheme.{0})) =
        Set.range (pushout.inl φU φV) ∪ Set.range (pushout.inr φU φV) := by
      ext x; simpa using pushout_cover φU φV x
    rw [hu]
    exact (isCompact_range (pushout.inl φU φV).continuous).union (isCompact_range (pushout.inr φU φV).continuous)
  have hQS := hQ φU φV inferInstance inferInstance inferInstance inferInstance
  exact ⟨hL, inferInstance, inferInstance⟩

end LateralTheory.E.LeafGlueTwoPfFP

theorem LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' (hQ : LateralTheory.E.LeafGlueTwoPfFP.LeafPushoutQS) :
    LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf

namespace LateralTheory.E.LeafInclPiecePf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') : incl h1' ≫ incl h1 = incl h := by
  simp only [incl]
  rw [← Spec.map_comp]
  rfl

def lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {D : Scheme.{0}} (q : D ⟶ Sp R) : pullback q (incl h) ⟶ pullback q (incl h1) :=
  pullback.lift (pullback.fst q (incl h)) (pullback.snd q (incl h) ≫ incl h1') (by
    rw [pullback.condition, Category.assoc, incl_comp h1 h h1'])

def descMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {DU DW : Scheme.{0}} (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R)
    (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1)) (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)) :
    pullback qW (incl h) ⟶ pullback qU (incl h) :=
  pullback.lift (lvl h1 h h1' qW ≫ ψ ≫ pullback.fst qU (incl h1)) (pullback.snd qW (incl h)) (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hψ, lvl, pullback.lift_snd_assoc, Category.assoc, incl_comp h1 h h1'])

theorem bcLift_lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ lvl h1 h h1' q = bcLift h1 w := by
  apply pullback.hom_ext
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_eq]

def LeafInclMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧
      ∃ ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1),
        ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1) ∧
        bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w

def LeafInclOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R))
    (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG →
    ∀ (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1))
      (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)),
      bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w →
    ∃ R' : Subalgebra k Ω, R1 ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R'') (h1' : R1 ≤ R''), R' ≤ R'' →
      IsOpenImmersion (descMap h1 h h1' qU qW ψ hψ)

theorem LeafInclPiece_of (hA : LeafInclMap) (hB : LeafInclOpen) : LeafInclPiece := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, ψ, hψ, hc⟩ := hA k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R', h1R', hR', H⟩ := hB k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW R1 h1 hR1 ψ hψ hc
  refine ⟨R', h1.trans h1R', hR', fun R'' h hR'' => ?_⟩
  have h1' : R1 ≤ R'' := h1R'.trans hR''
  refine ⟨descMap h1 h h1' qU qW ψ hψ, H R'' h h1' hR'', pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [descMap, Category.assoc, pullback.lift_fst]
    rw [reassoc_of% (bcLift_lvl h1 h h1' hW.w), reassoc_of% hc]
    unfold bcLift
    erw [pullback.lift_fst, pullback.lift_fst]
  · simp only [descMap, Category.assoc, pullback.lift_snd]
    unfold bcLift
    erw [pullback.lift_snd, pullback.lift_snd]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end LateralTheory.E.LeafInclPiecePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

theorem LeafTw0LocSplit_of (h1 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen) (h2 : LeafTw0TwFree) :
    LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit :=
  LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of h1 (LeafTw0GenFree_of h2)

end LateralTheory.E.LeafTw0LocSplitPfM
end
end

