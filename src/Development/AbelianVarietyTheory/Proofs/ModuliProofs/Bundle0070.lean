import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinimalAndDimLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.FullLevel.lft_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem krullDim_zeroLocus_le_of_isEmbedding {S T : Type} [CommRing S] [CommRing T]
    (f : PrimeSpectrum S → PrimeSpectrum T) (hf : Topology.IsEmbedding f) (p : PrimeSpectrum S) :
    Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set S)) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus ((f p).asIdeal : Set T)) := by
  have hle : ∀ a b, f a ≤ f b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hf.isInducing.specializes_iff]
  refine Order.krullDim_le_of_strictMono (fun a => ⟨f a.1, ?_⟩) ?_
  · have ha : p ≤ a.1 := by
      have := a.2
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
      exact this
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact (hle p a.1).2 ha
  · refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · exact (hle a.1 b.1).2 hab
    · exact Subtype.ext (hf.injective (congrArg Subtype.val hab))

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.FullLevel.dim_generic_chart {o K : Type} [CommRing o] [IsDomain o] [Field K]
    [Algebra o K] [IsFractionRing o K]
    {U : Scheme.{0}} (s : U ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp o) (d : WithBot ℕ∞)
    (h : ∀ (R : Type) [CommRing R] [Algebra o R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ U), IsOpenImmersion x →
      x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o R) →
      ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), d ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (R : Type) [CommRing R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)))
    [IsOpenImmersion x]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : d ≤ ringKrullDim (R ⧸ q) := by
  classical
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors o)
  let pr := pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))
  have hpr : Topology.IsEmbedding pr := IsPreimmersion.isEmbedding pr
  let y₀ : PrimeSpectrum R := ⟨q, hq.1.1⟩
  obtain ⟨O, hO, hOx⟩ := hpr.isInducing.isOpen_iff.1 x.isOpenEmbedding.isOpen_range
  have hyO : pr (x y₀) ∈ O := by
    have : x y₀ ∈ pr ⁻¹' O := hOx ▸ ⟨y₀, rfl⟩
    exact this
  obtain ⟨V, hV, hyV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 U.isBasis_affineOpens
    (show pr (x y₀) ∈ (⟨O, hO⟩ : TopologicalSpace.Opens U) from hyO)
  have hVa : IsAffineOpen V := hV
  let A : Type := Γ(U, V)
  let j : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ U := hVa.fromSpec
  haveI : IsOpenImmersion j := hVa.isOpenImmersion_fromSpec
  letI : Algebra o A := (Spec.preimage (j ≫ s)).hom.toAlgebra
  have hjs : j ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o A) := by
    rw [RingHom.algebraMap_toAlgebra]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  have hbound := h A j inferInstance hjs
  let e : A ⊗[o] K ≃ₐ[o] FractionRing o ⊗[o] A :=
    (Algebra.TensorProduct.comm o A K).trans
      (Algebra.TensorProduct.congr (IsLocalization.algEquiv (nonZeroDivisors o) K (FractionRing o))
        AlgEquiv.refl)
  let I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing o ⊗[o] A) ≅ pullback j pr :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom) ≪≫ (pullbackSpecIso o A K).symm ≪≫
      (pullback.congrHom hjs rfl).symm ≪≫ (pullbackRightPullbackFstIso s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) j).symm
  let F := I.hom ≫ pullback.snd j pr
  have hF : ∀ w, F w = pullback.snd j pr (I.hom w) := fun w => rfl
  have hrange : Set.range F ⊆ Set.range x := by
    rintro _ ⟨w, rfl⟩
    rw [← hOx]
    have hmem : pullback.snd j pr (I.hom w) ∈ Set.range (pullback.snd j pr) := ⟨_, rfl⟩
    rw [IsOpenImmersion.range_pullbackSnd] at hmem
    have hmem' : pr (pullback.snd j pr (I.hom w)) ∈ j.opensRange := hmem
    rw [hVa.opensRange_fromSpec] at hmem'
    show pr (F w) ∈ O
    rw [hF]
    exact hVO hmem'
  have hy : x y₀ ∈ Set.range F := by
    have : x y₀ ∈ Set.range (pullback.snd j pr) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      show pr (x y₀) ∈ j.opensRange
      rw [hVa.opensRange_fromSpec]
      exact hyV
    obtain ⟨p, hp⟩ := this
    refine ⟨I.inv p, ?_⟩
    show (I.inv ≫ I.hom ≫ pullback.snd j pr) p = _
    rw [Iso.inv_hom_id_assoc, hp]
  obtain ⟨z, hz⟩ := hy
  let g := IsOpenImmersion.lift x F hrange
  have hg : g ≫ x = F := IsOpenImmersion.lift_fac x F hrange
  haveI : IsOpenImmersion g := by
    haveI : IsOpenImmersion (g ≫ x) := hg ▸ inferInstance
    exact IsOpenImmersion.of_comp g x
  let gf : PrimeSpectrum (FractionRing o ⊗[o] A) → PrimeSpectrum R := fun a => g a
  have hgemb : Topology.IsEmbedding gf := g.isOpenEmbedding.isEmbedding
  have hgz : gf z = y₀ := x.isOpenEmbedding.injective (by
    show x (g z) = x y₀
    rw [← Scheme.Hom.comp_apply, hg, hz])
  have hle : ∀ a b, gf a ≤ gf b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hgemb.isInducing.specializes_iff]
  have hzmin : z.asIdeal ∈ minimalPrimes (FractionRing o ⊗[o] A) := by
    refine ⟨⟨z.isPrime, bot_le⟩, fun p' hp' hp'le => ?_⟩
    let w : PrimeSpectrum (FractionRing o ⊗[o] A) := ⟨p', hp'.1⟩
    have hwz : w ≤ z := hp'le
    have h1 : gf w ≤ y₀ := hgz ▸ (hle w z).2 hwz
    have h2 : y₀ ≤ gf w := hq.2 ⟨(gf w).isPrime, bot_le⟩ h1
    exact (hle z w).1 (hgz ▸ h2)
  have hq' : (gf z).asIdeal = q := congrArg PrimeSpectrum.asIdeal hgz
  calc d ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ z.asIdeal) := hbound _ hzmin
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (z.asIdeal : Set (FractionRing o ⊗[o] A))) :=
      ringKrullDim_quotient _
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus ((gf z).asIdeal : Set R)) :=
      krullDim_zeroLocus_le_of_isEmbedding gf hgemb z
    _ = ringKrullDim (R ⧸ q) := by rw [hq', ringKrullDim_quotient]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom {k K : Type} [Field k] [CharZero k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : CharZero K :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem isNilpotent_ker_fstHom_dualNumber {K : Type} [Field K] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hr hs
  rw [Ideal.mem_bot]
  ext <;> simp [hr, hs]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.FullLevel.eq_constPt {k K : Type} [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt x := by
  have hK : CharZero K :=
    _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ x)
  haveI : Algebra.IsSeparable ℚ k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified ℚ k := Algebra.FormallyUnramified.of_isSeparable ℚ k
  obtain ⟨φ, rfl⟩ : ∃ φ : k →+* DualNumber K, x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    ⟨(Spec.preimage x).hom, by simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]⟩
  let ψ : k →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)
  have hψ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ψ, ← Spec.map_comp]; rfl
  rw [hψ]
  congr 1
  have key := Algebra.FormallyUnramified.ext (R := ℚ) (A := k) (B := DualNumber K)
    (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) isNilpotent_ker_fstHom_dualNumber
    (g₁ := φ.toRatAlgHom) (g₂ := ψ.toRatAlgHom) ?_
  · exact congrArg AlgHom.toRingHom key
  · intro a
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp [ψ, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.ZM.FullLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PartialCocycle

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem gm_iso {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
  have h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b := inf_le_left
  have h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b' := inf_le_right
  have h1 := hw (a, b) (a', b')
  calc gm f z (M.U a ⊓ L.U b) (w.s (a, b))
      = gm f z _ (res h₁ (w.s (a, b))) := (gm_res_eq_gm f z h₁ hz _).symm
    _ = gm f z _ (res h₂ (M.g a a') * (res h₃ (L.g b b'))⁻¹ * res h₄ (w.s (a', b'))) := congrArg _ h1
    _ = _ := by
      rw [map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]
      exact congrArg _ (gm_res_eq_gm f z h₄ hz _)

private theorem algebraMap_OmS_eq_algebraMap_comp {G : Type*} [CommGroup G] (A B C s t u : G) :
    A * B⁻¹ * s * (B * C⁻¹ * t) * (A * C⁻¹ * u)⁻¹ = s * t * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gm_val_eq_germ_app' {X Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (U : X.Opens) (hz : g z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm g z U u : Z.presheaf.stalk z)) = Z.presheaf.germ (g ⁻¹ᵁ U) z hz (g.app U u.val) := by
  unfold gm
  rw [dif_pos hz]
  rfl

private theorem gm_id_val_eq_germ' {X : Scheme.{0}} (z : X) (U : X.Opens) (hz : z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm (𝟙 X) z U u : X.presheaf.stalk z)) = X.presheaf.germ U z hz u.val := by
  exact gm_val_eq_germ_app' (𝟙 X) z U hz u

theorem cocycle_of_rigid : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  intro X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc
  let T : M₁.ι × M₂.ι × M₃.ι → X.Opens := fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2
  have l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1 := fun i => inf_le_left
  have l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let t : ∀ i, Γ(X, T i)ˣ := fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) *
    (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹
  have hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) =
      gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) *
        (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹ := by
    intro Z g z i hz
    simp only [t, map_mul, map_inv]
    exact congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _))
      (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))
  have hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j),
      gm g z (T i) (t i) = gm g z (T j) (t j) := by
    intro Z g z i j hi hj
    rw [hprod g z i hi, hprod g z j hj]
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3,
      gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]
    exact algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val) := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) =
      X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]
    exact congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat
  have hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have m1 : x ∈ ⨆ a, M₁.U a := by rw [hU₁]; exact h1
    have m2 : x ∈ ⨆ a, M₂.U a := by rw [hU₂]; exact h2
    have m3 : x ∈ ⨆ a, M₃.U a := by rw [hU₃]; exact h3
    obtain ⟨a₁, ha₁⟩ := TopologicalSpace.Opens.mem_iSup.1 m1
    obtain ⟨a₂, ha₂⟩ := TopologicalSpace.Opens.mem_iSup.1 m2
    obtain ⟨a₃, ha₃⟩ := TopologicalSpace.Opens.mem_iSup.1 m3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
  have hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := by
    intro x hx
    show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃
    rw [hep]
    exact hx
  let u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := X.presheaf.map (homOfLE hcov).op s
  have hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T),
      X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val := by
    intro i z hz hz'
    have h := hs i
    dsimp only at h
    rw [← h]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm
  have hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1 := by
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    have hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := hV hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov hex)
    show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1
    rw [map_one]
    have k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx =
        X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have k2 := congrArg (fun g => g.hom u) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k2
    rw [k2]
    have hg1 : gm e x (T i) (t i) = 1 := by
      rw [hprod e x i hi]
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rw [hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]
    rw [← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]
    simp only [u]
    erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]
  have hu : u = 1 := hrig _ u hV hu1
  have hyT : y ∈ T (a, b, c) := ⟨⟨hya, hyb⟩, hyc⟩
  have hyS : y ∈ iSup T := TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩
  have fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1 := by
    apply Units.ext
    rw [gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]
    have hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := (le_iSup M₁.U a) hya
        rw [hU₁] at this
        exact this
      · have := (le_iSup M₂.U b) hyb
        rw [hU₂] at this
        exact this
      · have := (le_iSup M₃.U c) hyc
        rw [hU₃] at this
        exact this
    have k3 := congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu
    simp only [u, map_one] at k3
    erw [TopCat.Presheaf.germ_res_apply] at k3
    exact k3
  rw [hprod (𝟙 X) y (a, b, c) hyT] at fin
  exact mul_inv_eq_one.1 fin

end GlobalTheory.PartialCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  obtain ⟨w, hw⟩ := glue_unit ⊤ L.U (fun _ => le_top) (le_iSup_chart hL) (fun j => t.s j * (t'.s j)⁻¹) (fun i j y hy => by
    rw [← gm_res (𝟙 Y) y (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) hy,
      ← gm_res (𝟙 Y) y (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) hy]
    congr 1
    rw [map_mul, map_mul, map_inv, map_inv, ht i j, ht' i j, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  exact ⟨w, fun j => by rw [hw j, inv_mul_cancel_right]⟩

theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hL := pull_isLB hM x
  obtain ⟨w, hw⟩ := exists_global_unit hL hτ hτ'
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
end

