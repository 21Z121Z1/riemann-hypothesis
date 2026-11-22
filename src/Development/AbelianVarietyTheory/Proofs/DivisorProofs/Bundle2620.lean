import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_comp_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f →
      IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  intro R _ I hI W W' f j hf hj hA t ht hp
  obtain ⟨hs, hsp, hsc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f j hf inferInstance t ht hp
  obtain ⟨T, hTp, hTr⟩ := hA _ hs hsp

  have hs0 : ((((t 0).map j).support : Set W)) ⊆ Set.range j := by
    haveI : IsProper ((t 0).subschemeι ≫ j ≫ f) := hp 0
    haveI : IsProper (((t 0).subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance
    haveI : UniversallyClosed ((t 0).subschemeι ≫ j) := UniversallyClosed.of_comp_of_isSeparated _ f
    haveI : QuasiCompact ((t 0).subschemeι ≫ j) := QuasiCompact.of_comp _ f
    have hker : (t 0).map j = Scheme.Hom.ker ((t 0).subschemeι ≫ j) := by
      rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    rw [hker, Scheme.Hom.support_ker,
      (((t 0).subschemeι ≫ j).isClosedMap.isClosed_range).closure_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨(t 0).subschemeι x, by simp⟩

  have hT : ((T.support : Set W)) ⊆ Set.range j := by
    haveI : UniversallyClosed (T.subschemeι ≫ f) := inferInstance
    have hZ : IsClosed (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) :=
      (j.isOpenEmbedding.isOpen_range.isClosed_compl).preimage T.subschemeι.continuous
    have hE := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI T.subscheme (T.subschemeι ≫ f) inferInstance _ hZ (by
      intro x hx hIx
      apply hx
      apply hs0
      have h0 : T ⊔ baseIdeal f (I ^ (0 + 1)) = (t 0).map j := hTr 0
      rw [← h0, Scheme.IdealSheafData.support_sup]
      refine ⟨?_, ?_⟩
      · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      · refine ((GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).2.2 R W f (I ^ (0 + 1)) (T.subschemeι x)).2 ?_
        rw [zero_add, pow_one]
        simpa using hIx)
    intro y hy
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨x, rfl⟩ := hy
    by_contra hc
    have : x ∈ (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) := hc
    rw [hE] at this
    exact this
  refine ⟨T.comap j, ?_, fun e => ?_⟩
  · have hsurj : Function.Surjective (pullback.snd j T.subschemeι) := by
      intro x
      obtain ⟨w, hw⟩ := hT (by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
      exact ⟨z, hz⟩
    haveI : IsIso (pullback.snd j T.subschemeι) :=
      (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hsurj⟩⟩
    have he : (T.comap j).subschemeι ≫ j ≫ f =
        (T.comapIso j).hom ≫ pullback.snd j T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [he]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f j, ← Scheme.IdealSheafData.comap_sup, show T ⊔ baseIdeal f (I ^ (e + 1)) = (t e).map j from hTr e, hsc e]

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.VPre

theorem four_rescale : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  intro O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀
  obtain ⟨N, hN0, hN1, k, hk0, hku, hmain⟩ := hF y₀ N₀
  refine ⟨N, hN0, hN1, k, hk0, hku, ?_⟩
  intro l a c e
  obtain ⟨f, hf⟩ := hmain l a c e
  obtain ⟨b, hb⟩ := hw (e + 1)

  have hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y) := by
    intro y x hx
    haveI := Φ.ev_loc y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)
  have hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y) := by
    intro y
    rw [Ideal.map_le_iff_le_comap]
    exact le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)
  have hbu : IsUnit b := by
    by_contra hn
    have hbm : b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀) := hmax y₀ b hbm
    have h2 := hle y₀ (hb y₀)
    have h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀) := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)
  refine ⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := hf y j
  refine ⟨S, hS1, hS2, ?_⟩
  set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ
  have hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J :=
    le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right
  set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz
  set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww
  have hzb : z * Φ.ev y b = 1 := by
    rw [hz, ← map_mul]
    simp
  have hzw : z - ww ∈ J := by
    apply hIe
    have h := (hb y)
    have hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y))) := by
      have : ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1 := by simp [hww]
      linear_combination ww * hzb - z * this
    rw [hx]
    exact neg_mem (Ideal.mul_mem_left _ _ h)
  have hprod : ∀ mu : Fin l × Fin s → Φ.X y,
      (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l := by
    intro mu
    rw [show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from
        funext fun i => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J
  simp_rw [hprod]
  rw [← Finset.sum_mul, map_mul, map_pow, ← hz]
  set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))
  have hd : z ^ l - ww ^ l ∈ J := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow z ww l
    rw [hr]
    exact Ideal.mul_mem_right _ _ hzw
  have : Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)

end GlobalTheory.Poinc.VPre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenDesc

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def fracMap (ρ : R →+* R') (hρ : Function.Injective ρ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.map (A := R) (B := R') (K := FractionRing R) (L := FractionRing R') (j := ρ) hρ

theorem fracMap_algebraMap (ρ : R →+* R') (hρ : Function.Injective ρ) (r : R) :
    fracMap ρ hρ (algebraMap R _ r) = algebraMap R' _ (ρ r) := by
  simp [fracMap, IsFractionRing.map]

theorem jK_comp_spMap (ρ : R →+* R') (hρ : Function.Injective ρ) :
    jK R' ≫ spMap ρ = spMap (fracMap ρ hρ) ≫ jK R := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (fracMap_algebraMap ρ hρ r).symm

def fracAut (σ : R' ≃+* R') : FractionRing R' ≃+* FractionRing R' :=
  IsFractionRing.ringEquivOfRingEquiv σ

theorem fracAut_algebraMap (σ : R' ≃+* R') (x : R') :
    fracAut σ (algebraMap R' _ x) = algebraMap R' _ (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracAut_fracMap {ρ : R →+* R'} (hρ : Function.Injective ρ) (σ : Gal ρ) (x : FractionRing R) :
    fracAut σ.1 (fracMap ρ hρ x) = fracMap ρ hρ x := by
  have h : ((fracAut σ.1).toRingHom.comp (fracMap ρ hρ)) = fracMap ρ hρ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [fracMap_algebraMap, fracAut_algebraMap, σ.2 r]
  exact congrArg (fun f : FractionRing R →+* FractionRing R' => f x) h

def genMap {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ) (β : G'.left ⟶ G.left)
    (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R) :=
  pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _ ≫ spMap (fracMap ρ hρ)) (by
    rw [Category.assoc, hβ, ← Category.assoc, pullback.condition, Category.assoc, jK_comp_spMap ρ hρ,
      Category.assoc])

theorem genMap_fst {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β :=
  pullback.lift_fst _ _ _

theorem genMap_snd {G' : Over (Sp R')} {G : Over (Sp R)} {ρ : R →+* R'} (hρ : Function.Injective ρ)
    (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ) :
    genMap hρ β hβ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap ρ hρ) :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FracGen
open scoped nonZeroDivisors

theorem natCast_not_isUnit (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime) :
    ¬ IsUnit ((l : ℤ) : 𝓞 F) := by
  intro h
  have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  have h3 : Algebra.norm ℤ (((l : ℤ) : 𝓞 F)) = (l : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [← Algebra.norm_algebraMap]; rfl
  rw [h3] at h2
  have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h4 : IsUnit (l : ℤ) := (isUnit_pow_iff hpos.ne').1 h2
  rw [Int.isUnit_iff] at h4
  have := hl.two_le
  omega

theorem coprime_absNorm (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime)
    (K : Ideal (𝓞 F)) (hK : K ≠ ⊥) (hsup : Ideal.span {((l : ℕ) : 𝓞 F)} ⊔ K = ⊤) :
    (Ideal.absNorm K).Coprime l := by
  haveI : Fact l.Prime := ⟨hl⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Finite (𝓞 F ⧸ K) := Ideal.finiteQuotientOfFreeOfNeBot K hK
  have hcard : Ideal.absNorm K = Nat.card (𝓞 F ⧸ K) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 F ⧸ K) l hd
  have h1 : (1 : 𝓞 F) ∈ Ideal.span {((l : ℕ) : 𝓞 F)} ⊔ K := hsup ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hz0 : Ideal.Quotient.mk K z = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
  have hu : (l : 𝓞 F ⧸ K) * Ideal.Quotient.mk K w = 1 := by
    have := congrArg (Ideal.Quotient.mk K) hyz
    rw [map_add, hz0, add_zero, map_one, map_mul, map_natCast] at this
    rw [mul_comm]; exact this
  have hlx : l • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := by
    rw [nsmul_eq_mul] at hlx
    calc x = ((l : 𝓞 F ⧸ K) * Ideal.Quotient.mk K w) * x := by rw [hu, _root_.one_mul]
      _ = Ideal.Quotient.mk K w * ((l : 𝓞 F ⧸ K) * x) := by ring
      _ = 0 := by rw [hlx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hl.one_lt.ne hx

theorem exists_gen_int (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l.Prime)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    ∃ j₀ ∈ J, j₀ ≠ 0 ∧ ∃ n : ℕ, n.Coprime l ∧ ∀ j ∈ J, ∃ t : 𝓞 F, (n : 𝓞 F) * j = t * j₀ := by
  set L : Ideal (𝓞 F) := Ideal.span {((l : ℕ) : 𝓞 F)} with hLdef
  have hl0 : ((l : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hL0 : L ≠ ⊥ := by rw [hLdef, Ne, Ideal.span_singleton_eq_bot]; exact hl0
  have hLtop : L ≠ ⊤ := by
    rw [hLdef, Ne, Ideal.span_singleton_eq_top]
    have := natCast_not_isUnit F l hl
    simpa using this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := J * L) (J := J) Ideal.mul_le_left
    (mul_ne_zero hJ hL0)
  have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have hdvd : J ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem J).2 haJ)
  obtain ⟨K, hK⟩ := hdvd
  have hLK : L ⊔ K = ⊤ := by
    have : J * (L ⊔ K) = J * ⊤ := by rw [Ideal.mul_sup, ← hK, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ this
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hK
    have hK0 : K = ⊥ := by
      rcases mul_eq_zero.1 hK.symm with h | h
      · exact absurd h hJ
      · exact h
    rw [hK0, sup_bot_eq] at hLK
    exact hLtop hLK
  have hK0 : K ≠ ⊥ := by
    intro h; rw [h, Ideal.mul_bot] at hK
    exact ha0 (Ideal.span_singleton_eq_bot.1 hK)
  refine ⟨a, haJ, ha0, Ideal.absNorm K, coprime_absNorm F l hl K hK0 hLK, fun j hj => ?_⟩
  have hm : (Ideal.absNorm K : 𝓞 F) * j ∈ Ideal.span {a} := by
    rw [hK, mul_comm]; exact Ideal.mul_mem_mul (Ideal.absNorm_mem K) hj
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨t, ht.symm⟩

theorem exists_gen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (l : ℕ) [Fact l.Prime],
    ∃ c₀ : 𝔠.elt, (c₀ : F) ≠ 0 ∧ ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀ := by
  intro F _ _ 𝔠 l hl
  have hlp : l.Prime := hl.out
  obtain ⟨d, hdS, hd⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdS
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  let J : Ideal (𝓞 F) :=
    𝔠.elt.comap ((LinearMap.mulLeft (𝓞 F) (d : F)⁻¹) ∘ₗ Algebra.linearMap (𝓞 F) F)
  have hJ : ∀ o, o ∈ J ↔ (d : F)⁻¹ * algebraMap (𝓞 F) F o ∈ 𝔠.elt := fun o => Iff.rfl
  have hint : ∀ c ∈ 𝔠.elt, ∃ o ∈ J, (c : F) = (d : F)⁻¹ * algebraMap (𝓞 F) F o := by
    intro c hc
    obtain ⟨o, ho⟩ := hd c hc
    have e : c = (d : F)⁻¹ * algebraMap (𝓞 F) F o := by
      have : algebraMap (𝓞 F) F o = (d : F) * c := by rw [ho, Algebra.smul_def]
      rw [this, inv_mul_cancel_left₀ hdF]
    exact ⟨o, (hJ o).2 (e ▸ hc), e⟩
  have hJ0 : J ≠ ⊥ := by
    have hne : (𝔠 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔠.ne_zero
    have hne' : 𝔠.elt ≠ ⊥ := by
      intro h; apply hne
      exact FractionalIdeal.coeToSubmodule_eq_bot.1 h
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
    obtain ⟨o, ho, e⟩ := hint c hc
    intro h
    rw [h, Ideal.mem_bot] at ho
    apply hc0
    rw [e, ho]; simp
  obtain ⟨j₀, hj₀, hj₀0, n, hn, hgen⟩ := exists_gen_int F l hlp J hJ0
  refine ⟨⟨(d : F)⁻¹ * algebraMap (𝓞 F) F j₀, (hJ j₀).1 hj₀⟩, ?_, fun c => ?_⟩
  · simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]
    exact ⟨hdF, fun h => hj₀0 (RingOfIntegers.coe_injective (by exact h.trans (map_zero _).symm))⟩
  · obtain ⟨o, ho, e⟩ := hint c c.2
    obtain ⟨t, ht⟩ := hgen o ho
    refine ⟨n, t, hn, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_smul_of_tower]
    rw [e, nsmul_eq_mul, Algebra.smul_def]
    have := congrArg (algebraMap (𝓞 F) F) ht
    simp only [map_mul, map_natCast] at this
    linear_combination (d : F)⁻¹ * this

end GlobalTheory.FracGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealPartitionOfUnity
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open scoped nonZeroDivisors

namespace GlobalTheory.PartitionFracId

theorem exists_partition (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) :
    ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  set I : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hI
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔠⁻¹ : FracId F) : FractionalIdeal (𝓞 F)⁰ F) with hJ
  have hIJ : I * J = 1 := Units.mul_inv 𝔠
  have hJI : J * I = 1 := by rw [mul_comm]; exact hIJ
  have hmem : ∀ {u v : F}, u ∈ I → v ∈ J → ∃ r : 𝓞 F, (r : F) = u * v := by
    intro u v hu hv
    have h := FractionalIdeal.mul_mem_mul hu hv
    rw [hIJ] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  have hmem' : ∀ {u v : F}, v ∈ J → u ∈ I → ∃ r : 𝓞 F, (r : F) = v * u := by
    intro u v hv hu
    have h := FractionalIdeal.mul_mem_mul hv hu
    rw [hJI] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  let P : F → Prop := fun x => ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, (a j : F) = x
  have h1 : (1 : F) ∈ (I : Submodule (𝓞 F) F) * (J : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, hIJ]
    exact FractionalIdeal.one_mem_one _
  have hP : P 1 := by
    refine Submodule.mul_induction_on (C := P) h1 ?_ ?_
    · intro u hu v hv
      obtain ⟨r, hr⟩ := hmem hu hv
      refine ⟨1, fun _ => ⟨u, hu⟩, fun _ => r, ?_, ?_⟩
      · intro j e
        obtain ⟨s, hs⟩ := hmem' (u := (e : F)) hv e.2
        refine ⟨s, Subtype.ext ?_⟩
        show ((r • e : 𝔠.elt) : F) = ((s • (⟨u, hu⟩ : 𝔠.elt) : 𝔠.elt) : F)
        rw [Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def]
        change (r : F) * (e : F) = (s : F) * u
        rw [hr, hs]; ring
      · simp [hr]
    · rintro x y ⟨n, d, a, ha, hx⟩ ⟨m, d', a', ha', hy⟩
      refine ⟨n + m, Fin.append d d', Fin.append a a', ?_, ?_⟩
      · intro j e
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · obtain ⟨b, hb⟩ := ha i e
          exact ⟨b, by simpa using hb⟩
        · obtain ⟨b, hb⟩ := ha' i e
          exact ⟨b, by simpa using hb⟩
      · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  obtain ⟨n, d, a, ha, hs⟩ := hP
  refine ⟨n, d, a, ha, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using hs

end GlobalTheory.PartitionFracId
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ConjUnitary
open Matrix

theorem unitary_of_norm_preserving {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    V ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hn : ∀ v : EuclideanSpace ℂ (Fin N), ‖toEuclideanCLM (n := Fin N) (𝕜 := ℂ) V v‖ = ‖v‖ := by
    intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa using h v.ofLp
  have h1 := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 hn
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.mul_def, ← map_mul,
    ← map_one (toEuclideanCLM (n := Fin N) (𝕜 := ℂ))] at h1
  rw [Matrix.mem_unitaryGroup_iff']
  exact (toEuclideanCLM (n := Fin N) (𝕜 := ℂ)).injective h1

theorem conj_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    (fun j => (starRingEnd ℂ) ((M *ᵥ fun k => (starRingEnd ℂ) (z k)) j)) =
      M.map (starRingEnd ℂ) *ᵥ z := by
  ext j
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem conj_frame_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  intro K _ N A hC hdet σ
  set B := A ((starRingEnd ℂ).comp σ) with hBdef
  set A0 := A σ with hA0
  set C := A0.map (starRingEnd ℂ) with hCdef
  set V := B⁻¹ * C with hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 (hdet _)
  have hA0u : IsUnit A0.det := isUnit_iff_ne_zero.2 (hdet _)
  have hnorm : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have h := hC σ (A0 *ᵥ fun k => (starRingEnd ℂ) (z k))
    rw [← hBdef, ← hA0, conj_mulVec] at h
    unfold GlobalTheory.ChowHt.frameNorm at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA0u,
      Matrix.one_mulVec, ← hV] at h
    rw [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)] at h
    rw [h]
    simp
  have hVu := unitary_of_norm_preserving V hnorm
  refine ⟨star V, Unitary.star_mem hVu, ?_⟩
  have hVs : V * star V = 1 := (Matrix.mem_unitaryGroup_iff).1 hVu
  have hBV : B * V = C := by
    rw [hV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  rw [← hBV, Matrix.mul_assoc, hVs, Matrix.mul_one]

end GlobalTheory.ConjUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOddStatement
section
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_lifts <;> assumption)
end

