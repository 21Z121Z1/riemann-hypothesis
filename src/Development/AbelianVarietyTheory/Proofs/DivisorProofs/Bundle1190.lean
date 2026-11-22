import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportHfun
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.HeckeTraceIndep

variable {G : Type} [Group G]

def conjInter (K' : Subgroup G) (s : Finset G) : Subgroup G where
  carrier := {u | u ∈ K' ∧ ∀ g ∈ s, g⁻¹ * u * g ∈ K'}
  one_mem' := ⟨K'.one_mem, fun g _ => by simp [K'.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K'.mul_mem ha hb, fun g hg => ?_⟩
    convert K'.mul_mem (ha' g hg) (hb' g hg) using 1
    group
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K'.inv_mem ha, fun g hg => ?_⟩
    convert K'.inv_mem (ha' g hg) using 1
    group

theorem isOpen_conjInter [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (s : Finset G) : IsOpen (conjInter K' s : Set G) := by
  have : (conjInter K' s : Set G) = (K' : Set G) ∩ ⋂ g ∈ s, (fun u => g⁻¹ * u * g) ⁻¹' (K' : Set G) := by
    ext u
    simp [conjInter]
  rw [this]
  exact hK'.inter (isOpen_biInter_finset fun g _ => hK'.preimage (by fun_prop))

theorem fixed_apply {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {H : Subgroup G}
    {v : V} (hv : v ∈ fixed ρ H) (h : H) : ρ h v = v := by
  have := (show ∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v from hv) h
  simpa using this

def hfun (K' U : Subgroup G) [Fintype (K' ⧸ U.subgroupOf K')] (s : Finset G) (a : G → ℂ) (y : G) : ℂ :=
  ∑ q : K' ⧸ U.subgroupOf K', ∑ g ∈ s,
    a g * if (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk y then 1 else 0

variable (K' U : Subgroup G) [Fintype (K' ⧸ U.subgroupOf K')] (s : Finset G) (a : G → ℂ)

theorem hfun_mul_right {k : G} (hk : k ∈ K') (y : G) : hfun K' U s a (y * k) = hfun K' U s a y := by
  have : (QuotientGroup.mk (y * k) : G ⧸ K') = QuotientGroup.mk y :=
    QuotientGroup.eq.2 (by simp [mul_assoc, K'.inv_mem hk])
  simp only [hfun, this]

theorem hfun_mul_left (hU : ∀ u ∈ U, ∀ g ∈ s, g⁻¹ * u * g ∈ K') {k : G} (hk : k ∈ K') (y : G) :
    hfun K' U s a (k * y) = hfun K' U s a y := by
  unfold hfun
  let kk : K' := ⟨k, hk⟩
  refine (Fintype.sum_equiv (MulAction.toPerm kk) _ _ fun q => ?_).symm
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨u, hu⟩ : ∃ u : U.subgroupOf K', ((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') = kk * q.out * u := by
    have : (MulAction.toPerm kk q : K' ⧸ U.subgroupOf K') = QuotientGroup.mk (kk * q.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    exact QuotientGroup.mk_out_eq_mul _ _
  have hug : g⁻¹ * ((u : K') : G) * g ∈ K' := hU _ (Subgroup.mem_subgroupOf.1 u.2) g hg
  have hiff : (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = QuotientGroup.mk y ↔
      (QuotientGroup.mk ((((MulAction.toPerm kk q : K' ⧸ U.subgroupOf K').out : K') : G) * g) : G ⧸ K') =
        QuotientGroup.mk (k * y) := by
    rw [hu, QuotientGroup.eq, QuotientGroup.eq]
    simp only [Subgroup.coe_mul]
    constructor
    · intro h
      convert K'.mul_mem (K'.inv_mem hug) h using 1
      simp only [kk]
      group
    · intro h
      convert K'.mul_mem hug h using 1
      simp only [kk]
      group
  simp only [hiff]

theorem hfun_eq_zero (y : G) (hy : ∀ q : K' ⧸ U.subgroupOf K', ∀ g ∈ s, (((q.out : K') : G) * g)⁻¹ * y ∉ K') :
    hfun K' U s a y = 0 := by
  unfold hfun
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun g hg => ?_
  rw [if_neg (fun h => hy q g hg (QuotientGroup.eq.1 h)), mul_zero]

theorem hasCompactSupport_hfun [TopologicalSpace G] [IsTopologicalGroup G] (hK'c : IsCompact (K' : Set G))
    (hK'o : IsOpen (K' : Set G)) : HasCompactSupport (hfun K' U s a) := by
  haveI : Finite (K' ⧸ U.subgroupOf K') := inferInstance
  refine HasCompactSupport.intro' (K := ⋃ q : K' ⧸ U.subgroupOf K', ⋃ g ∈ s,
    (Homeomorph.mulLeft (((q.out : K') : G) * g)⁻¹) ⁻¹' (K' : Set G)) ?_ ?_ ?_
  · exact isCompact_iUnion fun q => s.isCompact_biUnion fun g _ => (Homeomorph.isCompact_preimage _).2 hK'c
  · exact isClosed_iUnion_of_finite fun q => isClosed_biUnion_finset fun g _ =>
      (Subgroup.isClosed_of_isOpen _ hK'o).preimage (Homeomorph.continuous _)
  · intro y hy
    refine hfun_eq_zero K' U s a y fun q g hg hmem => hy ?_
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion₂.2 ⟨g, hg, hmem⟩⟩

theorem levOp_hfun {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (v : V) (hv : v ∈ fixed ρ K') :
    levOp ρ K K' (hfun K' U s a) LinearMap.id v =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q : K' ⧸ U.subgroupOf K', ∑ g ∈ s, a g • ρ (((q.out : K') : G) * g) v := by
  set T : Finset (G ⧸ K') := Finset.univ.biUnion fun q : K' ⧸ U.subgroupOf K' =>
    s.image fun g => (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') with hT
  have hmemT : ∀ (q : K' ⧸ U.subgroupOf K'), ∀ g ∈ s, (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') ∈ T :=
    fun q g hg => Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have hsupp : (Function.support fun Q : G ⧸ K' => hfun K' U s a Q.out • (ρ Q.out ∘ₗ LinearMap.id)) ⊆ T := by
    intro Q hQ
    by_contra hQT
    apply hQ
    have : hfun K' U s a Q.out = 0 := by
      refine hfun_eq_zero K' U s a _ fun q g hg hmem => hQT ?_
      have : (QuotientGroup.mk (((q.out : K') : G) * g) : G ⧸ K') = Q := by
        rw [← QuotientGroup.out_eq' Q]
        exact QuotientGroup.eq.2 hmem
      rw [← this]
      exact hmemT q g hg
    simp [this]
  have hout : ∀ z : G, ρ ((QuotientGroup.mk z : G ⧸ K').out) v = ρ z v := by
    intro z
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' z
    rw [hh, map_mul, Module.End.mul_apply, fixed_apply hv h]
  unfold levOp
  rw [finsum_eq_sum_of_support_subset _ hsupp, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  simp only [hfun, Finset.sum_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, mul_ite,
    mul_one, mul_zero, ite_smul, zero_smul, QuotientGroup.out_eq']
  rw [Finset.sum_comm (s := T)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm (s := T)]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [← LinearMap.sum_apply, Finset.sum_ite_eq, if_pos (hmemT q g hg), LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.id_apply, hout]

end GlobalTheory.HeckeTraceIndep

namespace GlobalTheory.HeckeTraceIndep

theorem twTr_linearIndependent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ K' : Subgroup G, IsLevel (MonoidHom.id G) K K' → ∀ (ι : Type) [Fintype ι] (σ : ι → SmIrr G), (∀ i, FiniteDimensional ℂ (fixed (σ i).ρ K') ∧ fixed (σ i).ρ K' ≠ ⊥) → (∀ i j, Nonempty ((σ i).ρ.Equiv (σ j).ρ) → i = j) → ∀ c : ι → ℂ, (∀ f, IsHecke K' f → ∑ i, c i * twTr (σ i).ρ K K' f LinearMap.id = 0) → ∀ i, c i = 0 := by
  intro G _ _ _ K hKo hKc K' hL ι _ σ hfix hne c hc i₀
  obtain ⟨hK'o, hK'K, -⟩ := hL
  have hK'c : IsCompact (K' : Set G) := hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hK'o) hK'K
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).ρ.asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (σ i).irred
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).ρ.asModule →ₗ[MonoidAlgebra ℂ G] (σ j).ρ.asModule, f = 0 := by
    intro i j hij f
    haveI := (σ i).irred
    haveI := (σ j).irred
    haveI : IsEmpty ((σ i).ρ.Equiv (σ j).ρ) := ⟨fun e => hij (hne i j ⟨e⟩)⟩
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i).ρ (σ j).ρ).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  haveI : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ K') := fun i => (hfix i).1
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (fixed (σ i).ρ K'))) ℂ (fixed (σ i).ρ K') :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := GlobalTheory.SimpleCharIndep.exists_smul_eq_ite (R := MonoidAlgebra ℂ G)
    (fun i => (σ i).ρ.asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : fixed (σ i).ρ K') : (σ i).V) : (σ i).ρ.asModule))
  set s : Finset G := x.coeff.support
  set U : Subgroup G := conjInter K' s
  have hUo : IsOpen (U : Set G) := isOpen_conjInter K' hK'o s
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  haveI : Finite (K' ⧸ U.subgroupOf K') := Subgroup.quotient_finite_of_isOpen _ (by
    rw [Subgroup.coe_subgroupOf]; exact hUo.preimage continuous_subtype_val)
  letI : Fintype (K' ⧸ U.subgroupOf K') := Fintype.ofFinite _
  have hU : ∀ u ∈ U, ∀ g ∈ s, g⁻¹ * u * g ∈ K' := fun u hu => hu.2
  set f : G → ℂ := hfun K' U s (fun g => x.coeff g) with hf
  have hHecke : IsHecke K' f := ⟨hasCompactSupport_hfun K' U s _ hK'c hK'o,
    fun k hk y => ⟨hfun_mul_left K' U s _ hU hk y, hfun_mul_right K' U s _ hk y⟩⟩
  set r : ℂ := ((K'.relIndex K : ℕ) : ℂ) with hr_def
  set N : ℕ := Fintype.card (K' ⧸ U.subgroupOf K') with hN_def
  have hact : ∀ i (v : (σ i).V), v ∈ fixed (σ i).ρ K' → levOp (σ i).ρ K K' f LinearMap.id v =
      r⁻¹ • ∑ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) ((σ i).ρ.asAlgebraHom x v) := by
    intro i v hv
    rw [hf, levOp_hfun K' U s _ (σ i).ρ K v hv]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [map_mul, Module.End.mul_apply]
  have hbasis : ∀ i k, levOp (σ i).ρ K K' f LinearMap.id (b i k : (σ i).V) =
      (if i = i₀ then r⁻¹ * N else 0) • (b i k : (σ i).V) := by
    intro i k
    have hxk := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [hact i _ (b i k).2]
    by_cases hi : i = i₀
    · have e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = b i k := by
        exact hxk.trans (if_pos hi)
      rw [if_pos hi, e]
      have h2 : ∀ q : K' ⧸ U.subgroupOf K', (σ i).ρ ((q.out : K') : G) (b i k : (σ i).V) = b i k :=
        fun q => fixed_apply (b i k).2 q.out
      simp only [h2, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    · have e : (σ i).ρ.asAlgebraHom x (b i k : (σ i).V) = 0 := hxk.trans (if_neg hi)
      rw [if_neg hi, e]
      simp
  have hfixedEq : ∀ i, ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v =
      (if i = i₀ then r⁻¹ * N else 0) • v := by
    intro i v hv
    have := LinearMap.congr_fun ((b i).ext (f₁ := (levOp (σ i).ρ K K' f LinearMap.id).comp (fixed (σ i).ρ K').subtype)
      (f₂ := (if i = i₀ then r⁻¹ * N else 0) • (fixed (σ i).ρ K').subtype) (fun k => by
        rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply]
        exact hbasis i k)) ⟨v, hv⟩
    rw [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.subtype_apply] at this
    exact this
  have htr : ∀ i, twTr (σ i).ρ K K' f LinearMap.id =
      (if i = i₀ then r⁻¹ * N else 0) * Module.finrank ℂ (fixed (σ i).ρ K') := by
    intro i
    have hmem : ∀ v ∈ fixed (σ i).ρ K', levOp (σ i).ρ K K' f LinearMap.id v ∈ fixed (σ i).ρ K' :=
      fun v hv => by
        rw [hfixedEq i v hv]
        exact Submodule.smul_mem _ _ hv
    unfold twTr
    rw [dif_pos hmem]
    have : (levOp (σ i).ρ K K' f LinearMap.id).restrict hmem =
        (if i = i₀ then r⁻¹ * N else 0) • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [LinearMap.coe_restrict_apply, hfixedEq i v v.2, LinearMap.smul_apply, LinearMap.id_apply,
        Submodule.coe_smul]
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hsum := hc f hHecke
  simp only [htr] at hsum
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp), if_pos rfl] at hsum
  have hr : r ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val)
    rw [hr_def, Nat.cast_ne_zero]
    exact Subgroup.index_ne_zero_of_finite
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (Module.finrank ℂ (fixed (σ i₀).ρ K') : ℂ) ≠ 0 := by
    haveI : Nontrivial (fixed (σ i₀).ρ K') := Submodule.nontrivial_iff_ne_bot.2 (hfix i₀).2
    exact_mod_cast Module.finrank_pos.ne'
  exact (mul_eq_zero.1 hsum).resolve_right (mul_ne_zero (mul_ne_zero (inv_ne_zero hr) hN) hd)

end GlobalTheory.HeckeTraceIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPoint
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ)
    [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) →
    RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  intro Z _ q _ y hy r hr
  have hyt : y ∈ (⊤ : Z.Opens) := trivial
  obtain ⟨s, rfl⟩ := hr
  have hsurj : Function.Surjective ((Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤)) := by
    have e : (Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤) = (residueFieldIsoBase q y hy).inv.hom :=
      ReciprocityTheory.AnForm.R.constRes_eq q y hy
    rw [e]
    exact (residueFieldIsoBase q y hy).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨α, hα⟩ := hsurj (Z.residue y s)
  set g := Z.presheaf.germ ⊤ y hyt (algX q ⊤ α) with hgdef
  have hg : algebraMap (Z.presheaf.stalk y) Z.functionField g = GlobalTheory.Cartier.constFn q α := by
    rw [hgdef, algebraMap_germ]
    exact RingHom.congr_fun (fnOf_comp_algX q ⊤ _) α
  have hres : Z.residue y (s - g) = 0 := by
    rw [map_sub, sub_eq_zero, ← hα, hgdef, RingHom.comp_apply, ← Scheme.germ_residue, CommRingCat.comp_apply]
  have hnu : ¬ IsUnit (s - g) := by
    intro hu
    have : Z.residue y (s - g) ≠ 0 := by
      have := hu.map (Z.residue y).hom
      exact this.ne_zero
    exact this hres
  refine ⟨α, ?_⟩
  rw [← hg, ← map_sub]
  refine (nonUnit_iff (R := locRing y) ⟨_, s - g, rfl⟩).2 fun hu => hnu ?_
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨t, ht⟩ := u.2
  refine isUnit_iff_exists_inv.2 ⟨t, ?_⟩
  refine (IsFractionRing.injective (Z.presheaf.stalk y) Z.functionField ?_)
  rw [map_mul, map_one, ht]
  exact congrArg Subtype.val hu'

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.TheRec GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaSatake

open GlobalTheory.ThetaPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev cw (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

theorem theta_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (cFin E) (locGL E n (cw w) g) =
      locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cw v)) (locGL E n (cw w) g))) := fun v =>
    map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (cFin E) (locGL E n (cw w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key2 v)

theorem conjLoc_surj (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem absNorm_cw (w : HeightOneSpectrum (𝓞 E)) : Ideal.absNorm (cw w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

def cloc (w : HeightOneSpectrum (𝓞 E)) : (cw w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surj w⟩

theorem thetaGL_conj (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      PhiU n _ * GlobalTheory.LFun.ConjPlace.invT (cloc w) n g * (PhiU n _)⁻¹ := by
  have e1 : GlobalTheory.LFun.ConjPlace.invT (cloc w) n g =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  rw [e1]
  rfl

theorem phiU_mem {K : Type} [Field K] (O : Subring K) (n : ℕ) : PhiU n K ∈ Formalism.UG.GLint (Fin n) O := by
  have h : ∀ i j : Fin n, GlobalTheory.Tw.Phi n K i j ∈ O := fun i j => by
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact pow_mem (neg_mem (one_mem O)) _
    · exact zero_mem O
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, fun i j => h j i⟩

theorem hasSatGL_of_invT {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

theorem hasSat_thetaSub {a : ℕ} (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (C : Multiset ℂˣ)
    (h : (CG.mk π).HasSat (cw w) C) : (CG.mk (thetaSub π)).HasSat w (C.map (·⁻¹)) := by
  rw [CG.hasSat_mk] at h ⊢
  let ρ' := (thetaSub π).locRep w
  let T₀ : π.V ≃ₗ[ℂ] (thetaSub π).V := (pull E a).submoduleMap π.V
  have h0 : ∀ g x, ρ' (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (π.locRep (cw w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (pull_act (.fin (locGL E a (cw w) g)) x.1).symm
  let k := PhiU a (w.adicCompletion E)
  let S : (thetaSub π).V ≃ₗ[ℂ] (thetaSub π).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT (cloc w) (conjLoc_spec _ w).2.2 (absNorm_cw w).symm (T₀.trans S) (fun g x => ?_) h
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, thetaGL_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  dsimp only [k]
  group

end GlobalTheory.ThetaSatake
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSignStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  first | exact @GlobalTheory.LatVacSign.heisO_finRat_sign | exact GlobalTheory.LatVacSign.heisO_finRat_sign | (intros; apply GlobalTheory.LatVacSign.heisO_finRat_sign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.HSNef

open MeasureTheory

theorem gdeg_nonneg_of_semiPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ L : HermLB p, L.SemiPos D → 0 ≤ gdeg L D := by
  intro k _ X _ p D _ L hL
  unfold gdeg chInt
  refine finsum_nonneg fun σ => ?_
  rw [Weight.chernInt, Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]
  exact integral_nonneg fun _ => zero_le_one

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreePow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GdegPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_comb_unit (L : HermLB p) (n : ℕ) :
    (comb (fun _ : Unit => L) fun _ => (n : ℤ)).Isometric (L.pow n) :=
  HermLB.icls_eq_iff.1 (by rw [icls_comb, HermLB.icls_pow, Fintype.sum_unique, natCast_zsmul])

theorem lin_unit (c : ℝ) : (lin fun _ : Unit => c) = c • (MvPolynomial.X () : MvPolynomial Unit ℝ) := by
  rw [lin, Fintype.sum_unique, MvPolynomial.C_mul']

theorem gdeg_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  intro hC k _ X _ p D hX L n
  obtain ⟨Ψ, hΨ, -⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).2
  have key (m : ℕ) : gdeg (L.pow m) D = (m : ℝ) ^ D * Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (isometric_comb_unit L m).gdeg_eq, ← hΨ fun _ => (m : ℤ)]
    simp only [Int.cast_natCast]
    rw [lin_unit, smul_pow, map_smul, smul_eq_mul]
  have h1 : gdeg L D = Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (HermLB.icls_eq_iff.1 (by rw [HermLB.icls_pow, one_smul]) : (L.pow 1).Isometric L).gdeg_eq, key 1]
    simp
  rw [key n, h1]

end GlobalTheory.GdegPow
end
end

