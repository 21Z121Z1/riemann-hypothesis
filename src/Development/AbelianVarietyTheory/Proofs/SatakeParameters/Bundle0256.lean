import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfCharpoly
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.AbSub

open Polynomial Module

theorem eq_one_of_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hs : f.IsSemisimple) (hc : f.charpoly = (X - 1) ^ finrank ℂ V) : f = 1 := by
  have h1 : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.mpr hs
  have h2 : IsNilpotent (f - algebraMap ℂ (Module.End ℂ V) 1) := by
    refine ⟨finrank ℂ V, ?_⟩
    have := LinearMap.aeval_self_charpoly f
    rw [hc] at this
    simpa [map_pow, map_sub, aeval_X, map_one] using this
  have := Module.End.eq_zero_of_isNilpotent_isSemisimple h2 h1
  rw [map_one] at this
  exact sub_eq_zero.mp this

end GlobalTheory.AboveL.AbSub

namespace GlobalTheory.AboveL.AbSub

theorem exists_open_sub : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (y : WD h), AbW y → ∀ σ : Weil h, deg σ ≠ 0 → ∃ V : Subgroup (Dec (F := K) A), IsOpen (V : Set (Dec (F := K) A)) ∧ commutator (Dec (F := K) A) ≤ V ∧ (⟨(σ : G K Ω), Weil_le_Dec h σ.2⟩ : Dec (F := K) A) ∈ V ∧ ∀ τ : Ine (F := K) A, ∀ g ∈ V, (g : G K Ω) = τ → y.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ y.lpDim := by
  intro K Ω _ _ _ _ _ A v h y hy σ hσ
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  haveI : CompactSpace (Dec (F := K) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  obtain ⟨n0, a, rfl⟩ := WD.exists_rep y
  have hcomm : ∀ g g' : Weil h, a.ρ (g * g' * g⁻¹ * g'⁻¹) = 1 := fun g g' => by
    have := hy g g'
    rw [WD.charPol_mk, WD.lpDim_mk] at this
    exact eq_one_of_charpoly _ (a.semisimple _) this
  have hconj : ∀ w x : Weil h, a.ρ x = 1 → a.ρ (w * x * w⁻¹) = 1 := fun w x hx => by
    rw [map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]
  let J : Subgroup (Dec (F := K) A) :=
    { carrier := {d | (d : G K Ω) ∈ Ine (F := K) A ∧ ∀ hw : (d : G K Ω) ∈ Weil h, a.ρ ⟨d, hw⟩ = 1}
      one_mem' := ⟨(Ine (F := K) A).one_mem, fun _ => map_one a.ρ⟩
      mul_mem' := by
        rintro d1 d2 ⟨h1, h1'⟩ ⟨h2, h2'⟩
        refine ⟨(Ine (F := K) A).mul_mem h1 h2, fun hw => ?_⟩
        have e := map_mul a.ρ ⟨(d1 : G K Ω), Ine_le_Weil h h1⟩ ⟨(d2 : G K Ω), Ine_le_Weil h h2⟩
        rw [h1', h2', one_mul] at e
        exact e
      inv_mem' := by
        rintro d ⟨h1, h1'⟩
        refine ⟨(Ine (F := K) A).inv_mem h1, fun hw => ?_⟩
        have e := map_mul a.ρ ⟨((d⁻¹ : Dec (F := K) A) : G K Ω), hw⟩ ⟨(d : G K Ω), Ine_le_Weil h h1⟩
        rw [h1' (Ine_le_Weil h h1), mul_one] at e
        have e1 : (⟨((d⁻¹ : Dec (F := K) A) : G K Ω), hw⟩ * ⟨(d : G K Ω), Ine_le_Weil h h1⟩ : Weil h) = 1 :=
          Subtype.ext (inv_mul_cancel (d : G K Ω))
        rw [e1, map_one] at e
        exact e.symm }
  have memJ : ∀ d : Dec (F := K) A, d ∈ J ↔ ((d : G K Ω) ∈ Ine (F := K) A ∧
      ∀ hw : (d : G K Ω) ∈ Weil h, a.ρ ⟨d, hw⟩ = 1) := fun _ => Iff.rfl

  obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp a.smooth
  have hO1 : (1 : G K Ω) ∈ O := by
    have : (1 : Ine (F := K) A) ∈ Subtype.val ⁻¹' O := by
      rw [hOS]; exact map_one a.ρ
    exact this
  have hPW : ∀ d : Dec (F := K) A, (d : G K Ω) ∈ O → (d : G K Ω) ∈ Ine (F := K) A → d ∈ J := by
    intro d hd hI
    refine ⟨hI, fun hw => ?_⟩
    have : (⟨(d : G K Ω), hI⟩ : Ine (F := K) A) ∈ Subtype.val ⁻¹' O := hd
    rw [hOS] at this
    exact this
  have hW0 : IsOpen (Subtype.val ⁻¹' O : Set (Dec (F := K) A)) := hO.preimage continuous_subtype_val
  obtain ⟨U0, hU0⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW0 hO1
  haveI := U0.toSubgroup.quotient_finite_of_isOpen U0.isOpen
  let ι : Weil h →* Dec (F := K) A := Subgroup.inclusion (Weil_le_Dec h)
  obtain ⟨n, hn, -, hσn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := U0.toSubgroup)) (ι σ)
  have hm : 0 < n * (deg σ).natAbs := Nat.mul_pos hn (Int.natAbs_pos.mpr hσ)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg K Ω A v h _ hm
  have hW1 : IsOpen ((U0 : Set (Dec (F := K) A)) ∩ {d | (d : G K Ω) ζ = ζ}) := by
    refine U0.isOpen.inter ?_
    have := (stabilizer_isOpen_of_isIntegral (K := K) ζ).preimage
      (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A))
    convert this using 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW1
    ⟨U0.toSubgroup.one_mem, AlgEquiv.one_apply ζ⟩
  haveI : U.toSubgroup.Normal := U.isNormal'

  have hdense : ∀ d : Dec (F := K) A, ∃ w : Weil h, ∃ u ∈ U.toSubgroup, d = ι w * u := by
    intro d
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine K Ω A v h (ι (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (ι (frob h)) ⊔ (Ine (F := K) A).subgroupOf (Dec (F := K) A) ≤ ι.range := by
      refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    have hd : Dense (ι.range : Set (Dec (F := K) A)) := by
      intro x
      have hx : x ∈ (⊤ : Subgroup (Dec (F := K) A)) := trivial
      rw [← h1] at hx
      exact closure_mono h2 hx
    have hopen : IsOpen {x : Dec (F := K) A | d⁻¹ * x ∈ U.toSubgroup} :=
      U.isOpen.preimage (continuous_mul_left d⁻¹)
    obtain ⟨x, hxU, w, rfl⟩ := hd.inter_open_nonempty _ hopen ⟨d, by simp⟩
    exact ⟨w, (d⁻¹ * ι w)⁻¹, U.toSubgroup.inv_mem hxU, by group⟩
  have hJW : ∀ (w : Weil h) (j : Dec (F := K) A), j ∈ J → ι w * j * (ι w)⁻¹ ∈ J := by
    rintro w j ⟨hjI, hjρ⟩
    refine ⟨conj_mem_Ine (Weil_le_Dec h w.2) hjI, fun hw => ?_⟩
    exact hconj w ⟨j, Ine_le_Weil h hjI⟩ (hjρ _)
  have hU0J : ∀ d : Dec (F := K) A, d ∈ U0.toSubgroup → (d : G K Ω) ∈ Ine (F := K) A → d ∈ J :=
    fun d hd hI => hPW d (hU0 hd) hI
  have hUU0 : ∀ d : Dec (F := K) A, d ∈ U.toSubgroup → d ∈ U0.toSubgroup := fun d hd => (hU hd).1
  have hUζ : ∀ d : Dec (F := K) A, d ∈ U.toSubgroup → (d : G K Ω) ζ = ζ := fun d hd => (hU hd).2
  have hJI : ∀ j ∈ J, (j : G K Ω) ∈ Ine (F := K) A := fun j hj => hj.1
  haveI hJn : J.Normal := ⟨fun j hj d => by
    obtain ⟨w, u, hu, rfl⟩ := hdense d
    have h1 : u * j * u⁻¹ ∈ J := by
      have hc : u * j * u⁻¹ * j⁻¹ ∈ J := by
        refine hU0J _ (hUU0 _ ?_) ?_
        · have h3 : j * u⁻¹ * j⁻¹ ∈ U.toSubgroup :=
            (inferInstance : U.toSubgroup.Normal).conj_mem _ (U.toSubgroup.inv_mem hu) j
          have h4 := U.toSubgroup.mul_mem hu h3
          have e : u * (j * u⁻¹ * j⁻¹) = u * j * u⁻¹ * j⁻¹ := by group
          rwa [e] at h4
        · exact (Ine (F := K) A).mul_mem (conj_mem_Ine u.2 (hJI j hj)) ((Ine (F := K) A).inv_mem (hJI j hj))
      have h5 := J.mul_mem hc hj
      have e : u * j * u⁻¹ * j⁻¹ * j = u * j * u⁻¹ := by group
      rwa [e] at h5
    have h6 := hJW w _ h1
    have e : ι w * (u * j * u⁻¹) * (ι w)⁻¹ = ι w * u * j * (ι w * u)⁻¹ := by group
    rwa [e] at h6⟩
  let N : Subgroup (Dec (F := K) A) := J ⊔ U.toSubgroup
  have hNmem : ∀ x ∈ N, ∃ j ∈ J, ∃ u ∈ U.toSubgroup, j * u = x := by
    intro x hx
    have h1 : x ∈ ((J ⊔ U.toSubgroup : Subgroup _) : Set (Dec (F := K) A)) := hx
    rw [Subgroup.mul_normal] at h1
    obtain ⟨j, hj, u, hu, e⟩ := h1
    exact ⟨j, hj, u, hu, e⟩
  haveI hNn : N.Normal := Subgroup.sup_normal J U.toSubgroup
  have hk : ∀ x ∈ N, QuotientGroup.mk' N x = 1 := fun x hx => by
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hcN : commutator (Dec (F := K) A) ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro d1 _ d2 _
    obtain ⟨w1, u1, hu1, rfl⟩ := hdense d1
    obtain ⟨w2, u2, hu2, rfl⟩ := hdense d2
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    rw [map_commutatorElement, map_mul, map_mul, hk u1 (Subgroup.mem_sup_right hu1),
      hk u2 (Subgroup.mem_sup_right hu2), mul_one, mul_one, ← map_commutatorElement,
      ← map_commutatorElement]
    apply hk
    apply Subgroup.mem_sup_left
    rw [commutatorElement_def]
    have hd0 : deg (w1 * w2 * w1⁻¹ * w2⁻¹) = 0 := by
      rw [deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]; ring
    exact ⟨deg_eq_zero_iff.mp hd0, fun _ => hcomm w1 w2⟩

  refine ⟨Subgroup.zpowers (ι σ) ⊔ N, ?_, le_trans hcN le_sup_right,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers (ι σ)), ?_⟩
  · exact Subgroup.isOpen_mono (le_trans (le_sup_right : U.toSubgroup ≤ N) le_sup_right) U.isOpen
  intro τ g hg hgτ
  have hgI : (g : G K Ω) ∈ Ine (F := K) A := hgτ ▸ τ.2
  have hg' : g ∈ ((Subgroup.zpowers (ι σ) ⊔ N : Subgroup _) : Set (Dec (F := K) A)) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨s, hs, x, hx, rfl⟩ := hg'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  obtain ⟨j, hj, u, hu, rfl⟩ := hNmem x hx
  have hkW : ((ι σ ^ k : Dec (F := K) A) : G K Ω) ∈ Weil h := by
    rw [Subgroup.coe_zpow]; exact zpow_mem σ.2 k
  have huW : (u : G K Ω) ∈ Weil h := by
    have e : u = (ι σ ^ k * j)⁻¹ * (ι σ ^ k * (j * u)) := by group
    rw [e]
    exact (Weil h).mul_mem ((Weil h).inv_mem ((Weil h).mul_mem hkW (Ine_le_Weil h (hJI j hj))))
      (Ine_le_Weil h hgI)
  have hdeg : deg (⟨(u : G K Ω), huW⟩ : Weil h) = -(k * deg σ) := by
    have e : (⟨((ι σ ^ k * (j * u) : Dec (F := K) A) : G K Ω), Ine_le_Weil h hgI⟩ : Weil h) =
        σ ^ k * (⟨(j : G K Ω), Ine_le_Weil h (hJI j hj)⟩ * ⟨(u : G K Ω), huW⟩) := by
      apply Subtype.ext
      simp [Subgroup.coe_zpow, ι]
    have h0 := (deg_eq_zero_iff (σ := ⟨_, Ine_le_Weil h hgI⟩)).mpr hgI
    rw [e, deg_mul, deg_mul, deg_zpow,
      (deg_eq_zero_iff (σ := ⟨_, Ine_le_Weil h (hJI j hj)⟩)).mpr (hJI j hj)] at h0
    linarith
  have hnk : (n : ℤ) ∣ k := by
    have h1 := hζ ⟨(u : G K Ω), huW⟩ (hUζ u hu)
    rw [hdeg, dvd_neg, Nat.cast_mul, Int.natCast_natAbs,
      show (n : ℤ) * |deg σ| = |(n : ℤ) * deg σ| by rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg n)],
      abs_dvd] at h1
    exact (mul_dvd_mul_iff_right hσ).mp h1
  obtain ⟨t, ht⟩ := hnk
  have hk0 : ι σ ^ k ∈ U0.toSubgroup := by
    rw [ht, zpow_mul, zpow_natCast]; exact U0.toSubgroup.zpow_mem hσn t
  have hgJ : ι σ ^ k * (j * u) ∈ J := by
    have hj' : ι σ ^ k * j * (ι σ ^ k)⁻¹ ∈ J := by
      have h1 := hJW (σ ^ k) j hj
      rwa [map_zpow] at h1
    have hc0 : ι σ ^ k * u ∈ U0.toSubgroup := U0.toSubgroup.mul_mem hk0 (hUU0 u hu)
    have hcI : ((ι σ ^ k * u : Dec (F := K) A) : G K Ω) ∈ Ine (F := K) A := by
      have e2 : ι σ ^ k * u = (ι σ ^ k * j * (ι σ ^ k)⁻¹)⁻¹ * (ι σ ^ k * (j * u)) := by group
      rw [e2]
      exact (Ine (F := K) A).mul_mem ((Ine (F := K) A).inv_mem (hJI _ hj')) hgI
    have e : ι σ ^ k * (j * u) = (ι σ ^ k * j * (ι σ ^ k)⁻¹) * (ι σ ^ k * u) := by group
    rw [e]
    exact J.mul_mem hj' (hU0J _ hc0 hcI)
  obtain ⟨hgI', hgρ⟩ := hgJ
  rw [WD.charPol_mk, WD.lpDim_mk]
  have e : ineIncl h τ = ⟨((ι σ ^ k * (j * u) : Dec (F := K) A) : G K Ω), Ine_le_Weil h hgI'⟩ :=
    Subtype.ext hgτ.symm
  rw [e, hgρ, LinearMap.charpoly_one]

end GlobalTheory.AboveL.AbSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL GlobalTheory.SmGL

namespace GlobalTheory.AbStep

theorem loc_char : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion F)ˣ), IsLocalArtin h a → ∀ χ : Dec (F := F) A →* ℂˣ, IsOpen (χ.ker : Set (Dec (F := F) A)) → ∃ θ : (v.adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧ (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧ ∀ σ : Weil h, θ (a σ) = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := by
  intro Ω _ F _ _ _ _ A v h a ha χ hχ
  classical
  let ξ : Weil h →* ℂˣ := χ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
    have hc : Continuous (fun σ : Ine (F := F) A =>
        (⟨(σ : G F Ω), Weil_le_Dec h (Ine_le_Weil h σ.2)⟩ : Dec (F := F) A)) :=
      continuous_subtype_val.subtype_mk _
    exact hχ.preimage hc
  obtain ⟨θ, hθs, hθ⟩ := ha.factor ξ hξ
  have hfi : χ.ker.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A)
    (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl χ.ker hχ
  refine ⟨θ, hθs, ⟨χ.ker.index, Nat.pos_of_ne_zero hfi.index_ne_zero, ?_⟩, fun σ => ?_⟩
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, rfl⟩ := ha.surj x
    have hm := Subgroup.pow_index_mem χ.ker (Subgroup.inclusion (Weil_le_Dec h) σ)
    rw [MonoidHom.mem_ker, map_pow] at hm
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← MonoidHom.comp_apply θ a, ← hθ]
    exact hm
  · exact (DFunLike.congr_fun hθ σ).symm

theorem gal_char : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ η : HChar F, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) → (∀ u : InfinitePlace F, η.locInf u = 1) → ∃ ρ : Gab F Ω →* ℂˣ, IsOpen (ρ.ker : Set (Gab F Ω)) ∧ ∀ x, ρ (art x) = η.1 x := by
  intro F Ω _ _ _ _ art ha η hηf _
  obtain ⟨n, hn, hηn⟩ := hηf
  have hpow : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar F => ξ.1 x) hηn
  have hko : IsOpen (η.1.ker : Set (Ideles F)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow η.1 η.2.1 hn hpow
  have hinf : infConn F ≤ η.1.ker := by
    let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
      Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have hιc : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
    have hO : IsOpen ((η.1.ker.comap ι : Subgroup _) : Set (InfiniteAdeleRing F)ˣ) := hko.preimage hιc
    rintro _ ⟨y, hy, rfl⟩
    exact (IsClopen.connectedComponent_subset ⟨Subgroup.isClosed_of_isOpen _ hO, hO⟩
      (Subgroup.one_mem _)) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (η.1.ker.isClosed_of_isOpen hko)
    rintro _ ⟨k, rfl⟩
    exact η.2.2 k
  have hs : Function.Surjective art := ha.quot.surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective art hs
  let ρ : Gab F Ω →* ℂˣ := (QuotientGroup.lift art.ker η.1 hker).comp e.symm.toMonoidHom
  have hρ : ∀ x, ρ (art x) = η.1 x := fun x => by
    have he : e.symm (art x) = (x : Ideles F ⧸ art.ker) := e.symm_apply_eq.2 rfl
    show QuotientGroup.lift art.ker η.1 hker (e.symm (art x)) = _
    rw [he]
    rfl
  refine ⟨ρ, ?_, hρ⟩
  have hk : (ρ.ker : Set (Gab F Ω)) = art '' (η.1.ker : Set (Ideles F)) := by
    ext g
    obtain ⟨x, rfl⟩ := hs g
    constructor
    · intro hg
      exact ⟨x, by rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hρ]; exact hg, rfl⟩
    · rintro ⟨y, hy, e'⟩
      show ρ _ = 1
      rw [← e', hρ]
      exact hy
  rw [hk]
  exact ha.quot.isOpenMap _ hko

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem one_char (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v)
    (χ : Dec (F := F) A →* ℂˣ) (hχ : IsOpen (χ.ker : Set (Dec (F := F) A)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : v ∉ T) :
    ∃ r : G F Ω →* ℂˣ, IsOpen (r.ker : Set (G F Ω)) ∧ (∀ g : Dec (F := F) A, r g = χ g) ∧
      (∀ (j : Ω →+* ℂ) (c : G F Ω), (∀ x, j (c x) = starRingEnd ℂ (j x)) → r c = 1) ∧
      ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → ∀ g ∈ Dec (F := F) A', r g = 1 := by
  classical
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨a, haL⟩ := GlobalTheory.localArtinExists_holds F Ω A v h
  obtain ⟨θ, hθs, hθf, hθ⟩ := loc_char Ω F A v h a haL χ hχ
  have hne : ∀ u ∈ T, u ≠ v := fun u hu e => hT (e ▸ hu)
  obtain ⟨η, hηf, hηi, hηl⟩ := GlobalTheory.DelEps.Twist.exists_hchar_prescribed F (insert v T)
    (Function.update (fun _ => 1) v θ)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθs
      · rw [Function.update_of_ne (hne w hw)]
        unfold IsSmoothChar
        simp)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθf
      · rw [Function.update_of_ne (hne w hw)]
        exact ⟨1, one_pos, one_pow _⟩)
  have hηv : η.loc v = θ := by rw [hηl v (Finset.mem_insert_self _ _), Function.update_self]
  have hηT : ∀ u ∈ T, η.loc u = 1 := fun u hu => by
    rw [hηl u (Finset.mem_insert_of_mem hu), Function.update_of_ne (hne u hu)]
  obtain ⟨ρ, hρo, hρ⟩ := gal_char F Ω art ha η hηf hηi
  let r : G F Ω →* ℂˣ := ρ.comp (toAb F Ω)
  have hro : IsOpen (r.ker : Set (G F Ω)) :=
    hρo.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have hW : ∀ σ : Weil h, r σ = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := fun σ => by
    show ρ (toAb F Ω σ) = _
    rw [← haL.glob art ha σ, hρ, ← hθ σ, ← hηv]
    rfl
  have hD : ∀ g : Dec (F := F) A, r g = χ g := by
    intro g
    obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 hχ
    have h1 : (1 : G F Ω) ∈ O := by
      have : (1 : Dec (F := F) A) ∈ (χ.ker : Set (Dec (F := F) A)) := χ.ker.one_mem
      rw [← hO] at this
      exact this
    obtain ⟨L, hLf, hLs⟩ := (krullTopology_mem_nhds_one_iff F Ω _).1
      ((hro.inter hOo).mem_nhds ⟨r.ker.one_mem, h1⟩)
    obtain ⟨τ, hτ⟩ := GlobalTheory.ConjWD.exists_weil_eq_on (h := h) g.2 L
    have hfix : (τ : G F Ω)⁻¹ * g ∈ L.fixingSubgroup := fun x => by
      show ((τ : G F Ω)⁻¹ * (g : G F Ω)) x = x
      rw [AlgEquiv.mul_apply, ← hτ x x.2]
      show ((τ : G F Ω)⁻¹ * τ) x = x
      simp
    obtain ⟨hr1, hO1⟩ := hLs hfix
    have hk : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ χ.ker := by
      have : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ (Subtype.val ⁻¹' O : Set (Dec (F := F) A)) := hO1
      rw [hO] at this
      exact this
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    have hr1' : r ((τ : G F Ω)⁻¹ * g) = 1 := hr1
    rw [map_mul, map_inv, inv_mul_eq_one] at hr1'
    rw [← hr1', hW τ, hk]
  refine ⟨r, hro, hD, fun j c hc => ?_, fun u hu A' hA' g hg => ?_⟩
  · show ρ (toAb F Ω c) = 1
    rw [← GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hc, hρ]
    exact DFunLike.congr_fun (hηi _) (-1)
  · have hm : toAb F Ω g ∈ (art.comp (localIdele F u)).range.topologicalClosure := by
      rw [ha.dec u A' hA']
      exact ⟨g, hg, rfl⟩
    have hle : (art.comp (localIdele F u)).range ≤ ρ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hρ]
      exact DFunLike.congr_fun (hηT u hu) x
    exact Subgroup.topologicalClosure_minimal _ hle (ρ.ker.isClosed_of_isOpen hρo) hm

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem exists_abelian_real_field : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  intro Ω _ F _ _ _ _ _ A v h V hVo hVc T hvT
  haveI : V.Normal := GlobalTheory.normal_of_commutator_le V hVc
  haveI : V.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A) (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl V hVo
  letI : CommGroup (Dec (F := F) A ⧸ V) := { (inferInstance : Group (Dec (F := F) A ⧸ V)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hVc
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
      show _ ∈ ⁅(⊤ : Subgroup (Dec (F := F) A)), ⊤⁆
      simpa [commutatorElement_def, mul_assoc] using this }
  have hsep : ∀ q : Dec (F := F) A ⧸ V, ∃ ψ : (Dec (F := F) A ⧸ V) →* ℂˣ, q ≠ 1 → ψ q ≠ 1 := fun q => by
    by_cases hq : q = 1
    · exact ⟨1, fun h => (h hq).elim⟩
    · obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Dec (F := F) A ⧸ V) ℂ hq
      exact ⟨ψ, fun _ => hψ⟩
  choose ψ hψ using hsep
  have hopen : ∀ q, IsOpen (((ψ q).comp (QuotientGroup.mk' V)).ker : Set (Dec (F := F) A)) := fun q =>
    Subgroup.isOpen_mono (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff g).2 hg, map_one]) hVo
  choose r hro hrD hrc hrT using fun q => one_char Ω F A v h ((ψ q).comp (QuotientGroup.mk' V)) (hopen q) T hvT
  let φ : G F Ω →* (Dec (F := F) A ⧸ V → ℂˣ) := Pi.monoidHom r
  have hφ : ∀ σ, φ σ = 1 ↔ ∀ q, r q σ = 1 := fun σ => funext_iff
  have hker : (φ.ker : Set (G F Ω)) = ⋂ q, (r q).ker := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    exact hφ σ
  have ho : IsOpen (φ.ker : Set (G F Ω)) := by
    rw [hker]
    exact isOpen_iInter_of_finite hro
  obtain ⟨L, hLf, hLa, hL⟩ := GlobalTheory.RayFromArtin.exists_field φ ho
  have hmem : ∀ σ : G F Ω, σ ∈ L.fixingSubgroup ↔ ∀ q, r q σ = 1 := fun σ => by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hL, hφ]
  refine ⟨L, hLf, hLa, ?_, ?_, ?_⟩
  · intro φ'
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
    haveI : IsGalois F Ω := {}
    let j : Ω →+* ℂ := ComplexEmbedding.lift Ω φ'
    have hj : j.comp (algebraMap L Ω) = φ' := ComplexEmbedding.lift_comp_algebraMap _ _
    have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap F Ω)) := by
      exact IsTotallyReal.complexEmbedding_isReal _
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) j (ComplexEmbedding.conjugate j) (by
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.isReal_iff.1 hreal])
    have hc : ∀ x, j (σ.symm x) = starRingEnd ℂ (j x) := fun x => DFunLike.congr_fun hσ x
    have hfix : σ.symm ∈ L.fixingSubgroup := (hmem _).2 fun q => hrc q j σ.symm hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [← hj]
    show starRingEnd ℂ (j (x : Ω)) = j (x : Ω)
    rw [← hc]
    exact congrArg j (hfix x)
  · intro g
    rw [hmem]
    constructor
    · intro H
      by_contra hg
      have hq : (QuotientGroup.mk' V g) ≠ 1 := fun e => hg ((QuotientGroup.eq_one_iff g).1 e)
      exact hψ _ hq (by rw [← H (QuotientGroup.mk' V g), hrD]; rfl)
    · intro hg q
      rw [hrD, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · intro u hu A' hA' g hg
    exact (hmem g).2 fun q => hrT q u hu A' hA' g hg

end GlobalTheory.AbStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResDeg

theorem normV_eq_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ w
  refine ⟨w.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

end GlobalTheory.AboveL.ResDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem exists_open_trace_ne_zero (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : 1 ≤ a) (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) :
    ∃ N : Subgroup (G K Ω), IsOpen (N : Set (G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  have hc : Continuous fun g : G K Ω => (r g).val.trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G K Ω) := {g | (r g).val.trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have h1 : (1 : G K Ω) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (by omega : a ≠ 0)
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp (hUo.mem_nhds h1)
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun n hn => hEU hn⟩

end GlobalTheory.AboveL
end

