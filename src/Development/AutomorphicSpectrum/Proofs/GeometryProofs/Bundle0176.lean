import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0049
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationCharts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.Pick

theorem exists_indep_of_sat {R E : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [AddCommGroup E] [Module R E]
    [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E) (F : Submodule R E)
    (hF : ∀ x, x ∈ F ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ Submodule.span R T) :
    ∃ f : Fin (Module.finrank R F) → E, (∀ j, f j ∈ T) ∧ LinearIndependent R f :=
  _root_.UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat T F hF

def valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) : X.presheaf.stalk (centre z) →+* R :=
  (Scheme.stalkClosedPointTo z).hom

theorem isLocalHom_valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) :
    IsLocalHom (valMap z) :=
  inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)

theorem inv_nat_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) :
    (m : Ω) ≠ 0 ∧ (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  have hu : IsUnit ((m : X.presheaf.stalk (centre z))) := by
    have hv : IsUnit (valMap z (m : X.presheaf.stalk (centre z))) := by
      rw [map_natCast]; exact (Nat.cast_ne_zero.2 hm.ne').isUnit
    haveI := isLocalHom_valMap z
    exact isUnit_of_map_unit (valMap z) _ hv
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have h1 : (m : Ω) * genMap ξ ⟨centre z, h⟩ g = 1 := by
    have := congrArg (genMap ξ ⟨centre z, h⟩) hg
    rwa [map_mul, map_natCast, map_one] at this
  have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨h0, ⟨g, eq_inv_of_mul_eq_one_right h1⟩⟩

theorem reg_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h'⟩ := by
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem exists_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem valAt_zero_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (hg : IsCptGen ξ) (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) {a κ : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) (hκ : κ ∈ regAt ξ ⟨centre z, h⟩) (hκi : κ⁻¹ ∈ regAt ξ ⟨centre z, h⟩) (hκ0 : κ ≠ 0)
    (hv : ValAt ξ z ((m : Ω) * a * κ) 0) : ValAt ξ z a 0 := by
  obtain ⟨ga, hga⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = a := ha
  obtain ⟨gk, hgk⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ := hκ
  obtain ⟨gi, hgi⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ⁻¹ := hκi
  obtain ⟨_, gt, hgt, hgt0⟩ := hv
  replace hgt0 : valMap z gt = 0 := hgt0
  have e1 : gt = (m : X.presheaf.stalk (centre z)) * ga * gk := by
    apply hg.inj ⟨centre z, h⟩
    rw [hgt, map_mul, map_mul, map_natCast, hga, hgk]
  have e2 : gk * gi = 1 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_mul, map_one, hgk, hgi, mul_inv_cancel₀ hκ0]
  have e3 : valMap z gk * valMap z gi = 1 := by rw [← map_mul, e2, map_one]
  have e4 : valMap z gk ≠ 0 := left_ne_zero_of_mul_eq_one e3
  have e5 : valMap z ga = 0 := by
    rw [e1, map_mul, map_mul, map_natCast] at hgt0
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    simpa [hm', e4] using hgt0
  exact ⟨h, ga, hga, e5⟩

theorem lie_val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (hg : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v v' : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : M.ValAt z e v') : v = v' := by
  obtain ⟨h₁, u, hu, hv⟩ := h
  obtain ⟨h₂, u', hu', hv'⟩ := h'
  have : u = u' := (lieLat_carrier X G Ω ξ Li M ⟨centre z, h₁⟩).2 hg inferInstance e u u' hu hu'
  subst this
  apply Over.OverMorphism.ext
  rw [hv, hv']

theorem mem_lat_of_val {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : genPt ξ ⤳ centre z) : e ∈ M.lat ⟨centre z, h'⟩ := by
  obtain ⟨_, u, hu, -⟩ := h
  exact Submodule.subset_span ⟨u, hu⟩

theorem inChart_of_coords {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {L : Type} [Field L] {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (hw : CoordsAt ξ y z w)
    (h : genPt ξ ⤳ centre z) (c₀ : (k : K) → J k) (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ ⟨centre z, h⟩ := by
  have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (hc₀ k).isUnit).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k (c₀ k) (hc₀ k).isUnit).2 (c' k)
  exact reg_of_valAt hr h

theorem exists_cls {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b₀ (i + 1)) : ∃ t : Ω, IsCls b₀ i e t := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by simpa [IsCls] using hy⟩

theorem sub_coord_mem {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E)
    (π : Fin r → Module.Dual Ω E) (hπ : ∀ j l, π j (b l) = if j = l then 1 else 0) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b (i + 1)) : e - π i e • b i ∈ flagStep Ω b i := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hker : flagStep Ω b i ≤ LinearMap.ker (π i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have h0 : π i y = 0 := hker hy
  have : y + t • b i - π i (y + t • b i) • b i = y := by
    simp [h0, hπ]
  rwa [this]

theorem pick : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (f j) (vf j)) ∧
        M.ValAt _ e ve ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s ve ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ hc hall htie hm hind hsw hdeg L _ _ w z hw B MB F hsub c₀ hc₀
  have hg : IsCptGen ξ := htie.gen
  have hsub₀ : IsSubFibre M (flagStep Ω b₀ i) z MB (F.F i.castSucc) := by simpa using hsub i.castSucc
  have hsub₁ : IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB (F.F i.succ) := by simpa using hsub i.succ
  set zL := spMap (algebraMap (𝓞 L) L) ≫ z with hzL

  obtain ⟨f₀, hfT, hfi⟩ := exists_indep_of_sat _ (F.F i.castSucc) hsub₀
  have hrk : Module.finrank (𝓞 L) (F.F i.castSucc) = i := (F.rank i.castSucc).trans (by simp)
  have hrk₁ : Module.finrank (𝓞 L) (F.F i.succ) = i + 1 := (F.rank i.succ).trans (by simp)
  let f : Fin i → B.carrier := fun j => f₀ (Fin.cast hrk.symm j)
  have hfi' : LinearIndependent (𝓞 L) f := hfi.comp _ (Fin.cast_injective _)
  choose ef hef vf hv hl using fun j : Fin i => hfT (Fin.cast hrk.symm j)
  have hfF : ∀ j, f j ∈ F.F i.castSucc := fun j =>
    (hsub₀ _).2 ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span (hfT _)⟩

  obtain ⟨s, ⟨e, he, ve, hve, hsv⟩, hs0⟩ : ∃ s, (∃ e ∈ flagStep Ω b₀ (i + 1), ∃ v : epsAt zL ⟶ G,
      M.ValAt zL e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s v) ∧ s ∉ F.F i.castSucc := by
    by_contra hno
    push_neg at hno
    have hle : F.F i.succ ≤ F.F i.castSucc := by
      intro x hx
      obtain ⟨c, hc₁, hcx⟩ := (hsub₁ x).1 hx
      have hsp := Submodule.span_le.2 (fun t ht => hno t ht) hcx
      exact F.sat _ c x hc₁ hsp
    have heq : F.F i.succ = F.F i.castSucc := le_antisymm hle (F.mono Fin.castSucc_lt_succ.le)
    rw [heq, hrk] at hrk₁
    omega
  have hs1 : s ∈ F.F i.succ := (hsub₁ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨e, he, ve, hve, hsv⟩⟩

  have h : genPt ξ ⤳ centre zL := hall _
  obtain ⟨b, π, κ, hb, hfr, hmb, hπb, hπm, hκ0, hκ, hκi, hcl⟩ := cls_frame X Ω ξ K J y G Li M V r b₀ m i a e₀ hind hsw hdeg
    ⟨centre zL, h⟩ c₀ (inChart_of_coords hw h c₀ hc₀)
  obtain ⟨t, ht⟩ := exists_cls b₀ i he
  have hm0 := inv_nat_reg (ξ := ξ) zL h hm
  have he_lat := mem_lat_of_val M hve h
  have hAr : π i e ∈ regAt ξ ⟨centre zL, h⟩ := by
    have := mul_mem hm0.2 (hπm i e he_lat)
    rwa [inv_mul_cancel_left₀ hm0.1] at this
  have hα : (m : Ω)⁻¹ * π i e ∈ regAt ξ ⟨centre zL, h⟩ := mul_mem hm0.2 hAr
  have htg : t / gen y a e₀ c₀ = (m : Ω) * ((m : Ω)⁻¹ * π i e) * κ := by
    rw [hcl e t he ht, mul_inv_cancel_left₀ hm0.1]
  have hreg : t / gen y a e₀ c₀ ∈ regAt ξ ⟨centre zL, h⟩ := by
    rw [hcl e t he ht]; exact mul_mem hAr hκ
  obtain ⟨u, hu⟩ := exists_valAt hreg
  refine ⟨f, fun j => ef j, s, e, t, u, fun j => vf j, ve, hfF, hfi', hs1, hs0, hef, he,
    fun j => ⟨hv j, hl j⟩, hve, hsv, ht, hu, ?_⟩

  rintro rfl
  have hv0 : ValAt ξ zL ((m : Ω)⁻¹ * π i e) 0 :=
    valAt_zero_factor hg zL h hm hα hκ hκi hκ0 (htg ▸ hu)
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G L zL
  obtain ⟨ev, hev, hevs, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M L zL h ER MR hg inferInstance
  let ar : regAt ξ ⟨centre zL, h⟩ := ⟨_, hα⟩
  let xb : M.lat ⟨centre zL, h⟩ := ⟨_, hmb i⟩
  let xe : M.lat ⟨centre zL, h⟩ := ⟨e, he_lat⟩
  have h1 : ev (ar • xb) = 0 := by rw [hevs ar 0 xb hv0, zero_smul]
  have h2 : ((xe - ar • xb : M.lat ⟨centre zL, h⟩) : Li) = e - π i e • b i := by
    show e - ((m : Ω)⁻¹ * π i e) • (m : Ω) • b i = _
    have hmm : ((m : Ω)⁻¹ * π i e) * (m : Ω) = π i e := by
      have := hm0.1
      field_simp
    rw [smul_smul, hmm]
  have hval : M.ValAt zL e (MR.pt (ev xe)) := (hev e _).2 ⟨he_lat, rfl⟩
  have hveq : ve = MR.pt (ev xe) := lie_val_unique M hg hve hval
  have hval' : M.ValAt zL (e - π i e • b i) ve := by
    rw [hveq]
    refine (hev _ _).2 ⟨h2 ▸ (xe - ar • xb).2, ?_⟩
    have : (⟨e - π i e • b i, h2 ▸ (xe - ar • xb).2⟩ : M.lat ⟨centre zL, h⟩) = xe - ar • xb := Subtype.ext h2.symm
    rw [this, map_sub, h1, sub_zero]
  have hmem : e - π i e • b i ∈ flagStep Ω b₀ i := by
    rw [← hb i]
    exact sub_coord_mem b π hπb i (by rw [hb]; exact he)
  exact hs0 ((hsub₀ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨_, hmem, ve, hval', hsv⟩⟩)

end GlobalTheory.CompanionTheory.Ar.RootHt.Pick
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualBC
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add, map_add, ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add, hw₀, hw₀, hw₀, map_add, mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_pullback_points : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback | exact GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.TorsPull.torsion_of_pullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlagStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_compare_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | exact GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts

theorem exists_halfPolydisc_cover : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) :=
  PositivityTheory.Xgn.quotient_uniformization_charts

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLatticeMapCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_lattice_map_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) → (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) → (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) → (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) → spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f → ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SingVal.value_map | exact GlobalTheory.CompanionTheory.Ar.SingVal.value_map | (intros; apply GlobalTheory.CompanionTheory.Ar.SingVal.value_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeEigenProjectorExistsStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_eigen_projector_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | exact GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc <;> assumption)
end

