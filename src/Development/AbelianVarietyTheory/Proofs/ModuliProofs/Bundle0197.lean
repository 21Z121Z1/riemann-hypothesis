import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV

namespace GlobalTheory.EmbCut

theorem powIsLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem isoPullAlong {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L j j rfl) (Geo.Tor.chartPullPull M j j rfl) h

theorem symB_of_iso {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hs : SymB L)
    {Y : Scheme.{0}} (e : Y ≅ A.left) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) :
    SymB (A := A) (M.pull e.inv) := by
  have h1 : LBIso (M.pull e.inv) (lbPow L N) :=
    LBIso.chartPull (Geo.Tor.chartPullPull M e.inv e.inv rfl) (Geo.Tor.chartPullSec _ e.hom e.inv e.inv_hom_id) h
  have hN := powIsLB hL N
  have hM' := Geo.Tor.pull_isLB hM e.inv
  obtain ⟨-, a, -, -, c, -⟩ := GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K A.left A.hom L hL
  exact LBIso.trans hM' hN (Geo.Tor.pull_isLB hM' _) h1 (LBIso.trans hN (Geo.Tor.pull_isLB hN _) (Geo.Tor.pull_isLB hM' _)
    (LBIso.trans hN (powIsLB (Geo.Tor.pull_isLB hL _) N) (Geo.Tor.pull_isLB hN _) ((a _ (Geo.Tor.pull_isLB hL _) hs).2 N) (c _ _ N))
    (isoPullAlong h1.symm _))

theorem sectionsHaveFiniteDimension_of_iso_pulled_pow {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB)
    (e : Y ≅ X) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) (n r : ℕ)
    (hr : SectionsHaveFiniteDimension p (lbPow L (N * n)) r) : SectionsHaveFiniteDimension (e.hom ≫ p) (lbPow M n) r := by
  have hN := powIsLB hL N
  have h1 : SectionsHaveFiniteDimension p (lbPow (lbPow L N) n) r :=
    ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hL (N * n))).2.1 _ (powIsLB hN n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p L hL).2.2.1 N n).symm).1 r hr
  have h2 := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hN n)).2.2.2.2.2 Y e r).1 h1
  have h3 : LBIso (lbPow M n) ((lbPow (lbPow L N) n).pull e.hom) :=
    LBIso.trans (powIsLB hM n) (powIsLB (Geo.Tor.pull_isLB hN _) n) (Geo.Tor.pull_isLB (powIsLB hN n) _)
      (((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) M hM).2.1 _ (Geo.Tor.pull_isLB hN _) h).2 n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ hN).2.2.2.2.1 Y e.hom n)
  exact ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) _ (Geo.Tor.pull_isLB (powIsLB hN n) _)).2.1 _ (powIsLB hM n) h3.symm).1 r h2

end GlobalTheory.EmbCut

namespace GlobalTheory

open EmbCut in

theorem cutBy_embedded_abelian : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  intro H H2 g J _ Mat κ n hn hodd
  have hn2 := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, hd⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H H2 g ((n ^ 2) ^ 2) (Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdvd' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  obtain ⟨Q, hQ⟩ := hd _ le_rfl (Ix g ((n ^ j) ^ 2)) (fun a i => ZMod.castHom hdvd' (ZMod ((n ^ 2) ^ 2)) (a i))
    (fun c => by
      choose a ha using fun i => ZMod.castHom_surjective hdvd' (c i)
      exact ⟨a, funext ha⟩)
  refine ⟨Ix g ((n ^ j) ^ 2), inferInstance, id, Q, d, fun K _ _ β t σ p hE hp => ?_⟩
  obtain ⟨hiso, hM, hV, hL, hmod, -, hlab⟩ := GlobalTheory.T.thetaSections_veryAmple_periodic H H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (by nlinarith) hE
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    pullback.condition.symm.trans (Category.comp_id _)
  have hk : ((n ^ j : ℕ) : K) ≠ 0 := fun h => by
    have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow, h] at this
    exact this (by simp)
  have key := hQ K t.pol rfl _ e _ σ (n ^ j) _ (fun h => t.lab h ^ n ^ j) p hM
    (symB_of_iso t.isLB (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample H H2 K t.pol).2.2.1 e hM _ hL) (he.symm ▸ hV)
    (fun a a' h => hmod a a' fun i => by
      have := congrFun h i
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [ZMod.castHom_apply, ZMod.natCast_val] using this)
    (fun m hm => sectionsHaveFiniteDimension_of_iso_pulled_pow t.A.hom t.isLB e hM _ hL m _ (by
      rw [← mul_pow]
      exact PowSec.exists_basis_sections H.globalSectionsRank K t.pol _ (Nat.mul_pos (by positivity) hm)))
    ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn2).le) hk hlab
    (fun h => by
      have : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := by
        rw [Iso.comp_inv_eq]
        exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j))).symm
      exact this.symm ▸ hp h)
  exact he ▸ key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  first | exact @GlobalTheory.SharpFamily.exists_isSharp_of_dense | exact GlobalTheory.SharpFamily.exists_isSharp_of_dense | (intros; apply GlobalTheory.SharpFamily.exists_isSharp_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPELTriple_of_dense_fibres : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  first | exact @GlobalTheory.PELFamily.exists_isPEL_of_dense | exact GlobalTheory.PELFamily.exists_isPEL_of_dense | (intros; apply GlobalTheory.PELFamily.exists_isPEL_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem linear_eq_zero_of_mem_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) (z : Fin g → ℂ) : F z = 0 := by
  have hc : Continuous fun w => (⟨F w, h w⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
  simpa using congrArg Subtype.val this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm

open Matrix in

theorem exists_coord {g : ℕ} {La La' : Type} [AddCommGroup La] [AddCommGroup La'] (Q : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : La' ≃+ La) (Q' : La' →+ (Fin g → ℂ))
    (hQ : ∀ x, h (Q' x) = Q (e x)) (inj : Function.Injective Q) (disc : DiscreteTopology Q.range)
    (span : Submodule.span ℝ (Set.range Q) = ⊤) (herm : Hm.IsHermitian)
    (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Function.Injective Q' ∧ DiscreteTopology Q'.range ∧
      Submodule.span ℝ (Set.range Q') = ⊤ ∧ Hm'.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧
      ∀ x y, hermForm Hm' (Q' x) (Q' y) = hermForm Hm (Q (e x)) (Q (e y)) := by
  let L := h.toLinearMap
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, fun x y hxy => e.injective (inj (by rw [← hQ, ← hQ, hxy])), ?_, ?_,
    isHermitian_mul_mul_conjTranspose _ herm, fun z hz => ?_, fun x y => ?_⟩
  · let m : Q'.range → Q.range := fun z => ⟨h z, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨e x, (hQ x).symm⟩⟩
    have hm : Continuous m :=
      (L.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hm fun z w hzw =>
      Subtype.ext (h.injective (congrArg Subtype.val hzw))
  · have r : Set.range Q' = (h.symm.toLinearMap.restrictScalars ℝ) '' Set.range Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨e x, rfl⟩, by simp [← hQ]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e.symm x, h.injective (by simp [hQ])⟩
    rw [r, Submodule.span_image, span, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · rw [key]
    exact pos _ fun h0 => hz (h.injective (h0.trans (map_zero h).symm))
  · rw [key, ← hQ, ← hQ]
    rfl

theorem exists_module {O : Type} [CommRing O] {g : ℕ} {La : Type} [AddCommGroup La] (ty : Fin g → (O →+* ℂ))
    (Q : La →+ (Fin g → ℂ)) (inj : Function.Injective Q) (st : ∀ c x, ∃ y, ∀ i, Q y i = ty i c * Q x i) :
    ∃ _ : Module O La, ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := by
  choose sm hsm using st
  letI : SMul O La := ⟨sm⟩
  have hs : ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := hsm
  refine ⟨{ one_smul := fun x => inj (funext fun i => by simp [hs])
            mul_smul := fun c d x => inj (funext fun i => by simp [hs, _root_.mul_assoc])
            smul_zero := fun c => inj (funext fun i => by simp [hs])
            smul_add := fun c x y => inj (funext fun i => by simp [hs, mul_add])
            add_smul := fun c d x => inj (funext fun i => by simp [hs, add_mul])
            zero_smul := fun x => inj (funext fun i => by simp [hs]) }, hs⟩

theorem exists_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro l1 l2 l3 l4 E _ _ _ H D o _ g k J b em w w' a bas ρ ty t hw hw' hρ hty hP
  obtain ⟨La, _, EF, lam, ac, Q₀, Hm₀, hbij, hpol, -, u, χ, hAH, hΛ, hχ, hpt, hac⟩ :=
    GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta l1 l2 l3 l4 o g k J b em w w' t ((GlobalTheory.T.pelObjectClass_prim_and_iso_closed E H D o g k J b em w w' a bas ρ t hP).1 hw hw')
  obtain ⟨act, haj, hdet, hadj, I, hζ, hev⟩ := exists_act hP
  change OAct (𝓞 E) t.A at act
  rw [hρ] at hdet
  obtain ⟨h, hh⟩ : ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ (c : 𝓞 E) z,
      u.ex (h (fun i => ty i (c : E) * z i)) = u.ex (h z) ≫ act.act c :=
    GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition l1 l2 l3 l4 E H D t.pol u Hm₀ χ act ty hAH hty hdet
  obtain ⟨inj, disc, span, herm, pos, him⟩ := id hpol
  let F : 𝓞 E → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun c =>
    h.toLinearMap ∘ₗ (LinearMap.pi fun i => ty i (c : E) • LinearMap.proj i) ∘ₗ h.symm.toLinearMap
  have hF₀ : ∀ c z, F c z = h fun i => ty i (c : E) * h.symm z i := fun c z => rfl
  have hF : ∀ c z, u.ex (F c z) = u.ex z ≫ act.act c := fun c z => by
    have := hh c (h.symm z)
    rw [h.apply_symm_apply] at this
    exact this
  let Q₁ : La →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp Q₀
  have hQ₁ : ∀ x, h (Q₁ x) = Q₀ x := fun x => h.apply_symm_apply _
  obtain ⟨Hm₁, inj₁, disc₁, span₁, herm₁, pos₁, him₁⟩ :=
    exists_coord Q₀ Hm₀ h (AddEquiv.refl _) Q₁ hQ₁ inj disc span herm pos
  obtain ⟨_, hs⟩ := exists_module (fun i => (ty i).comp (algebraMap (𝓞 E) E)) Q₁ inj₁ (fun c x => by
    haveI := act.hom c
    have h1 : u.ex (Q₀ x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    have h2 : u.ex (F c (Q₀ x)) = 1 := by
      rw [hF, h1]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := (hΛ _).1 ((u.ker _).1 h2)
    refine ⟨y, fun i => ?_⟩
    show h.symm (Q₀ y) i = _
    rw [hy, hF₀, h.symm_apply_apply]
    rfl)
  have hs₀ : ∀ c x, Q₀ (c • x) = F c (Q₀ x) := fun c x => by
    rw [← hQ₁, hF₀]
    exact congrArg h (funext fun i => hs c x i)
  have adj : ∀ (c : 𝓞 E) x y, EF (c • x) y = EF x (H.bar c • y) := fun c x y => by
    have := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint l1 l2 l3 l4 t.pol u Hm₀ χ _ _ (F c) (F (H.bar c)) hAH (act.hom _) (act.hom _)
      (hF c) (hF _)).1 (hadj c) (Q₀ x) (Q₀ y)
    have h2 : ((EF (c • x) y : ℤ) : ℝ) = EF x (H.bar c • y) := by
      rw [← him, ← him, hs₀, hs₀]
      exact congrArg Complex.im this
    exact_mod_cast h2
  obtain ⟨D', e, hp, hq, hEF⟩ := GlobalTheory.PeriodDatum.exists_datum E H La EF D.p D.q g ty Q₁ Hm₁ hty hbij adj hs inj₁
    disc₁ span₁ herm₁ pos₁ (fun x y => by rw [him₁]; exact him x y)
  let Q₂ : D'.La →+ (Fin g → ℂ) := Q₀.comp e.toLinearMap.toAddMonoidHom
  have hQ₂ : ∀ x, Q₂ x = Q₀ (e x) := fun x => rfl
  obtain ⟨f, ν, hgen, hf⟩ := GlobalTheory.T.period_lattice_in_genus_alt l1 l2 l3 l4 E H D D' t.pol u Hm₀ χ act Q₂ hp hq hAH
    (inj.comp e.injective)
    (fun z => (hΛ z).trans ⟨fun ⟨x, hx⟩ => ⟨e.symm x, (congrArg Q₀ (e.apply_symm_apply x)).trans hx⟩,
      fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩)
    (fun x y => by rw [hEF]; exact him _ _)
    (fun c n x => by
      have := hF c ((n : ℂ)⁻¹ • Q₀ (e x))
      rw [map_smul, ← hs₀, ← map_smul e] at this
      exact this) I
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  obtain ⟨hζ', hev'⟩ := hf k (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hk))
  let Q : D'.La →+ (Fin g → ℂ) := Q₁.comp e.toLinearMap.toAddMonoidHom
  obtain ⟨Hm, inj', disc', span', herm', pos', him'⟩ :=
    exists_coord Q₀ Hm₀ h e.toAddEquiv Q (fun x => hQ₁ _) inj disc span herm pos
  have him'' : ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y := fun x y => by
    rw [him', hEF]; exact him _ _
  refine ⟨D', f, ν, Q, Hm, hgen, hζ.symm.trans hζ', ⟨fun c x i => ?_, inj', disc', span', Hm, herm', pos', him''⟩,
    ⟨inj', disc', span', herm', pos', him''⟩, ?_⟩
  · show Q₁ (e (c • x)) i = _ * Q₁ (e x) i
    rw [map_smul]
    exact hs _ _ _
  · refine GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates o g k J b em w w' t La EF lam ac Q₀ Hm₀ D'.La D'.EF
      (fun i => f k (bas (Pi.single i 1))) (fun j x => a j • x) Q Hm e.symm.toAddEquiv h.symm hpol
      ⟨inj', disc', span', herm', pos', him''⟩ (fun x => ?_) (fun x y => ?_) (fun j x => ?_) (fun i => ?_)
      ⟨u, χ, hAH, hΛ, hχ, hpt, hac⟩
    · show Q₁ (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl
    · show D'.EF (e.symm x) (e.symm y) = _
      rw [hEF, e.apply_symm_apply, e.apply_symm_apply]
    · show e.symm (ac j x) = a j • e.symm x
      rw [← map_smul]
      congr 1
      obtain ⟨G, hG, hG'⟩ := hac j
      haveI := u.discrete
      have h0 := linear_eq_zero_of_mem_discrete u.Λ (G - F (a j))
        (fun z => sub_mem_of_ex_eq u (by rw [hG', hF, haj])) (Q₀ x)
      apply inj
      rw [hs₀, ← hG]
      exact sub_eq_zero.1 h0
    · have h1 : u.ex ((k : ℂ)⁻¹ • Q₀ (lam i)) = u.ex ((k : ℂ)⁻¹ • Q₂ (f k (bas (Pi.single i 1)))) :=
        Over.OverMorphism.ext ((hpt i).symm.trans ((hev i).symm.trans (hev' _)))
      obtain ⟨y, hy⟩ := (hΛ _).1 (sub_mem_of_ex_eq u h1)
      refine ⟨e.symm y, e.injective (inj ?_)⟩
      show Q₀ (e (e.symm (lam i))) = Q₀ (e (f k (bas (Pi.single i 1)) + k • e.symm y))
      rw [e.apply_symm_apply, map_add, map_nsmul, e.apply_symm_apply, map_add, map_nsmul, hy, hQ₂, ← smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

end GlobalTheory.PELPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDenseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  first | exact @GlobalTheory.MulDescent.exists_polarisation_of_veryDense | exact GlobalTheory.MulDescent.exists_polarisation_of_veryDense | (intros; apply GlobalTheory.MulDescent.exists_polarisation_of_veryDense <;> assumption)
end

