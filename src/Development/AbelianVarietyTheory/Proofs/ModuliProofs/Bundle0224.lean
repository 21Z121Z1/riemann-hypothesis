import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodReductionOfThetaPointUnits
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNsmulOfDvd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHermFormCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DetCondOfNotIsSquare
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0060
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0144

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodReductionOfThetaPointUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodReduction_of_thetaPoint_units : Out.Laws → Out.Laws2 → GlobalTheory.SS.SemistablePol → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → ∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  first | exact @GlobalTheory.ThetaCrit.good_reduction_of_theta_point | exact GlobalTheory.ThetaCrit.good_reduction_of_theta_point | (intros; apply GlobalTheory.ThetaCrit.good_reduction_of_theta_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPts

theorem exists_geomPt (S : Scheme.{0}) (p : S) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S), Set.range x = {p} := by
  refine ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p))))
      ≫ S.fromSpecResidueField p, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨IsLocalRing.closedPoint _, ?_⟩, ?_⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

theorem eq_comp_section {S X : Scheme.{0}} (g : X ⟶ S) [IsSeparated g] (τ : S ⟶ X) (w : τ ≫ g = 𝟙 S) {k : Type}
    [Field k] (x : Sp k ⟶ S) (z : Sp k ⟶ X) (hz : z ≫ g = x)
    (h : z (IsLocalRing.closedPoint k) ∈ Set.range τ) : x ≫ τ = z := by
  have : IsClosedImmersion (τ ≫ g) := by rw [w]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ g
  have : Surjective (pullback.fst z τ) := ⟨fun q => by
    rw [← Set.mem_range, Scheme.Pullback.range_fst, Subsingleton.elim q (IsLocalRing.closedPoint k)]
    exact h⟩
  have : IsIso (pullback.fst z τ) := isIso_of_isClosedImmersion_of_surjective _
  have e : (inv (pullback.fst z τ) ≫ pullback.snd z τ) ≫ τ = z := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← hz, ← e]
  simp only [Category.assoc, reassoc_of% w]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {J : Type}
    (σ : J → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (σ j).left) ↔ ∃ j, toUnit (Over.mk x) ≫ σ j = z := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨IsLocalRing.closedPoint k, rfl⟩)
    exact ⟨j, Over.OverMorphism.ext (eq_comp_section G.hom (σ j).left (Over.w _) x z.left (Over.w z) hj)⟩
  · rintro ⟨j, rfl⟩ _ ⟨q, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, _, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {P : Ideal (𝓞 E)} {p i : ℕ}

theorem heckeSet_eq {S : Scheme.{0}} {t : SAB H S} {K K' : Set t.G.left} (hp : p ≠ 0) (h : HeckeSet D t P p i K)
    (h' : HeckeSet D t P p i K') (hle : K ⊆ K') : K = K' := by
  refine hle.antisymm fun g hg => ?_
  obtain ⟨k, _, _, z, hz⟩ := exists_geomPt _ g
  obtain ⟨C, hC, hk⟩ := h k (z ≫ t.G.hom)
  obtain ⟨C', hC', hk'⟩ := h' k (z ≫ t.G.hom)
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [hk'.2.2.2.2.1]; exact pow_ne_zero _ hp)
  have e : C = C' := Subgroup.eq_of_le_of_card_ge (fun u hu => (hC' u).2 (((hC u).1 hu).trans hle))
    (by rw [hk.2.2.2.2.1, hk'.2.2.2.2.1])
  have m : (Over.homMk z rfl : Over.mk (z ≫ t.G.hom) ⟶ t.G) ∈ C := by
    rw [e, hC']
    exact hz.subset.trans (Set.singleton_subset_iff.2 hg)
  exact (hC _).1 m (hz.symm.subset rfl)

theorem pow_eq_one {S : Scheme.{0}} {t : SAB H S} {T : Over S} {C : Subgroup (T ⟶ t.G)} (hp : (p : 𝓞 E) ∈ P)
    (h : t.HeckeKer T D P p i C) {x : T ⟶ t.G} (hx : x ∈ C) : x ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span t x (p ^ 2)).1 fun a ha => h.2.2.1 hx a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp
  rwa [map_natCast] at this

theorem exists_set (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k] {s : Sp k ⟶ Sp (KA l)} (o : Ob D l s)
    (C : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G)) (h : o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C) :
    ∃ K : Set o.t.G.left, EtSet o.t.G K ∧ HeckeSet D o.t P p i K ∧ (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧
      ∀ K', (∀ z ∈ C, Set.range z.left ⊆ K') → K ⊆ K' := by
  have := o.proper
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [h.2.2.2.2.1]; exact pow_ne_zero _ hA.2.2.1.ne_zero)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let σ : Fin n → (𝟙_ (Over (Sp k)) ⟶ o.t.G) := fun j => (e.symm j).1
  have tu : ∀ j, toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j = (e.symm j).1 := fun j => by
    apply Over.OverMorphism.ext
    simp [σ]
  have hσ : ∀ j, σ j ^ p ^ 2 = 1 := fun j => pow_eq_one (T := 𝟙_ (Over (Sp k))) hA.2.2.2.1 h (e.symm j).2
  have hC : (C : Set _) = Set.range (fun j => toUnit (Over.mk (𝟙 (Sp k))) ≫ σ j) := by
    ext z
    refine ⟨fun hz => ⟨e ⟨z, hz⟩, by simp only [tu, Equiv.symm_apply_apply]⟩, ?_⟩
    rintro ⟨j, rfl⟩
    simp only [tu]
    exact (e.symm j).2
  obtain ⟨V, -, hV⟩ := GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel E H D l P p i n _ s o σ hA hσ
  have h1 : Set.range (𝟙 (Sp k) :) ⊆ V := (hV k _).2 ⟨fun a b hab => e.symm.injective (Subtype.ext
    (Over.OverMorphism.ext (by simpa [σ] using hab))), C, hC, h⟩
  have h2 := fun (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) =>
    (hV k' x).1 fun q _ => h1 ⟨q, rfl⟩
  refine ⟨⋃ j, Set.range (σ j).left, ?_, fun k' _ _ x => ?_, fun z => ?_, fun K' hK' => ?_⟩
  · obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_id o.t
    refine GlobalTheory.HkFam.etSet_of_lists _ _ (𝟙 _) o.t.G o.t.G m.φ (p ^ 2) n σ _
      ⟨o.t.semi.comm, o.t.semi.smooth, inferInstance, o.t.semi.geomConnected⟩ m.cart ?_ inferInstance inferInstance
      inferInstance ⟨hσ, by rw [hm]; rfl, fun k' _ _ x => (h2 k' x).1⟩
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  · obtain ⟨C', hC', hk⟩ := (h2 k' x).2
    refine ⟨C', fun z => ?_, hk⟩
    rw [range_subset_iff, ← SetLike.mem_coe, hC']
    rfl
  · rw [range_subset_iff, ← SetLike.mem_coe, hC]
    rfl
  · exact Set.iUnion_subset fun j => hK' _ (e.symm j).2

theorem existsUnique_carries {Xo : Moduli D l} (Z : KerScheme Xo P p i) (hA : admitted l P p) (k : Type) [Field k]
    [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (h : Xo.univ.t.HeckeKer (Over.mk y) D P p i C) : ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y rfl rfl
    (by simp [spMap]) Xo.univ
  have key : ∀ y' : Sp k ⟶ Xo.X, 𝟙 _ ≫ y = y' → ∀ C : Subgroup (Over.mk y' ⟶ Xo.univ.t.G),
      Xo.univ.t.HeckeKer (Over.mk y') D P p i C → ∃ C' : Subgroup (Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      o.t.HeckeKer (Over.mk (𝟙 (Sp k))) D P p i C' ∧
      ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk y' ⟶ Xo.univ.t.G), v.left = u.left ≫ m.toSABMap.φ →
        (u ∈ C' ↔ v ∈ C) := by
    rintro _ rfl C h
    obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk (𝟙 (Sp k)))
    have hh : ∀ (u : Over.mk (𝟙 (Sp k)) ⟶ o.t.G) (v : Over.mk (𝟙 _ ≫ y) ⟶ Xo.univ.t.G),
        v.left = u.left ≫ m.toSABMap.φ → (u ∈ Subgroup.comap ρ.toMonoidHom C ↔ v ∈ C) := fun u v e => by
      rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
      rfl
    exact ⟨_, (GlobalTheory.HkSetPull.heckeKer_iff D P p i m.toSABMap (Over.mk (𝟙 (Sp k))) _ C hh).2 h, hh⟩
  obtain ⟨C', h', hCC⟩ := key y (Category.id_comp _) C h
  obtain ⟨K, het, hK, hmem, hmin⟩ := exists_set hA o C' h'
  obtain ⟨z, ⟨hz, n, hn⟩, huniq⟩ := Z.rep _ (y ≫ Xo.s) inferInstance o K het hK
  have cc := fun z : Sp k ⟶ Z.Hk => (GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₁ o).2
    Z.π₁ z Z.m₁
  have pre : ∀ {z : Sp k ⟶ Z.Hk} (n : ObjMap o Z.o₁ z) (w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G),
      Set.range (w.left ≫ n.toSABMap.φ) ⊆ Z.K ↔ Set.range w.left ⊆ n.toSABMap.φ ⁻¹' Z.K := fun n w => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_subset_iff]
  refine ⟨z, ?_, fun z' hz' => huniq z' ?_⟩
  · obtain ⟨m', hm'⟩ := (cc z).1 n
    have e : z ≫ Z.π₁ = y := (Xo.rep _ (y ≫ Xo.s) inferInstance o).unique
      ⟨(Category.assoc _ _ _).trans hz, ⟨m'⟩⟩ ⟨rfl, ⟨m⟩⟩
    have rigid : ∀ (y' : Sp k ⟶ Xo.X) (m' : ObjMap o Xo.univ y'), y = y' → m'.toSABMap.φ = m.toSABMap.φ := by
      rintro _ m' rfl
      exact GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o y (.inl inferInstance) _ _
        fun a => ⟨_, m'.eta a, m.eta a⟩
    refine ⟨e, fun u v huv => ?_⟩
    let w : Over.mk (𝟙 (Sp k)) ⟶ o.t.G := Over.homMk (n.cart.1.lift u.left (𝟙 _) (by simpa using Over.w u))
      (n.cart.1.lift_snd _ _ _)
    have hw : w.left ≫ n.toSABMap.φ = u.left := n.cart.1.lift_fst _ _ _
    rw [← hCC w v (by rw [huv, ← hw, Category.assoc, ← hm', rigid _ m' e.symm]), hmem, hn, ← pre, hw]
  · obtain ⟨rfl, hc⟩ := hz'
    obtain ⟨n', hn'⟩ := (cc z').2 m
    refine ⟨(Category.assoc _ _ _).symm, n', heckeSet_eq hA.2.2.1.ne_zero hK
      (GlobalTheory.HkSetPull.heckeSet_pull D P p i n'.toSABMap _ Z.hecke) (hmin _ fun w hw => ?_)⟩
    have ww : w.left ≫ o.t.G.hom = 𝟙 _ := Over.w w
    let u : Over.mk z' ⟶ Z.o₁.t.G := Over.homMk (w.left ≫ n'.toSABMap.φ) (by
      rw [Category.assoc, n'.cart.1.w, reassoc_of% ww]; rfl)
    let v : Over.mk (z' ≫ Z.π₁) ⟶ Xo.univ.t.G := Over.homMk (w.left ≫ m.toSABMap.φ) (by
      rw [Category.assoc, m.cart.1.w, reassoc_of% ww]; rfl)
    exact (pre n' w).1 ((hc u v ((congrArg (w.left ≫ ·) hn').trans (Category.assoc _ _ _).symm)).2 ((hCC w v rfl).1 hw))

end GlobalTheory.HkPts

theorem GlobalTheory.kerScheme_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  intro E _ _ _ H D l Xo P p i Z hA
  refine ⟨GlobalTheory.HkPts.existsUnique_carries Z hA, fun hi => ⟨fun q => ?_⟩⟩
  obtain ⟨k, _, _, y, hy⟩ := GlobalTheory.HkPts.exists_geomPt _ q
  obtain ⟨C, hC⟩ := GlobalTheory.exists_heckeKer E H D l Xo P p i hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 hi k y
  obtain ⟨z, ⟨rfl, -⟩, -⟩ := GlobalTheory.HkPts.existsUnique_carries Z hA k y C hC
  obtain ⟨a, ha⟩ := hy.symm.subset rfl
  exact ⟨z a, (Scheme.Hom.comp_apply _ _ _).symm.trans ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.ExCompare

open GlobalTheory.IndefiniteRowSideFullHecke.PositiveSignKForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem weilIs_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (s' : Sp ℂ ⟶ S') (s : Sp ℂ ⟶ S) (hs : s = s' ≫ f) (k : ℤ) (x y : Over.mk s' ⟶ t'.G) (x₀ y₀ : Over.mk s ⟶ t.G)
    (c : ℂˣ) (hx : x₀.left = x.left ≫ m.φ) (hy : y₀.left = y.left ≫ m.φ) :
    Out.WeilIs t'.G t'.PP.L k x y (unitOn c) ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ (unitOn c) := by
  subst hs
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk s') k x y x₀ y₀ _ hx hy

theorem exists_isExp_of_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ₀ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {R K : Type} [CommRing R] [Field K] (f : R →+* K) (σ : K →+* ℂ)
    (B : PAT H (Sp R)) {y : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t y) (n : SABMap t B.t (spMap f))
    (hy : spMap σ ≫ y = FU.u i Pe) :
    ∃ eB : (Fin g → ℂ) → (Over.mk (spMap (σ.comp f)) ⟶ B.t.G), IsExp B (σ.comp f) (FU.Di i) ty Pe eB ∧
      ∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ t.G.hom = spMap σ ∧ x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left := by
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap σ)) (FU.u i Pe) hy.symm
  obtain ⟨q, hq⟩ := LiePull.exists_pushEquiv n.cart (Over.mk (spMap σ)) (spMap (σ.comp f)) (spMap_comp f σ).symm
  have hp' : ∀ z, (p.symm (FU.ex i Pe z)).left ≫ m.φ = (FU.ex i Pe z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => q (p.symm (FU.ex i Pe z)), ⟨hP, ?_, fun z w => ?_,
    q.surjective.comp (p.symm.surjective.comp (FU.ex_onto i Pe hP)), fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩, fun z => ⟨(p.symm (FU.ex i Pe z)).left, Over.w _, (hq _).symm, hp' z⟩⟩
  · have hpb := (IsPullback.of_hasPullback t.G.hom (spMap σ)).paste_horiz m.cart.1
    let c : (Fin g → ℂ) → (Sp ℂ ⟶ pullback t.G.hom (spMap σ)) := fun z =>
      pullback.lift (p.symm (FU.ex i Pe z)).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)
    have hc := ThetaPoint.isHolTo_fibre hpb c (fun z => pullback.lift_snd _ _ _) (by
      have e : (fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ m.cm.F) = fun z => (FU.ex i Pe z).left :=
        funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hp' z
      rw [e]
      exact ExpUniqFamily.isHolTo_ex FU i Pe hP)
    have e : (fun z => (q (p.symm (FU.ex i Pe z))).left) = fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ n.φ :=
      funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hq _
    rw [e]
    exact isHolTo_comp_hom hc _
  · beta_reduce
    rw [FU.ex_add i Pe hP, map_mul, map_mul]
  · exact (map_eq_one_iff q q.injective).trans ((map_eq_one_iff _ p.symm.injective).trans (FU.ex_ker i Pe hP z))
  · have e : p.symm (FU.ex i Pe z ≫ Xo.univ.t.act.act a) = p.symm (FU.ex i Pe z) ≫ t.act.act a := by
      rw [p.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
      exact congrArg (· ≫ _) (hp' z).symm
    apply Over.OverMorphism.ext
    beta_reduce
    rw [FU.ex_lin i Pe hP, e, Over.comp_left, hq, hq, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (n.act a)
  · exact (weilIs_iff n _ _ (spMap_comp f σ).symm k _ _ _ _ c (hq _) (hq _)).1
      ((weilIs_iff m _ _ hy.symm k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (FU.ex_weil i Pe hP k a b c hk hc))

section Comparison₂

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end Comparison₂

section CMStatement

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

def PointFirst (Z : CMLat hP D.p D.q) (k : IntermediateField ℚ ℂ) : Prop :=
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ρ : 𝓞 K₁)
    (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁))
    (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (gA : Bool → ℕ) (tyA : ∀ b, Fin (gA b) → (E →+* ℂ)) (PA : ∀ b, (Z.D₁ b).La →+ (Fin (gA b) → ℂ))
    (e : ∀ b, (Fin (gA b) → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ (X.A b).t.G))
    (F : ∀ j : Fin D.p ⊕ Fin D.q, (Fin (gA j.isLeft) → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    k ≤ K₁ ∧ ((ρ : K₁) : ℂ) = H.rt0 ∧ X.hh = Z.hh ∧
    y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    (∀ b, IsTypeFn H (Z.D₁ b).p (Z.D₁ b).q (tyA b) ∧ IsExp (X.A b) _ (Z.D₁ b) (tyA b) (PA b) (e b)) ∧
    (∀ j a, F j (PA _ a) = Pe (Z.f j a)) ∧
    ∀ (j : Fin D.p ⊕ Fin D.q) (z : Fin (gA j.isLeft) → ℂ) (x : Sp ℂ ⟶ t₀.G.left),
      x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) →
      x ≫ m'.φ = (e _ z ≫ X.φ j).left → x ≫ m.φ = (FU.ex i Pe (F j z)).left

def PointSecond (Z : CMLat hP D.p D.q) (K' : IntermediateField ℚ ℂ) : Prop :=
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hK : KA l ≤ K₁) (ρ : 𝓞 K₁)
    (X : CMObj H K₁ ρ (algebraMap K₁ ℂ) D.p D.q) (y : Sp K₁ ⟶ Xo.X) (t : SAB H (Sp K₁))
    (m : SABMap t Xo.univ.t y) (n : SABMap t X.B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (eB : (Fin g → ℂ) → (Over.mk (spMap ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁))) ⟶ X.B.t.G)),
    K' ≤ K₁ ∧ algebraMap K₁ ℂ (ρ : K₁) = H.rt0 ∧
    y ≫ Xo.s = spMap (IntermediateField.inclusion hK).toRingHom ∧
    spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    (∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left) ∧
    TiedToLattices Z X eB

end CMStatement

def PointFor (r : ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), r (D.p + D.q) → FiniteDimensional ℚ k → PointSecond Z k

section Tensor

end Tensor

section TensorStatement

def TensorFirst (D : Datum H) (l : Level H) (k : IntermediateField ℚ ℂ) : Prop :=
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : 𝓞 K₁) (C : Ell H (𝓞 K₁) ω) (ε : ℤˣ)
    (h : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K₁)))
    (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hk).toRingHom)),
    k ≤ K₁ ∧ C.IsPrincipalAt ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) ∧
    IsKForm D ε h ∧ Nonempty (IsTen C D h T) ∧ Nonempty (SABMap o.t T.t (spMap (algebraMap (𝓞 K₁) K₁)))

variable {M : Type} [Field M] [NumberField M] {ω : 𝓞 M}

def Fits (D : Datum H) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ) : Prop :=
  ((D.q = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = H.rt0) ∨ (D.p = 0 ∧ σ ((2 * ω - 1 : 𝓞 M) : M) = -H.rt0)) ∧
    C.IsPrincipalAt (σ.comp (algebraMap (𝓞 M) M))

def TensorSecond (D : Datum H) (l : Level H) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ) : Prop :=
  ∃ (ε : ℤˣ) (T : PAT H (Sp (𝓞 M))), IsPosSign D ε ∧ Nonempty (IsTen C D (kForm D ε) T) ∧
    ∃ (K₁ : IntermediateField ℚ ℂ) (hK : KA l ≤ K₁) (jM : M →+* K₁)
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom)),
      FiniteDimensional ℚ K₁ ∧ (algebraMap K₁ ℂ).comp jM = σ ∧
      Nonempty (SABMap o.t T.t (spMap (jM.comp (algebraMap (𝓞 M) M))))

end TensorStatement

def TensorForSomeCurve (r : ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H), r (D.p + D.q) →
    D.p = 0 ∨ D.q = 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ),
      Fits D C σ ∧ TensorSecond D l C σ

def CurveExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (_ : Level H), 1 ≤ D.p + D.q →
    D.p = 0 ∨ D.q = 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ),
      Fits D C σ

def CurveIndependent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H), 1 ≤ D.p + D.q →
    ∀ (M : Type) [Field M] [NumberField M] (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (σ : M →+* ℂ)
      (M' : Type) [Field M'] [NumberField M'] (ω' : 𝓞 M') (C' : Ell H (𝓞 M') ω') (σ' : M' →+* ℂ),
      Fits D C σ → Fits D C' σ' → TensorSecond D l C σ → TensorSecond D l C' σ'

def FirstFor (r : ℕ → Prop) : Prop :=
  (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (k : IntermediateField ℚ ℂ), r (D.p + D.q) → FiniteDimensional ℚ k → D.p = 0 ∨ D.q = 0 → TensorFirst D l k) ∧
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (Z : CMLat hP D.p D.q)
    (k : IntermediateField ℚ ℂ), r (D.p + D.q) → FiniteDimensional ℚ k → PointFirst Z k

end GlobalTheory.CM.ExCompare
end
end

