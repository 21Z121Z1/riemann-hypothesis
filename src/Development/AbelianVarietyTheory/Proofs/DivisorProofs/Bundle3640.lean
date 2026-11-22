import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3636
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.IntLatGEqCanLatOfSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HTSummand.LieMod

variable {R : Type} [CommRing R]

def epsIso : epsR R ≅ GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) := Over.isoMk (Iso.refl _) (by simp)

@[simp] lemma epsIso_hom_left : (epsIso (R := R)).hom.left = 𝟙 _ := rfl
@[simp] lemma epsIso_inv_left : (epsIso (R := R)).inv.left = 𝟙 _ := rfl

lemma one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Scheme.{0}} (x : X ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

lemma comp_prod {S : Scheme.{0}} {G Y Z : Over S} [GrpObj G] (f : Z ⟶ Y) (l : List (Y ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

lemma isLieImage_sum {A : Over (Sp R)} [GrpObj A] : ∀ (n : ℕ) (u : Fin n → HdR A) (w : Fin n → (epsR R ⟶ A)),
    (∀ i, IsLieImage (u i) (w i)) → IsLieImage (∑ i, u i) (List.ofFn w).prod
  | 0, u, w, _ => by simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, u, w, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact (h 0).add (isLieImage_sum n _ _ fun i => h i.succ)

lemma isLieImage_eq {A : Over (Sp R)} [GrpObj A] (H : LieExact A) {h h' : HdR A} {v v' : epsR R ⟶ A}
    (e : IsLieImage h v) (e' : IsLieImage h' v') (hd : h - h' ∈ Fil A) : v = v' := by
  have k : IsLieImage (h' + (h - h')) (v' * 1) := e'.add (isLieImage_one_iff.2 hd)
  rw [add_sub_cancel, _root_.mul_one] at k
  exact (H.1 h).unique e k

lemma tan_of {A : Over (Sp R)} [GrpObj A] {v : epsR R ⟶ A} (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsIso.inv ≫ v).left =
      (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, Category.id_comp, Over.comp_left, epsIso_inv_left, Category.id_comp]
  exact hv

lemma tan_to {A : Over (Sp R)} [GrpObj A] {w : GlobalTheory.UPel.HT.epsPtR (𝟙 (Sp R)) ⟶ A}
    (hw : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp R)) ⟶ A).left) :
    IsTangent (epsIso.hom ≫ w) := by
  rw [one_left, Category.id_comp] at hw
  show _ ≫ (epsIso.hom ≫ w).left = _
  rw [Over.comp_left, epsIso_hom_left, Category.id_comp]
  exact hw

end GlobalTheory.HTSummand.LieMod

namespace GlobalTheory.HTSummand

open LieMod in

theorem lie_mod_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ _ β s hs o₀ y hy
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab
  have H : LieExact o₀.A := (GlobalTheory.abelianDeRham.2.1 C₀ o₀.A g o₀.ab hg).1
  obtain ⟨v, hv, -⟩ := H.1 y
  set ωO := algebraMap (𝓞 D.F) D.O D.ω
  haveI := o₀.act.hom ωO
  have hω : v ≫ o₀.act.act ωO = GlobalTheory.GrpTangent.epsScale (β b.ρ) ≫ v :=
    isLieImage_eq H (hv.push (o₀.act.act ωO)) (hv.smul (β b.ρ)) hy
  have hx : 𝟙 (Sp C₀) ≫ s = spMap β := by rw [Category.id_comp, hs]
  have hvT : GlobalTheory.UPel.HT.IsTanScal o₀.act (𝟙 (Sp C₀)) ωO (β b.ρ) (epsIso.inv ≫ v) := by
    refine ⟨tan_of hv.1, ?_⟩
    rw [Category.assoc, Over.comp_left, hω, Over.comp_left, Over.comp_left, epsIso_inv_left, Category.id_comp,
      Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
  obtain ⟨w, hw, hprod⟩ := o₀.lie C₀ β (𝟙 (Sp C₀)) hx (epsIso.inv ≫ v) hvT
  have hwT : ∀ i, IsTangent (epsIso.hom ≫ w i) := fun i => tan_to (hw i 0).1
  choose u hu using fun i => H.2 _ (hwT i)
  refine ⟨u, fun i c => ?_, ?_⟩
  · haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e : (epsIso.hom ≫ w i) ≫ o₀.act.act (algebraMap (𝓞 D.F) D.O c) =
        GlobalTheory.GrpTangent.epsScale (β (b.t i c)) ≫ epsIso.hom ≫ w i := by
      ext1
      simp only [Over.comp_left, epsIso_hom_left, Category.id_comp, GlobalTheory.GrpTangent.epsScale_left]
      rw [← Over.comp_left]
      exact (hw i c).2
    have k₁ := (hu i).push (o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    rw [e] at k₁
    exact k₁.sub_mem ((hu i).smul (β (b.t i c)))
  · have k := isLieImage_sum D.a u _ hu
    have e : (List.ofFn fun i => epsIso.hom ≫ w i).prod = v := by
      rw [show (List.ofFn fun i => epsIso.hom ≫ w i) = (List.ofFn w).map (epsIso.hom ≫ ·) from
        List.map_ofFn.symm, ← comp_prod, ← hprod, Iso.hom_inv_id_assoc]
    rw [e] at k
    exact hv.sub_mem k

end GlobalTheory.HTSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.FormFacts
open GlobalTheory.AbDual

theorem formFacts : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → FiniteDimensional k (HdR o₀.A) ∧ 2 * Module.finrank k (Fil o₀.A) = Module.finrank k (HdR o₀.A) ∧ (∀ x y, φ x y = -φ y x) ∧ ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ x y = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ hφ
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, hdimH, hdimF⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab
  have gAB := smooth_prod hg hg
  have C := cupSquare_of_free H.1 hAB gAB
  refine ⟨hfd, by rw [hdimH, hdimF], GlobalTheory.SymmPoincare.skew_of_symm C o₀.isLB (LBIso.symm o₀.symm) hφ, ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB o₀.P o₀.isLB ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

end GlobalTheory.UPel.HT.FormFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTPolPair
open GlobalTheory.AbDual

theorem nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht φ hφ x hx
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  let A' : GlobalTheory.AV.AbVar k := ⟨o₀.A, o₀.ab, g, hg⟩
  obtain ⟨B, P₀, ⟨h1, h2⟩, hdim⟩ := GlobalTheory.AV.exists_dualPair k A'
  have hgB : SmoothOfRelativeDimension g B.X.hom := by
    have := B.smooth; rw [hdim] at this; exact this
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks k o₀.A B.X o₀.ab B.ab P₀ h1 o₀.P o₀.isLB o₀.rig₁ o₀.rig₂
  obtain ⟨iso, hker⟩ := GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint k o₀.A B.X P₀ h1 o₀.P o₀.isLB o₀.symm l hlP
  obtain ⟨e, he, hkP⟩ := o₀.kerP
  have hu : IsUnit (e : k) := by
    have := (b.unit e he).map β
    simpa using this
  obtain ⟨m, hm, hlm⟩ := GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed k o₀.A B.X g o₀.ab B.ab hg hgB l hl e hu fun T y hy => hkP T y (hker T y hy)
  have hPf : IsPerfect B.X o₀.A (swap P₀) := (IsDual.isPerfect h1 h2).swap
  have CAA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  have CBA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor B.X o₀.A B.ab o₀.ab)
    (smooth_prod hgB hg)
  obtain ⟨φ', hφ'⟩ := exists_isCorrForm CBA hPf.isLB hPf.zero_left hPf.zero_right
  have hadj := IsCorrForm.adjoint CAA o₀.isLB hPf.isLB hφ hφ' l (𝟙 o₀.A) iso
  have perf := (IsCorrForm.perfect GlobalTheory.abelianDeRham B.ab hgB o₀.ab hg hPf hφ').1
  have h0 : push (dp0 k) (𝟙 _) l x = 0 := by
    refine (injective_iff_map_eq_zero _).1 perf.bijective_left.1 _ (LinearMap.ext fun y => ?_)
    rw [← hadj x y, push_id]
    exact hx y

  have hpowM : ∀ j : ℕ, IsMonHom (𝟙 o₀.A ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero]; exact isMonHom_one o₀.A o₀.A
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 o₀.A ^ n) (𝟙 o₀.A) ≫ μ[o₀.A]))
  have hpush : ∀ j : ℕ, push (dp0 k) (𝟙 _) (𝟙 o₀.A ^ j) = (j : k) • LinearMap.id := by
    intro j
    induction j with
    | zero =>
      rw [push_congr (dp0 k) (𝟙 _) (pow_zero (𝟙 o₀.A)), push_one]
      simp
    | succ n ih =>
      haveI := hpowM n
      haveI : IsMonHom (𝟙 o₀.A ^ n * 𝟙 o₀.A) := by rw [← pow_succ]; exact hpowM (n + 1)
      rw [push_congr (dp0 k) (𝟙 _) (pow_succ (𝟙 o₀.A) n), push_mul, ih, push_id]
      push_cast
      rw [add_smul, one_smul]
  haveI := hpowM e
  have key : push (dp0 k) (𝟙 _) m (push (dp0 k) (𝟙 _) l x) = (e : k) • x := by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 k) (𝟙 _) hlm, hpush]
    rfl
  rw [h0, map_zero] at key
  exact (hu.smul_eq_zero.1 key.symm)

end GlobalTheory.HTPolPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KSGraph

theorem connectedSpace_sp_dualNumber (k : Type) [Field k] : ConnectedSpace (Sp (DualNumber k)) := by
  change ConnectedSpace (PrimeSpectrum (DualNumber k))
  have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩

theorem exists_dim {k : Type} [Field k] (A' : Over (Sp (DualNumber k))) [GrpObj A']
    (hA' : IsAbelianScheme A') : ∃ g, SmoothOfRelativeDimension g A'.hom := by
  have := hA'.smooth
  have := hA'.geomConnected
  have := connectedSpace_sp_dualNumber k
  have : ConnectedSpace A'.left := GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap
  exact exists_dim_of_preconnected A'.hom (Classical.arbitrary _)

theorem isFilLift_iff_sub_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  intro k _ A₀ _ A' _ i h hA' x hx y y' hy
  obtain ⟨g, hg⟩ := exists_dim A' hA'
  have P := GlobalTheory.abelianDeRham
  have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 k A₀ g hA₀ g₀).1
  have reg := ksRegular_of_isAbelianScheme P h hA' hg
  constructor
  · intro hy'
    obtain ⟨w, hw, -⟩ := hL.1 y
    obtain ⟨w', hw', -⟩ := hL.1 y'
    have e := (reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩
    subst e
    exact hw'.sub_mem hw
  · intro hz
    obtain ⟨v, ⟨z, hz', -⟩, -⟩ := reg (y' - y) hz
    obtain ⟨d, hd, e⟩ := hy
    obtain ⟨d', hd', e'⟩ := hz'
    refine ⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]
    ext <;> simp

end GlobalTheory.KSGraph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolFormIsNabla
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolFormNabla

theorem cupSquare_eps {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : GlobalTheory.AbDual.CupSquare (epsDP R) (GlobalTheory.DeRham.epsRed R) A := by
  obtain ⟨C, _, φ, j, hφ, hic, -⟩ := exists_const A
  have hC := PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  exact GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys GlobalTheory.abelianDeRham.1 GlobalTheory.abelianDualCrystal.2
    (isDPNilpotent_squareZero _) su rfl hC gC hic.1 (liftMor (epsDP R) hic)

end GlobalTheory.PolFormNabla
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPNFaithfullyFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QuotTower

open scoped TensorProduct

variable {p : ℕ} {R : Type} [CommRing R]

def mulPN (G : PDivGroup p R) (n : ℕ) (k : ℕ) : G.A n →ₐc[R] G.A (n + k) :=
  Nat.rec (motive := fun k => G.A n →ₐc[R] G.A (n + k)) (BialgHom.id R _)
    (fun k f => (G.mulP (n + k)).comp f) k

def resLE (G : PDivGroup p R) {m : ℕ} : ∀ {m' : ℕ}, m ≤ m' → (G.A m' →ₐc[R] G.A m) :=
  @Nat.leRec m (fun m' _ => G.A m' →ₐc[R] G.A m) (BialgHom.id R _) (fun k _ f => f.comp (G.res k))

theorem comp_pow {A X Y : Over (Sp R)} [GrpObj A] (f : X ⟶ Y) (g : Y ⟶ A) (k : ℕ) :
    f ≫ g ^ k = (f ≫ g) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]

variable {G H : PDivGroup p R} {A : Over (Sp R)} [GrpObj A]

theorem mulP_faithfullyFlat (G : PDivGroup p R) (n : ℕ) :
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)).FaithfullyFlat := by
  refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨mulP_flat p R G n, fun P => ?_⟩
  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower R (G.A n) (G.A (n + 1)) := IsScalarTower.of_algebraMap_eq fun r =>
    ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)).commutes r).symm
  haveI : Module.Finite (G.A n) (G.A (n + 1)) := Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨Q, -, hQ, e⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := G.A (n + 1)) P.asIdeal ⊥ (by
    rw [← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot (algebraMap (G.A n) (G.A (n + 1)))).1 (Test.mulP_injective G n)]
    exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext e⟩

theorem mulPN_faithfullyFlat (G : PDivGroup p R) (n k : ℕ) :
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)) : G.A n →+* G.A (n + k)).FaithfullyFlat := by
  induction k with
  | zero => exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  | succ k ih => exact RingHom.FaithfullyFlat.stableUnderComposition _ _ ih (mulP_faithfullyFlat G (n + k))

theorem exists_lift (G : PDivGroup p R) (n k : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (φ : G.A n →ₐ[R] B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (j : B →ₐ[R] B') (φ' : G.A (n + k) →ₐ[R] B'),
      (j : B →+* B').FaithfullyFlat ∧ φ'.comp (mulPN G n k : G.A n →ₐ[R] G.A (n + k)) = j.comp φ := by
  letI : Algebra (G.A n) B := (φ : G.A n →+* B).toAlgebra
  letI : Algebra (G.A n) (G.A (n + k)) :=
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)) : G.A n →+* G.A (n + k)).toAlgebra
  haveI : IsScalarTower R (G.A n) B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : IsScalarTower R (G.A n) (G.A (n + k)) := IsScalarTower.of_algebraMap_eq fun r =>
    ((mulPN G n k : G.A n →ₐ[R] G.A (n + k)).commutes r).symm
  haveI : Module.FaithfullyFlat (G.A n) (G.A (n + k)) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 (mulPN_faithfullyFlat G n k)
  refine ⟨B ⊗[G.A n] G.A (n + k), inferInstance, inferInstance, Algebra.TensorProduct.includeLeft,
    (Algebra.TensorProduct.includeRight : G.A (n + k) →ₐ[G.A n] _).restrictScalars R, ?_, ?_⟩
  · exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  · refine AlgHom.ext fun a => ?_
    change (1 : B) ⊗ₜ[G.A n] (algebraMap (G.A n) (G.A (n + k)) a) = (algebraMap (G.A n) B a) ⊗ₜ[G.A n] 1
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

end GlobalTheory.QuotTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointSeparationPairOfPrincipalisation
section
theorem GlobalTheory.pointSeparationPair_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.PointSeparationPair := fun hP =>
  GlobalTheory.T.kollarTwoPointSeparation_of_nadelVanishing hP (GlobalTheory.T.nadel_vanishing_pairs_of_principalisation hP) GlobalTheory.T.nefLineBundleNumericalTheorems_proof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulPowApp
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

open scoped TensorProduct

namespace GlobalTheory.RedQuot

open WithConv Coalgebra Bialgebra

theorem semi_mulBy {R R₀ A A' : Type} [CommRing R] [CommRing R₀] [CommRing A] [CommRing A'] [Bialgebra R A]
    [Bialgebra R₀ A'] [IsCocomm R A] [IsCocomm R₀ A'] {σ : R →+* R₀} (f : SemiBialgHom σ A A') (k : ℕ) (a : A) :
    f (mulBy R A k a) = mulBy R₀ A' k (f a) := by
  letI : Algebra R A' := ((algebraMap R₀ A').comp σ).toAlgebra
  have hB : ∀ r, algebraMap R A' r = algebraMap R₀ A' (σ r) := fun _ => rfl
  have h := map_pow (f.pts A' hB) (toConv (AlgHom.id R₀ A')) k
  have e1 : ((f.pts A' hB) (toConv (AlgHom.id R₀ A') ^ k)).ofConv a = mulBy R₀ A' k (f a) := by
    rw [SemiBialgHom.pts_apply, ← comp_mulBy_pts]; rfl
  have e2 : ((f.pts A' hB (toConv (AlgHom.id R₀ A'))) ^ k).ofConv a = f (mulBy R A k a) := by
    rw [← toConv_ofConv (f.pts A' hB (toConv (AlgHom.id R₀ A'))), ← comp_mulBy_pts]; rfl
  rw [← e1, ← e2, h]

theorem smul_pow_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O) (k n : ℕ) (a : G.A n) :
    Hom.app (((p : ℤ_[p]) ^ k) • 𝟙 G) n a = mulBy O (G.A n) (p ^ k) a := by
  rw [← Nat.cast_pow, natCast_smul_id_app]

theorem ident {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]
    {G' G : PDivGroup p R} {G₀ : PDivGroup p R₀} (s : SemiHom (algebraMap R R₀) G₀ G)
    (s' : SemiHom (algebraMap R R₀) G₀ G') (ψ : G ⟶ G') (χ : G' ⟶ G) (m N : ℕ)
    (h1 : ∀ n a, s.app n (ψ.app n a) = s'.app n (Hom.app (((p : ℤ_[p]) ^ m) • 𝟙 G') n a))
    (h2 : ψ ≫ χ = ((p : ℤ_[p]) ^ N) • 𝟙 G) (n : ℕ) (a : G.A n) :
    s.app n (mulBy R (G.A n) (p ^ N) a) = mulBy R₀ (G₀.A n) (p ^ m) (s'.app n (χ.app n a)) := by
  have e2 : Hom.app (ψ ≫ χ) n a = mulBy R (G.A n) (p ^ N) a := by rw [h2, smul_pow_app]
  rw [← e2, comp_app]
  change s.app n (ψ.app n (χ.app n a)) = _
  rw [h1, smul_pow_app]
  exact semi_mulBy (s'.app n) _ _

end GlobalTheory.RedQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteCompatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_tower_stage_finite_compat : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  first | exact @GlobalTheory.StageFinNonzero.finNonzero | exact GlobalTheory.StageFinNonzero.finNonzero | (intros; apply GlobalTheory.StageFinNonzero.finNonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap : GlobalTheory.Poinc.Sep.SepSt → ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified := by
  first | exact @GlobalTheory.TChartEt.isEtaleCompletion_tautChart | exact GlobalTheory.TChartEt.isEtaleCompletion_tautChart | (intros; apply GlobalTheory.TChartEt.isEtaleCompletion_tautChart <;> assumption)
end

