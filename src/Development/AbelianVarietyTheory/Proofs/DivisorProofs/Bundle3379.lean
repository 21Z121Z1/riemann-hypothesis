import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3367
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberWeightSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.JetsCst.jets_cst : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f : Cusp Z Y.U la, evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ (vV T.V (evI y' ((f : Rul Y.d.Xo₂ Y.d.c₂))) : ℝ) ≤ cst * φT := by
  intro hP hD hS hF
  have hA := GlobalTheory.T.jet_numerator_weight_bound hP hD hS hF
  have hB := GlobalTheory.T.cusp_form_stalk_integral_frame hP hD hS hF
  have hG := GlobalTheory.T.weight_antitone_boundary hS
  unfold Covers Lifts at hA hB hG ⊢
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hA hB) hG) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, hC1, x1, h1⟩, ⟨C2, hC2, x2, h2⟩⟩, ⟨C3, hC3, x3, h3⟩⟩
  refine ⟨0, le_rfl, max x1 (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY
  have b := h2 x hx ((le_max_left _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  have c := h3 x hx ((le_max_right _ _).trans ((le_max_right _ _).trans hle)) ι p hp i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨f, hf, hne, hv⟩ := a Z TF la hla cst hJ y hy T io y' g φT hg hφ hfac
  obtain ⟨hp1, hgap⟩ := c
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb).2.1
  rw [hw] at hf
  have h4 : (4 : ℤ) ∣ ((GlobalTheory.RefSum.nCol (dat p i) / 2 : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨k, by rw [hk]; omega⟩
  obtain ⟨f', hne', hv'⟩ := b Z TF la _ _ h4 f hf y T io y' g hg hfac hne
  exact ⟨f', hne', by rw [hv']; exact hv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullOfConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ConstDefSym

open GlobalTheory.CechPic

theorem lbIso_pull_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (Q.P.L.pull π₁) (Q.P.L.pull π₂) := by
  intro R _ _ Q k _ _ ρ B' _ π₁ π₂ h₁ h₂ hfib

  let ρ₀ : R →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  let A₀ : Over (Sp k) := (Over.pullback (spMap ρ₀)).obj Q.P.A
  letI : GrpObj A₀ := Functor.grpObjObj
  have hj : IsGrpPullback A₀ Q.P.A (spMap ρ₀) (pullback.fst Q.P.A.hom (spMap ρ₀)) := isGrpPullback_pullback Q.P.A (spMap ρ₀)
  have ec : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h₂' : IsGrpPullback B' Q.P.A (spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀) π₂ := h₂.congr ec rfl
  let q : B'.left ⟶ A₀.left := hj.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    (by rw [h₂'.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst Q.P.A.hom (spMap ρ₀) = π₂ := hj.1.lift_fst _ _ _
  have hq₂ : q ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hj.1.lift_snd _ _ _
  have hq : IsGrpPullback B' A₀ (spMap (algebraMap k (DualNumber k))) q :=
    IsGrpPullback.cancel hj (h₂'.congr rfl hq₁.symm) hq₂
  have eid : GlobalTheory.DeRham.epsRed k ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [GlobalTheory.DeRham.epsRed, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k)
    ext x
    simp
  let i : A₀.left ⟶ B'.left := hq.1.lift (𝟙 _) (A₀.hom ≫ GlobalTheory.DeRham.epsRed k)
    (by rw [Category.id_comp, Category.assoc, eid, Category.comp_id])
  have e : i ≫ q = 𝟙 _ := hq.1.lift_fst _ _ _
  have hi₂ : i ≫ B'.hom = A₀.hom ≫ GlobalTheory.DeRham.epsRed k := hq.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  have hi : IsGrpPullback A₀ B' (GlobalTheory.DeRham.epsRed k) i :=
    IsGrpPullback.cancel hq ((isGrpPullback_of_iso (Iso.refl A₀)).congr eid.symm (by rw [e]; rfl)) hi₂
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hj

  have hL := Q.P.isLB
  have hsymA : pull (GrpObj.inv : Q.P.A ⟶ Q.P.A).left (cls Q.P.L hL) = cls Q.P.L hL := by
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨Q.sym, Q.sym_gen⟩
    rw [cls_linComb hL] at h0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul,
      pull_id] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have key : ∀ {f : Sp (DualNumber k) ⟶ Sp R} (π : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A f π →
      LBIso ((Q.P.L.pull π).pull (GrpObj.inv : B' ⟶ B').left) (Q.P.L.pull π) := by
    intro f π hπ
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)]
    show pull _ (pull π (cls Q.P.L hL)) = pull π (cls Q.P.L hL)
    rw [← pull_comp, GlobalTheory.SymSpread.inv_comp_of_isGrpPullback hπ, pull_comp, hsymA]
  have hfib' : i ≫ π₁ = i ≫ π₂ := hfib A₀.left i A₀.hom hi₂
  have hclosed : LBIso ((Q.P.L.pull π₁).pull i) ((Q.P.L.pull π₂).pull i) := by
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)]
    show pull i (pull π₁ (cls Q.P.L hL)) = pull i (pull π₂ (cls Q.P.L hL))
    rw [← pull_comp, ← pull_comp, hfib']
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric k A₀ B' i q hA₀ hi hq e _ _ (pull_isLB hL _) (pull_isLB hL _)
    (key π₁ h₁) (key π₂ h₂) hclosed

end GlobalTheory.ConstDefSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocDerKMono
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Heat.DerComm
open GlobalTheory.KS GlobalTheory.LocDerExt

theorem appLE_congr {X Y : Scheme.{0}} {g g' : Y ⟶ X} (e : g = g') (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (h' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V h = g'.appLE U V h' := by
  subst e; rfl

theorem locDerK_mono {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ W₁ : X.Opens}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D W₀ d) (hW : W₁ ≤ W₀) :
    LocDerK q p m D W₁ d :=
  ⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW),
   fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩

theorem eq_of_gen {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {V : X.Opens}
    {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D V d)
    (h' : LocDerK q p m D V d') {M : Type} (r : M → Γ(X, V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ V (fun _ _ => trivial)).hom r))
    (he : ∀ j, d V (r j) = d' V (r j)) : d V = d' V := by
  funext f
  obtain ⟨P, rfl⟩ := hs f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := by
      simp
    have : (p.appLE ⊤ V (fun _ _ => trivial)).hom a =
        constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
      unfold constFn; rw [e]
    rw [this, h.base V le_rfl, h'.base V le_rfl]
  | add P Q hP hQ => rw [map_add, h.add V le_rfl, h'.add V le_rfl, hP, hQ]
  | mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]

theorem comm_of_gen : ∀ {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (dl : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK q p m D ⊤ dl → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y), T₀ ≫ m = m ≫ T → T₀ ≫ q = q → T ≫ p = p → ∀ (Ix : Type) (U : Ix → X.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(X, U i)), (⨆ i, U i = ⊤) → (∀ i, IsAffineOpen (U i)) → (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) → (∀ i j, dl (T ⁻¹ᵁ U i) ((T.app (U i)).hom (r i j)) = pbT T₀ (dl (U i) (r i j)) (m ⁻¹ᵁ (T ⁻¹ᵁ U i))) → ∀ (W : X.Opens) (f : Γ(X, W)), dl (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (dl W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W)) := by
  intro R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg
  have pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V) := fun V => by
    rw [← hm]; exact le_rfl
  have app1 : ∀ (V : X.Opens) (g : Γ(X, V)),
      (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g := by
    intro V g; rw [Scheme.Hom.comp_app]; rfl
  have app2 : ∀ (V : X.Opens) (g : Γ(X, V)),
      pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g := by
    intro V g
    rw [pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    have := congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))
    refine this.trans ?_
    exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)
  let d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)
  let d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)
  have h1 : LocDerK q p (m ≫ T) D ⊤ d1 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d1, map_add]; exact hdl.add _ le_top _ _
    · simp only [d1, map_mul]; rw [hdl.mul _ le_top, app1, app1]; exact rfl
    · simp only [d1]; rw [app_res T h, hdl.res _ _ _ le_top]; rfl
    · simp only [d1]
      rw [Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]
      exact hdl.base _ le_top a
  have h2 : LocDerK q p (m ≫ T) D ⊤ d2 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d2]; rw [hdl.add _ le_top, pbT_add]
    · simp only [d2]; rw [hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]
    · simp only [d2]
      rw [hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]
    · simp only [d2]; rw [hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]
  have key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V := fun i V hV =>
    GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top)
      (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV
  intro W f
  show d1 W f = d2 W f
  refine eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_
  · intro y hy
    have : (m ≫ T).base y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  · intro k
    rw [← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]

end GlobalTheory.Heat.DerComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyParamNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoParam

theorem t_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  intro R _ _ Q m t gam hM hli hsym i hti
  have hdiag : ∀ y, gam i y y = 0 := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := hM y
    have h0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
    have hni : n i = 0 := by
      by_contra hne
      apply h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hti]; exact zero_pow hne), mul_zero]
    rw [hn i, hni]; simp
  have hz : gam i = 0 := by
    refine LinearMap.ext₂ fun y z => ?_
    have h := hdiag (y + z)
    simp only [map_add, LinearMap.add_apply, hdiag y, hdiag z, hsym i z y] at h
    simp only [LinearMap.zero_apply]
    omega
  exact hli.ne_zero i hz

end GlobalTheory.MonoParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_gen_of_top {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j₀ : K → M.ι) (all : ∀ w : Y, w ∈ LB.wchart M φ j₀) (v : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v := by
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j w hw => ⟨hw, all w⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀) * res (le_top : LB.wchart M φ j ≤ ⊤) v⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v :=
    fun Z r z j h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z (le j) h _).trans (gm_linComb M φ ε r z j j₀ h (all _))) (gm_res r z le_top h _))
  refine ⟨t, fun j j' => Geo.Tor.unit_ext fun w hw => ?_, key⟩
  have hm : (𝟙 Y : Y ⟶ Y) w ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hw
  refine ((gm_res _ w _ hm _).trans (key _ _ w j hm.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) w j j' hm.1 hm.2)
      ((gm_res _ w _ hm _).trans (key _ _ w j' hm.2)))).symm)
  rw [← trF_trans hM φ ε (𝟙 Y) w hm.1 hm.2 (all _), _root_.mul_assoc]
  rfl

theorem jK_app_toOpen {R : Type} [CommRing R] [IsDomain R] (r : R) :
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem exists_isUnitPart : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ y, ∃ n ψ₀, IsUnitPart Q t gam y n ψ₀ := by
  intro R _ _ Q m t gam h y
  obtain ⟨u, n, hn, hc⟩ := h y
  have h0 : ∏ i, t i ^ n i ≠ 0 := right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord hc)
  have h1 : algebraMap R (FractionRing R) (∏ i, t i ^ n i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0
  obtain ⟨j₀, hj, hle, e⟩ := hc
  have all : ∀ w, w ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c y).left) j₀ := fun w =>
    Set.mem_iInter.2 fun _ => hj trivial
  obtain ⟨ψ₀, hg, hv⟩ := exists_gen_of_top Q.P.isLB (K := PUnit) (fun _ => (Q.c y).left) (fun _ => -1) j₀ all (unitOn u)
  refine ⟨n, ψ₀, hg, hn, Units.mk0 _ h1, rfl, fun z J hJ => ?_⟩
  have m₀ : (𝟙 (TK R).left : _ ⟶ _) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀ := hle trivial
  have a := gen_trans (Q.psi_gen y) (𝟙 (TK R).left) z (hJ.mem (fun _ : PUnit => Q.xK y) (𝟙 _)) m₀
  have b := hv _ (toUnit (TK R)).left z _ (hJ.mem (fun _ : PUnit => (Q.c y).left) (toUnit (TK R)).left)
  have c : gm (𝟙 (TK R).left) z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀) ((Q.psi y).s j₀) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (Units.mk0 _ h1)) * gm (toUnit (TK R)).left z ⊤ (unitOn u) := by
    have d : res hle ((Q.psi y).s j₀) =
        unitOn (Units.mk0 _ h1) * (show Γ(Sp (FractionRing R), ⊤)ˣ from pullU (jK R) ⊤ (unitOn u)) := by
      refine Units.ext (e.symm.trans ?_)
      rw [jK_app_toOpen, map_mul, _root_.mul_comm, map_mul]
      refine congrArg₂ (· * ·) rfl ?_
      rw [← jK_app_toOpen]
      exact congrArg _ (by simp [DegPre.toOpen, unitOn])
    refine (gm_res _ z hle trivial _).symm.trans ((congrArg _ d).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))
    exact gm_pull (𝟙 _) (jK R) z ⊤ trivial _
  refine a.trans (Eq.trans ?_ (congrArg _ b).symm)
  rw [c, mul_left_comm]
  rfl

end GlobalTheory.UnitPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenChartOfSmoothFamilyGeomFibreInjective
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCrit

theorem openChart : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → FibInj A M → IsChart A M := by
  intro R _ _ A _ g hA hAg U M hU hM hF
  have hUf : LocallyOfFiniteType U.hom := by
    haveI := hU
    haveI : Smooth U.hom := SmoothOfRelativeDimension.smooth g _
    infer_instance
  have hI : Inj A M := GlobalTheory.T.lineBundleFamilyParamInjective_of_geomFiberInjective R A hA U M hUf hM hF
  refine ⟨hM, hI, ?_⟩
  intro T N hN
  refine GlobalTheory.T.lineBundleFamilyChart_of_affine_parameters (Sp R) A hA U M hM hI ?_ T N hN
  intro T _ N hN
  refine GlobalTheory.T.additiveFamily_chart_affine_of_chart_finiteType R A hA U M hM ?_ T N hN
  intro T _ hT N hN
  exact GlobalTheory.T.lineBundleFamily_openChart_affine_finiteType R A hA U M hUf hM hI (fun f _ _ _ h => GlobalTheory.T.isOpenImmersion_of_mono_lift_smallArtinExtensions f h) T hT N hN
    (GlobalTheory.T.smoothInjectiveFamily_lifts_small_artinian R A g hA hAg U M hU hM hI T N hN)

end GlobalTheory.ChartCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu WithConv

namespace GlobalTheory.Dieu

theorem hom_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {k : Type} [CommRing k]
    {G H : PDivGroup p k} (m : ℕ) {f : G ⟶ H} (e : (p : ℤ_[p]) ^ m • f = 0) : f = 0 := by
  induction m generalizing f with
  | zero => simpa using e
  | succ m ih =>
    refine ih ?_
    refine eq_zero_of_prime_smul_eq_zero ?_
    rw [← mul_smul, ← pow_succ']
    exact e

theorem exists_comp_eq_of_kerIdeal_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q →
    kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ k _ _ G Q H m q q' f h1 h2 hk

  have hq : kerIdeal (q.app m) ≤ RingHom.ker (q'.app m : G.A m →ₐ[k] Q.A m) := by
    refine (kerIdeal_le_ker_iff (q.app m) _).2 fun c => ?_
    have e := congrArg (fun x => Hom.conv x m) h2
    simp only [pow_smul_conv] at e
    have e2 := DFunLike.congr_fun (congrArg ofConv (congrArg toPts e)) c
    rw [map_one] at e2
    refine e2.trans ?_
    rfl
  have hf := (kerIdeal_le_ker_iff (f.app m) _).1 (hk.trans hq)
  have hc : Hom.conv (q' ≫ f) m = 1 := by
    refine toPts_injective (ofConv_injective (AlgHom.ext fun c => ?_))
    rw [map_one]
    refine (hf c).trans ?_
    rfl
  obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k Q H m (q' ≫ f) hc
  refine ⟨g, sub_eq_zero.1 (hom_eq_zero_of_pow_smul_eq_zero m ?_)⟩
  rw [smul_sub, ← Linear.comp_smul, ← hg, ← Category.assoc, h1, Linear.smul_comp,
    Category.id_comp, sub_self]

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToPdivisibleOmegaSurjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem surjective_of_isCan_field : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 → ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p K) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[K] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → Function.Surjective ψ := by
  intro hH p _ K _ hp A _ g hA hg G t ψ hψ
  have hL : LieExact A :=
    GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH K A g hA hg
  have hx := GlobalTheory.T.eq_zero_of_forall_apply_hodgePrimitive_eq_zero p K 1 (by rw [pow_one]; exact hp) A hA hL G t ψ hψ
  rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
  intro x hx0
  exact hx x fun c ↦ by simpa using LinearMap.congr_fun hx0 c

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundlesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_sections_generatedBundles : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.RecSec.reciprocity_sec | exact GlobalTheory.RecSec.reciprocity_sec | (intros; apply GlobalTheory.RecSec.reciprocity_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stein_factorisation_connected_fibres : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  first | exact @GlobalTheory.SteinFact.stein_factorisation | exact GlobalTheory.SteinFact.stein_factorisation | (intros; apply GlobalTheory.SteinFact.stein_factorisation <;> assumption)
end

