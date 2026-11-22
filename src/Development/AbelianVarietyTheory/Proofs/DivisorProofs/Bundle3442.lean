import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationVectorBundleAbelianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombinationKillingFunctionsCoeffZe
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)
    simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldOfTangentVectorLinearCombina
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.InvComb

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem tv_finsum {κ : Type} (s : Finset κ) (f : κ → TanM (𝟙 (Sp R)) G) :
    tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, PullbackSections.tv_add, ih]

theorem isField_comb (g : ℕ) (e : Fin g → Fld G.left) (he : ∀ c, IsField ⊤ (e c)) (a : Fin g → R) :
    IsField ⊤ (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · have h1 := fun c => (he c).1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib]
  · have h1 := fun c => (he c).2.1 W hW f f'
    simp only [h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun c _ => by ring
  · have h1 := fun c => (he c).2.2 W W' h hW f
    simp only [h1, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← GlobalTheory.ArcPts.SecValue.res_constFn G.hom h (a c)]

theorem isInv_comb : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) →
    ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  intro R _ G _ _ g w e hw a
  refine ⟨isField_comb g e (fun c => (hw c).1) a, ?_⟩
  intro S _ φ x w' O f hx hO htr
  letI : Algebra R S := φ.toAlgebra
  have hG := GlobalTheory.Heat.CoeffWt.isGrpPullback_self G
  choose u hu using fun c => PullbackSections.push_surj hG (tv (w c))
  have hul : ∀ c, (u c).left = (tv (w c)).left := fun c =>
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) (hu c))
  have ht : ∀ c, IsTangent (u c) := fun c => (PullbackSections.isTangent_iff hG _).2 (by rw [hu c]; exact PullbackSections.tv_mem _)
  let z0 : Chart.sp (R₀ := R) S ⟶ G := Over.homMk x hx
  let z : Chart.sp (R₀ := R) (DualNumber S) ⟶ G := Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z0
  let ee : Fin g → DualNumber S := fun c => inr (φ (a c))
  have hee : ∀ i j, ee i * ee j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom x O hO
  obtain ⟨b₁, b₂⟩ := GlobalTheory.Heat.CoeffWt.valR_prod hul ht hw ee hee z O a₁ Finset.univ

  choose U hU using PullbackSections.push_surj hG (tv (∑ c, a c • w c))
  have hU' : U = ∏ c, PullbackSections.scK (a c) (u c) := by
    refine PullbackSections.push_inj hG ?_
    rw [hU, map_prod, tv_finsum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [PullbackSections.push_scK, hu c, PullbackSections.tv_smul]
  have hUl : U.left = (tv (∑ c, a c • w c)).left :=
    (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hU)
  obtain ⟨g', v', hg', hv', rfl⟩ := htr
  let ρ : Chart.sp (R₀ := R) (DualNumber S) ⟶ tEpsG (x ≫ G.hom) := Over.homMk (𝟙 _) (by
    rw [hx]
    refine (Category.id_comp _).trans ?_
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap S (DualNumber S)))).symm)
  have k₁ : ρ ≫ g' = z := Over.OverMorphism.ext ((Category.id_comp _).trans hg')
  have k₂ : ρ ≫ v' = ∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G) := by
    have k₃ : ρ ≫ v' = Chart.spMap (GlobalTheory.SqZero.dualMap (Algebra.ofId R S)) ≫ U := by
      refine Over.OverMorphism.ext ((Category.id_comp _).trans (hv'.trans ?_))
      show _ = _ ≫ U.left
      rw [hUl]
      refine congrArg (fun q : DualNumber R →+* DualNumber S => spMap q ≫ _) (RingHom.ext fun r => ?_)
      ext <;> simp [dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl
    rw [k₃, hU', comp_prodT]
    refine Finset.prod_congr rfl fun c _ => Over.OverMorphism.ext ?_
    show _ ≫ spMap (epsScaleR (a c)) ≫ (u c).left = _ ≫ (u c).left
    rw [← Category.assoc]
    refine congrArg (· ≫ (u c).left) ?_
    simp only [Chart.spMap_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [epsScaleR, GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, ee, Algebra.smul_def] <;> rfl
  have key : (g' * v').left = ((∏ c, (Chart.spMap (GlobalTheory.SqZero.epsTo R (ee c) (hee c c)) ≫ u c :
      Chart.sp (R₀ := R) (DualNumber S) ⟶ G)) * z).left := by
    rw [← k₂, ← k₁, _root_.mul_comm, ← MonObj.comp_mul]
    exact (Category.id_comp _).symm
  rw [key, b₂ f]
  have a₃ : ∀ h, valR z.left O h = inl (valR x O h) := a₂
  simp only [a₃]
  show _ = valR x O (∑ c, constFn G.hom O (a c) * e c O f)
  conv_rhs => rw [GlobalTheory.ZH.CrdCalc.valR_eq x O hO, map_sum]
  simp only [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq x O hO]
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x O hO, GlobalTheory.ArcPts.SecValue.valR_constFn G.hom φ x hx O hO]
  simp [ee, mul_comm]

end GlobalTheory.Heat.InvComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangent
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DlogBasis

section Coch

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kap (r : A) : C1 U := fun i j => constFn q (U i ⊓ U j) r

theorem rsT_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := by simp [rsT, h]

theorem resG_constFn' {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) : resG Y h (constFn q O₀ r) = constFn q O r := by
  simp only [constFn, resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  first
    | (erw [Scheme.Hom.appLE_map])
    | (simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]; rfl)

theorem rsT_add' {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg' {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mulc {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) (s : Γ(Y, O₀)) :
    rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  rw [rsT_le h, rsT_le h, map_mul, resG_constFn' q h]

theorem kap_add (r s : A) : kap q U (r + s) = kap q U r + kap q U s := by funext i j; simp [kap, constFn]

theorem kap_mul (r s : A) : kap q U (r * s) = kap q U r * kap q U s := by funext i j; simp [kap, constFn]

theorem kap_zero : kap q U 0 = 0 := by funext i j; simp [kap, constFn]

variable {q U}

theorem isCob_zero : IsCob U 0 := ⟨0, fun i j => by simp only [Pi.zero_apply]; unfold rsT; split_ifs <;> simp⟩

theorem isCob_add {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c + d) := by
  obtain ⟨b, hb⟩ := hc
  obtain ⟨b', hb'⟩ := hd
  refine ⟨b + b', fun i j => ?_⟩
  simp only [Pi.add_apply, hb, hb', rsT_add']
  ring

theorem isCob_neg {c : C1 U} (hc : IsCob U c) : IsCob U (-c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨-b, fun i j => ?_⟩
  simp only [Pi.neg_apply, hb, rsT_neg']
  ring

theorem isCob_sub {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c - d) := by simpa [sub_eq_add_neg] using isCob_add hc (isCob_neg hd)

theorem isCob_kap_mul (r : A) {c : C1 U} (hc : IsCob U c) : IsCob U (kap q U r * c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun i => constFn q (U i) r * b i, fun i j => ?_⟩
  simp only [Pi.mul_apply, hb, kap, rsT_mulc q inf_le_right, rsT_mulc q inf_le_left]
  ring

theorem isCob_sum {n : ℕ} (c : Fin n → C1 U) (hc : ∀ a, IsCob U (c a)) : IsCob U (∑ a, c a) := Finset.sum_induction _ (fun x => IsCob U x) (fun _ _ => isCob_add) isCob_zero (fun a _ => hc a)

theorem isCob_congr {c d : C1 U} (h : c = d) (hc : IsCob U c) : IsCob U d := h ▸ hc

end Coch

section Coc

theorem pbT_id {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT
  rw [dif_pos (show O ≤ 𝟙 X ⁻¹ᵁ O₀ from h)]
  simp [resG, Scheme.Hom.appLE]
  (erw [Category.id_comp]) <;> rfl

theorem dlg_res {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  have e : ∀ s : Γ(B.left, L.U i ⊓ L.U j), pbT (𝟙 _) s (L.U i ⊓ L.U j) = s := fun s => by
    rw [pbT_id s le_rfl]; simp [resG]
  simp only [dlg, e]
  rw [rsT_le hT, map_mul, ← hδ.2.2 _ _ hT le_top]
  rfl

theorem s1 : ∀ (A : Type) [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left), L.IsLB → ∀ δ : Fld B.left, IsField ⊤ δ → IsCoc L.U (fun i j => dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) := by
  intro A _ B _ _ L hL δ hδ i j k
  have h1 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j := inf_le_left
  have h2 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h3 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  dsimp only
  rw [dlg_res B L δ hδ i j h1, dlg_res B L δ hδ j k h2, dlg_res B L δ hδ i k h3, ← hL.cocycle i j k]
  generalize res h1 (L.g i j) = a
  generalize res h2 (L.g j k) = b
  simp only [Units.val_mul, mul_inv_rev, hδ.2.1 _ le_top]
  linear_combination (-(δ _ ↑b * ↑b⁻¹)) * a.mul_inv + (-(δ _ ↑a * ↑a⁻¹)) * b.mul_inv

end Coc

theorem s2 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := GlobalTheory.T.abelian_cech_h1_basis_cocycles

theorem s3 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := GlobalTheory.T.logDerivatives_coboundary_coeffs_mem_maximalIdeal

section Main

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kapH : A →+* C1 U where
  toFun := kap q U
  map_one' := by funext i j; simp [kap, constFn]
  map_mul' := kap_mul q U
  map_zero' := kap_zero q U
  map_add' := kap_add q U

theorem kapH_apply (r : A) (i j : I) : kapH q U r i j = constFn q (U i ⊓ U j) r := rfl

theorem lin_eq {n : ℕ} (c : C1 U) (cc : Fin n → A) (b : Fin n → C1 U) :
    (fun i j => c i j - ∑ a, constFn q (U i ⊓ U j) (cc a) * b a i j) = c - ∑ a, kapH q U (cc a) * b a := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem cechCochain_sum_sub_sum_constFn_eq_ringHom {n N : ℕ} (c : Fin n → A) (φ : Fin n → C1 U) (t : Fin N → A) (z : Fin N → C1 U) :
    (fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j - ∑ k, constFn q (U i ⊓ U j) (t k) * z k i j) =
      ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U (t k) * z k := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem comb_eq {n : ℕ} (φ b : Fin n → C1 U) (P : Matrix (Fin n) (Fin n) A) (c : Fin n → A) :
    ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U ((c ᵥ* P) k) * b k =
      ∑ a, kapH q U (c a) * (φ a - ∑ k, kapH q U (P a k) * b k) := by
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

end Main

open Classical in

theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  intro A _ _ _ B _ _ g L hab hsm hL hamp hK haff hfin v dd hinv hbasis c hc
  haveI := hfin
  let φ : Fin g → C1 L.U := fun a i j => dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)
  obtain ⟨b, -, hb⟩ := s2 A B g L.ι L.U hab hsm hL.cover haff
  have hφ : ∀ a, IsCoc L.U (φ a) := fun a => s1 A B L hL (dd a) (hinv a).1
  choose P hP using fun a => (hb (φ a) (hφ a)).exists
  have key : ∀ y : Fin g → A, IsCob L.U
      (∑ a, kapH B.hom L.U (y a) * φ a - ∑ k, kapH B.hom L.U ((y ᵥ* Matrix.of P) k) * b k) := by
    intro y
    rw [comb_eq]
    exact isCob_sum _ fun a => isCob_kap_mul _ (isCob_congr (lin_eq B.hom L.U (φ a) (P a) b) (hP a))
  have hmem : ∀ y : Fin g → A, (∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A) → ∀ a, y a ∈ maximalIdeal A := by
    intro y hy
    exact s3 A B g L hab hsm hL hamp hK haff hfin v dd hinv hbasis y g (y ᵥ* Matrix.of P) b hy
      (isCob_congr (cechCochain_sum_sub_sum_constFn_eq_ringHom B.hom L.U y φ (y ᵥ* Matrix.of P) b).symm (key y))
  have hdet : IsUnit (Matrix.of P).det := by
    by_contra hnd
    have h0 : IsLocalRing.residue A (Matrix.of P).det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnd))
    rw [RingHom.map_det] at h0
    obtain ⟨ybar, hy0, hyP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨y, rfl⟩ : ∃ y : Fin g → A, (fun a => IsLocalRing.residue A (y a)) = ybar :=
      ⟨fun a => (IsLocalRing.residue_surjective (ybar a)).choose,
        funext fun a => (IsLocalRing.residue_surjective (ybar a)).choose_spec⟩
    apply hy0
    funext a
    have hk : ∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A := by
      intro k
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrFun hyP k
      simpa [Matrix.vecMul, dotProduct, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    simpa [IsLocalRing.residue_eq_zero_iff] using hmem y hk a
  obtain ⟨e, he, heu⟩ := hb c hc
  refine ⟨e ᵥ* (Matrix.of P)⁻¹, ?_, ?_⟩
  · have h1 := key (e ᵥ* (Matrix.of P)⁻¹)
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one] at h1
    have h2 := isCob_sub (isCob_congr (lin_eq B.hom L.U c e b) he) h1
    exact isCob_congr (lin_eq B.hom L.U c _ φ).symm (isCob_congr (sub_sub_sub_cancel_right _ _ _) h2)
  · intro cc' hcc'
    have h3 := isCob_add (isCob_congr (lin_eq B.hom L.U c cc' φ) hcc') (key cc')
    have h4 : IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom (L.U i ⊓ L.U j) ((cc' ᵥ* Matrix.of P) a) * b a i j) :=
      isCob_congr (lin_eq B.hom L.U c _ b).symm (isCob_congr (sub_add_sub_cancel _ _ _) h3)
    have h5 := heu _ h4
    rw [← h5, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end GlobalTheory.DlogBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory

theorem isClosed_singleton_of_isFinite : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X,
    IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  intro X Z f hf x hx
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : f w = f x := (h.map f.continuous).mem_closed hx rfl
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem isFrame_chart (h : IsGrpPullback H G x ψ) (j : PUnit → (hodge G g).ι) :
    IsFrame fun i => (omegaBase h).app (LB.wchart (hodge G g) (fun _ => x) j)
      (pullbackSections x (omega G) (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit) ((j PUnit.unit).e i)) :=
  (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame _).map_iso (omegaBase h)

def gen (h : IsGrpPullback H G x ψ) {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) : LB.Gen ((hodge G g).pull x) where
  s j := (isFrame_chart h j).detUnit ha le_rfl le_top

end GlobalTheory.HodgeFrameGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValuesDetOmegaDeltaUnitAffineOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyValues_detOmega_delta_unit_affineOpens : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → IsLocallyNoetherian S →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → NzFib σ →
    (∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (ξ : Sp A ⟶ S),
      IsOpenImmersion ξ → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)] (L' : RigLB ((Over.pullback ξ).obj G)) (σ' : L'.L.Sec)
      (x : KeyIn (FractionRing A)) (y : Fin x.P.g → (epsR A ⟶ (Over.pullback ξ).obj G)),
      LBIso (L.L.pull (pullback.fst G.hom ξ)) L'.L → SmoothOfRelativeDimension x.P.g ((Over.pullback ξ).obj G).hom →
      IsOpen (abLocus ((Over.pullback ξ).obj G)) → L'.IsSymmetric → PolOnAb ((Over.pullback ξ).obj G) L'.L →
      IsLieBasis y → NzFib σ' → KeyOn (algebraMap A (FractionRing A)) x ((Over.pullback ξ).obj G) L' σ' y →
      ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u) →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsGen.keyVals | exact GlobalTheory.KeyValsGen.keyVals | (intros; apply GlobalTheory.KeyValsGen.keyVals <;> assumption)
end

